"""Compile untrusted Lean in an OS sandbox, then replay and audit read-only artifacts."""
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile
import time
import tomllib
import uuid

from check import command, require, strip_comments, target_source, witness_source


def lean_options(lean_root):
    """The Lake package's Lean options, as flags for modules compiled outside Lake."""
    options = tomllib.loads((lean_root/'lakefile.toml').read_text()).get('leanOptions', {})
    return [f'-D{name}={str(value).lower() if isinstance(value, bool) else value}'
            for name, value in options.items()]


def _chmod_tree_writable(root_dir):
    root_dir.chmod(0o777)
    for subdir in root_dir.rglob('*'):
        if subdir.is_dir():
            subdir.chmod(0o777)


def _has_declarations(raw):
    decls = re.sub(r'^import\s+[^\n]+', '', strip_comments(raw.decode()), flags=re.M)
    return bool(decls.strip())


def verify(root, files, instance, metadata, order, imports, policy, output, *,
           prepared=False, library_order=(), library_files=None):
    lean_root = root/'formal/lean'
    options = lean_options(lean_root)
    lake = shutil.which('lake')
    require(lake, 'Install the pinned Lean toolchain and Lake first')
    library_order = list(library_order)
    library_files = dict(library_files or {})
    if not prepared:
        preparation = [lake,'--no-cache','build','HodgeComputer.Verify',*imports]
        if platform.system() == 'Darwin':
            preparation = ['/usr/bin/sandbox-exec','-p','(version 1)(allow default)(deny network*)',*preparation]
        command(preparation,cwd=lean_root,timeout=policy['timeoutSeconds'])
    lean_path = command([lake,'env','printenv','LEAN_PATH'],cwd=lean_root).decode().strip()
    prefix = Path(command([lake,'env','lean','--print-prefix'],cwd=lean_root).decode().strip()).resolve()
    lean = prefix/'bin/lean'; checker = prefix/'bin/leanchecker'
    require(checker.is_file(), 'The pinned toolchain must include leanchecker')
    version = command([str(lean),'--version']).decode().strip()
    require('version 4.36.0,' in version, 'Wrong Lean version')
    system = platform.system()
    require(system in ('Darwin','Linux'), 'Supported verification hosts are macOS and Linux')
    if system == 'Darwin':
        require(Path('/usr/bin/sandbox-exec').is_file(), 'OS sandbox unavailable; refusing unisolated verification')
    else:
        require(shutil.which('docker'), 'Docker is required on Linux; refusing unisolated verification')
        require(os.getuid() != 0, 'Run the verifier as a non-root user')
        command(['docker','pull','ubuntu:24.04'],timeout=180)
    deadline = time.monotonic()+policy['timeoutSeconds']
    with tempfile.TemporaryDirectory(prefix='hodge-proof-') as temp:
        tmp = Path(temp).resolve(); tmp.chmod(0o755)
        sources = tmp/'source'; artifacts = tmp/'artifacts'; protected = tmp/'protected'; checked = tmp/'checked'
        (sources/'Proposal').mkdir(parents=True)
        for directory in (artifacts,protected,checked):
            directory.mkdir()
            directory.chmod(0o777)
        (artifacts/'Proposal').mkdir()
        (artifacts/'Proposal').chmod(0o777)
        lib_src = None; lib_art = None; lib_overlay = None
        if library_order:
            lib_src = tmp/'lib_source'; lib_art = tmp/'lib_artifacts'; lib_overlay = tmp/'lib_overlay'
            lib_src.mkdir(); lib_art.mkdir(); lib_overlay.mkdir()
            # Populate a read-only HodgeComputer overlay with all trusted base .olean* files
            # outside library_order so Lean 4's package-root LEAN_PATH lookup finds both
            # base HodgeComputer.* modules and freshly compiled companion modules without
            # ever exposing base .olean files to a writable sandbox directory.
            excluded_stems = {Path(*mod.split('.')).as_posix() for mod in library_order}
            base_lib_dir = lean_root / '.lake/build/lib/lean'
            for item in (base_lib_dir / 'HodgeComputer',):
                if item.is_dir():
                    for src_file in item.rglob('*'):
                        if not src_file.is_file(): continue
                        rel_posix = src_file.relative_to(base_lib_dir).as_posix()
                        if not (rel_posix.endswith('.olean') or rel_posix.endswith('.olean.private') or rel_posix.endswith('.olean.server')):
                            continue
                        stem = rel_posix.split('.olean', 1)[0]
                        if stem in excluded_stems:
                            continue
                        dst_file = lib_overlay / rel_posix
                        dst_file.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(src_file, dst_file)
            for top_file in base_lib_dir.glob('HodgeComputer.olean*'):
                if top_file.is_file():
                    shutil.copy2(top_file, lib_overlay / top_file.name)
            for mod in library_order:
                rel = Path(*mod.split('.')).with_suffix('.lean')
                src_path = lib_src / rel
                src_path.parent.mkdir(parents=True, exist_ok=True)
                src_path.write_bytes(library_files[mod])
                (lib_art / rel.parent).mkdir(parents=True, exist_ok=True)
                (lib_overlay / rel.parent).mkdir(parents=True, exist_ok=True)
            _chmod_tree_writable(lib_art)
        for name, raw in files.items():
            if name.endswith('.lean'): (sources/'Proposal'/name).write_bytes(raw)
        (sources/'HodgeTarget.lean').write_text(target_source(instance))
        has_witness = 'witness.json' in files
        if has_witness:
            (sources/'HodgeWitness.lean').write_text(witness_source(files['witness.json']))
        (sources/'HodgeChecked.lean').write_text(
            'import '+('HodgeWitness' if has_witness else 'HodgeTarget')+'\nimport Proposal.Solution\n'
            'theorem HodgeSubmission.checked : HodgeComputer.HasCertificate '
            '(n := HodgeSubmission.n) HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := '+metadata['theorem']+'\n'+
            ('theorem HodgeSubmission.checkedWitness : HodgeComputer.Verify '
             '(n := HodgeSubmission.n) HodgeSubmission.F HodgeSubmission.A HodgeSubmission.d HodgeSubmission.q '
             'HodgeWitness.D HodgeWitness.N HodgeWitness.Q := '+metadata['witnessTheorem']+'\n' if has_witness else ''))
        # Protected and checked artifacts come first so candidate library or proposal outputs
        # can never shadow HodgeTarget, HodgeWitness, or HodgeChecked. The read-only
        # lib_overlay precedes lean_path so companion Constructions modules override base builds.
        search_entries = [str(protected), str(checked)]
        if lib_overlay is not None:
            search_entries.append(str(lib_overlay))
        search_entries.extend([lean_path, str(artifacts)])
        env = {'PATH':str(prefix/'bin')+':/usr/bin:/bin','HOME':'/nonexistent','LEAN_SYSROOT':str(prefix),
               'LEAN_PATH':':'.join(search_entries),'LANG':'en_US.UTF-8'}
        mounted_dirs = [root,prefix,sources,artifacts,protected,checked]
        if lib_src is not None:
            mounted_dirs.extend([lib_src, lib_art, lib_overlay])
        def run(args, label, writable=None, workdir=None):
            cwd = workdir or sources
            remaining = int(deadline-time.monotonic())
            require(remaining > 0, 'Verification time budget exhausted')
            if system == 'Darwin':
                quote = json.dumps
                reads = [*mounted_dirs,Path('/System'),Path('/usr/lib'),Path('/usr/share'),Path('/Library/Apple/System'),Path('/dev/null'),Path('/dev/urandom')]
                profile = '(version 1)\n(deny default)\n(allow process-exec sysctl-read mach-lookup file-read-metadata)\n'
                profile += '(allow file-read* (literal "/") '+ ' '.join('(subpath '+quote(str(p))+')' for p in reads)+')\n'
                profile += '(allow file-write* (literal "/dev/null")'+(' (subpath '+quote(str(writable))+')' if writable else '')+')\n'
                command_line = ['/usr/bin/sandbox-exec','-p',profile,*args]
            else:
                container_name = 'hodge-proof-'+uuid.uuid4().hex
                command_line = ['docker','run','--rm','--name',container_name,'--network','none','--read-only','--cap-drop','ALL',
                    '--security-opt','no-new-privileges','--pids-limit','128','--memory',f'{policy["memoryMb"]}m',
                    '--cpus','2','--user',f'{os.getuid()}:{os.getgid()}',
                    '--tmpfs','/tmp:rw,noexec,nosuid,size=64m']
                for p in mounted_dirs:
                    mode = 'rw' if p == writable else 'ro'
                    command_line += ['-v',f'{p}:{p}:{mode}']
                for k,v in env.items(): command_line += ['-e',f'{k}={v}']
                command_line += ['-w',str(cwd),'ubuntu:24.04',*args]
            started = time.monotonic()
            print(f'{label}: starting', flush=True)
            try:
                with (output/f'{label}.log').open('wb') as log:
                    command(command_line,cwd=cwd,env=env,timeout=remaining,stdout=log)
            except ValueError as error:
                print(f'{label}: failed after {time.monotonic()-started:.1f}s', flush=True)
                raise ValueError(f'{label} failed; see {label}.log in the verification artifact: {error}') from error
            else:
                print(f'{label}: passed in {time.monotonic()-started:.1f}s', flush=True)
            finally:
                if system == 'Linux':
                    subprocess.run(['docker','rm','--force',container_name],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=30)
        def check_outputs(directory, rel_names):
            allowed = {f'{name.removesuffix(".lean")}{suffix}' for name in rel_names
                       for suffix in ('.olean','.olean.private','.olean.server')}
            for file in directory.rglob('*'):
                require(not file.is_symlink(), 'Symlink compiler artifact')
                if file.is_dir(): continue
                require(file.is_file() and file.relative_to(directory).as_posix() in allowed,
                        'Unexpected compiler artifact')
        protected_names = ['HodgeTarget.lean'] + (['HodgeWitness.lean'] if has_witness else [])
        for file in protected_names:
            run([str(lean),'-j','2','-M',str(policy['memoryMb']),*options,
                 '-o',str(protected/file.replace('.lean','.olean')),
                 file], 'compile-'+file.removesuffix('.lean'),protected)
        check_outputs(protected, protected_names)
        if library_order:
            for mod in library_order:
                rel = Path(*mod.split('.')).with_suffix('.lean').as_posix()
                run([str(lean),'-j','2','-M',str(policy['memoryMb']),*options,
                     '-o',str(lib_art/rel.replace('.lean','.olean')),
                     rel], 'compile-lib-'+mod, lib_art, workdir=lib_src)
                check_outputs(lib_art, [rel])
                for produced in list(lib_art.rglob('*')):
                    if produced.is_file():
                        rel_out = produced.relative_to(lib_art)
                        dst = lib_overlay / rel_out
                        dst.parent.mkdir(parents=True, exist_ok=True)
                        shutil.move(str(produced), str(dst))
        for file in order:
            relative = 'Proposal/'+file
            run([str(lean),'-j','2','-M',str(policy['memoryMb']),*options,
                 '-o',str(artifacts/relative.replace('.lean','.olean')),
                 relative], 'compile-'+file.removesuffix('.lean'),artifacts)
        check_outputs(artifacts, ['Proposal/'+f for f in order])
        run([str(lean),'-j','2','-M',str(policy['memoryMb']),*options,
             '-o',str(checked/'HodgeChecked.olean'),
             'HodgeChecked.lean'], 'compile-HodgeChecked',checked)
        check_outputs(checked, ['HodgeChecked.lean'])
        # leanchecker starts one concurrent task per matching module. A namespace
        # replay can exhaust memory on large submissions even with Docker CPU limits.
        # Use a fresh, read-only process for every module, including unused helpers.
        for mod in library_order:
            if _has_declarations(library_files[mod]):
                run([str(checker),'--verbose',mod], 'kernel-lib-'+mod)
        sequence = [*protected_names,*order,'HodgeChecked.lean']
        for file in sequence:
            stem = file.removesuffix('.lean')
            module = stem if file in protected_names or file == 'HodgeChecked.lean' else 'Proposal.'+stem
            run([str(checker),'--verbose',module], 'kernel-'+stem)
        run([str(lean),'--run',str(root/'scripts/proposals/Audit.lean'),*(['witness'] if has_witness else [])], 'theorem-audit')
        audit = json.loads((output/'theorem-audit.log').read_text())
        require(audit['theorem']=='HodgeSubmission.checked', 'Missing trusted theorem audit')
        require(audit['witnessChecked'] == has_witness, 'Missing witness binding audit')
        result = {'leanVersion':version,'kernelReplay':True,'axioms':audit['axioms'],'witnessChecked':has_witness,
                  'theorem':metadata['theorem'],'sandbox':'sandbox-exec' if system=='Darwin' else 'docker-no-network',
                  'toolchain':(lean_root/'lean-toolchain').read_text().strip()}
        if library_order:
            result['libraryModules'] = library_order
        return result
