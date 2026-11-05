"""Compile untrusted Lean in an OS sandbox, then replay and audit read-only artifacts."""
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import time
import uuid

from check import command, require, target_source, witness_source


def verify(root, files, instance, metadata, order, imports, policy, output, *, prepared=False):
    lean_root = root/'formal/lean'
    lake = shutil.which('lake')
    require(lake, 'Install the pinned Lean toolchain and Lake first')
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
    require('version 4.33.1,' in version, 'Wrong Lean version')
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
        for name, raw in files.items():
            if name.endswith('.lean'): (sources/'Proposal'/name).write_bytes(raw)
        (sources/'HodgeTarget.lean').write_text(target_source(instance))
        has_witness = 'witness.json' in files
        if has_witness:
            (sources/'HodgeWitness.lean').write_text(witness_source(files['witness.json']))
        (sources/'HodgeChecked.lean').write_text(
            'import '+('HodgeWitness' if has_witness else 'HodgeTarget')+'\nimport Proposal.Solution\n'
            'theorem HodgeSubmission.checked : HodgeComputer.HasCertificate '
            'HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := '+metadata['theorem']+'\n'+
            ('theorem HodgeSubmission.checkedWitness : HodgeComputer.Verify '
             '(n := HodgeSubmission.n) HodgeSubmission.F HodgeSubmission.A HodgeSubmission.d HodgeSubmission.q '
             'HodgeWitness.D HodgeWitness.N HodgeWitness.Q := '+metadata['witnessTheorem']+'\n' if has_witness else ''))
        env = {'PATH':str(prefix/'bin')+':/usr/bin:/bin','HOME':'/nonexistent','LEAN_SYSROOT':str(prefix),
               'LEAN_PATH':lean_path+':'+':'.join(map(str,(protected,checked,artifacts))),'LANG':'en_US.UTF-8'}
        def run(args, label, writable=None):
            remaining = int(deadline-time.monotonic())
            require(remaining > 0, 'Verification time budget exhausted')
            if system == 'Darwin':
                quote = json.dumps
                reads = [root,prefix,sources,artifacts,protected,checked,Path('/System'),Path('/usr/lib'),Path('/usr/share'),Path('/Library/Apple/System'),Path('/dev/null'),Path('/dev/urandom')]
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
                for p in (root,prefix,sources,artifacts,protected,checked):
                    mode = 'rw' if p == writable else 'ro'
                    command_line += ['-v',f'{p}:{p}:{mode}']
                for k,v in env.items(): command_line += ['-e',f'{k}={v}']
                command_line += ['-w',str(sources),'ubuntu:24.04',*args]
            started = time.monotonic()
            print(f'{label}: starting', flush=True)
            try:
                with (output/f'{label}.log').open('wb') as log:
                    command(command_line,cwd=sources,env=env,timeout=remaining,stdout=log)
            except ValueError as error:
                print(f'{label}: failed after {time.monotonic()-started:.1f}s', flush=True)
                raise ValueError(f'{label} failed; see {label}.log in the verification artifact: {error}') from error
            else:
                print(f'{label}: passed in {time.monotonic()-started:.1f}s', flush=True)
            finally:
                if system == 'Linux':
                    subprocess.run(['docker','rm','--force',container_name],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=30)
        protected_names = ['HodgeTarget.lean'] + (['HodgeWitness.lean'] if has_witness else [])
        sequence = [*protected_names,*order,'HodgeChecked.lean']
        for file in sequence:
            destination = protected if file in protected_names else checked if file=='HodgeChecked.lean' else artifacts
            relative = 'Proposal/'+file if destination==artifacts else file
            run([str(lean),'-j','2','-M',str(policy['memoryMb']),'-o',str(destination/relative.replace('.lean','.olean')),
                 relative], 'compile-'+file.removesuffix('.lean'),destination)
        # Reject compiler outputs that could shadow a protected module or load native code.
        for directory,names in ((protected,protected_names),(checked,['HodgeChecked.lean']),(artifacts,['Proposal/'+f for f in order])):
            allowed={f'{name.removesuffix(".lean")}{suffix}' for name in names
                     for suffix in ('.olean','.olean.private','.olean.server')}
            for file in directory.rglob('*'):
                require(not file.is_symlink(), 'Symlink compiler artifact')
                if file.is_dir(): continue
                require(file.is_file() and str(file.relative_to(directory)) in allowed,
                        'Unexpected compiler artifact')
        # leanchecker starts one concurrent task per matching module. A namespace
        # replay can exhaust memory on large submissions even with Docker CPU limits.
        # Use a fresh, read-only process for every module, including unused helpers.
        for file in sequence:
            stem = file.removesuffix('.lean')
            module = stem if file in protected_names or file == 'HodgeChecked.lean' else 'Proposal.'+stem
            run([str(checker),'--verbose',module], 'kernel-'+stem)
        run([str(lean),'--run',str(root/'scripts/proposals/Audit.lean'),*(['witness'] if has_witness else [])], 'theorem-audit')
        audit = json.loads((output/'theorem-audit.log').read_text())
        require(audit['theorem']=='HodgeSubmission.checked', 'Missing trusted theorem audit')
        require(audit['witnessChecked'] == has_witness, 'Missing witness binding audit')
        return {'leanVersion':version,'kernelReplay':True,'axioms':audit['axioms'],'witnessChecked':has_witness,
                'theorem':metadata['theorem'],'sandbox':'sandbox-exec' if system=='Darwin' else 'docker-no-network',
                'toolchain':(lean_root/'lean-toolchain').read_text().strip()}
