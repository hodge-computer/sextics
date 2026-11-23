#!/usr/bin/env python3
"""Trusted solve-PR checks. Never merges, changes credits, or grants formal acceptance."""
import argparse
import ast
from datetime import datetime, timezone
import json
import os
from pathlib import Path, PurePosixPath
import re
import signal
import subprocess

import yaml

ROOT = Path(__file__).resolve().parents[2]
NAME = r'[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*'
ID = r'[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*'
BANNED = r'\b(?:axiom|sorry|admit|unsafe|native_decide|run_cmd|run_tac|initialize|builtin_initialize|elab|macro|syntax)\b|#(?:eval|exit)|\[\s*extern\b'
LIBRARY_PREFIX = 'formal/lean/HodgeComputer/Constructions/'
LIBRARY_MODULE_PREFIX = 'HodgeComputer.Constructions.'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def command(args, *, cwd=None, env=None, timeout=120, stdout=None):
    p = subprocess.Popen(args, cwd=cwd, env=env, stdout=stdout or subprocess.PIPE,
                         stderr=subprocess.STDOUT, start_new_session=True)
    try:
        output, _ = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.wait()
        raise ValueError('Check exceeded its time limit') from None
    if p.returncode and stdout is not None:
        stdout.flush()
        output = Path(stdout.name).read_bytes()[-4000:]
    require(p.returncode == 0, f'Command failed ({p.returncode}): {args[0]}\n{(output or b"").decode(errors="replace")[-4000:]}')
    return output or b''


def git(*args):
    return command(['git', *args], cwd=ROOT)


def object_bytes(commit, name):
    return git('show', f'{commit}:{name}')


def companion_kind(name):
    """Classify optional shared-library and book companion files allowed in a solve PR."""
    if re.fullmatch(r'formal/lean/HodgeComputer/Constructions/(?:[A-Z][A-Za-z0-9_]*/)*[A-Z][A-Za-z0-9_]*\.lean', name):
        return 'library'
    if (re.fullmatch(r'formal/lean/HodgeComputer/Constructions/(?:[A-Z][A-Za-z0-9_]*/)*README\.md', name)
            or name in ('formal/TECHNIQUES.md', 'formal/README.md')):
        return 'library_doc'
    if re.fullmatch(r'docs/[A-Za-z0-9][A-Za-z0-9._-]*\.md', name):
        return 'book_doc'
    if name == 'docs/index.json':
        return 'book_index'
    return None


def library_module_name(repo_path):
    """Map formal/lean/<Path>.lean to its Lean module name."""
    return PurePosixPath(repo_path).relative_to('formal/lean').with_suffix('').as_posix().replace('/', '.')


def validate_book_index(raw, root, companion_paths):
    index = json.loads(raw)
    require(isinstance(index, dict) and index.get('schemaVersion') == 1, 'Invalid docs/index.json schemaVersion')
    overview = index.get('overview')
    require(isinstance(overview, dict), 'docs/index.json must define overview')
    for entry in [overview, *index.get('pages', [])]:
        require(isinstance(entry, dict), 'Invalid docs/index.json entry')
        source = entry.get('source')
        content = entry.get('content')
        require(isinstance(source, str) and companion_kind(source) == 'book_doc',
                f'Invalid book source in docs/index.json: {source}')
        require(isinstance(content, str) and re.fullmatch(r'docs/[A-Za-z0-9][A-Za-z0-9._-]*\.html', content),
                f'Invalid book HTML path in docs/index.json: {content}')
        require(source in companion_paths or (root / source).is_file(),
                f'Missing book source referenced by docs/index.json: {source}')
    pages = index.get('pages')
    require(isinstance(pages, list) and pages, 'docs/index.json must list book pages')
    ids = []
    for page in pages:
        pid = page.get('id')
        require(isinstance(pid, str) and re.fullmatch(ID, pid), f'Invalid book page id: {pid}')
        ids.append(pid)
    require(len(ids) == len(set(ids)), 'Duplicate book page id in docs/index.json')


def read_proposal(base, head, author, policy):
    for commit in (base, head):
        require(re.fullmatch(r'[0-9a-f]{40}', commit), 'Use immutable full commit SHAs')
    require(re.fullmatch(r'[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?', author), 'Invalid PR author')
    merge_base = git('merge-base', base, head).decode().strip()
    # The complete tree difference, including inherited changes, must stay within
    # one new solve folder plus optional shared-library / book companion paths.
    changes = git('diff', '--name-status', '--no-renames', merge_base, head).decode().splitlines()
    require(changes, 'Empty proposal')
    solve_paths = []
    companion_paths = []
    for row in changes:
        kind, name = row.split('\t', 1)
        ckind = companion_kind(name)
        if ckind is not None:
            require(kind in ('A', 'M'),
                    'Solve PRs may only add or edit companion shared-library and book files')
            companion_paths.append(name)
            continue
        require(kind == 'A', 'Solve PRs may only add new solution files')
        path = PurePosixPath(name)
        require(len(path.parts) == 3 and path.parts[0] == 'data' and
                re.fullmatch(ID, path.parts[1]),
                'Solve PRs may only edit one existing data/<instance>/ folder plus allowed library/book companions')
        require(path.name in ('proof.json', 'solution.md', 'witness.json') or
                re.fullmatch(r'[A-Z][A-Za-z0-9_]*\.lean', path.name), 'Unexpected proposal file')
        require(path.name not in ('Target.lean', 'Checked.lean', 'Audit.lean'), 'Protected module name')
        solve_paths.append(name)
    require(solve_paths, 'Missing solution files in data/<instance>/')
    ids = {PurePosixPath(p).parts[1] for p in solve_paths}
    require(len(ids) == 1, 'Submit one instance per PR')
    rid = ids.pop()
    folder = f'data/{rid}'
    # New solves use this submission format; existing solves are maintained through repository CI.
    require(git('ls-tree', base, folder+'/instance.rec').strip(), 'Choose an existing protected instance')
    require(not git('ls-tree', base, folder+'/proof.json').strip(), 'This instance already has a merged proof')
    all_paths = solve_paths + companion_paths
    require(len(all_paths) <= policy['maxFiles'], 'Too many proposal files')
    tree_rows = git('ls-tree', head, '--', *all_paths).decode().splitlines()
    modes = {}
    for entry in tree_rows:
        meta, name = entry.split('\t', 1)
        modes[name] = meta.split()[0]
    require(set(modes) == set(all_paths), 'Every proposed file must exist in the head commit')
    for name, mode in modes.items():
        require(mode == '100644', 'Symlinks, executable files, and submodules are forbidden')
    files = {PurePosixPath(name).name: object_bytes(head, name) for name in solve_paths}
    companions = {name: object_bytes(head, name) for name in companion_paths}
    require(len(files) + len(companions) <= policy['maxFiles'], 'Too many proposal files')
    require({'proof.json', 'solution.md', 'Solution.lean'} <= files.keys(), 'Missing proof.json, solution.md, or Solution.lean')
    metadata = json.loads(files['proof.json'])
    fields = {'schemaVersion', 'instanceId', 'theorem'}
    if 'witness.json' in files: fields.add('witnessTheorem')
    require(set(metadata) == fields, 'Unexpected proposal metadata; attribution comes from GitHub')
    require(metadata['schemaVersion'] == 2 and metadata['instanceId'] == rid, 'Wrong proposal identity')
    require(isinstance(metadata['theorem'], str) and re.fullmatch(NAME, metadata['theorem']), 'Invalid theorem name')
    if 'witness.json' in files:
        require(isinstance(metadata['witnessTheorem'], str) and re.fullmatch(NAME, metadata['witnessTheorem']), 'Invalid witness theorem name')
        witness_source(files['witness.json'])
    require(files['solution.md'].decode().strip(), 'Explain the mathematical argument')
    for name, raw in companions.items():
        if companion_kind(name) in ('book_doc', 'library_doc'):
            require(raw.decode().strip(), f'Empty documentation file: {name}')
    if 'docs/index.json' in companions:
        validate_book_index(companions['docs/index.json'], ROOT, set(companions))
    instance = yaml.safe_load(object_bytes(base, f'data/{rid}/instance.rec'))
    require(instance['id'] == rid and instance['q'] in (1, 2), 'Unknown or invalid protected instance')
    return rid, metadata, files, instance, companions


def strip_comments(source):
    """Mask nested comments and strings before inspecting module headers and commands."""
    out = []; i = 0; depth = 0; string = False; line = False
    while i < len(source):
        pair = source[i:i+2]; c = source[i]
        if line:
            out.append('\n' if c == '\n' else ' '); line = c != '\n'; i += 1
        elif depth:
            if pair == '/-': depth += 1; out.append('  '); i += 2
            elif pair == '-/': depth -= 1; out.append('  '); i += 2
            else: out.append('\n' if c == '\n' else ' '); i += 1
        elif string:
            if c == '\\': out.append('  '); i += 2
            else:
                out.append('\n' if c == '\n' else ' '); i += 1
                if c == '"': string = False
        elif pair == '--': line = True; out.append('  '); i += 2
        elif pair == '/-': depth = 1; out.append('  '); i += 2
        elif c == '"': string = True; out.append(' '); i += 1
        else: out.append(c); i += 1
    require(not depth and not string, 'Unclosed Lean comment or string')
    return ''.join(out)


def parse_header_imports(label, raw, *, allow_proposal=True):
    """Validate Lean source against banned constructs and extract header imports."""
    code = strip_comments(raw.decode())
    # Ordinary declarations and tactic proofs only; executable extensions need separate review.
    require(not re.search(BANNED, code), f'{label}: executable extensions or proof placeholders are not permitted')
    local_deps = []
    ext_imports = []
    header = True
    for line in code.splitlines():
        line = line.strip()
        if not line: continue
        if line.startswith('import '):
            require(header, 'Imports must be in the module header')
            for mod in line[7:].split():
                require(re.fullmatch(NAME, mod), 'Invalid import')
                if allow_proposal and mod in ('HodgeTarget', 'HodgeWitness'):
                    continue
                if allow_proposal and mod.startswith('Proposal.'):
                    require(mod.count('.') == 1, 'Proposal helpers must be flat modules')
                    local_deps.append(mod.split('.')[1]+'.lean')
                else:
                    require(mod.startswith(('Mathlib.', 'HodgeComputer.', 'HodgeTestbed.')), 'Unreviewed import prefix')
                    ext_imports.append(mod)
        else: header = False
    return local_deps, ext_imports


def module_order(files):
    graph = {}; imports = set()
    for file, raw in files.items():
        if not file.endswith('.lean'): continue
        deps, ext = parse_header_imports(file, raw, allow_proposal=True)
        graph[file] = deps
        imports.update(ext)
    ordered = []; pending = set(graph)
    while pending:
        ready = sorted(n for n in pending if all(d in ordered for d in graph[n]))
        require(ready, 'Missing helper module or cyclic imports')
        ordered += ready; pending -= set(ready)
    return ordered, sorted(imports)


def library_module_order(root, library_files):
    """Validate companion HodgeComputer.Constructions.* modules and compute their sandbox build order."""
    if not library_files:
        return [], [], {}
    lean = root / 'formal/lean'
    base_sources = {
        p.relative_to(lean).with_suffix('').as_posix().replace('/', '.'): p
        for p in lean.rglob('*.lean')
        if '.lake' not in p.relative_to(lean).parts
    }
    base_imports = {
        name: {
            item
            for line in re.findall(r'^import\s+([^\n]+)', strip_comments(path.read_text()), re.M)
            for item in line.split()
        }
        for name, path in base_sources.items()
    }
    proposed_imports = {}
    for mod, raw in library_files.items():
        require(mod.startswith(LIBRARY_MODULE_PREFIX) and re.fullmatch(NAME, mod),
                f'Companion Lean modules must live under {LIBRARY_MODULE_PREFIX}')
        _, ext = parse_header_imports(mod, raw, allow_proposal=False)
        proposed_imports[mod] = set(ext)
    known_local = set(base_sources) | set(library_files)
    for mod, deps in proposed_imports.items():
        for dep in deps:
            if dep.startswith(('HodgeComputer.', 'HodgeTestbed.')):
                require(dep in known_local, f'{mod}: missing shared library import {dep}')
    eff_imports = dict(base_imports)
    eff_imports.update(proposed_imports)
    affected = set(library_files)
    while True:
        expanded = affected | {name for name, deps in eff_imports.items() if deps & affected}
        if expanded == affected:
            break
        affected = expanded
    require(all(m.startswith(LIBRARY_MODULE_PREFIX) for m in affected),
            'Companion library changes may not affect protected core modules')
    graph = {m: sorted(d for d in eff_imports[m] if d in affected) for m in affected}
    ordered = []; pending = set(graph)
    while pending:
        ready = sorted(n for n in pending if all(d in ordered for d in graph[n]))
        require(ready, 'Cyclic imports in shared library modules')
        ordered += ready; pending -= set(ready)
    staged = {
        m: (library_files[m] if m in library_files else base_sources[m].read_bytes())
        for m in ordered
    }
    ext_imports = sorted({d for m in ordered for d in eff_imports[m] if d not in affected})
    return ordered, ext_imports, staged


def polynomial(source):
    """Translate the trusted exact expression, without eval or symbolic code execution."""
    variables = dict(zip(('X0','X1','X2','Y0','Y1','Y2'), range(6)))
    def translate(n):
        if isinstance(n, ast.Name) and n.id in variables:
            return f'(MvPolynomial.X (R := ℂ) ({variables[n.id]} : Fin 6))'
        if isinstance(n, ast.Constant) and type(n.value) is int:
            return f'({n.value} : MvPolynomial (Fin 6) ℂ)'
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub): return f'(-{translate(n.operand)})'
        if isinstance(n, ast.BinOp):
            if isinstance(n.op, ast.Pow):
                require(isinstance(n.right, ast.Constant) and type(n.right.value) is int and n.right.value >= 0, 'Invalid polynomial power')
                return f'({translate(n.left)} ^ ({n.right.value} : ℕ))'
            if isinstance(n.op, ast.Div):
                require(isinstance(n.right, ast.Constant) and type(n.right.value) is int and n.right.value > 0, 'Only integer polynomial denominators are allowed')
                return f'({translate(n.left)} * MvPolynomial.C (σ := Fin 6) (1 / {n.right.value} : ℂ))'
            op = {ast.Add:'+', ast.Sub:'-', ast.Mult:'*'}.get(type(n.op))
            if op: return f'({translate(n.left)} {op} {translate(n.right)})'
        raise ValueError('Unsupported exact polynomial expression')
    return translate(ast.parse(source, mode='eval').body)


def target_source(instance):
    return ('import HodgeComputer.Verify\nnoncomputable section\nnamespace HodgeSubmission\n'
            'def n : ℕ := 5\ndef d : ℕ := 6\n'
            f'def F : MvPolynomial (Fin 6) ℂ := {polynomial(instance["F"])}\n'
            f'def A : MvPolynomial (Fin 6) ℂ := {polynomial(instance["A"])}\n'
            f'def q : ℕ := {instance["q"]}\nend HodgeSubmission\n')


def witness_source(raw):
    """Bind the displayed exact witness to an additional protected Lean theorem."""
    witness = json.loads(raw)
    require(set(witness) == {'D', 'N', 'Q'}, 'Witness fields must be exactly D, N, Q')
    require(isinstance(witness['N'], list) and len(witness['N']) == 6, 'A witness needs six numerators')
    expressions = [witness['D'], *witness['N'], witness['Q']]
    require(all(isinstance(value, str) and value for value in expressions), 'Witness entries must be exact polynomial expressions')
    translated = [polynomial(value) for value in expressions]
    lines = ['import HodgeTarget', 'noncomputable section', 'namespace HodgeWitness',
             f'def D : MvPolynomial (Fin 6) ℂ := {translated[0]}',
             f'def Q : MvPolynomial (Fin 6) ℂ := {translated[-1]}']
    lines += [f'def N{i} : MvPolynomial (Fin 6) ℂ := {value}' for i,value in enumerate(translated[1:-1])]
    lines += ['def N : Fin 6 → MvPolynomial (Fin 6) ℂ := fun i => ' + ''.join(f'if i.val = {i} then N{i} else ' for i in range(5)) + 'N5',
              'end HodgeWitness']
    return '\n'.join(lines)+'\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', required=True); parser.add_argument('--head', required=True)
    parser.add_argument('--author', required=True); parser.add_argument('--pr', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--structure-only', action='store_true')
    args = parser.parse_args()
    policy = json.loads((ROOT/'.github/solve-policy.json').read_text())
    require(policy['mode'] == 'live', 'Invalid submission mode')
    require(git('rev-parse','HEAD').decode().strip() == args.base, 'Run the checker from the trusted base checkout')
    rid, metadata, files, instance, companions = read_proposal(args.base,args.head,args.author,policy)
    order, proposal_imports = module_order(files)
    lib_files = {
        library_module_name(path): raw
        for path, raw in companions.items()
        if companion_kind(path) == 'library'
    }
    lib_order, lib_imports, staged_library = library_module_order(ROOT, lib_files)
    base_imports = sorted((set(proposal_imports) | set(lib_imports)) - set(lib_order))
    report = {'schemaVersion':2,'mode':policy['mode'],'instanceId':rid,'pullRequest':args.pr,
              'githubLogin':args.author,'baseCommit':args.base,'headCommit':args.head,
              'checkedAt':datetime.now(timezone.utc).isoformat()}
    if companions:
        report['companionFiles'] = sorted(companions)
    if lib_order:
        report['libraryModules'] = lib_order
    args.output.mkdir(parents=True,exist_ok=True)
    if args.structure_only:
        report['result']='structure-only'
    else:
        from sandbox import verify
        report.update(verify(ROOT,files,instance,metadata,order,base_imports,policy,args.output,
                             library_order=lib_order,library_files=staged_library))
        report['result']='lean-checked-awaiting-owner'
    (args.output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
