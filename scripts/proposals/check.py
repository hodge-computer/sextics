#!/usr/bin/env python3
"""Trusted solve-PR checks. Never merges, changes credits, or grants formal acceptance."""
import argparse
import ast
from datetime import datetime, timezone
import hashlib
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


def read_proposal(base, head, author, policy):
    for commit in (base, head):
        require(re.fullmatch(r'[0-9a-f]{40}', commit), 'Use immutable full commit SHAs')
    require(re.fullmatch(r'[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?', author), 'Invalid PR author')
    merge_base = git('merge-base', base, head).decode().strip()
    # The complete tree difference, including inherited changes, must be confined to the proposal.
    changes = git('diff', '--name-status', '--no-renames', merge_base, head).decode().splitlines()
    require(changes, 'Empty proposal')
    paths = []
    for row in changes:
        kind, name = row.split('\t', 1)
        require(kind == 'A', 'Solve PRs may only add new solution files')
        path = PurePosixPath(name)
        require(len(path.parts) == 3 and path.parts[0] == 'data' and
                re.fullmatch(ID, path.parts[1]), 'Solve PRs may only edit one existing data/<instance>/ folder')
        require(path.name in ('proof.json', 'solution.md', 'witness.json') or
                re.fullmatch(r'[A-Z][A-Za-z0-9_]*\.lean', path.name), 'Unexpected proposal file')
        require(path.name not in ('Target.lean', 'Checked.lean', 'Audit.lean'), 'Protected module name')
        paths.append(name)
    ids = {PurePosixPath(p).parts[1] for p in paths}
    require(len(ids) == 1, 'Submit one instance per PR')
    rid = ids.pop()
    folder = f'data/{rid}'
    # A solve proposal is immutable once merged; revisions need an explicitly reviewed new format.
    require(git('ls-tree', base, folder+'/instance.rec').strip(), 'Choose an existing protected instance')
    require(not git('ls-tree', base, folder+'/proof.json').strip(), 'This instance already has a merged proof')
    # Rebase if the PR carries changes to protected data that were not part of its own diff.
    require(not git('diff', '--name-only', merge_base, head, '--', '.', f':(exclude){folder}').strip(),
            'Protected files changed')
    entries = [row for row in git('ls-tree', '-r', head, folder).decode().splitlines() if row.split('\t',1)[1] in paths]
    require(len(entries) <= policy['maxFiles'], 'Too many proposal files')
    files = {}
    total = 0
    for entry in entries:
        meta, name = entry.split('\t', 1)
        require(meta.split()[0] == '100644', 'Symlinks, executable files, and submodules are forbidden')
        require(name in paths, 'Every proposed file must be part of this PR')
        total += int(git('cat-file', '-s', f'{head}:{name}'))
        require(total <= policy['maxBytes'], 'Proposal too large')
        files[PurePosixPath(name).name] = object_bytes(head, name)
    require(len(files) <= policy['maxFiles'] and sum(map(len, files.values())) <= policy['maxBytes'], 'Proposal too large')
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
    instance = yaml.safe_load(object_bytes(base, f'data/{rid}/instance.rec'))
    require(instance['id'] == rid and instance['q'] in (1, 2), 'Unknown or invalid protected instance')
    return rid, metadata, files, instance


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


def module_order(files):
    graph = {}; imports = set()
    for file, raw in files.items():
        if not file.endswith('.lean'): continue
        code = strip_comments(raw.decode())
        # This format accepts ordinary declarations and tactic proofs; custom executable extensions need review.
        banned = r'\b(?:axiom|sorry|admit|unsafe|native_decide|run_cmd|run_tac|initialize|builtin_initialize|elab|macro|syntax)\b|#(?:eval|exit)|\[\s*extern\b'
        require(not re.search(banned, code), f'{file}: executable extensions or proof placeholders are not permitted')
        deps = []
        header = True
        for line in code.splitlines():
            line = line.strip()
            if not line: continue
            if line.startswith('import '):
                require(header, 'Imports must be in the module header')
                for mod in line[7:].split():
                    require(re.fullmatch(NAME, mod), 'Invalid import')
                    if mod in ('HodgeTarget', 'HodgeWitness'):
                        continue
                    if mod.startswith('Proposal.'):
                        require(mod.count('.') == 1, 'Proposal helpers must be flat modules')
                        deps.append(mod.split('.')[1]+'.lean')
                    else:
                        require(mod.startswith(('Mathlib.', 'HodgeComputer.', 'HodgeTestbed.')), 'Unreviewed import prefix')
                        imports.add(mod)
            else: header = False
        graph[file] = deps
    ordered = []; pending = set(graph)
    while pending:
        ready = sorted(n for n in pending if all(d in ordered for d in graph[n]))
        require(ready, 'Missing helper module or cyclic imports')
        ordered += ready; pending -= set(ready)
    return ordered, sorted(imports)


def polynomial(source):
    """Translate the trusted exact expression, without eval or symbolic code execution."""
    variables = dict(zip(('X0','X1','X2','Y0','Y1','Y2'), range(6)))
    def translate(n):
        if isinstance(n, ast.Name) and n.id in variables:
            return f'(MvPolynomial.X (R := ℂ) ({variables[n.id]} : Fin 6))'
        if isinstance(n, ast.Constant) and type(n.value) is int:
            return f'({n.value} : HodgeComputer.Poly)'
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
            f'def F : HodgeComputer.Poly := {polynomial(instance["F"])}\n'
            f'def A : HodgeComputer.Poly := {polynomial(instance["A"])}\n'
            f'def q : ℕ := {instance["q"]}\nend HodgeSubmission\n')


def witness_source(raw):
    """Bind the displayed exact witness to an additional protected Lean theorem."""
    witness = json.loads(raw)
    require(set(witness) == {'d', 'D', 'N', 'Q'}, 'Witness fields must be exactly d, D, N, Q')
    require(type(witness['d']) is int and witness['d'] >= 0, 'Invalid denominator degree')
    require(isinstance(witness['N'], list) and len(witness['N']) == 6, 'A witness needs six numerators')
    expressions = [witness['D'], *witness['N'], witness['Q']]
    require(all(isinstance(value, str) and value for value in expressions), 'Witness entries must be exact polynomial expressions')
    translated = [polynomial(value) for value in expressions]
    lines = ['import HodgeTarget', 'noncomputable section', 'namespace HodgeWitness',
             f'def d : ℕ := {witness["d"]}', f'def D : HodgeComputer.Poly := {translated[0]}',
             f'def Q : HodgeComputer.Poly := {translated[-1]}']
    lines += [f'def N{i} : HodgeComputer.Poly := {value}' for i,value in enumerate(translated[1:-1])]
    lines += ['def N : Fin 6 → HodgeComputer.Poly := fun i => ' + ''.join(f'if i.val = {i} then N{i} else ' for i in range(5)) + 'N5',
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
    rid, metadata, files, instance = read_proposal(args.base,args.head,args.author,policy)
    order, imports = module_order(files)
    report = {'schemaVersion':2,'mode':policy['mode'],'instanceId':rid,'pullRequest':args.pr,
              'githubLogin':args.author,'baseCommit':args.base,'headCommit':args.head,
              'checkedAt':datetime.now(timezone.utc).isoformat(),'formalAcceptance':False,
              'verifierSha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in [Path(__file__),ROOT/'scripts/proposals/sandbox.py',ROOT/'scripts/proposals/Audit.lean',
                            ROOT/'formal/lean/HodgeComputer/Verify.lean',ROOT/'formal/lean/lake-manifest.json',ROOT/'.github/solve-policy.json',ROOT/'.github/workflows/solve-proposal.yml']},
              'statementSha256':hashlib.sha256(json.dumps({k:instance[k] for k in ('F','q','A')},sort_keys=True,separators=(',',':')).encode()).hexdigest(),
              'sourceHashes':{n:hashlib.sha256(b).hexdigest() for n,b in files.items()}}
    args.output.mkdir(parents=True,exist_ok=True)
    if args.structure_only:
        report['result']='structure-only'
    else:
        from sandbox import verify
        report.update(verify(ROOT,files,instance,metadata,order,imports,policy,args.output))
        report['result']='lean-checked-awaiting-owner'
    (args.output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
