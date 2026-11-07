#!/usr/bin/env python3
"""Static provenance/import audit of the pinned public openai/math sources.

This is NOT a Lean kernel check.  In particular, finding no admission tokens
does not prove the transitive axiom set of a declaration.  The separate receipt
retains this limitation explicitly.

Usage:
  python3 audit_openai_foundations.py --archive SOURCE.tar.gz --index
  python3 audit_openai_foundations.py --archive SOURCE.tar.gz --extract

The archive may end after the complete lean/ subtree: papers are unnecessary.
No source is changed.  Extracted files retain the upstream path and contents.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import tarfile

HERE = Path(__file__).resolve().parent
COMMIT = '4eaee87548250b2682affda7d05d947c05554bae'
INDEX = HERE / 'external/openai_math_source_index.json'
COMPACT_INDEX = HERE / 'external/openai_foundations_closure_index.json'
ROOTS = {
    'projective_comparison':
        'OAI.AlgebraicGeometry.Comparison.Betti.Projective.SmoothIsomorphism',
    'projective_filtered_comparison':
        'OAI.AlgebraicGeometry.Comparison.Betti.Projective.FilteredImage',
    'hodge_decomposition':
        'OAI.Analysis.HodgeTheory.Decomposition.Constructions',
    'cech_algebraic_de_rham':
        'OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechHypercohomology',
    'native_poincare':
        'OAI.AlgebraicTopology.Duality.Poincare.Manifold',
    'singular_supported_cycle_restriction':
        'OAI.AlgebraicGeometry.CycleClass.Thom.Supported.AnalyticRestriction',
    'singular_supported_thom_gysin':
        'OAI.AlgebraicGeometry.CycleClass.Thom.Supported.GysinEnlargement',
}


def sha256(b):
    return hashlib.sha256(b).hexdigest()


def unquoted_code(s):
    """Remove nested Lean comments and quoted strings, preserving newlines."""
    tokens = re.compile(r'/-|-/|--|"|\\|\n')
    out = []
    pos = 0
    depth = 0
    string = False
    while pos < len(s):
        m = tokens.search(s, pos)
        if m is None:
            if not depth and not string:
                out.append(s[pos:])
            break
        if not depth and not string:
            out.append(s[pos:m.start()])
        tok = m.group()
        pos = m.end()
        if depth:
            if tok == '/-':
                depth += 1
            elif tok == '-/':
                depth -= 1
                if depth == 0:
                    out.append(' ')
            elif tok == '\n':
                out.append('\n')
        elif string:
            if tok == '\\':
                pos += 1
            elif tok == '"':
                string = False
                out.append(' ')
            elif tok == '\n':
                out.append('\n')
        elif tok == '/-':
            depth = 1
        elif tok == '--':
            end = s.find('\n', pos)
            pos = len(s) if end < 0 else end
        elif tok == '"':
            string = True
        else:
            out.append(tok)
    return ''.join(out)


def index_archive(archive):
    files, control = {}, {}
    entered = False
    finished = False
    last = ''
    with tarfile.open(archive, mode='r|gz') as tar:
        for member in tar:
            if not member.isfile():
                continue
            path = member.name.split('/', 1)[1]
            if not path.startswith('lean/'):
                if entered:
                    finished = True
                    break
                continue
            entered = True
            if not (path.endswith('.lean') or path in (
                    'lean/lean-toolchain', 'lean/lake-manifest.json',
                    'lean/README.md', 'lean/LICENSE')):
                continue
            data = tar.extractfile(member).read()
            last = path
            if not path.endswith('.lean'):
                control[path] = data.decode('utf-8')
                continue
            code = unquoted_code(data.decode('utf-8'))
            imports = []
            for match in re.finditer(
                    r'^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+([^\n\r]+)',
                    code, re.M):
                imports.extend(match.group(1).strip().split())
            flags = [
                {'token': m.group(), 'line': code.count('\n', 0, m.start()) + 1}
                for m in re.finditer(
                    r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b',
                    code)
            ]
            files[path] = {
                'sha256': sha256(data),
                'git_blob_sha1': hashlib.sha1(
                    b'blob ' + str(len(data)).encode() + b'\x00' + data).hexdigest(),
                'bytes': len(data), 'imports': imports, 'flags': flags,
            }
    assert finished, 'Archive must contain the complete lean/ subtree.'
    result = {
        'repo': 'openai/math', 'commit': COMMIT,
        'archive_complete': False,
        'lean_subtree_pass_finished': finished,
        'last_lean_entry': last,
        'files': files, 'control_files': control,
        'errors': [],
    }
    INDEX.write_text(json.dumps(result, separators=(',', ':')) + '\n')


def source_path(module):
    if module.startswith('HodgeConjecture.'):
        return ('lean/ComparatorChallenges/HodgeConjectureCMAbelianVarieties/'
                + module.replace('.', '/') + '.lean')
    return 'lean/' + module.replace('.', '/') + '.lean'


def closure(root, files):
    todo = [root]
    seen = set()
    external = set()
    while todo:
        module = todo.pop()
        path = source_path(module)
        if path in seen or module in external:
            continue
        if path not in files:
            external.add(module)
            continue
        seen.add(path)
        todo.extend(files[path]['imports'])
    return seen, external


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--archive', type=Path,
                    default=HERE / 'external/openai_math_4eaee875.tar.part')
    ap.add_argument('--index', action='store_true')
    ap.add_argument('--extract', action='store_true')
    ap.add_argument('--local-only', action='store_true',
                    help='Use the portable closure index and replay extracted source hashes/imports.')
    args = ap.parse_args()
    if args.index:
        index_archive(args.archive)
    index_path = COMPACT_INDEX if args.local_only or not INDEX.exists() else INDEX
    index = json.loads(index_path.read_text())
    assert index['commit'] == COMMIT and index['lean_subtree_pass_finished']
    files = index['files']
    all_sources, all_external = set(), set()
    roots = {}
    for label, root in ROOTS.items():
        paths, external = closure(root, files)
        assert source_path(root) in paths
        all_sources |= paths
        all_external |= external
        roots[label] = {
            'module': root, 'source_files': len(paths),
            'source_bytes': sum(files[p]['bytes'] for p in paths),
            'external_imports': sorted(external),
            'flagged_sources': {p: files[p]['flags'] for p in sorted(paths)
                                if files[p]['flags']},
        }
    receipt = {
        'status': 'STATIC_SOURCE_AUDIT_ONLY',
        'repo': 'https://github.com/openai/math', 'commit': COMMIT,
        'toolchain': index['control_files']['lean/lean-toolchain'].strip(),
        'mathlib_rev': next(p['rev'] for p in json.loads(
            index['control_files']['lean/lake-manifest.json'])['packages']
                           if p['name'] == 'mathlib'),
        'source_index_sha256': index.get('full_source_index_sha256',
                                        sha256(index_path.read_bytes())),
        'roots': roots,
        'union_source_files': len(all_sources),
        'union_source_bytes': sum(files[p]['bytes'] for p in all_sources),
        'union_external_imports': sorted(all_external),
        'union_flagged_sources': {p: files[p]['flags'] for p in sorted(all_sources)
                                  if files[p]['flags']},
        'source_manifest': {p: {k: files[p][k] for k in
                                ('sha256', 'git_blob_sha1', 'bytes')}
                            for p in sorted(all_sources)},
        'kernel_replayed': False,
        'full_primitive_or_GF_proved': False,
        'limitation': 'Lexical source audit does not establish a theorem axiom set; '
                      'kernel compilation and #print axioms are still required.',
    }
    target = HERE / 'openai_foundations_static_receipt.json'
    target.write_text(json.dumps(receipt, indent=2) + '\n')
    if args.extract:
        dest = HERE / 'external/openai_math_foundations'
        remaining = set(all_sources)
        controls = {'lean/lean-toolchain', 'lean/lakefile.lean',
                    'lean/lake-manifest.json', 'lean/README.md', 'lean/LICENSE', 'LICENSE'}
        with tarfile.open(args.archive, mode='r|gz') as tar:
            for member in tar:
                if not member.isfile():
                    continue
                path = member.name.split('/', 1)[1]
                if path not in remaining and path not in controls:
                    continue
                data = tar.extractfile(member).read()
                if path in remaining:
                    assert sha256(data) == files[path]['sha256']
                    remaining.remove(path)
                controls.discard(path)
                output = dest / path
                assert '..' not in Path(path).parts
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_bytes(data)
                if not remaining and not controls:
                    break
        assert not remaining and not controls
    local_root = HERE / 'external/openai_math_foundations'
    portable_archive = HERE / 'openai_foundations_sources.tar.gz'
    if args.local_only and not local_root.exists() and portable_archive.exists():
        wanted = set(all_sources)
        controls = {'LICENSE', 'lean/LICENSE', 'lean/lean-toolchain',
                    'lean/lakefile.lean', 'lean/lake-manifest.json', 'lean/README.md'}
        with tarfile.open(portable_archive, mode='r:gz') as tar:
            for member in tar:
                path = member.name
                if not member.isfile() or path not in wanted | controls:
                    continue
                assert not Path(path).is_absolute() and '..' not in Path(path).parts
                data = tar.extractfile(member).read()
                if path in wanted:
                    assert sha256(data) == files[path]['sha256'], path
                    wanted.remove(path)
                controls.discard(path)
                output = local_root / path
                output.parent.mkdir(parents=True, exist_ok=True)
                output.write_bytes(data)
        assert not wanted and not controls
    if args.local_only or local_root.exists():
        checked = 0
        for path in sorted(all_sources):
            data = (local_root / path).read_bytes()
            assert sha256(data) == files[path]['sha256'], path
            code = unquoted_code(data.decode('utf-8'))
            actual_imports = []
            for match in re.finditer(
                    r'^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+([^\n\r]+)',
                    code, re.M):
                actual_imports.extend(match.group(1).strip().split())
            assert actual_imports == files[path]['imports'], path
            actual_flags = [
                {'token': m.group(), 'line': code.count('\n', 0, m.start()) + 1}
                for m in re.finditer(
                    r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b',
                    code)
            ]
            assert actual_flags == files[path]['flags'], path
            checked += 1
        replay = {
            'status': 'PASS_STATIC_LOCAL_REPLAY', 'commit': COMMIT,
            'source_files_rehashed_and_reparsed': checked,
            'all_local_dependencies_present': not any(
                m.startswith(('OAI.', 'HodgeConjecture.')) for m in all_external),
            'external_roots': sorted({m.split('.')[0] for m in all_external}),
            'static_receipt_sha256': sha256(target.read_bytes()),
            'kernel_replayed': False, 'full_primitive_or_GF_proved': False,
        }
        assert replay['all_local_dependencies_present']
        (HERE / 'openai_local_source_replay.json').write_text(
            json.dumps(replay, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k not in
                      ('source_manifest', 'union_external_imports', 'roots')}, indent=2))
    print(json.dumps({k: {'files': v['source_files'], 'bytes': v['source_bytes'],
                         'external': len(v['external_imports']),
                         'flagged': len(v['flagged_sources'])}
                      for k, v in roots.items()}, indent=2))


if __name__ == '__main__':
    main()
