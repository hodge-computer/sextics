#!/usr/bin/env python3
"""Compile local .rec and Markdown sources. No network access or proof acceptance."""
from fractions import Fraction
import json
import re
import sys
from pathlib import Path
import sympy as sp

from content import render
from divisors import validate_program, validate_slice_identity
import yaml
sys.path.insert(0, str(Path(__file__).resolve().parent / "proposals"))
from acceptance import exact_polynomial, read_acceptance

ROOT = Path(__file__).resolve().parents[1]
ATLAS = ROOT / 'assets/atlas'
outputs = {}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def local_path(relative, base=None):
    base = (base or ROOT).resolve()
    path = (base / relative).resolve()
    require(path.is_relative_to(base), f'Path leaves its content folder: {relative}')
    return path

def prose(path):
    text = path.read_text()
    require(text.strip() and not text.strip().startswith('<!--'), f'Missing prose: {path}')
    return text


def emit(path, text):
    outputs[path] = text

def write_output(path, text):
    if path.exists() and path.read_text() == text:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(text)
    temporary.replace(path)

def dump(path, value):
    emit(path, json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def polynomial(expression, degree):
    variables = sp.symbols('X0 X1 X2 Y0 Y1 Y2')
    value = sp.Poly(exact_polynomial(expression, variables), *variables)
    require(not value.is_zero and value.is_homogeneous and value.total_degree() == degree,
            f'Invalid homogeneous polynomial of degree {degree}')
    terms = [[str(c), list(m)] for m, c in value.terms() if c]
    return {'expression': expression, 'latex': sp.latex(value.as_expr()),
            'degree': value.total_degree(), 'termCount': len(terms), 'terms': terms}


catalogue = json.loads((ROOT / 'data/catalogue.json').read_text())
presentation = json.loads((ROOT / 'assets/atlas-presentation.json').read_text())
summaries = []
require(catalogue['schemaVersion'] == 2, 'Unsupported catalogue schema')
require(len(catalogue['instanceIds']) == len(set(catalogue['instanceIds'])), 'Duplicate instance ID')
for rid in catalogue['instanceIds']:
    require(re.fullmatch(r'[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*', rid), 'Invalid instance ID')
    folder = ROOT / 'data' / rid
    record = yaml.load((folder / 'instance.rec').read_text(), Loader=yaml.CSafeLoader)
    require(record['id'] == rid, f'{rid}: mismatched instance ID')
    require(record['q'] in (1, 2), f'{rid}: unsupported pole order')
    display = presentation[rid]
    for name, degree in (('F', 6), ('A', 6 * record['q'])):
        record[name] = {**polynomial(record[name], degree), 'latex': display[name]}
    record['category'] = display['category']
    record['displayDefinitions'] = display['definitions']
    record['render'] = json.loads((ROOT / 'slices' / f'{rid}.json').read_text())
    record['evidenceKind'] = 'none'
    record['formalStatus'] = 'unproved'
    record['content'] = {'why': f'assets/atlas/{rid}/why.html'}
    emit(ATLAS / rid / 'why.html', render(prose(local_path(record['rationale'], folder)), root=ROOT, source_path=local_path(record['rationale'], folder)))
    if (folder / 'acceptance.json').is_file():
        receipt = read_acceptance(ROOT, rid)
        record['pullRequest'] = receipt['pullRequest']
        record['formalStatus'] = 'proved'
        record['evidenceKind'] = 'existence-proof'
        if (folder / 'witness.json').is_file():
            witness = json.loads((folder / 'witness.json').read_text())
            record['D'] = polynomial(witness['D'], witness['d'])
            record['render']['divisorTerms'] = [[float(Fraction(c)), m] for c,m in record['D']['terms']]
            record['evidenceKind'] = 'explicit-certificate'
        record['leanVerification'] = {
            'formalStatus': 'proved', 'status': 'accepted',
            'proofFile': f'data/{rid}/Solution.lean', 'receipt': f'data/{rid}/acceptance.json',
            'theorem': receipt['verification']['theorem'], 'checker': receipt['verification']['leanVersion']}
        display_divisor = ROOT / 'slices/divisors' / f'{rid}.json'
        if display_divisor.is_file():
            display = validate_program(json.loads(display_divisor.read_text()), ROOT)
            if 'sliceRestriction' in display:
                require(display['sliceRestriction'] == {key: record['render'][key] for key in ('planeMatrix', 'phaseSigns')},
                        f'{rid}: display divisor belongs to a different saved section')
            if 'D' in record:
                validate_slice_identity(display, record['D'], record['render'], folder)
            else:
                require('sliceIdentity' not in display, f'{rid}: slice identity needs an explicit denominator')
            record['render']['divisorProgram'] = display
        record['credit'] = {'githubLogin': receipt['githubLogin'], 'acceptedAt': receipt['acceptedAt']}
        record['content']['solution'] = f'assets/atlas/{rid}/solution.html'
        emit(ATLAS / rid / 'solution.html', render(prose(folder / 'solution.md'), root=ROOT, source_path=folder / 'solution.md'))
    if record['formalStatus'] == 'unproved':
        require(not (ROOT / 'slices/divisors' / f'{rid}.json').exists(), f'{rid}: display divisor requires an accepted proof')
    dump(ATLAS / rid / 'record.json', record)
    summary = {k: record[k] for k in ['id', 'title', 'formalStatus', 'evidenceKind', 'category', 'q']}
    summary['path'] = f'assets/atlas/{rid}/record.json'
    if 'credit' in record:
        summary['credit'] = record['credit']
    summaries.append(summary)
home = json.loads((ROOT / 'slices/home.json').read_text())
dump(ROOT / 'assets/home-scene.json', {key: home[key] for key in ['pairId', 'seed', 'mesh', 'camera']})
dump(ATLAS / 'index.json', {'schemaVersion': 2, 'records': summaries})

doc_index = json.loads((ROOT / 'docs/index.json').read_text())
for page in doc_index['pages']:
    source = prose(local_path(page['source']))
    # The page shell supplies the title; retain all other chapter content.
    source = re.sub(r'^# [^\n]+\n', '', source, count=1)
    emit(local_path(page['content']), render(source))

if doc_index.get('overview'):
    emit(local_path(doc_index['overview']['content']), render(prose(local_path(doc_index['overview']['source']))))

# Delete only known generated exports, after every source has passed the build.
# Removing a solution must also retire its old downloadable explanation.
generated = [*ATLAS.glob('*/record.json'), *ATLAS.glob('*/why.html'), *ATLAS.glob('*/solution.html'), *ROOT.glob('docs/*.html')]
for path in generated:
    if path not in outputs:
        path.unlink()
for path, text in outputs.items():
    write_output(path, text)
print(f'Built {len(summaries)} instances, {sum("credit" in record for record in summaries)} credited constructions, and {len(doc_index["pages"])} chapters.')
