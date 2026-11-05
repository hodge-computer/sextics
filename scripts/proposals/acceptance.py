"""Read durable acceptance records written by the trusted post-merge publisher.

This validates bindings for the content build; it does not run Lean or grant acceptance.
Solve PRs cannot write this module, acceptance records, or generated site records.
"""
import ast
import hashlib
import json
import re

import yaml

REPOSITORY = 'hodge-computer/sextics'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def require(condition, message):
    if not condition: raise ValueError(message)


def sha256(value):
    return hashlib.sha256(value).hexdigest()


def statement_hash(instance):
    return sha256(json.dumps({k:instance[k] for k in ('F','q','A')}, sort_keys=True, separators=(',',':')).encode())


def exact_polynomial(expression, variables):
    """Parse data without eval, sympify(string), or executable parser transformations."""
    import sympy as s
    names=dict(zip(('X0','X1','X2','Y0','Y1','Y2'),variables))
    def visit(node):
        if isinstance(node,ast.Constant) and type(node.value) is int: return s.Integer(node.value)
        if isinstance(node,ast.Name) and node.id in names: return names[node.id]
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub): return -visit(node.operand)
        if isinstance(node,ast.BinOp):
            if isinstance(node.op,ast.Pow):
                require(isinstance(node.right,ast.Constant) and type(node.right.value) is int and node.right.value>=0,'Invalid power')
                return visit(node.left)**node.right.value
            if isinstance(node.op,ast.Div):
                require(isinstance(node.right,ast.Constant) and type(node.right.value) is int and node.right.value>0,'Invalid denominator')
                return visit(node.left)/node.right.value
            if isinstance(node.op,ast.Add): return visit(node.left)+visit(node.right)
            if isinstance(node.op,ast.Sub): return visit(node.left)-visit(node.right)
            if isinstance(node.op,ast.Mult): return visit(node.left)*visit(node.right)
        raise ValueError('Invalid exact polynomial expression')
    return visit(ast.parse(expression,mode='eval').body)


def accepted_sources(folder):
    require(folder.is_dir() and not folder.is_symlink(), 'Invalid instance folder')
    selected = [p for p in folder.iterdir() if p.name in ('proof.json','solution.md','witness.json') or
                re.fullmatch(r'[A-Z][A-Za-z0-9_]*\.lean',p.name)]
    require(all(p.is_file() and not p.is_symlink() for p in selected), 'Invalid proof source')
    require({'proof.json','solution.md','Solution.lean'} <= {p.name for p in selected}, 'Missing proof sources')
    return {p.name:sha256(p.read_bytes()) for p in selected}


def read_acceptance(root, instance_id):
    path = root/'data'/instance_id/'acceptance.json'
    receipt = json.loads(path.read_text())
    require(receipt.get('schemaVersion') == 1 and receipt.get('formalAcceptance') is True,
            'Formal acceptance requires a trusted merged-proof receipt')
    require(receipt.get('repository') == REPOSITORY and receipt.get('instanceId') == instance_id,
            'Acceptance repository or instance mismatch')
    proof = receipt['verification']
    require(proof.get('instanceId') == instance_id and proof.get('mode') == 'live' and
            proof.get('kernelReplay') is True and proof.get('result') == 'lean-checked-awaiting-owner',
            'Acceptance requires a live protected Lean check')
    require(isinstance(proof.get('axioms'), list) and set(proof['axioms']) <= ALLOWED_AXIOMS,
            'Unapproved theorem axioms')
    require(proof.get('verifierSha256') and proof.get('sandbox') in ('sandbox-exec','docker-no-network'),
            'Missing protected verifier evidence')
    pr = receipt['pullRequest']
    require(type(pr.get('number')) is int and pr['number'] > 0 and
            pr.get('url') == f'https://github.com/{REPOSITORY}/pull/{pr["number"]}', 'Invalid accepted PR')
    for key in ('headCommit','baseCommit','mergeCommit'):
        require(isinstance(pr.get(key),str) and re.fullmatch('[0-9a-f]{40}', pr[key]), 'Invalid acceptance commit')
    require(proof['headCommit'] == pr['headCommit'] and proof['baseCommit'] == pr['baseCommit'] and
            proof['pullRequest'] == pr['number'], 'Verification does not match the merged PR')
    require(receipt['githubLogin'] == proof['githubLogin'] and
            re.fullmatch(r'[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?', receipt['githubLogin']),
            'Attribution must match the checked PR author')
    require(receipt['run']['workflowPath'] == '.github/workflows/solve-proposal.yml' and
            type(receipt['run']['id']) is int and receipt['run']['conclusion'] == 'success',
            'Missing successful protected workflow')
    instance = yaml.safe_load((root/'data'/instance_id/'instance.rec').read_text())
    require(statement_hash(instance) == proof['statementSha256'], 'Accepted target has changed')
    folder = root/'data'/instance_id
    actual = accepted_sources(folder)
    # The receipt records the original submission. Prose can be edited after
    # acceptance without changing the theorem that Lean checked.
    checked = proof['sourceHashes']
    require({n:h for n,h in actual.items() if n != 'solution.md'} ==
            {n:h for n,h in checked.items() if n != 'solution.md'},
            'Accepted proof or witness has changed')
    require((folder/'solution.md').read_text().strip(), 'Missing solution explanation')
    manifest = json.loads((folder/'proof.json').read_text())
    require(manifest['schemaVersion'] == 2 and manifest['instanceId'] == instance_id and
            manifest['theorem'] == proof['theorem'], 'Accepted theorem identity mismatch')
    require(proof.get('witnessChecked') is ('witness.json' in actual), 'Witness was not checked against Lean')
    return receipt
