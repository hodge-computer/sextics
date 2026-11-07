#!/usr/bin/env python3
"""Exact variable permutation for the audited point-scaled cubic system.

This changes only the order of variables.  The 19 quartic coefficients are the
first elimination block.  No additional equations, open conditions or roots are
removed.  It is a solver input, not a computed basis or trace certificate.
"""
from pathlib import Path
from hashlib import sha256
import importlib.util
import json

HERE=Path(__file__).resolve().parent
SOURCE=next((HERE.parent/p for p in ('research_memory','proof_attempt6')
             if (HERE.parent/p/'point_scaled_system.json').exists()))

def main():
    spec=importlib.util.spec_from_file_location('point_scaled_system',SOURCE/'point_scaled_system.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    packet=json.loads((SOURCE/'point_scaled_system.json').read_text())
    old_names=packet['variable_order']+packet['small_open_inverse_variables']
    roots=packet['equation_nodes']+packet['small_open_equation_nodes']
    names=[n for n in old_names if n.startswith('g2_')]+[n for n in old_names if not n.startswith('g2_')]
    assert len(names)==50 and sum(n.startswith('g2_') for n in names)==19
    base={'lam':1,'r':2,'s':3};prime=37
    old_polys=module.evaluate_modular(packet,roots,old_names,prime,base)
    polys=module.evaluate_modular(packet,roots,names,prime,base)
    permutation=[old_names.index(n) for n in names]
    for before,after in zip(old_polys,polys):
        assert {tuple(e[i] for i in permutation):c for e,c in before.items()}==after
    old_text=','.join(old_names)+'\n'+str(prime)+'\n'+',\n'.join(module.poly_string(p,old_names) for p in old_polys)+'\n'
    assert old_text==(SOURCE/'point_scaled_p37_smallopens.ms').read_text()
    text=','.join(names)+'\n'+str(prime)+'\n'+',\n'.join(module.poly_string(p,names) for p in polys)+'\n'
    path=HERE/'finite_g2block_p37.ms';path.write_text(text)
    cubic_support=set()
    for p in old_polys[:44]:
        for e in p:
            if sum(e)==3:cubic_support.update(n for n,k in zip(old_names,e) if k)
    g2_indices={i for i,n in enumerate(old_names) if n.startswith('g2_')}
    assert all(sum(e[i] for i in g2_indices)<=1 for p in old_polys[:44] for e in p)
    receipt={
        'status':'EXACT_VARIABLE_PERMUTATION_VERIFIED','prime':prime,'base':base,
        'source_packet_sha256':sha256((SOURCE/'point_scaled_system.json').read_bytes()).hexdigest(),
        'source_input_sha256':sha256((SOURCE/'point_scaled_p37_smallopens.ms').read_bytes()).hexdigest(),
        'input_file':path.name,'input_sha256':sha256(path.read_bytes()).hexdigest(),
        'elimination_block':names[:19],'retained_variables':names[19:],
        'variables':len(names),'equations':len(polys),'maximum_total_degree':max(sum(e) for p in polys for e in p),
        'terms':sum(map(len,polys)),
        'contact_equations_are_linear_in_g2_block':True,
        'degree_three_contact_term_variable_support':sorted(cubic_support),
        'included_opens':list(packet['small_open_nodes']),
        'omitted_full_localization':['J44','delta9_hat','D10_hat'],
        'scope':'The exact same 50 equations over F37 with a different variable order. Excess components are possible, not proved. No finite quotient or trace has been computed.',
        'basis_verified':False,'quotient_degree_known':False,'source_trace_proved':False,
    }
    (HERE/'finite_g2block_input_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
