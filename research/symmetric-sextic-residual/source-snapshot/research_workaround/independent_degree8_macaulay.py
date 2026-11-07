#!/usr/bin/env python3
"""Reconstruct the Macaulay map with exponent vectors and a second prime.

The matrix is transposed relative to the original script. Variables are
permuted, columns run multiplier-first, and coefficients are accumulated.
No construction routine from the original script is imported.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/"python_deps"))
from flint import nmod_mat


def exponents(n,d):
    if n==1:
        yield (d,)
    else:
        for e in range(d+1):
            for tail in exponents(n-1,d-e):
                yield (e,)+tail


def main():
    started=time.time()
    prime=int(sys.argv[1]) if len(sys.argv)>1 else 103
    source=HERE/"degree8_pure_quadrics.json"
    data=json.loads(source.read_text())
    n=data["denominator_parameters"]
    permutation=[(5*i+7)%n for i in range(n)]
    assert sorted(permutation)==list(range(n))
    quadrics=[]
    for row in reversed(data["pure_quadrics"]):
        polynomial={}
        for pair,value in row:
            c=Fraction(value)
            assert c.denominator%prime, "Prime divides a rational denominator"
            exponent=[0]*n
            for i in pair: exponent[permutation[i]]+=1
            k=tuple(exponent)
            polynomial[k]=(polynomial.get(k,0)+c.numerator*pow(c.denominator,-1,prime))%prime
        quadrics.append({e:c for e,c in polynomial.items() if c})
    targets=list(exponents(n,4))
    factors=list(exponents(n,2))
    positions={e:i for i,e in enumerate(targets)}
    M=nmod_mat(len(targets),len(factors)*len(quadrics),prime)
    entries=0
    column=0
    for factor in factors:
        for q in quadrics:
            for exponent,c in q.items():
                row=positions[tuple(a+b for a,b in zip(exponent,factor))]
                M[row,column]=(int(M[row,column])+c)%prime
                entries+=1
            column+=1
    print(json.dumps({"stage":"constructed","rows":M.nrows(),"columns":M.ncols(),"prime":prime}),flush=True)
    rank=M.rank()
    receipt={"status":"PASS" if rank==len(targets) else "RANK_DEFICIT",
        "prime":prime,"matrix_rows":M.nrows(),"matrix_columns":M.ncols(),"rank":rank,
        "nonzero_entries":entries,"degree":4,"denominator_parameters":n,
        "quadrics":len(quadrics),"variable_permutation":permutation,
        "construction":"Exponent vectors, permuted variables, reversed quadrics, multiplier-first columns, transposed matrix, coefficient accumulation.",
        "all_rational_denominators_units_mod_prime":True,
        "source_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
        "seconds":time.time()-started,
        "scope":"Exact CAS rank. Conditional on these rational quadrics being necessary consequences of the complete certificate equations, full rank excludes all nonzero characteristic-zero denominator parameter points. Not a Lean theorem or a certificate."}
    (HERE/f"independent_degree8_macaulay_{prime}.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt),flush=True)


if __name__=="__main__":main()
