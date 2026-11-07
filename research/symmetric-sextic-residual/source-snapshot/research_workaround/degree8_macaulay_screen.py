"""Exact modular homogeneous-ideal test of the degree-eight necessary quadrics.

Full column rank of a degree-d Macaulay matrix proves that the characteristic
zero homogeneous ideal contains every degree-d monomial. Thus it excludes all
nonzero complex denominator parameters, without assuming Fp rational points.
A rank deficit alone has no such consequence.
"""
from pathlib import Path
from flint import fmpq,nmod_mat
from itertools import combinations_with_replacement
import json,time,hashlib,argparse

HERE=Path(__file__).resolve().parent

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--prime',type=int,default=101)
    parser.add_argument('--degree',type=int,default=4);args=parser.parse_args()
    prime=args.prime;degree=args.degree;start=time.time()
    source=HERE/'degree8_pure_quadrics.json';data=json.loads(source.read_text())
    n=data['denominator_parameters'];polys=[]
    for row in data['pure_quadrics']:
        p={}
        for pair,s in row:
            c=fmpq(s);den=int(c.denominator)%prime
            assert den,'Prime divides an exact rational denominator'
            v=int(c.numerator)%prime*pow(den,-1,prime)%prime
            if v:p[tuple(pair)]=v
        polys.append(p)
    monomials=list(combinations_with_replacement(range(n),degree))
    positions={e:i for i,e in enumerate(monomials)}
    multipliers=list(combinations_with_replacement(range(n),degree-2))
    nrows=len(polys)*len(multipliers);ncols=len(monomials)
    print(json.dumps({'stage':'allocate','rows':nrows,'columns':ncols,'prime':prime}),flush=True)
    M=nmod_mat(nrows,ncols,prime)
    row=0;entries=0
    for polynomial in polys:
        for factor in multipliers:
            for pair,v in polynomial.items():
                col=positions[tuple(sorted(pair+factor))]
                M[row,col]=v;entries+=1
            row+=1
    print(json.dumps({'stage':'matrix_ready','nonzero_entries':entries,'seconds':time.time()-start}),flush=True)
    rank=M.rank()
    output={'status':'FULL_RANK' if rank==ncols else 'RANK_DEFICIT',
            'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'prime':prime,'macaulay_degree':degree,'matrix_rows':nrows,'matrix_columns':ncols,
            'rank':rank,'nonzero_entries':entries,'seconds':time.time()-start,
            'all_rational_denominators_units_mod_prime':True,
            'all_complex_denominators_of_tested_invariant_degree_excluded':rank==ncols,
            'full_certificate_proved':False}
    (HERE/f'degree8_macaulay_{degree}_{prime}.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output),flush=True)

if __name__=='__main__':main()
