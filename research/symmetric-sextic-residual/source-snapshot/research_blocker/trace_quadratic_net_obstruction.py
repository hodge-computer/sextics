#!/usr/bin/env python3
"""Exact obstruction to a ternary quadratic net containing xy+xz+yz.

Pure Python standard library. The finite-field certificate excludes every
partition of the twelve conic-intersection roots into three quartics with
linearly dependent coefficient vectors. The accompanying proof explains why
one good completely split prime certifies nonexistence over characteristic0.
No numerical root approximation or Groebner solver is used.
"""
from pathlib import Path
from functools import lru_cache
from itertools import combinations
from math import comb, isqrt
import hashlib, json, time

HERE=Path(__file__).resolve().parent
PRIME=1459
ROOTS=(41,188,426,550,633,660,798,825,908,1032,1270,1417)


def add(*polys):
    out=[0]*max(map(len,polys),default=0)
    for p in polys:
        for i,c in enumerate(p):out[i]+=c
    while out and out[-1]==0:out.pop()
    return out


def mul(p,q):
    out=[0]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    while out and out[-1]==0:out.pop()
    return out


def power(p,n):
    result=[1]
    for _ in range(n):result=mul(result,p)
    return result


def main():
    started=time.monotonic();p=PRIME
    assert p>2 and all(p%d for d in range(2,isqrt(p)+1))
    # The homogeneous conic parametrization is
    # (x,y,z)=(u(u+v),v(u+v),-uv); here v=1.
    x,y,z=[0,1,1],[1,1],[0,-1]
    assert add(mul(x,y),mul(x,z),mul(y,z))==[]
    F=add(power(x,6),power(y,6),power(z,6))
    expected=[0]*13
    for i in range(7):expected[i]+=comb(6,i);expected[i+6]+=comb(6,i)
    expected[6]+=1
    assert F==expected==[1,6,15,20,15,6,3,6,15,20,15,6,1]
    assert len(set(ROOTS))==12 and all(0<=r<p for r in ROOTS)
    product=[1]
    for root in ROOTS:product=[c%p for c in mul(product,[-root,1])]
    assert product==[c%p for c in F]

    @lru_cache(None)
    def quartic(group):
        result=[1]
        for j in group:result=[c%p for c in mul(result,[-ROOTS[j],1])]
        assert len(result)==5 and result[-1]==1
        return tuple(result)

    witnesses=[];all_indices=set(range(12))
    for a_tail in combinations(range(1,12),3):
        A=(0,)+a_tail;rest=sorted(all_indices-set(A))
        # The block containing0 is A. Of the remaining blocks, B is the one
        # containing the smallest remaining index. Hence no partition is
        # omitted or counted twice.
        for b_tail in combinations(rest[1:],3):
            B=(rest[0],)+b_tail;C=tuple(sorted(set(rest)-set(B)))
            aa,bb,cc=map(quartic,(A,B,C))
            U=[(aa[i]-cc[i])%p for i in range(4)]
            V=[(bb[i]-cc[i])%p for i in range(4)]
            j=next(i for i in range(4) if U[i])
            candidates=[(k,(U[j]*V[k]-V[j]*U[k])%p) for k in range(4)]
            k,minor=next((k,m) for k,m in candidates if m)
            # Nonzero2-by-2 difference minor equals a3-by-3 coefficient
            # minor after using the common leading coefficient1.
            assert minor!=0
            witnesses.append([sum(1<<i for i in A),sum(1<<i for i in B),j,k,minor])
    assert len(witnesses)==comb(11,3)*comb(7,3)==5775
    certificate={'schema':'fermat6-conic-no-quartic-pencil-v1','prime':p,
        'univariate_polynomial_coefficients_ascending':F,'distinct_roots':list(ROOTS),
        'witness_columns':['A_index_bitmask','B_index_bitmask','difference_row_j','difference_row_k','nonzero_minor_mod_p'],
        'partition_minor_witnesses':witnesses,
        'third_block':'The complement of the first two bitmasks in the12 roots.'}
    path=HERE/'trace_quadratic_net_certificate.json'
    path.write_text(json.dumps(certificate,separators=(',',':'))+'\n')
    receipt={'status':'PASS','integer_conic_parametrization_checked':True,
        'integer_fermat_restriction_checked':True,'prime':p,'primality_checked':True,
        'complete_distinct_linear_factorization_checked':True,'partitions_checked':len(witnesses),
        'dependent_partitions':0,'each_partition_has_nonzero_coefficient_minor':True,
        'characteristic_zero_conclusion':'There is no subspace W of ternary quadrics of dimension at most3 containing xy+xz+yz for which x^6+y^6+z^6 lies in Sym^3(W).',
        'six_variable_application':'The actual target coefficient of X0^2 X1^2 forces (5/7)q(Y) into any Y net; swapping blocks forces (10/7)q(X). Thus the new quadratic-net theorem cannot be applied through either original block, even after arbitrary within-block coordinate changes.',
        'scope':'The reduction argument in trace_quadratic_net_obstruction.txt converts this exhaustive good-prime certificate to nonexistence over C. This is not an obstruction to all other geometric methods, to coordinate changes mixing the two blocks, or to the original certificate.',
        'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'full_original_certificate_proved':False,'seconds':time.monotonic()-started}
    (HERE/'trace_quadratic_net_obstruction_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
