#!/usr/bin/env python3
"""Exact semantic audit using an independent sparse polynomial engine.

SymPy's polynomial ring performs all multiplication, differentiation, and
division.  The variables are reordered so ordinary lexicographic division
uses the r^2 term of G.  FLINT is used only for rational linear algebra.
The large intermediate second-equation RREF JSON is deliberately not loaded:
we reconstruct the raw equations and eliminate mixed terms directly.
"""
from pathlib import Path
from itertools import product, permutations
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/"python_deps"))
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
from flint import fmpq, fmpq_mat

# Internal order is r,p,q,P,Q,R; external packets use p,q,r,P,Q,R.
S,r,p,q,P,Q,R=ring("r,p,q,P,Q,R",QQ)
variables=(p,q,r,P,Q,R)
weights=(1,2,3,1,2,3)


def inward(e):return (e[2],e[0],e[1],e[3],e[4],e[5])
def outward(e):return (e[1],e[2],e[0],e[3],e[4],e[5])
def decode(entries):return S.from_dict({inward(e):QQ(c) for e,c in entries})


def monomials(degree,parity):
    return [e for e in product(*(range(degree//w+1) for w in weights))
            if sum(i*w for i,w in zip(e,weights))==degree and (e[3]+e[5])%2==parity]


def monomial(e):return S.from_dict({inward(e):QQ.one})
def act(v,f):return sum((a*f.diff(t) for a,t in zip(v,variables)),S.zero)


def disc(a,b,c):return a*a*b*b-4*b**3-4*a**3*c-27*c*c+18*a*b*c


def determinant3(M):
    value=S.zero
    for sigma in permutations(range(3)):
        sign=(-1)**sum(sigma[i]>sigma[j] for i in range(3) for j in range(i+1,3))
        value+=sign*M[0][sigma[0]]*M[1][sigma[1]]*M[2][sigma[2]]
    return value


def matrix(columns):
    rows=sorted(set().union(*(f.keys() for f in columns)))
    return rows,fmpq_mat([[f.get(e,0) for f in columns] for e in rows])


def matrix_rank(M):return M.rank()


def assert_degrees(f,degree,parity):
    for e in f:
        e=outward(e)
        assert sum(a*w for a,w in zip(e,weights))==degree
        assert (e[3]+e[5])%2==parity


def main():
    start=time.time()
    first_path=HERE/"degree8_exact_first_equation.json"
    pure_path=HERE/"degree8_pure_quadrics.json"
    first=json.loads(first_path.read_text())
    pure_packet=json.loads(pure_path.read_text())
    assert first["degree"]==8
    def newton(a,b,c):return a**6-6*a**4*b+9*a*a*b*b-2*b**3+6*a**3*c-12*a*b*c+3*c*c
    G=7*(newton(p,q,r)+newton(P,Q,R))+5*q*q*Q+10*q*Q*Q
    A=r*R
    assert G==decode(first["F"]) and A==decode(first["A"])
    local=[]
    for a,b,c in ((p,q,r),(P,Q,R)):
        local.append(((S(3),2*a,b),(a,2*b,3*c),(a*a-2*b,a*b-3*c,a*c)))
    local_div=((S.zero,S(3),2*p),(S.zero,S(3),2*P))
    basis=[]; divs=[]; descriptors=[]
    for block in range(2):
        for k in range(3):
            vk=[S.zero]*6
            vk[3*block:3*block+3]=local[block][k]
            for e in monomials(9-k,1 if block==0 else k%2):
                m=monomial(e)
                basis.append([m*a for a in vk])
                divs.append(act(vk,m)+m*local_div[block][k])
                descriptors.append({"block":block,"power":k,"exponent":list(e)})
    assert descriptors==first["numerator_basis"]
    dmons=monomials(8,0)
    DB=[monomial(e) for e in dmons]
    first_rows,Fmatrix=matrix([act(v,G) for v in basis]+[-A*d for d in DB])
    first_rank=matrix_rank(Fmatrix)
    assert (len(basis),len(DB),len(first_rows),first_rank)==(324,64,322,318)
    delta=disc(p,q,r)*disc(P,Q,R)
    E=[[[local[b][k][j] for k in range(3)] for j in range(3)] for b in range(2)]
    E_det=[determinant3(e) for e in E]

    def check_field(D,v,div):
        assert_degrees(D,8,0)
        assert act(v,G)==A*D
        assert 2*delta*(sum((a.diff(t) for a,t in zip(v,variables)),S.zero)-div)-act(v,delta)==0
        coefficients=[]
        for block in range(2):
            for k in range(3):
                M=[row.copy() for row in E[block]]
                for j in range(3):M[j][k]=v[3*block+j]
                f,remainder=determinant3(M).div(E_det[block])
                assert remainder==0
                assert_degrees(f,9-k,1 if block==0 else k%2)
                coefficients.extend(f.get(inward(e),0) for e in monomials(9-k,1 if block==0 else k%2))
        assert len(coefficients)==len(basis)
        assert all(sum((c*b[j] for c,b in zip(coefficients,basis)),S.zero)==v[j] for j in range(6))
        assert sum((c*b for c,b in zip(coefficients,divs)),S.zero)==div
        return (D,v,div,coefficients)

    kernels=[check_field(S.zero,[decode(f) for f in k["field"]],decode(k["div"])) for k in first["kernelN"]]
    eligible=[check_field(decode(k["D"]),[decode(f) for f in k["field"]],decode(k["div"])) for k in first["eligible"]]
    assert len(kernels)==48 and len(eligible)==18
    gauges=[]
    for e in monomials(2,0):
        B=monomial(e)
        gauges.append(check_field(B*G,[QQ(w,6)*A*B*t for w,t in zip(weights,variables)],QQ(14,6)*A*B))
    assert len(gauges)==4
    solutions=kernels+eligible+gauges
    vectors=[k[3]+[k[0].get(inward(e),0) for e in dmons] for k in solutions]
    V=fmpq_mat([[v[j] for v in vectors] for j in range(388)])
    assert matrix_rank(V)==70==Fmatrix.ncols()-first_rank
    assert Fmatrix*V==fmpq_mat(322,70)
    assert matrix_rank(matrix([k[0] for k in eligible+gauges])[1])==22
    assert all(not D or max(e[0] for e in D)<2 for D,_,_,_ in eligible)
    print(json.dumps({"stage":"first_equation_audited","rank":first_rank,"complete_kernel":70,"seconds":time.time()-start}),flush=True)

    # Directly order every mixed column before every pure quadratic column.
    # This independently eliminates nuisance terms without the 96 MB RREF.
    def bilinear(D,N):return (D*N[2]-act(N[1],D)).rem(G)
    columns=[]
    for D,_,_,_ in eligible:
        for N in kernels:columns.append(bilinear(D,N))
    mixed_count=len(columns)
    pairs=[]
    for i,N in enumerate(eligible):
        for j in range(i,len(eligible)):
            c=bilinear(N[0],eligible[j])
            if i!=j:c+=bilinear(eligible[j][0],N)
            columns.append(c);pairs.append((i,j))
    second_rows,M=matrix(columns)
    assert (len(second_rows),M.ncols(),mixed_count)==(435,1035,864)
    print(json.dumps({"stage":"raw_second_matrix","rows":435,"columns":1035,"seconds":time.time()-start}),flush=True)
    rr,second_rank=M.rref()
    reconstructed=[];mixed_rank=0
    for i in range(second_rank):
        if any(rr[i,j] for j in range(mixed_count)):
            mixed_rank+=1
        else:
            reconstructed.append([[list(pair),str(rr[i,mixed_count+j])] for j,pair in enumerate(pairs) if rr[i,mixed_count+j]])
    assert (second_rank,mixed_rank,len(reconstructed))==(435,391,44)
    assert reconstructed==pure_packet["pure_quadrics"]

    # Check the algebra behind the higher-degree denominator gauge on a
    # generating set. B need not be constant when d=8.
    gauge_checks=0
    for B in (monomial(e) for e in monomials(2,0)):
        correction=[QQ(w,6)*A*B*t for w,t in zip(weights,variables)]
        correction_div=QQ(14,6)*A*B
        for D,N,div,_ in eligible:
            D1=D+B*G
            N1=[v+w for v,w in zip(N,correction)]
            actual=D1*(div+correction_div)-act(N1,D1)
            expected=D*div-act(N,D)+G*(B*div-act(N,B)+A*B*B)
            assert actual==expected
            gauge_checks+=1

    receipt={"status":"PASS","method":"Independent SymPy sparse polynomial arithmetic, lex order r,p,q,P,Q,R, exact rational FLINT ranks; no upstream polynomial routines imported.",
        "first_equation":{"N_columns":324,"D_columns":64,"rows":322,"rank":318,
            "complete_kernel_dimension":70,"pure_N_kernel":48,"gauge_dimension":4,"D_mod_F_dimension":18},
        "field_semantics":"Every field reconstructed uniquely in the free polynomial E0,E1,E2 bases; ambient divergences independently checked with the discriminant Jacobian volume formula.",
        "second_equation":{"raw_rows":435,"columns":1035,"rank":435,"mixed_columns":864,"mixed_rank":391,"necessary_pure_quadrics":44,
            "exact_match_to_published_pure_quadrics":True},
        "gauge_checks":gauge_checks,
        "gauge_identity":"B_(D+BF)(N+AB epsilon/6) = B_D(N) + F*(B div N-N(B)+AB^2), with F denoting the integral polynomial G=7F_target in this computation.",
        "large_intermediate_rref":"Not loaded; the necessary quadrics were independently derived by direct elimination from the reconstructed raw equations.",
        "inputs":{a.name:hashlib.sha256(a.read_bytes()).hexdigest() for a in (first_path,pure_path)},
        "seconds":time.time()-start,"formal_lean_proof":False,"full_certificate_proved":False,
        "scope":"Proves computationally that these 44 rational quadrics are necessary for every invariant Y-even degree-eight certificate after the valid denominator gauge. Combine with a full-rank Macaulay certificate to exclude nonzero parameters."}
    (HERE/"independent_degree8_audit.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps(receipt,indent=2),flush=True)


if __name__=="__main__":main()
