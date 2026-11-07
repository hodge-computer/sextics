#!/usr/bin/env python3
"""Bounded actual-target contact-curve obstruction-jet calculation.

The protected reflection pencil is specialized to lambda=1, without changing
its rational coefficients. This uses the existing certified contact merely
as a starting point, refines and certifies a root, and computes the local
fixed-equation contact curve. All claimed enclosures use FLINT/Arb outward
rounding. This is NOT a Lean proof and does not construct a rational primitive.
"""
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
from itertools import product
import argparse
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
PREVIOUS=next(p for p in [BASE/'proof_attempt4',BASE/'research_contact'] if p.is_dir())
sys.path.insert(0,str(PREVIOUS))
import contact_certify as C
import flint
from flint import acb,arb,acb_mat,acb_series,fmpq,ctx

CONTACT_POLYS=C.POLYS[:44]
ACTIVE=list(range(1,45))
QBASE=C.QBASE
ABASE=C.ABASE
BBASE=C.BBASE
M4=C.M4

def aq(x):
    return acb(fmpq(x.numerator,x.denominator)) if isinstance(x,Fraction) else acb(x)

def l1(x):
    return (x.real.abs_upper()+x.imag.abs_upper()).upper()

def norm_vec(x):
    return max(l1(z) for z in x)

def norm_mat(M):
    return max(sum((l1(M[i,j]) for j in range(M.ncols())),arb(0)).upper()
               for i in range(M.nrows()))

def evaluate(p,x):
    s=acb(0)
    for m,c in p.items():
        z=aq(c)
        for i in m:z*=x[i]
        s+=z
    return s

def equations(x):return acb_mat([[evaluate(p,x)] for p in CONTACT_POLYS])

def jacobian(x):
    return acb_mat([[evaluate(row[j],x) for j in ACTIVE] for row in C.DERIVS[:44]])

def encode_arb(z):
    return {'mid':[int(x) for x in z.mid().man_exp()],
            'rad':[int(x) for x in z.rad().man_exp()]}

def encode_acb(z):return [encode_arb(z.real),encode_arb(z.imag)]

def encode_mid(z):
    return [[int(y) for y in z.real.mid().man_exp()],
            [int(y) for y in z.imag.mid().man_exp()]]

def encode_matrix_mid(M):
    return [[encode_mid(M[i,j]) for j in range(M.ncols())] for i in range(M.nrows())]

def simple(z,digits=12):return z.str(digits,more=True)

def root(digits):
    previous=json.loads((PREVIOUS/'contact_exact_ball.json').read_text())
    center=[acb(fmpq(z[0]),fmpq(z[1])).mid() for z in previous['center'][:45]]
    center[0]=acb(fmpq(1,4))
    refinements=[]
    for k in range(9):
        F=equations(center)
        residual=norm_vec(F.entries())
        refinements.append(simple(residual))
        print('Newton',k,simple(residual),flush=True)
        if residual<arb(10)**(-(digits-20)):break
        dx=jacobian(center).solve(F,algorithm='approx')
        for i,z in zip(ACTIVE,dx.entries()):center[i]=(center[i]-z).mid()
    J=jacobian(center)
    B=J.inv().mid()
    identity=acb_mat([[int(i==j) for j in ACTIVE] for i in ACTIVE])
    defect=norm_mat(identity-B*J)
    nb=norm_mat(B)
    eta=norm_vec((B*equations(center)).entries())
    radius=fmpq(1,10**(digits-40))
    ar=arb(radius)
    coord_bound=int((norm_vec(center)+2*ar).ceil().fmpz())+1
    h=max(sum(abs(c)*len(m)*(len(m)-1)*coord_bound**max(0,len(m)-2)
              for m,c in p.items()) for p in CONTACT_POLYS)
    contraction=defect+nb*aq(h).real*ar
    assert contraction<1
    assert eta+contraction*ar<ar
    # This root is inside the earlier contact polydisc. Earlier existence is
    # not reused to infer the new existence; the contraction above does that.
    old_radius=arb(fmpq(previous['radius']))
    distance=max(l1(z-acb(fmpq(w[0]),fmpq(w[1])))
                 for z,w in zip(center,previous['center'][:45]))
    assert distance+2*ar<old_radius
    old_contraction=defect+nb*aq(h).real*(distance+old_radius)
    assert old_contraction<1
    x=[acb(arb(z.real.mid(),radius),arb(z.imag.mid(),radius)) for z in center]
    x[0]=acb(fmpq(1,4))
    Ji=jacobian(x).inv()
    proof={'newton_residuals':refinements,'radius':str(radius),
           'norm':'max_i(abs(Re x_i)+abs(Im x_i))',
           'inverse_norm_upper':encode_arb(nb),
           'inverse_defect_upper':encode_arb(defect),
           'Newton_displacement_upper':encode_arb(eta),
           'Hessian_bound':str(h),'coordinate_bound':coord_bound,
           'contraction_upper':encode_arb(contraction),
           'mapping_bound':encode_arb(eta+contraction*ar),
           'inside_prior_contact_ball':True,
           'unique_contact_root_in_prior_contact_ball':True,
           'prior_ball_injectivity_bound':encode_arb(old_contraction),
           'inverse_midpoint':encode_matrix_mid(B),
           'center':[encode_acb(z) for z in center]}
    return x,Ji,proof

def all_series_values(polys,coeffs,n):
    X=[acb_series(v[:n+1],prec=n+1) for v in coeffs]
    cache={():acb_series([1],prec=n+1)}
    def mon(m):
        if m not in cache:cache[m]=mon(m[:-1])*X[m[-1]]
        return cache[m]
    out=[]
    for p in polys:
        z=acb_series([],prec=n+1)
        for m,c in p.items():z+=aq(c)*mon(m)
        out.append(z)
    return out

def contact_series(x,Ji,order,scale):
    coeffs=[[z]+[acb(0)]*order for z in x]
    coeffs[0][1]=aq(scale)
    for n in range(1,order+1):
        f=acb_mat([[-z[n]] for z in all_series_values(CONTACT_POLYS,coeffs,n)])
        dx=Ji*f
        for i,z in zip(ACTIVE,dx.entries()):coeffs[i][n]=z
        if n%8==0 or n==order:
            print('Contact series',n,'coefficient norm',simple(norm_vec(dx.entries())),flush=True)
    # Every retained nonconstant coefficient contains zero; this is a useful
    # arithmetic implementation check, not an independent exact identity proof.
    resid=all_series_values(CONTACT_POLYS,coeffs,order)
    assert all(z[n].contains(0) for z in resid for n in range(1,order+1))
    return [acb_series(v,prec=order+1) for v in coeffs]

def monomials(d,parity):
    return sorted(e for e in product(range(d+1),repeat=4)
                  if sum(e)==d and (e[2]+e[3])%2==parity)

def pplus(f,g):
    out=f.copy()
    for e,c in g.items():out[e]=out.get(e,0)+c
    return out

def pmul(f,g):
    out={}
    for e,c in f.items():
        for z,v in g.items():
            m=tuple(a+b for a,b in zip(e,z));out[m]=out.get(m,0)+c*v
    return out

def pmultiple(f,c):return {e:c*v for e,v in f.items()}

def negative_ideal(X,order):
    blocks=C.coefficient_blocks(json.loads(C.CIRCUIT.read_text()))
    h2={e:aq(c) for e,c in zip(C.M2,blocks[0]) if c}
    h4={e:aq(c) for e,c in zip(C.M4,blocks[1]) if c}
    Q=dict(zip(QBASE,X[:5]))
    Q2=pplus(dict(zip(QBASE,X[5:10])),{C.AB:acb_series([1],prec=order+1)})
    g1=pplus(pplus(pmultiple(pmul(Q,Q),3),pmultiple(pmul(h2,Q),-2)),h4)
    A=dict(zip(ABASE,X[10:18]));B=dict(zip(BBASE,X[18:26]));g2=dict(zip(M4,X[26:45]))
    basis=monomials(6,1);index={m:i for i,m in enumerate(basis)}
    cols=[]
    for form,degree,parity in [(Q2,2,0),(g1,4,0),(g2,4,0),(A,3,0),(B,3,1)]:
        for m in monomials(6-degree,1-parity):
            col=[acb_series([],prec=order+1) for _ in basis]
            for e,c in form.items():
                k=index[tuple(x+y for x,y in zip(e,m))]
                col[k]=c if isinstance(c,acb_series) else acb_series([c],prec=order+1)
            cols.append(col)
    assert len(basis)==40 and len(cols)==44
    return basis,cols,Q

def numerical_pivots(cols):
    import numpy as np
    from scipy.linalg import qr
    M=np.array([[complex(float(z[0].real.mid()),float(z[0].imag.mid())) for z in col]
                for col in cols]).T
    _,_,piv=qr(M,mode='economic',pivoting=True)
    chosen=list(map(int,piv[:39]))
    _,_,rowpiv=qr(M[:,chosen].T,mode='economic',pivoting=True)
    missing=list(set(range(40))-set(map(int,rowpiv[:39])))
    assert len(missing)==1
    return chosen,missing[0]

def obstruction_series(cols,order):
    chosen,normalization=numerical_pivots(cols)
    matrices=[]
    for n in range(order+1):
        rows=[[cols[j][i][n] for i in range(40)] for j in chosen]
        rows.append([int(n==0 and i==normalization) for i in range(40)])
        matrices.append(acb_mat(rows))
    inv=matrices[0].inv()
    rhs=acb_mat([[int(i==39)] for i in range(40)])
    ell=[inv*rhs]
    for n in range(1,order+1):
        q=acb_mat(40,1)
        for k in range(1,n+1):q+=matrices[k]*ell[n-k]
        ell.append(-(inv*q))
    E=[acb_series([v[i,0] for v in ell],prec=order+1) for i in range(40)]
    # This interval check detects an implementation contradiction. By itself
    # it is not a proof of an exact annihilator identity for unused columns.
    tested=[]
    for j,col in enumerate(cols):
        z=sum((a*b for a,b in zip(E,col)),acb_series([],prec=order+1))
        ok=all(z[n].contains(0) for n in range(order+1))
        tested.append(ok)
    print('Ideal constraint enclosure checks',sum(tested),'/',len(tested),flush=True)
    return E,{'selected_columns':chosen,'normalization_coordinate':normalization,
              'constant_inverse_midpoint':encode_matrix_mid(inv.mid()),
              'all_44_column_checks_contain_zero':all(tested),
              'constraint_check_scope':'Interval consistency only; geometric rank upper bound still required.'}

def weighted_rows(E,basis,Q,order):
    weighted=sorted(e+(u,) for u in range(4) for e in monomials(6-2*u,1))
    assert len(weighted)==60
    powers=[{(0,0,0,0):acb_series([1],prec=order+1)}]
    for _ in range(2):powers.append(pmultiple(pmul(powers[-1],Q),-1))
    index={e:i for i,e in enumerate(basis)}
    vals=[]
    for m in weighted:
        v=acb_series([],prec=order+1)
        for e,c in powers[m[4]].items():
            z=tuple(x+y for x,y in zip(e,m[:4]))
            v+=c*E[index[z]]
        vals.append(v)
    return weighted,[[z[n] for z in vals] for n in range(order+1)]

def rank_witness(rows,desired=48):
    A=[row[:] for row in rows]
    piv=[];used=set();det=acb(1)
    # Rows are in Taylor order. Row normalization is exact division by a
    # positive power of two and does not change rank.
    scales=[]
    for i,row in enumerate(A):
        upper=norm_vec(row)
        exponent=int((upper.log()/arb(2).log()).ceil().fmpz()) if upper>0 else 0
        scale=arb((1,-exponent))
        scales.append(exponent)
        A[i]=[z*scale for z in row]
    for i in range(min(desired,len(A))):
        choices=[(A[i][j].abs_lower(),j) for j in range(len(A[i])) if j not in used]
        lower,j=max(choices,key=lambda pair:float(pair[0]))
        if not lower>0:
            print('Rank enclosure stops at',i,flush=True);break
        used.add(j);piv.append(j);det*=A[i][j]
        row=[z/A[i][j] for z in A[i]]
        for k in range(i+1,len(A)):
            a=A[k][j];A[k]=[x-a*y for x,y in zip(A[k],row)]
        if (i+1)%8==0:print('Certified nonzero pivots',i+1,flush=True)
    if len(piv)==desired:
        M=acb_mat([[rows[i][j]*arb((1,-scales[i])) for j in piv] for i in range(desired)])
        determinant=M.det()
        print('Selected minor determinant',simple(determinant),flush=True)
        assert not determinant.contains(0)
        preconditioner=encode_matrix_mid(M.inv().mid())
    else:determinant=acb(0);preconditioner=[]
    return {'certified_rank_lower_bound':len(piv),'selected_columns':piv,
            'row_scale_binary_exponents':scales,
            'inverse_midpoint':preconditioner,
            'scaled_minor_determinant':encode_acb(determinant)}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--digits',type=int,default=400)
    ap.add_argument('--order',type=int,default=47);args=ap.parse_args()
    ctx.dps=args.digits;ctx.cap=args.order+1;ctx.threads=1
    start=time.time()
    x,Ji,root_receipt=root(args.digits)
    scale=Fraction(1,4096)
    X=contact_series(x,Ji,args.order,scale)
    basis,cols,Q=negative_ideal(X,args.order)
    E,constraint=obstruction_series(cols,args.order)
    weighted,rows=weighted_rows(E,basis,Q,args.order)
    result=rank_witness(rows)
    receipt={'status':'ENCLOSURE_COMPLETE','target_lambda':'1',
       'source_circuit_sha256':hashlib.sha256(C.CIRCUIT.read_bytes()).hexdigest(),
       'prior_contact_ball_sha256':hashlib.sha256((PREVIOUS/'contact_exact_ball.json').read_bytes()).hexdigest(),
       'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'python_flint_version':flint.__version__,'precision_digits':args.digits,
       'Taylor_order':args.order,'curve_parameter':'rho0=1/4+t/4096',
       'root':root_receipt,'negative_ideal':constraint,'jet_minor':result,
       'weighted_degree_six_negative_basis':weighted,
       'seconds':time.time()-start,'Lean_proof':False,
       'full_certificate_proved':False,'literal_source_trace_proved':False,
       'cohomological_interpretation_requires':'The actual normal-obstruction/Abel-Jacobi pairing and smooth-curve hypotheses; the numerical interval consistency of unused columns alone does not prove their exact vanishing.'}
    out=HERE/f'exact_target_contact_jets_{args.order}_{args.digits}.json'
    out.write_text(json.dumps(receipt,indent=2)+'\n')
    witness={'schema':'exact-target-finite-contact-jet-rational-witness-v1',
        'source_circuit_sha256':receipt['source_circuit_sha256'],
        'prior_contact_ball_sha256':receipt['prior_contact_ball_sha256'],
        'Taylor_order':args.order,'root_radius':root_receipt['radius'],
        'curve_parameter_scale':str(scale),
        'contact_coefficients':[[encode_mid(z[n]) for n in range(args.order+1)] for z in X],
        'contact_constant_preconditioner':root_receipt['inverse_midpoint'],
        'ideal_selected_columns':constraint['selected_columns'],
        'ideal_normalization_coordinate':constraint['normalization_coordinate'],
        'functional_coefficients':[[encode_mid(z[n]) for n in range(args.order+1)] for z in E],
        'functional_constant_preconditioner':constraint['constant_inverse_midpoint'],
        'weighted_degree_six_negative_basis':weighted,
        'span_selected_columns':result['selected_columns'],
        'span_row_scale_binary_exponents':result['row_scale_binary_exponents'],
        'span_preconditioner':result['inverse_midpoint'],
        'scope':'Exact dyadic approximation data. The separate rational checker derives its own rigorous errors; the data alone are not an existence or rank proof.'}
    wpath=HERE/'exact_target_contact_jet_witness.json'
    wpath.write_text(json.dumps(witness,separators=(',',':'))+'\n')
    print(json.dumps({'file':out.name,'witness':wpath.name,'witness_bytes':wpath.stat().st_size,
                     'seconds':receipt['seconds'],'rank_lower_bound':result['certified_rank_lower_bound']}),flush=True)

if __name__=='__main__':main()
