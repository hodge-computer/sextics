#!/usr/bin/env python3
"""Independent exact audit of the nonzero canonical symmetric-target form.

Uses only adjacent explicit witnesses and the independent target/form builders.
No contact_forms_nonzero, contact_forms_regularity, contact_certify, homotopy,
or circuit generator is imported. The original source and the four-variable
Jacobian determinant are independently reconstructed.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import permutations
import hashlib
import json
import math
import time
import contact_lift_independent_audit as A
import contact_lift_regularity_audit as R

HERE=Path(__file__).resolve().parent

def padd(*polys):
    out={}
    for p in polys:
        for e,c in p.items():out[e]=A.gadd(out.get(e,A.ZERO),c)
    return {e:c for e,c in out.items() if c!=A.ZERO}
def pscale(p,c):
    return {e:A.gmul(v,(Q(c),Q(0))) for e,v in p.items() if v!=A.ZERO and c}
def pmul(p,q):
    out={}
    for e,c in p.items():
        for f,d in q.items():
            m=tuple(i+j for i,j in zip(e,f))
            out[m]=A.gadd(out.get(m,A.ZERO),A.gmul(c,d))
    return {e:c for e,c in out.items() if c!=A.ZERO}
def pdiff(p,j):
    return {tuple(k-int(i==j) for i,k in enumerate(e)):A.gmul(c,(Q(e[j]),Q(0)))
            for e,c in p.items() if e[j]}
def jacobian_determinant(forms):
    M=[[pdiff(f,j) for j in range(4)] for f in forms]
    out={}
    for perm in permutations(range(4)):
        term={(0,0,0,0):(Q(1),Q(0))}
        for i in range(4):term=pmul(term,M[i][perm[i]])
        inversions=sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4))
        out=padd(out,pscale(term,(-1)**inversions))
    return out
def plip(p,M):return sum(abs(c)*len(m)*M**max(0,len(m)-1) for m,c in p.items())

def main():
    started=time.monotonic()
    bp=HERE/'contact_exact_ball.json';wp=HERE/'contact_forms_nonzero_witness.json'
    rp=HERE/'contact_forms_regularity_witness.json'
    ball=json.loads(bp.read_text());w=json.loads(wp.read_text())
    assert w['source_ball_sha256']==hashlib.sha256(bp.read_bytes()).hexdigest()
    assert w['regularity_witness_sha256']==hashlib.sha256(rp.read_bytes()).hexdigest()
    x=list(map(A.decode,ball['center']));radius=Q(ball['radius'])
    assert x[0]==(Q(1,4),Q(0)) and radius>0
    fs=R.independent_forms()
    ff=[{e:A.evaluate(p,x) for e,p in f.items()} for f in fs]
    jac=jacobian_determinant(ff)
    rows=R.monomials(9);idx={e:i for i,e in enumerate(rows)};n=len(rows)
    assert n==220 and all(sum(e)==9 for e in jac)
    cols=[]
    for f,d in zip(fs,[2,3,4,4]):
        for m in R.monomials(9-d):
            cols.append({idx[tuple(i+j for i,j in zip(e,m))]:p for e,p in f.items()})
    assert len(cols)==316
    selected=w['selected_ideal_columns']
    assert len(selected)==len(set(selected))==219 and all(0<=k<316 for k in selected)
    powers=w['row_scale_powers_of_two']
    assert len(powers)==220 and all(isinstance(p,int) and p>=0 for p in powers)
    scales=[Q(1,2**p) for p in powers]
    S=[]
    for i,k in enumerate(selected):
        row=[A.ZERO]*n
        for j,p in cols[k].items():row[j]=A.gmul(A.evaluate(p,x),(scales[i],Q(0)))
        S.append(row)
    S.append([A.gmul(jac.get(e,A.ZERO),(scales[-1],Q(0))) for e in rows])
    common=1
    for row in S:
        for z in row:common=math.lcm(common,z[0].denominator,z[1].denominator)
    entries=[[(i,int(S[i][j][0]*common),int(S[i][j][1]*common)) for i in range(n) if S[i][j]!=A.ZERO]
             for j in range(n)]
    B=w['inverse_integer_pairs'];den=int(w['inverse_denominator'])
    assert len(B)==n and all(len(row)==n for row in B) and den>0
    num,backend=R.integer_defect(B,entries,n,den*common)
    center_defect=Q(num,den*common)
    nb=Q(max(sum(abs(a)+abs(b) for a,b in row) for row in B),den)
    M=max(1,math.ceil(max(map(A.gnorm,x))+radius))

    entry_norm=[[Q(0)]*4 for _ in range(4)]
    entry_lip=[[Q(0)]*4 for _ in range(4)]
    for i,f in enumerate(fs):
        for j in range(4):
            for e,p in f.items():
                if e[j]:
                    lip=e[j]*plip(p,M)
                    entry_lip[i][j]+=lip
                    entry_norm[i][j]+=e[j]*A.gnorm(A.evaluate(p,x))+lip*radius
    jac_lip=Q(0)
    for perm in permutations(range(4)):
        for i in range(4):
            term=entry_lip[i][perm[i]]
            for k in range(4):
                if k!=i:term*=entry_norm[k][perm[k]]
            jac_lip+=term
    L=max([scales[i]*sum(plip(p,M) for p in cols[k].values()) for i,k in enumerate(selected)]
          +[scales[-1]*jac_lip])
    epsilon=center_defect+nb*L*radius
    assert epsilon<1
    rhs=96*scales[-1]
    tau0=[(Q(row[-1][0],den)*rhs,Q(row[-1][1],den)*rhs) for row in B]
    ntau=max(map(A.gnorm,tau0))
    tau_error=epsilon*ntau/(1-epsilon)

    # Recompute the root tangent enclosure from the original-target equations,
    # without trusting a PASS label or rounded bounds from another receipt.
    _,_,equations=A.reconstruct_equations()
    derivatives=[[A.derivative(p,j) for j in range(47)] for p in equations]
    J=[[A.evaluate(row[j],x) for j in range(1,47)] for row in derivatives]
    j0=[A.evaluate(row[0],x) for row in derivatives]
    BR=[[A.decode(z) for z in row] for row in ball['inverse']]
    nbroot=A.matnorm(BR)
    Hess=max(sum(abs(c)*len(m)*(len(m)-1)*M**max(0,len(m)-2) for m,c in p.items()) for p in equations)
    root_epsilon=A.defect(BR,J)+nbroot*Hess*radius
    root_eta=max(A.gnorm(A.dot(row,[A.evaluate(p,x) for p in equations])) for row in BR)
    assert root_epsilon<1 and root_eta+root_epsilon*radius<radius
    tangent0=[(Q(1),Q(0))]+[tuple(-q for q in A.dot(row,j0)) for row in BR]
    tangent_norm=max(map(A.gnorm,tangent0))
    tangent_error=(root_epsilon*tangent_norm+nbroot*Hess*radius)/(1-root_epsilon)

    # Actual protected homogeneous source, with lambda=1 and ell=13/7.
    q1=dict(zip(A.QBASE,x[:5]))
    a2={(2,0,0,0):(Q(1),Q(0))};c2={(0,0,2,0):(Q(1),Q(0))}
    bd={(0,1,0,1):(Q(1),Q(0))}
    source=pscale(pmul(bd,pmul(padd(a2,q1),padd(c2,q1))),Q(98,169))
    dh=dict(zip(A.ABASE+A.BBASE,tangent0[10:26]))
    W=pmul(source,dh)
    assert all(sum(e)==9 for e in W)
    value=A.ZERO
    for e,c in W.items():value=A.gadd(value,A.gmul(tau0[idx[e]],c))
    qnorm=sum(A.gnorm(z) for z in x[:5]);qerror=5*radius
    source_error=Q(98,169)*(2*(1+qnorm)*qerror+qerror*qerror)
    source_norm=sum(map(A.gnorm,source.values()));dh_norm=sum(map(A.gnorm,dh.values()))
    dh_error=16*tangent_error
    W_error=source_error*(dh_norm+dh_error)+source_norm*dh_error
    W_norm=sum(map(A.gnorm,W.values()))
    value_error=tau_error*W_norm+(ntau+tau_error)*W_error
    margin=abs(value[0])-value_error
    assert margin>0
    receipt={'status':'PASS','independent_original_target_source':True,
      'independent_24_permutation_Jacobian':True,'independent_root_tangent_bound':True,
      'normalized_socle_matrix':220,'selected_ideal_columns':219,'Jacobian_normalization':96,
      'socle_center_defect_upper_bound':A.power_upper(center_defect),
      'socle_ball_defect_upper_bound':A.power_upper(epsilon),
      'socle_inverse_norm_upper_bound':A.power_upper(nb),
      'tau_error_upper_bound':A.power_upper(tau_error),
      'tangent_error_upper_bound':A.power_upper(tangent_error),
      'target_form_error_upper_bound':A.power_upper(value_error),
      'target_form_center_value':[float(value[0]),float(value[1])],
      'target_form_center_value_exact':[str(v) for v in value],
      'target_form_error_exact':str(value_error),'real_part_margin_exact':str(margin),
      'target_form_nonzero_at_actual_contact':True,
      'source_ball_sha256':hashlib.sha256(bp.read_bytes()).hexdigest(),
      'nonzero_witness_sha256':hashlib.sha256(wp.read_bytes()).hexdigest(),
      'regularity_witness_sha256':hashlib.sha256(rp.read_bytes()).hexdigest(),
      'audit_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'integer_backend':backend,'seconds':round(time.monotonic()-started,3),
      'scope':'Independent exact enclosure proving eta_target(D) nonzero, D(rho0)=1. Uses the separately audited regularity certificate for the canonical residue interpretation. Classical proof, not Lean; no global trace identity or final certificate.'}
    (HERE/'contact_lift_nonzero_audit_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if not k.endswith('_exact')},indent=2),flush=True)

if __name__=='__main__':main()
