#!/usr/bin/env python3
"""Certify the actual target's canonical form is nonzero at the contact.

Uses exact rational error bounds for a normalized degree-nine socle dual and
the existing certified contact tangent. Numerical QR chooses a minor only;
every asserted enclosure is subsequently verified over Q(i).
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations, permutations
import argparse, hashlib, json, math, time
import contact_forms_regularity as R
import contact_certify as C

HERE=Path(__file__).resolve().parent

def p_add(*ps):
    out={}
    for p in ps:
        for e,c in p.items():out[e]=out.get(e,C.QC())+c
    return out
def p_scale(p,c):return {e:v*c for e,v in p.items()}
def p_mul(p,q):
    out={}
    for e,v in p.items():
        for f,w in q.items():
            g=tuple(a+b for a,b in zip(e,f));out[g]=out.get(g,C.QC())+v*w
    return out
def p_diff(p,j):
    return {tuple(x-int(i==j) for i,x in enumerate(e)):c*e[j] for e,c in p.items() if e[j]}
def det2(a,b,c,d):return p_add(p_mul(a,d),p_scale(p_mul(b,c),-1))
def jacobian(fs):
    matrix=[[p_diff(f,j) for j in range(4)] for f in fs]
    out={}
    for cols in combinations(range(4),2):
        rest=[j for j in range(4) if j not in cols];i,j=cols;k,l=rest
        left=det2(matrix[0][i],matrix[0][j],matrix[1][i],matrix[1][j])
        right=det2(matrix[2][k],matrix[2][l],matrix[3][k],matrix[3][l])
        out=p_add(out,p_scale(p_mul(left,right),(-1)**(i+j+1)))
    return out
def evaluated_forms(fs,x):return [{e:R.coefficient_value(p,x) for e,p in f.items()} for f in fs]
def parameter_polynomial_lipschitz(p,M):
    return sum(abs(c)*len(m)*M**max(0,len(m)-1) for m,c in p.items())
def source_bar(x):
    # lambda=1 and ell=13/7, fixed exactly in the certified ball.
    q=dict(zip(R.QBASE,x[:5]));a2={(2,0,0,0):C.QC(1)};c2={(0,0,2,0):C.QC(1)}
    return p_scale(p_mul({(0,1,0,1):C.QC(1)},p_mul(p_add(a2,q),p_add(c2,q))),F(98,169))

def setup(ball,fs):
    x=R.complex_pairs(ball);rows,columns=R.matrix_structure(9,fs)
    ff=evaluated_forms(fs,x);jac=jacobian(ff)
    return x,rows,columns,ff,jac

def discover(ball,fs,setup_data):
    import numpy as np
    import scipy.linalg as la
    x,rows,columns,ff,jac=setup_data
    M=R.sparse_numeric(columns,len(rows),x)
    _,_,piv=la.qr(M,mode='economic',pivoting=True,check_finite=False)
    chosen=list(map(int,piv[:219]))
    jcol=np.array([complex(float(jac.get(e,C.QC()).a),float(jac.get(e,C.QC()).b)) for e in rows])
    S=np.column_stack((M[:,chosen],jcol)).T
    powers=[max(0,int(math.ceil(math.log2(max(abs(z) for z in row))))) for row in S]
    scales=np.array([2.**(-p) for p in powers]);S=scales[:,None]*S
    inv=la.inv(S,check_finite=False);den=10**18
    B=[[[int(round(z.real*den)),int(round(z.imag*den))] for z in row] for row in inv]
    witness={'schema':'symmetric-contact-target-form-nonzero-v1',
        'source_ball_sha256':hashlib.sha256((HERE/'contact_exact_ball.json').read_bytes()).hexdigest(),
        'regularity_witness_sha256':hashlib.sha256((HERE/'contact_forms_regularity_witness.json').read_bytes()).hexdigest(),
        'selected_ideal_columns':chosen,'row_scale_powers_of_two':powers,
        'inverse_denominator':str(den),'inverse_integer_pairs':B,
        'numerical_discovery_only':{'condition_number':float(np.linalg.cond(S)),
                                   'largest_inverse_entry':float(np.max(np.abs(inv)))},
        'normalization':'tau(Jacobian(Q2,h,G_u(-Q1),g2))=96',
        'tangent_normalization':'D(rho0)=1 on the contact curve, fixed lambda',
        'source':'2*b*d*(a^2-u)*(c^2-u)/ell^2, ell=13/7'}
    (HERE/'contact_forms_nonzero_witness.json').write_text(json.dumps(witness,separators=(',',':'))+'\n')
    print('Normalized socle-dual condition',witness['numerical_discovery_only'],flush=True)
    return witness

def verify(ball,fs,w,setup_data):
    from flint import fmpz_mat
    start=time.time();x,rows,columns,ff,jac=setup_data;n=220
    assert w['source_ball_sha256']==hashlib.sha256((HERE/'contact_exact_ball.json').read_bytes()).hexdigest()
    assert w['regularity_witness_sha256']==hashlib.sha256((HERE/'contact_forms_regularity_witness.json').read_bytes()).hexdigest()
    selected=w['selected_ideal_columns'];assert len(set(selected))==219
    index={e:i for i,e in enumerate(rows)};S=[]
    for k in selected:
        row=[C.QC() for _ in range(n)]
        for i,p in columns[k]['entries'].items():row[i]=R.coefficient_value(p,x)
        S.append(row)
    S.append([jac.get(e,C.QC()) for e in rows])
    scales=[F(1,2**p) for p in w['row_scale_powers_of_two']]
    S=[[z*scale for z in row] for row,scale in zip(S,scales)]
    common=1
    for row in S:
        for z in row:common=math.lcm(common,z.a.denominator,z.b.denominator)
    Mr=fmpz_mat([[int(z.a*common) for z in row] for row in S])
    Mi=fmpz_mat([[int(z.b*common) for z in row] for row in S])
    den=int(w['inverse_denominator']);B=w['inverse_integer_pairs']
    Br=fmpz_mat([[z[0] for z in row] for row in B]);Bi=fmpz_mat([[z[1] for z in row] for row in B])
    real=Br*Mr-Bi*Mi;imag=Br*Mi+Bi*Mr;scale=common*den
    defect=F(max(sum(abs(scale*int(i==j)-int(real[i,j]))+abs(int(imag[i,j])) for j in range(n))
                 for i in range(n)),scale)
    nb=F(max(sum(abs(a)+abs(b) for a,b in row) for row in B),den)
    radius=F(ball['radius']);M=max(F(1),F(math.ceil(max(z.norm() for z in x)+radius)))
    # Norm/Lipschitz bounds for the four-variable Jacobian determinant.
    entry_norm=[[F(0) for _ in range(4)] for _ in range(4)]
    entry_lip=[[F(0) for _ in range(4)] for _ in range(4)]
    for i,f in enumerate(fs):
        for j in range(4):
            for e,p in f.items():
                if e[j]:
                    lip=e[j]*parameter_polynomial_lipschitz(p,M)
                    entry_lip[i][j]+=lip
                    entry_norm[i][j]+=e[j]*R.coefficient_value(p,x).norm()+lip*radius
    jac_lip=F(0)
    for perm in permutations(range(4)):
        for i in range(4):
            term=entry_lip[i][perm[i]]
            for k in range(4):
                if k!=i:term*=entry_norm[k][perm[k]]
            jac_lip+=term
    ls=[sum(parameter_polynomial_lipschitz(p,M) for p in columns[k]['entries'].values())*scales[i]
        for i,k in enumerate(selected)]+[jac_lip*scales[-1]]
    L=max(ls);epsilon=defect+nb*L*radius
    assert epsilon<1
    rhs=96*scales[-1]
    tau0=[C.QC(F(row[-1][0],den)*rhs,F(row[-1][1],den)*rhs) for row in B]
    ntau=max(z.norm() for z in tau0);tau_error=epsilon*ntau/(1-epsilon)

    # Use the exact rounded contact inverse, whose full-ball error has already
    # been certified; recompute the relevant conservative rational inequalities.
    BB=[[C.decode(z) for z in row] for row in ball['inverse']]
    jb=[R.coefficient_value(row[0],x) for row in C.DERIVS]
    tangent0=[C.QC(1)]+[-C.dot(row,jb) for row in BB]
    contact_receipt=json.loads((HERE/'contact_exact_ball_receipt.json').read_text())
    assert contact_receipt['status']=='PASS' and contact_receipt['witness_sha256']==w['source_ball_sha256']
    def bound(text):
        assert text.startswith('10^');return F(10)**int(text[3:])
    root_epsilon=bound(contact_receipt['contraction_constant_upper_bound'])
    root_nb=bound(contact_receipt['inverse_norm_upper_bound'])
    root_hessian=F(contact_receipt['hessian_bound'])
    tangent_norm=max(z.norm() for z in tangent0)
    tangent_error=(root_epsilon*tangent_norm+root_nb*root_hessian*radius)/(1-root_epsilon)
    dh0=dict(zip(R.ABASE+R.BBASE,tangent0[10:26]))
    target0=source_bar(x);W0=p_mul(target0,dh0)
    value0=sum((tau0[index[e]]*v for e,v in W0.items()),C.QC())
    # Rbar=(98/169)*bd*(a²+Q1)*(c²+Q1); coefficient l1 bounds.
    qnorm=sum(z.norm() for z in x[:5]);q_error=5*radius
    target_error=F(98,169)*(2*(1+qnorm)*q_error+q_error*q_error)
    target_norm=sum(z.norm() for z in target0.values())
    dh_norm=sum(z.norm() for z in dh0.values());dh_error=16*tangent_error
    W_error=target_error*(dh_norm+dh_error)+target_norm*dh_error
    W_norm=sum(z.norm() for z in W0.values())
    value_error=tau_error*W_norm+(ntau+tau_error)*W_error
    margin=abs(value0.a)-value_error
    assert margin>0
    receipt={'status':'PASS','method':'Exact rational enclosure of normalized residue dual and contact tangent',
        'normalized_socle_matrix':220,'ideal_columns':219,'jacobian_normalization':96,
        'socle_center_inverse_defect_upper_bound':C.upper_power(defect),
        'socle_ball_inverse_defect_upper_bound':C.upper_power(epsilon),
        'socle_inverse_norm_upper_bound':C.upper_power(nb),
        'tangent_error_upper_bound':C.upper_power(tangent_error),
        'tau_vector_error_upper_bound':C.upper_power(tau_error),
        'form_value_error_upper_bound':C.upper_power(value_error),
        'form_value_approximation':[float(value0.a),float(value0.b)],
        'form_value_approximation_exact':value0.encode(),
        'form_value_error_exact':str(value_error),'real_part_nonzero_margin_exact':str(margin),
        'real_part_separated_from_zero':True,
        'meaning':'eta_target(D) is nonzero at the certified actual contact, where D(rho0)=1; eta_target=tau(R dh).',
        'source_ball_sha256':w['source_ball_sha256'],
        'root_receipt_sha256':hashlib.sha256((HERE/'contact_exact_ball_receipt.json').read_bytes()).hexdigest(),
        'witness_sha256':hashlib.sha256((HERE/'contact_forms_nonzero_witness.json').read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'verification_seconds':time.time()-start,
        'source_trace_proved':False,'full_certificate_proved':False,'Lean_proof':False}
    (HERE/'contact_forms_nonzero_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if not k.endswith('_exact')},indent=2),flush=True)
    return receipt

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--verify-only',action='store_true');args=ap.parse_args()
    ball=json.loads((HERE/'contact_exact_ball.json').read_text());fs=R.forms()
    setup_data=setup(ball,fs)
    w=json.loads((HERE/'contact_forms_nonzero_witness.json').read_text()) if args.verify_only else discover(ball,fs,setup_data)
    verify(ball,fs,w,setup_data)

if __name__=='__main__':main()
