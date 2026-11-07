#!/usr/bin/env python3
"""Exact regular-sequence certificate for the certified norm contact.

Discovery selects a degree-ten Macaulay minor by numerical QR and rounds an
inverse. Verification is entirely rational/integer arithmetic. It proves the
minor invertible throughout the contact_exact_ball.json ball, hence at its
certified contact. This is classical exact verification, not a Lean theorem.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
import argparse, hashlib, json, math, time

HERE=Path(__file__).resolve().parent

def monomials(d):
    return sorted(e for e in product(range(d+1),repeat=4) if sum(e)==d)

QBASE=[(2,0,0,0),(0,2,0,0),(0,0,2,0),(0,0,1,1),(0,0,0,2)]
ABASE=[(3,0,0,0),(0,3,0,0),(1,0,2,0),(1,0,1,1),(1,0,0,2),
       (0,1,2,0),(0,1,1,1),(0,1,0,2)]
BBASE=[(2,0,1,0),(2,0,0,1),(0,2,1,0),(0,2,0,1),
       (0,0,3,0),(0,0,2,1),(0,0,1,2),(0,0,0,3)]
AB=(1,1,0,0)

def forms():
    """Actual Q2,h,G_u(-Q1),g2; coefficients are polynomials in 45 data."""
    import contact_homotopy as H
    exact=H.coef_as_fraction(json.loads(H.CIRCUIT.read_text()))
    h2,h4,_=[dict(zip(ms,block)) for ms,block in zip((H.M2,H.M4,H.M6),exact)]
    result=[defaultdict(lambda:defaultdict(F)) for _ in range(4)]
    def term(i,e,c,variables=()):result[i][e][tuple(sorted(variables))]+=c
    term(0,AB,F(1))
    for j,e in enumerate(QBASE):term(0,e,F(1),(5+j,))
    for base,off in [(ABASE,10),(BBASE,18)]:
        for j,e in enumerate(base):term(1,e,F(1),(off+j,))
    for i,e in enumerate(QBASE):
        for j,f in enumerate(QBASE):
            term(2,tuple(x+y for x,y in zip(e,f)),F(3),(i,j))
        for f,c in h2.items():
            term(2,tuple(x+y for x,y in zip(e,f)),-2*c,(i,))
    for e,c in h4.items():term(2,e,c)
    for j,e in enumerate(H.M4):term(3,e,F(1),(26+j,))
    return [{e:{v:c for v,c in p.items() if c} for e,p in f.items() if any(p.values())}
            for f in result]

def matrix_structure(degree,fs):
    rows=monomials(degree);index={e:i for i,e in enumerate(rows)}
    columns=[]
    for i,(f,d) in enumerate(zip(fs,[2,3,4,4])):
        for m in monomials(degree-d):
            columns.append({'form':i,'multiplier':m,'entries':
                {index[tuple(x+y for x,y in zip(e,m))]:p for e,p in f.items()}})
    return rows,columns

def complex_pairs(data):
    import contact_certify as C
    return list(map(C.decode,data['center']))

def coefficient_value(p,x):
    import contact_certify as C
    return C.value(p,x,C.QC,C.QC())

def sparse_numeric(columns,n,x):
    import numpy as np
    result=np.zeros((n,len(columns)),dtype=complex)
    for j,col in enumerate(columns):
        for i,p in col['entries'].items():
            z=coefficient_value(p,x);result[i,j]=complex(float(z.a),float(z.b))
    return result

def discover(ball,fs):
    import numpy as np
    import scipy.linalg as la
    rows,columns=matrix_structure(10,fs)
    x=complex_pairs(ball);M=sparse_numeric(columns,len(rows),x)
    # Only selection and an approximate inverse use floating point.
    _,_,piv=la.qr(M,mode='economic',pivoting=True,check_finite=False)
    chosen=list(map(int,piv[:len(rows)]));minor=M[:,chosen]
    inverse=la.inv(minor,check_finite=False)
    denominator=10**18
    B=[[[int(round(z.real*denominator)),int(round(z.imag*denominator))]
        for z in row] for row in inverse]
    singular=la.svdvals(minor,check_finite=False)
    out={'schema':'symmetric-contact-residue-regularity-v1',
        'source_ball_sha256':hashlib.sha256((HERE/'contact_exact_ball.json').read_bytes()).hexdigest(),
        'circuit_sha256':ball['circuit_sha256'],
        'degree':10,'row_count':len(rows),'column_count':len(columns),
        'selected_columns':chosen,'inverse_denominator':str(denominator),
        'inverse_integer_pairs':B,
        'numerical_discovery_only':{'condition_number':float(singular[0]/singular[-1]),
          'smallest_singular_value':float(singular[-1]),
          'largest_inverse_entry':float(np.max(np.abs(inverse)))},
        'form_order':['Q2','A+B','G_u(-Q1)','g2'],
        'form_degrees':[2,3,4,4],
        'claim':'The selected degree-ten coefficient matrix is invertible on the entire stated ball.'}
    (HERE/'contact_forms_regularity_witness.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('Selected 286-column Macaulay minor; numerical condition',out['numerical_discovery_only'],flush=True)
    return out

def verify(ball,fs,witness):
    from flint import fmpz_mat
    import contact_certify as C
    start=time.time()
    assert witness['source_ball_sha256']==hashlib.sha256((HERE/'contact_exact_ball.json').read_bytes()).hexdigest()
    assert witness['circuit_sha256']==ball['circuit_sha256']
    rows,columns=matrix_structure(10,fs);n=len(rows)
    assert n==286 and len(columns)==453
    selected=witness['selected_columns'];assert len(set(selected))==n
    assert all(0<=j<len(columns) for j in selected)
    x=complex_pairs(ball);radius=F(ball['radius'])
    exact=[[C.QC() for _ in range(n)] for _ in range(n)]
    common=1
    for j,k in enumerate(selected):
        for i,p in columns[k]['entries'].items():
            z=coefficient_value(p,x);exact[i][j]=z
            common=math.lcm(common,z.a.denominator,z.b.denominator)
    integer=lambda component:fmpz_mat([[int(getattr(z,component)*common) for z in row] for row in exact])
    Mr,Mi=integer('a'),integer('b')
    B=witness['inverse_integer_pairs'];den=int(witness['inverse_denominator'])
    assert len(B)==n and all(len(row)==n for row in B) and den>0
    Br=fmpz_mat([[z[0] for z in row] for row in B]);Bi=fmpz_mat([[z[1] for z in row] for row in B])
    print('Verifying exact 286x286 complex products with common integer scales.',flush=True)
    real=Br*Mr-Bi*Mi;imag=Br*Mi+Bi*Mr
    scale=den*common
    defect_numerator=max(sum(abs(scale*int(i==j)-int(real[i,j]))+abs(int(imag[i,j]))
                              for j in range(n)) for i in range(n))
    defect=F(defect_numerator,scale)
    inverse_norm=F(max(sum(abs(a)+abs(b) for a,b in row) for row in B),den)
    coordinate_bound=max(F(1),F(math.ceil(max(z.norm() for z in x)+radius)))
    # For every monomial c*x^m, telescoping along the line segment bounds
    # its variation by |c|*degree(m)*M^(degree(m)-1)*radius.
    row_lipschitz=[F(0) for _ in range(n)]
    for k in selected:
        for i,p in columns[k]['entries'].items():
            row_lipschitz[i]+=sum(abs(c)*len(m)*coordinate_bound**max(0,len(m)-1)
                                  for m,c in p.items())
    matrix_lipschitz=max(row_lipschitz)
    total=defect+inverse_norm*matrix_lipschitz*radius
    assert total<1
    receipt={'status':'PASS','method':'Exact rational Neumann inequality on the previously certified root ball',
        'degree':10,'matrix_shape':[286,453],'selected_square_minor':286,
        'center_inverse_defect_upper_bound':C.upper_power(defect),
        'inverse_norm_upper_bound':C.upper_power(inverse_norm),
        'coordinate_bound':str(coordinate_bound),'matrix_lipschitz_bound':str(matrix_lipschitz),
        'radius':str(radius),'ball_inverse_defect_upper_bound':C.upper_power(total),
        'exact_center_defect':str(defect),'exact_inverse_norm':str(inverse_norm),
        'exact_ball_defect':str(total),
        'strict_inequality_ball_defect_lt_one':True,
        'consequence':'Q2,h,G_u(-Q1),g2 have no nonzero common zero; their homogeneous quotient is the degree-(2,3,4,4) Artinian complete intersection.',
        'length':96,'socle_degree':9,
        'source_ball_sha256':witness['source_ball_sha256'],
        'witness_sha256':hashlib.sha256((HERE/'contact_forms_regularity_witness.json').read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'verification_seconds':time.time()-start,
        'source_trace_proved':False,'full_certificate_proved':False,'Lean_proof':False}
    (HERE/'contact_forms_regularity_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if not k.startswith('exact_')},indent=2),flush=True)
    return receipt

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--verify-only',action='store_true');args=ap.parse_args()
    ball=json.loads((HERE/'contact_exact_ball.json').read_text());fs=forms()
    witness=json.loads((HERE/'contact_forms_regularity_witness.json').read_text()) if args.verify_only else discover(ball,fs)
    verify(ball,fs,witness)

if __name__=='__main__':main()
