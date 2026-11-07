#!/usr/bin/env python3
"""Independent regular-sequence audit for the certified contact.

Rebuilds Q2,h,G_u(-Q1),g2 from the original sextic using the independent target
reconstruction. Does not import contact_forms_regularity, contact_homotopy, or
contact_certify. The integer inverse products use python-flint when available,
with a sparse standard-library fallback.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import math
import time
import contact_lift_independent_audit as A

HERE=Path(__file__).resolve().parent

def monomials(d):
    return [(a,b,c,d-a-b-c) for a in range(d+1)
            for b in range(d-a+1) for c in range(d-a-b+1)]

def independent_forms():
    _,G=A.original_target()
    q1=A.unknown_form(A.QBASE,0)
    q2=A.outer_add({A.AB:{():Q(1)}},A.unknown_form(A.QBASE,5))
    h=A.outer_add(A.unknown_form(A.ABASE,10),A.unknown_form(A.BBASE,18))
    gu={}
    # Differentiate the actual monic cubic first, then substitute u=-Q1.
    for e,c in G.items():
        if e[4]:
            term=A.outer_mul({e[:4]:{():c*e[4]}},
                A.outer_power(A.outer_scale(q1,-1),e[4]-1))
            gu=A.outer_add(gu,term)
    g2=A.unknown_form(A.M4,26)
    forms=[q2,h,gu,g2]
    for f,d in zip(forms,[2,3,4,4]):assert all(sum(e)==d for e in f)
    return forms

def independent_columns(forms):
    rows=monomials(10);index={e:i for i,e in enumerate(rows)};cols=[]
    for i,(f,d) in enumerate(zip(forms,[2,3,4,4])):
        for m in monomials(10-d):
            entries={index[tuple(x+y for x,y in zip(e,m))]:p for e,p in f.items()}
            cols.append((i,m,entries))
    assert len(rows)==286 and len(cols)==453
    return rows,cols

def integer_defect(B,entries,n,scale):
    try:
        from flint import fmpz_mat
    except ImportError:
        # M is sparse: each selected column has at most nineteen nonzero entries.
        # Accumulating integers directly avoids rational arithmetic in products.
        bound=0
        for i,row in enumerate(B):
            total=0
            for j,col in enumerate(entries):
                real=0;imag=0
                for k,mr,mi in col:
                    br,bi=row[k]
                    real+=br*mr-bi*mi;imag+=br*mi+bi*mr
                total+=abs(scale*int(i==j)-real)+abs(imag)
            bound=max(bound,total)
        return bound,'sparse standard-library integer products'
    Mr=[[0]*n for _ in range(n)];Mi=[[0]*n for _ in range(n)]
    for j,col in enumerate(entries):
        for k,r,i in col:Mr[k][j]=r;Mi[k][j]=i
    Br=fmpz_mat([[z[0] for z in row] for row in B])
    Bi=fmpz_mat([[z[1] for z in row] for row in B])
    Mr=fmpz_mat(Mr);Mi=fmpz_mat(Mi)
    R=Br*Mr-Bi*Mi;I=Br*Mi+Bi*Mr
    return max(sum(abs(scale*int(i==j)-int(R[i,j]))+abs(int(I[i,j])) for j in range(n))
               for i in range(n)),'python-flint exact integer products'

def main():
    started=time.monotonic()
    bp=HERE/'contact_exact_ball.json';wp=HERE/'contact_forms_regularity_witness.json'
    ball=json.loads(bp.read_text());w=json.loads(wp.read_text())
    assert w['source_ball_sha256']==hashlib.sha256(bp.read_bytes()).hexdigest()
    assert w['degree']==10 and w['row_count']==286 and w['column_count']==453
    assert w['form_order']==['Q2','A+B','G_u(-Q1)','g2'] and w['form_degrees']==[2,3,4,4]
    x=list(map(A.decode,ball['center']));radius=Q(ball['radius']);assert radius>0
    fs=independent_forms();rows,cols=independent_columns(fs)
    chosen=w['selected_columns'];n=len(rows)
    assert len(chosen)==len(set(chosen))==n and all(0<=k<len(cols) for k in chosen)
    exact=[];common=1
    for k in chosen:
        column=[]
        for row,p in cols[k][2].items():
            z=A.evaluate(p,x)
            common=math.lcm(common,z[0].denominator,z[1].denominator)
            column.append((row,z))
        exact.append(column)
    entries=[[(i,int(z[0]*common),int(z[1]*common)) for i,z in col if z!=A.ZERO] for col in exact]
    B=w['inverse_integer_pairs'];den=int(w['inverse_denominator'])
    assert den>0 and len(B)==n and all(len(row)==n for row in B)
    assert all(len(z)==2 and all(isinstance(v,int) for v in z) for row in B for z in row)
    numerator,backend=integer_defect(B,entries,n,den*common)
    center_defect=Q(numerator,den*common)
    inverse_norm=Q(max(sum(abs(a)+abs(b) for a,b in row) for row in B),den)
    M=max(1,math.ceil(max(map(A.gnorm,x))+radius))
    row_variations=[Q(0) for _ in rows]
    for k in chosen:
        for row,p in cols[k][2].items():
            row_variations[row]+=sum(abs(c)*len(m)*M**max(0,len(m)-1) for m,c in p.items())
    lipschitz=max(row_variations)
    ball_defect=center_defect+inverse_norm*lipschitz*radius
    assert center_defect<1 and ball_defect<1

    hilbert=[1]
    for d in [2,3,4,4]:
        out=[0]*(len(hilbert)+d-1)
        for i,c in enumerate(hilbert):
            for j in range(d):out[i+j]+=c
        hilbert=out
    assert hilbert==[1,4,9,15,19,19,15,9,4,1] and sum(hilbert)==96
    forms_encoded=[[[list(e),[[list(m),str(c)] for m,c in sorted(p.items())]]
                    for e,p in sorted(f.items())] for f in fs]
    # Extra outer list in each entry is merely a stable serialization wrapper.
    metadata={'forms':forms_encoded,'rows':[list(e) for e in rows],
              'selected_columns':[{'index':k,'form':cols[k][0],'multiplier':list(cols[k][1])} for k in chosen]}
    text=json.dumps(metadata,separators=(',',':'))
    (HERE/'contact_lift_independent_regularity_matrix.json').write_text(text+'\n')
    receipt={'status':'PASS','independent_original_target_and_derivative_reconstruction':True,
      'matrix_shape':[286,453],'selected_minor':286,'exact_product_backend':backend,
      'center_inverse_defect_upper_bound':A.power_upper(center_defect),
      'inverse_norm_upper_bound':A.power_upper(inverse_norm),
      'coordinate_bound':M,'matrix_lipschitz_bound':str(lipschitz),'radius':str(radius),
      'ball_inverse_defect_upper_bound':A.power_upper(ball_defect),
      'strict_ball_neumann_inequality':True,
      'exact_center_defect':str(center_defect),'exact_inverse_norm':str(inverse_norm),
      'exact_ball_defect':str(ball_defect),
      'complete_intersection_degrees':[2,3,4,4],'hilbert_coefficients':hilbert,
      'length':96,'socle_degree':9,'top_graded_dimension':1,
      'weighted_elimination_jacobian_sign':'+1',
      'source_ball_sha256':hashlib.sha256(bp.read_bytes()).hexdigest(),
      'regularity_witness_sha256':hashlib.sha256(wp.read_bytes()).hexdigest(),
      'independent_matrix_sha256':hashlib.sha256(text.encode()).hexdigest(),
      'audit_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'verification_seconds':round(time.monotonic()-started,3),
      'scope':'Exact regularity audit on the certified contact ball, with classical Artinian-complete-intersection consequences. No Lean proof, no trace evaluation, no final certificate.'}
    (HERE/'contact_lift_regularity_audit_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if not k.startswith('exact_')},indent=2),flush=True)

if __name__=='__main__':main()
