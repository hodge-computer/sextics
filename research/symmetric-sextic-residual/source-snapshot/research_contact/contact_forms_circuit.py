#!/usr/bin/env python3
"""Actual canonical contact form and Jacobian-residue source circuit.

Extends the exact protected norm-contact circuit. It emits the degree-nine
Macaulay dual system for the canonical one-form and the nine numerator/target
coefficient pairs for a subsequent global-residue computation. No successful
source trace is asserted. The accompanying regularity certificate establishes
that the canonical residue functional exists on the certified component.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product
import copy, hashlib, json, os, sys

HERE=Path(__file__).resolve().parent
OLD=HERE.parent/'research_workaround'
if not OLD.exists():OLD=HERE.parent/'proof_attempt3'
sys.path.insert(0,str(OLD))
import symmetric_norm_contact_circuit as N


class Polynomials:
    def __init__(self,C,n):self.C,self.n=C,n
    def const(self,c):return {(0,)*self.n:c} if c!=self.C.zero else {}
    def coord(self,j):return {tuple(int(i==j) for i in range(self.n)):self.C.one}
    def add(self,*polys):
        out={}
        for p in polys:
            for e,v in p.items():out[e]=self.C.add(out.get(e,self.C.zero),v)
        return {e:v for e,v in out.items() if v!=self.C.zero}
    def scale(self,p,c):return {e:self.C.mul(v,c) for e,v in p.items() if self.C.mul(v,c)!=self.C.zero}
    def neg(self,p):return self.scale(p,self.C.const(-1))
    def mul(self,*polys):
        out=self.const(self.C.one)
        for p in polys:
            new={}
            for e,v in out.items():
                for f,w in p.items():
                    g=tuple(a+b for a,b in zip(e,f))
                    new[g]=self.C.add(new.get(g,self.C.zero),self.C.mul(v,w))
            out={e:v for e,v in new.items() if v!=self.C.zero}
        return out
    def pow(self,p,n):return self.mul(*([p]*n))
    def diff(self,p,j):
        return {tuple(x-int(i==j) for i,x in enumerate(e)):self.C.mul(v,self.C.const(e[j]))
                for e,v in p.items() if e[j]}
    def evaluate(self,p,x):
        return self.C.add(*(self.C.mul(v,*(self.C.pow(a,n) for a,n in zip(x,e)))
                            for e,v in p.items()))
    def shift(self,p,e):return {tuple(x+y for x,y in zip(e,f)):v for f,v in p.items()}
    def encode(self,p):return [{'exponent':list(e),'coefficient_node':v} for e,v in sorted(p.items())]


def mons(d):return sorted(e for e in product(range(d+1),repeat=4) if sum(e)==d)


def build():
    base_path=HERE/'contact_target_circuit.json'
    if not base_path.exists():base_path=OLD/'symmetric_norm_contact_circuit.json'
    packet=json.loads(base_path.read_text())
    C=N.Circuit();C.nodes=copy.deepcopy(packet['nodes']);C.solves=copy.deepcopy(packet['linear_solves'])
    C.memo={(v['op'],tuple(v['data']) if isinstance(v['data'],list) else v['data']):i
            for i,v in enumerate(C.nodes)}
    P=Polynomials(C,4);X=Polynomials(C,1)
    def source(name):return {tuple(t['exponent']):t['coefficient_node'] for t in packet['polynomials'][name]}
    Q1,Q2,A,B,g2=[source(name) for name in ('Q1','Q2','A','B','g2_quartic')]
    h=P.add(A,B);k=P.add(A,P.neg(B))
    G=source('G');ell=packet['ell_node'];lam=C.var('lam')
    h2={e[:4]:v for e,v in G.items() if e[4]==2}
    h4={e[:4]:v for e,v in G.items() if e[4]==1}
    g1bar=P.add(P.scale(P.pow(Q1,2),C.const(3)),P.scale(P.mul(h2,Q1),C.const(-2)),h4)
    a,b,c,d=[P.coord(i) for i in range(4)]
    Rbar=P.scale(P.mul(b,d,P.add(P.pow(a,2),Q1),
                     P.add(P.pow(c,2),P.scale(Q1,C.pow(lam,2)))),
                 C.mul(C.const(2),C.pow(C.inv(ell),2)))
    fs=[Q2,h,g1bar,g2];degrees=[2,3,4,4]
    rows=mons(9);index={e:i for i,e in enumerate(rows)};columns=[]
    for j,(f,degree) in enumerate(zip(fs,degrees)):
        for m in mons(9-degree):
            columns.append({'form_index':j,'multiplier_exponent':list(m),
                'entries':[[index[tuple(x+y for x,y in zip(e,m))],v] for e,v in sorted(f.items())]})
    assert len(rows)==220 and len(columns)==316
    eta=[]
    for j,e in enumerate(N.ABASE+N.BBASE):
        numerator=P.shift(Rbar,e)
        eta.append({'parameter':packet['parameter_order'][10+j],
                    'socle_coefficient_nodes':[[index[f],v] for f,v in sorted(numerator.items())]})

    # Incidence partials hold the contact parameters fixed.
    r,s,alpha=[C.var(v) for v in ('r','s','alpha')]
    point=[C.one,r,alpha,C.mul(s,alpha)]
    def partials(f):
        fr=P.evaluate(P.diff(f,1),point)
        fs=C.mul(alpha,P.evaluate(P.diff(f,3),point))
        fa=C.add(P.evaluate(P.diff(f,2),point),C.mul(s,P.evaluate(P.diff(f,3),point)))
        return fr,fs,fa
    qr,qs,qa=partials(Q2);hr,hs,ha=partials(h)
    br,bs,ba=partials(P.neg(Q1));beta=packet['point_beta_node']
    sub=lambda a,b:C.add(a,C.neg(b))
    un=sub(C.mul(qa,hr),C.mul(ha,qr))
    vn=sub(C.mul(qa,hs),C.mul(ha,qs))
    zn=sub(C.mul(qr,hs),C.mul(qs,hr))
    yn=C.add(C.mul(ba,zn),C.mul(un,bs),C.neg(C.mul(vn,br)))
    qalpha=C.pow(alpha,2);x=X.coord(0)

    # Actual coefficient polynomials a(x),b(x),c(x) and their base partials.
    coeff=[];coeffr=[];coeffs=[]
    for power in (2,1,0):
        block={};dr={};ds={}
        for e,v in G.items():
            if e[4]!=power:continue
            assert (e[2]+e[3])%2==0
            degree=((e[2]+e[3])//2,)
            term=C.mul(v,C.pow(r,e[1]),C.pow(s,e[3]))
            block[degree]=C.add(block.get(degree,C.zero),term)
            if e[1]:dr[degree]=C.add(dr.get(degree,C.zero),C.mul(v,C.const(e[1]),C.pow(r,e[1]-1),C.pow(s,e[3])))
            if e[3]:ds[degree]=C.add(ds.get(degree,C.zero),C.mul(v,C.const(e[3]),C.pow(r,e[1]),C.pow(s,e[3]-1)))
        coeff.append(block);coeffr.append(dr);coeffs.append(ds)
    aa,bb,cc=coeff
    ra,rb,rc=[X.add(X.scale(ds,un),X.scale(dr,C.neg(vn))) for dr,ds in zip(coeffr,coeffs)]
    da,db,dc=[X.add(X.scale(X.mul(x,X.diff(f,0)),C.mul(C.const(-2),zn)),
                   X.scale(rf,C.neg(alpha))) for f,rf in zip(coeff,(ra,rb,rc))]
    aq,bq=[X.evaluate(f,[qalpha]) for f in (aa,bb)]
    dq=C.add(beta,aq);eq=C.add(C.pow(beta,2),C.mul(aq,beta),bq)
    aqmotion=C.add(X.evaluate(ra,[qalpha]),C.mul(C.const(2),alpha,zn,X.evaluate(X.diff(aa,0),[qalpha])))
    bqmotion=C.add(X.evaluate(rb,[qalpha]),C.mul(C.const(2),alpha,zn,X.evaluate(X.diff(bb,0),[qalpha])))
    dd=C.mul(C.neg(alpha),C.add(yn,aqmotion))
    de=C.mul(C.neg(alpha),C.add(C.mul(C.add(C.mul(C.const(2),beta),aq),yn),C.mul(beta,aqmotion),bqmotion))
    # Exact universal general-cubic source formulas, linear in the form.
    N1=X.add(
        X.mul(da,X.add(X.scale(X.mul(aa,bb),dq),X.scale(X.pow(bb,2),C.const(-2)),X.scale(bb,C.mul(C.const(-2),eq)),X.scale(cc,C.mul(C.const(3),dq)))),
        X.mul(db,X.add(X.mul(aa,bb),X.scale(bb,C.mul(C.const(-2),dq)),X.scale(cc,C.const(3)))),
        X.mul(dc,X.add(X.scale(bb,C.const(-2)),X.const(C.mul(C.const(6),eq)))),
        X.scale(X.add(X.neg(X.mul(X.pow(aa,2),bb)),X.scale(X.mul(aa,cc),C.const(-3)),X.scale(X.pow(bb,2),C.const(4))),dd),
        X.scale(X.add(X.mul(aa,bb),X.scale(cc,C.const(-9))),de))
    N2=X.add(
        X.mul(da,X.add(X.scale(X.pow(aa,2),dq),X.scale(X.mul(aa,bb),C.const(-2)),X.scale(aa,C.mul(C.const(-2),eq)),X.scale(cc,C.const(6)))),
        X.mul(db,X.add(X.pow(aa,2),X.scale(aa,C.mul(C.const(-2),dq)),X.const(C.mul(C.const(3),eq)))),
        X.mul(dc,X.add(X.scale(aa,C.const(-2)),X.const(C.mul(C.const(3),dq)))),
        X.scale(X.add(X.neg(X.pow(aa,3)),X.scale(X.mul(aa,bb),C.const(4)),X.scale(cc,C.const(-9))),dd),
        X.scale(X.add(X.pow(aa,2),X.scale(bb,C.const(-3))),de))
    def divide(f):
        degree=max(e[0] for e in f);carry=C.zero;quot={}
        for i in range(degree,0,-1):
            carry=C.add(f.get((i,),C.zero),C.mul(qalpha,carry));quot[(i-1,)]=carry
        remainder=C.add(f.get((0,),C.zero),C.mul(qalpha,carry))
        return quot,remainder
    P1,rem1=divide(N1);P2,rem2=divide(N2)
    assert max(i[0] for i in P1)<=4 and max(i[0] for i in P2)<=3
    cf=C.mul(C.const(2),r,s,C.pow(C.inv(ell),2))
    target1=X.scale(X.mul(x,X.add(X.scale(bb,C.pow(lam,2)),X.scale(x,C.const(-3)))),cf)
    target2=X.scale(X.mul(x,X.add(X.scale(x,C.const(3)),X.const(C.mul(C.const(3),C.pow(lam,2))),
                     X.scale(aa,C.mul(C.const(2),C.pow(lam,2))))),C.mul(cf,C.const(Fraction(1,2))))
    target_pairs=[]
    for i,source,target,n in [(1,P1,target1,5),(2,P2,target2,4)]:
        for j in range(n):target_pairs.append({'source_component':i,'x_degree':j,
            'P_coefficient_node':source.get((j,),C.zero),'target_coefficient_node':target.get((j,),C.zero)})
    source_point_motion=C.add(
        C.mul(C.add(C.mul(C.const(3),C.pow(beta,2)),C.mul(C.const(2),aq,beta),bq),yn),
        C.mul(C.const(2),alpha,zn,C.add(*(C.mul(X.evaluate(X.diff(f,0),[qalpha]),C.pow(beta,power))
                                                    for f,power in zip(coeff,(2,1,0))))),
        C.add(*(C.mul(X.evaluate(rf,[qalpha]),C.pow(beta,power)) for rf,power in zip((ra,rb,rc),(2,1,0)))))
    return {'schema':'symmetric-canonical-contact-form-and-trace-v1',
        'base_circuit_sha256':hashlib.sha256(base_path.read_bytes()).hexdigest(),
        'base_circuit_file':os.path.relpath(base_path,HERE),
        'coefficient_field':'Q(lambda)',
        'source_polynomial':'R=2*b*d*(a^2-u)*(c^2-lambda^2*u)/ell^2',
        'source_after_u_elimination':P.encode(Rbar),
        'residue_forms':{name:P.encode(f) for name,f in zip(('Q2','h','g1bar','g2'),fs)},
        'residue_form_degrees':degrees,'residue_length':96,'socle_degree':9,
        'socle_basis':[list(e) for e in rows],'ideal_product_columns':columns,
        'normalization_jacobian_matrix':[[P.encode(P.diff(f,j)) for j in range(4)] for f in fs],
        'dual_functional_definition':{'unknowns':'tau[0:220]',
            'linear_equations':'tau annihilates every ideal_product_column; tau(coefficients(det(normalization_jacobian_matrix)))=96',
            'existence_guard':'The degree-ten Macaulay map is surjective, certified on the actual root ball by contact_forms_regularity.py.'},
        'canonical_one_form':{'formula':'eta_R=sum_j tau(R * partial(h)/partial(p_j)) dp_j',
            'zero_components':packet['parameter_order'][:10],
            'components':eta,
            'differentiate_before_eliminating_u':True,
            'closedness':'The coefficients depend only on the contact parameters and lambda; restriction to the one-dimensional contact curve gives d_relative_lambda eta_R=0. Thus d(eta_R wedge d(lambda))=0.'},
        'cofactor_tangent':{'parameter_order':packet['parameter_order'],
            'formula':'K_j=(-1)^(25+j) det(dE/dp with column j omitted), j=0,...,25',
            'canonical_density':'f=sum_j K_j*eta_R[j]',
            'incidence_Jacobian':'J=det d(E_1,...,E_25,q,h)/d(p_0,...,p_25,alpha)=(K.q_p)*h_alpha-q_alpha*(K.h_p)'},
        'point_partial_nodes':dict(zip(('q_r','q_s','q_alpha','h_r','h_s','h_alpha','beta_r','beta_s','beta_alpha'),(qr,qs,qa,hr,hs,ha,br,bs,ba))),
        'current_numerator_nodes':{'u':un,'v':vn,'z':zn,'y':yn},
        'current_conversion':'U=f*u/J, V=f*v/J, Z=f*z/J, Y=f*y/J, M_i=f*P_i/J',
        'P1':X.encode(P1),'P2':X.encode(P2),
        'remainder_nodes':[rem1,rem2],'point_equation_node':packet['point_binding']['left_G_at_point_node'],
        'point_motion_node':source_point_motion,
        'target_pairs':target_pairs,
        'trace_obligation':{'identity':'For each of the nine target_pairs: Res_incidence(f*P_coefficient)=n*target_coefficient.',
            'residue':'Res_incidence(H)=sum over the chosen finite etale component H(point)/J(point).',
            'normalization':'n is the degree of that component over Q(lambda,r,s), including any required constant field extension.',
            'equivalent':'Tr(M_i)/n equals the exact protected target coefficient polynomial.',
            'status':'NOT VERIFIED: this circuit computes the required functions but no finite algebra trace has been evaluated.'},
        'nodes':C.nodes,'linear_solves':C.solves,
        'scope':'Actual target form and source circuit. Exact local regularity and universal algebra are checked separately. No final source trace or HasCertificate claim.'}


def main():
    packet=build();path=HERE/'contact_forms_residue_system.json'
    path.write_text(json.dumps(packet,separators=(',',':'))+'\n')
    receipt={'node_count':len(packet['nodes']),'socle_rows':220,'ideal_columns':316,
        'canonical_cubic_parameter_slots':16,'source_coefficient_obligations':len(packet['target_pairs']),
        'P1_x_degree':4,'P2_x_degree':3,'output_bytes':path.stat().st_size,
        'output_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'source_trace_proved':False,'full_certificate_proved':False}
    (HERE/'contact_forms_circuit_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
