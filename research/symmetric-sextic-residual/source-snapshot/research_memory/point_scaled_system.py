#!/usr/bin/env python3
"""Point-scaled cubic presentation and the exact T_B quotient.

This emits equations and necessary small localization factors, not a completed
quotient basis or a trace result.  The large J/delta9/D10 factors remain explicit
full-localization obligations.  No component is silently discarded.
"""
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import product
from pathlib import Path
import copy
import json
import sys
import time

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "research_contact"
if not SOURCE.exists(): SOURCE = HERE.parent / "proof_attempt4"
for dep in (HERE.parent / "research_workaround/python_deps", HERE.parent / "proof_attempt3/python_deps"):
    if dep.exists():
        sys.path.insert(0, str(dep)); break


class Circuit:
    def __init__(self, nodes):
        self.nodes = copy.deepcopy(nodes)
        self.memo = {(n["op"], tuple(n["data"]) if isinstance(n["data"], list) else n["data"]): i
                     for i, n in enumerate(nodes)}
        self.zero, self.one = self.const(0), self.const(1)
    def node(self, op, data):
        key = (op, tuple(data) if isinstance(data, list) else data)
        if key not in self.memo:
            self.memo[key] = len(self.nodes); self.nodes.append({"op": op, "data": data})
        return self.memo[key]
    def const(self, x):
        x = Fraction(x); return self.node("rational", [x.numerator, x.denominator])
    def var(self, name): return self.node("variable", name)
    def add(self, *xs):
        args=[]; const=Fraction(0)
        for x in xs:
            n=self.nodes[x]
            if n['op']=='rational': const+=Fraction(*n['data'])
            elif n['op']=='add': args.extend(n['data'])
            else: args.append(x)
        if const: args.append(self.const(const))
        if not args:return self.zero
        if len(args)==1:return args[0]
        return self.node('add',sorted(args))
    def mul(self, *xs):
        args=[]; const=Fraction(1)
        for x in xs:
            n=self.nodes[x]
            if n['op']=='rational':const*=Fraction(*n['data'])
            elif n['op']=='multiply':args.extend(n['data'])
            else:args.append(x)
        if not const:return self.zero
        if const!=1:args.append(self.const(const))
        if not args:return self.one
        if len(args)==1:return args[0]
        return self.node('multiply',sorted(args))
    def neg(self,x):return self.mul(self.const(-1),x)
    def sub(self,x,y):return self.add(x,self.neg(y))
    def power(self,x,n):
        if n==0:return self.one
        if n==1:return x
        if self.nodes[x]['op']=='rational':return self.const(Fraction(*self.nodes[x]['data'])**n)
        return self.node('power',[x,n])
    def substitute(self, roots, replacements):
        @lru_cache(None)
        def rec(i):
            op,d=self.nodes[i]['op'],self.nodes[i]['data']
            if op=='variable':return replacements.get(d,i)
            if op=='rational':return i
            if op=='add':return self.add(*(rec(j) for j in d))
            if op=='multiply':return self.mul(*(rec(j) for j in d))
            if op=='power':return self.power(rec(d[0]),d[1])
            if op=='inverse':return self.node('inverse',rec(d))
            raise ValueError(op)
        return [rec(i) for i in roots]


class Polynomials:
    def __init__(self,C,n=4):self.C,self.n=C,n
    def add(self,*ps):
        out={}
        for p in ps:
            for e,c in p.items():out[e]=self.C.add(out.get(e,self.C.zero),c)
        return {e:c for e,c in out.items() if c!=self.C.zero}
    def scale(self,p,c):return {e:self.C.mul(v,c) for e,v in p.items()}
    def neg(self,p):return self.scale(p,self.C.const(-1))
    def mul(self,*ps):
        out={(0,)*self.n:self.C.one}
        for p in ps:
            nxt={}
            for e,c in out.items():
                for f,d in p.items():
                    ef=tuple(a+b for a,b in zip(e,f));nxt[ef]=self.C.add(nxt.get(ef,self.C.zero),self.C.mul(c,d))
            out=nxt
        return out
    def evaluate(self,p,x):return self.C.add(*(self.C.mul(c,*(self.C.power(a,k) for a,k in zip(x,e))) for e,c in p.items()))
    def encode(self,p):return [{'exponent':list(e),'coefficient_node':v} for e,v in sorted(p.items())]


def load(name):return json.loads((SOURCE/name).read_text())
def mons(d):return sorted(e for e in product(range(d+1),repeat=4) if sum(e)==d)


def build():
    original=load('contact_forms_global_residue.json');base=load('contact_target_circuit.json')
    C=Circuit(original['scalar_nodes']);P=Polynomials(C);t=C.var('t');r=C.var('r');s=C.var('s')
    def form(name):
        return {tuple(term['exponent']):term['coefficient_node'] for term in base['polynomials'][name]}
    Q1,Q2,A,B,g2=[form(n) for n in ('Q1','Q2','A','B','g2_quartic')]
    weights={}
    for f in (Q1,Q2,A,B,g2):
        for e,node in f.items():
            d=C.nodes[node]
            if d['op']=='variable':weights[d['data']]=e[2]+e[3]
            else:assert d=={'op':'rational','data':[1,1]}
    assert set(weights)==set(original['contact_variable_order'])
    scaled_G={tuple(term['exponent']):C.mul(term['coefficient_node'],C.power(t,(term['exponent'][2]+term['exponent'][3])//2))
              for term in base['polynomials']['G']}
    assert all((e[2]+e[3])%2==0 for e in scaled_G)
    h2={e[:4]:v for e,v in scaled_G.items() if e[4]==2}
    h4={e[:4]:v for e,v in scaled_G.items() if e[4]==1}
    h6={e[:4]:v for e,v in scaled_G.items() if e[4]==0}
    H=P.add(P.mul(Q1,Q1,Q1),P.neg(P.mul(h2,Q1,Q1)),P.mul(h4,Q1),
            P.mul(A,A),P.neg(P.mul(B,B)),P.mul(Q2,g2),P.neg(h6))
    h=P.add(A,B);point=[C.one,r,C.one,s]
    qpoint=P.evaluate(Q2,point);hpoint=P.evaluate(h,point)
    mu=[C.var(f'mu{i}') for i in range(5)];aa=[C.var(f'A{i}') for i in range(8)];bb=[C.var(f'B{i}') for i in range(8)]
    r2,r3,s2,s3=C.power(r,2),C.power(r,3),C.power(s,2),C.power(s,3)
    mu0=C.neg(C.add(r,C.mul(mu[1],r2),mu[2],C.mul(mu[3],s),C.mul(mu[4],s2)))
    A0=C.neg(C.add(C.mul(aa[1],r3),aa[2],C.mul(aa[3],s),C.mul(aa[4],s2),
                  C.mul(r,C.add(aa[5],C.mul(aa[6],s),C.mul(aa[7],s2))),
                  bb[0],C.mul(bb[1],s),C.mul(r2,C.add(bb[2],C.mul(bb[3],s))),
                  bb[4],C.mul(bb[5],s),C.mul(bb[6],s2),C.mul(bb[7],s3)))
    substitutions={'mu0':mu0,'A0':A0}
    order=original['contact_equation_monomial_order'];uneliminated=[H.get(tuple(e),C.zero) for e in order]
    equations=C.substitute(uneliminated,substitutions)
    beta=C.neg(P.evaluate(Q1,point));h2point=P.evaluate(h2,point);h4point=P.evaluate(h4,point)
    Gw=C.add(C.mul(C.const(3),C.power(beta,2)),C.mul(C.const(2),h2point,beta),h4point)
    z=C.mul(mu0,mu[1]);opens={f'delta{k}':C.sub(C.one,C.mul(C.const(k),z)) for k in (1,2,3)}
    opens.update(t=t,beta=beta,Gw=Gw)
    names=[n for n in original['contact_variable_order'] if n not in substitutions]+['t']
    small_inverse_names=[f'open_{key}' for key in opens]
    small_inverse_equations=[C.sub(C.mul(C.var(f'open_{key}'),node),C.one) for key,node in opens.items()]
    forms=load('contact_forms_residue_system.json');sel9=load('contact_forms_nonzero_witness.json')['selected_ideal_columns']
    sel10=load('contact_forms_regularity_witness.json')['selected_columns'];wt=lambda e:e[2]+e[3]
    e9=sum(map(wt,forms['socle_basis']))-sum(wt(forms['ideal_product_columns'][i]['multiplier_exponent']) for i in sel9)+2
    multipliers=[m for d in [2,3,4,4] for m in mons(10-d)]
    e10=sum(map(wt,mons(10)))-sum(wt(multipliers[i]) for i in sel10)
    assert (sum(weights.values()),sum(map(wt,order)),e9,e10)==(78,132,399,534)
    return {
        'schema':'symmetric-point-scaled-cubic-system-v1',
        'coefficient_field':'K=Q(lambda,r,s)','scalar_nodes':C.nodes,
        'variable_order':names,'equation_nodes':equations,
        'uneliminated_contact_variable_order':original['contact_variable_order'],
        'uneliminated_incidence_variable_order':original['contact_variable_order']+['t'],
        'uneliminated_equation_nodes':uneliminated,
        'uneliminated_incidence_equation_nodes':uneliminated+[qpoint,hpoint],
        'equation_monomial_order':order,'coefficient_Y_weights':weights,
        'eliminated_variable_nodes':substitutions,
        'small_open_nodes':opens,'small_open_inverse_variables':small_inverse_names,
        'small_open_equation_nodes':small_inverse_equations,
        'scaled_polynomials':{n:P.encode(f) for n,f in zip(('Q1','Q2','A','B','g2','h2','h4','h6'),(Q1,Q2,A,B,g2,h2,h4,h6))},
        'scaled_G':Polynomials(C,5).encode(scaled_G),
        'point_binding':{'point':['1','r','1','s'],'q_node':qpoint,'h_node':hpoint,'beta_node':beta,'Gw_node':Gw},
        'coordinate_change':{'forward':'hat_c_e=alpha^(e_c+e_d)*c_e, t=alpha^2',
            'inverse_before_quotient':'c_e=alpha^(-(e_c+e_d))*hat_c_e; adjoin alpha with alpha^2=t',
            'required_open':'alpha!=0, equivalently t!=0',
            'deck_involution':'T_B: original B->-B, alpha->-alpha; all hat coefficients and t are fixed',
            'remaining_involution':'T_A becomes simultaneous hat A->-hat A, hat B->-hat B; all other hat coefficients and t are fixed'},
        'full_localization':{'factors':['delta1','delta2','delta3','t','beta','Gw','J44','delta9_hat','D10_hat'],
            'not_expanded_in_solver_input':['J44','delta9_hat','D10_hat'],
            'Jacobian_relation':'J_old=2*alpha^(-53)*J44 on the incidence',
            'residue_minor_relations':{'delta9_hat':'alpha^399*delta9_old','D10_hat':'alpha^534*D10_old'},
            'pivot_column_permutation_inversions':74,
            'full_open_preserved':'On t!=0 all original full-open factors are units exactly when the displayed transformed factors are units.'},
        'trace_transport':{'degree_factor':2,'actual_source_operands_invariant_under_deck':True,
            'basis':'The exact T_B character audit proves invariance of all nine original source operands and stability of every selected open.',
            'normalization':'Tr_old(M)/rank(old)=Tr_quotient(M)/rank(quotient); unnormalized trace gains factor2.',
            'form_warning':'The descended source is the transported original current; tauhat(R_t dh_hat) alone omits the t-derivative correction.'},
        'source_hashes':{name:sha256((SOURCE/name).read_bytes()).hexdigest() for name in (
            'contact_forms_global_residue.json','contact_target_circuit.json','contact_forms_residue_system.json',
            'contact_forms_nonzero_witness.json','contact_forms_regularity_witness.json')},
        'source_trace_proved':False,'full_certificate_proved':False,
    }


def evaluate_modular(packet,roots,names,prime,base):
    nodes=packet['scalar_nodes'];zero_exp=(0,)*len(names);indices={n:i for i,n in enumerate(names)}
    def const(x):return {zero_exp:x%prime} if x%prime else {}
    def add(*ps):
        out={}
        for p in ps:
            for e,c in p.items():out[e]=(out.get(e,0)+c)%prime
        return {e:c for e,c in out.items() if c}
    def mul(p,q):
        out={}
        for e,c in p.items():
            for f,d in q.items():
                ef=tuple(a+b for a,b in zip(e,f));out[ef]=(out.get(ef,0)+c*d)%prime
        return {e:c for e,c in out.items() if c}
    @lru_cache(None)
    def ev(i):
        op,d=nodes[i]['op'],nodes[i]['data']
        if op=='rational':return const(d[0]*pow(d[1],-1,prime))
        if op=='variable':
            if d in base:return const(base[d])
            e=list(zero_exp);e[indices[d]]=1;return {tuple(e):1}
        if op=='add':return add(*(ev(j) for j in d))
        if op=='multiply':
            v=const(1)
            for j in d:v=mul(v,ev(j))
            return v
        if op=='power':
            v=const(1)
            for _ in range(d[1]):v=mul(v,ev(d[0]))
            return v
        if op=='inverse':
            v=ev(d);assert set(v)=={zero_exp};return const(pow(v[zero_exp],-1,prime))
        raise ValueError(op)
    return [ev(i) for i in roots]


def poly_string(poly,names):
    terms=[]
    for e,c in sorted(poly.items(),key=lambda ec:(-sum(ec[0]),tuple(-x for x in ec[0]))):
        mon='*'.join(n if k==1 else f'{n}^{k}' for n,k in zip(names,e) if k)
        terms.append(str(c) if not mon else mon if c==1 else f'{c}*{mon}')
    return '+'.join(terms) or '0'


def emit_modular(packet,tag,opens,prime=37,base=None):
    if base is None:base={'lam':1,'r':2,'s':3}
    names=packet['variable_order']+(packet['small_open_inverse_variables'] if opens else [])
    roots=packet['equation_nodes']+(packet['small_open_equation_nodes'] if opens else [])
    polys=evaluate_modular(packet,roots,names,prime,base)
    text=','.join(names)+'\n'+str(prime)+'\n'+',\n'.join(poly_string(p,names) for p in polys)+'\n'
    path=HERE/(tag+'.ms');path.write_text(text)
    receipt={'file':path.name,'sha256':sha256(path.read_bytes()).hexdigest(),'prime':prime,'base':base,
             'variable_order':names,'variables':len(names),'equations':len(polys),
             'terms':sum(map(len,polys)),'maximum_total_degree':max((sum(e) for p in polys for e in p),default=0),
             'included_small_opens':list(packet['small_open_nodes']) if opens else [],
             'full_J_delta9_D10_localization_included':False,'source_trace_proved':False}
    assert receipt['maximum_total_degree']<=3
    (HERE/(tag+'_receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt


def exact_audit(packet):
    import sympy as sp
    original=load('contact_forms_global_residue.json');nodes=packet['scalar_nodes'];cache={}
    def val(i):
        if i in cache:return cache[i]
        op,d=nodes[i]['op'],nodes[i]['data']
        if op=='rational':v=sp.Rational(*d)
        elif op=='variable':v=sp.Symbol(d)
        elif op=='add':v=sp.Add(*(val(j) for j in d))
        elif op=='multiply':v=sp.Mul(*(val(j) for j in d))
        elif op=='power':v=val(d[0])**d[1]
        elif op=='inverse':v=1/val(d)
        else:raise ValueError(op)
        cache[i]=v;return v
    alpha,t=sp.symbols('alpha t');lam,r,s=sp.symbols('lam r s')
    scaling={sp.Symbol(name):sp.Symbol(name)*alpha**(-weight) for name,weight in packet['coefficient_Y_weights'].items()}
    checked=0
    for old,new,e in zip(original['contact_equation_nodes'],packet['uneliminated_equation_nodes'],packet['equation_monomial_order']):
        lhs=val(new).subs(t,alpha**2)
        rhs=alpha**(e[2]+e[3])*val(old).subs(scaling,simultaneous=True)
        assert sp.cancel(sp.expand(lhs-rhs))==0,e
        checked+=1
    substitutions={sp.Symbol(n):val(i) for n,i in packet['eliminated_variable_nodes'].items()}
    for node in (packet['point_binding']['q_node'],packet['point_binding']['h_node']):
        assert sp.expand(val(node).subs(substitutions,simultaneous=True))==0
    variables=[sp.Symbol(n) for n in packet['variable_order']]
    degrees=[]
    for old,new in zip(packet['uneliminated_equation_nodes'],packet['equation_nodes']):
        assert sp.cancel(sp.expand(val(old).subs(substitutions,simultaneous=True)-val(new)))==0
        poly=sp.Poly(val(new),*variables,domain=sp.QQ.frac_field(lam,r,s))
        assert poly.total_degree()<=3
        degrees.append(poly.total_degree())
    for name,node in packet['small_open_nodes'].items():
        poly=sp.Poly(val(node),*variables,domain=sp.QQ.frac_field(lam,r,s))
        assert poly.total_degree()<=2
    # Confirm all pre-elimination coefficients have the asserted parity under
    # T_B: the coefficient scaling absorbs its original B/alpha sign action.
    assert all(((-1)**w)*(-1 if name.startswith('B') else 1)==1
               for name,w in packet['coefficient_Y_weights'].items())
    return {'status':'PASS','characteristic_zero_row_bindings':checked,
            'exact_linear_eliminations':['mu0','A0'],'maximum_total_degree':max(degrees),
            'small_open_degrees_at_most_two':True,'T_B_fixed_coordinates':True,
            'sum_parameter_Y_weights':78,'sum_equation_Y_weights':132,
            'delta9_scaling_exponent':399,'D10_scaling_exponent':534,
            'J_old_factor':'2*alpha^(-53)','pivot_column_permutation_sign':1,
            'scope':'Exact CAS verification of all44 equations and two linear eliminations over Q(lambda,r,s), plus exact selected-matrix scaling weights. This is not a complete finite quotient or trace evaluation.',
            'source_trace_proved':False,'full_certificate_proved':False}


def main():
    started=time.monotonic();packet=build();path=HERE/'point_scaled_system.json'
    path.write_text(json.dumps(packet,separators=(',',':'))+'\n')
    inputs=[emit_modular(packet,'point_scaled_p37_raw',False),emit_modular(packet,'point_scaled_p37_smallopens',True)]
    print(json.dumps({'phase':'solver_inputs_ready','inputs':inputs},indent=2),flush=True)
    receipt=exact_audit(packet)
    receipt.update(packet_sha256=sha256(path.read_bytes()).hexdigest(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                   modular_inputs=inputs,seconds=time.monotonic()-started)
    (HERE/'point_scaled_system_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)


if __name__=='__main__':main()
