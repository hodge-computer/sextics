#!/usr/bin/env python3
"""Transport the actual nine current operands to the point-scaled quotient.

The construction keeps determinant frames as small sparse matrices over a
scalar DAG. It never expands their determinants into contact polynomials.
It is an exact circuit transformation, not an evaluation of an incidence trace.
"""
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
from itertools import product, permutations
import copy, hashlib, json, random, time

HERE=Path(__file__).resolve().parent
CONTACT=HERE.parent/'research_contact'
if not CONTACT.exists():CONTACT=HERE.parent/'proof_attempt4'
QBASE=[(2,0,0,0),(0,2,0,0),(0,0,2,0),(0,0,1,1),(0,0,0,2)]
ABASE=[(3,0,0,0),(0,3,0,0),(1,0,2,0),(1,0,1,1),(1,0,0,2),(0,1,2,0),(0,1,1,1),(0,1,0,2)]
BBASE=[(2,0,1,0),(2,0,0,1),(0,2,1,0),(0,2,0,1),(0,0,3,0),(0,0,2,1),(0,0,1,2),(0,0,0,3)]
def mons(d,even=False):
    return sorted(e for e in product(range(d+1),repeat=4) if sum(e)==d and (not even or (e[2]+e[3])%2==0))
def yd(e):return e[2]+e[3]

class DAG:
    def __init__(self,nodes=()):
        self.nodes=copy.deepcopy(list(nodes));self.memo={}
        for i,n in enumerate(self.nodes):self.memo[self.key(n['op'],n['data'])]=i
        self.zero=self.const(0);self.one=self.const(1);self.dc={}
    def key(self,op,d):return op,tuple(d) if isinstance(d,list) else d
    def make(self,op,d):
        k=self.key(op,d)
        if k not in self.memo:self.memo[k]=len(self.nodes);self.nodes.append({'op':op,'data':d})
        return self.memo[k]
    def const(self,v):
        v=Fraction(v);return self.make('rational',[v.numerator,v.denominator])
    def var(self,n):return self.make('variable',n)
    def add(self,*xs):
        xs=[x for x in xs if x!=self.zero]
        if not xs:return self.zero
        if len(xs)==1:return xs[0]
        return self.make('add',xs)
    def mul(self,*xs):
        if self.zero in xs:return self.zero
        xs=[x for x in xs if x!=self.one]
        if not xs:return self.one
        if len(xs)==1:return xs[0]
        return self.make('multiply',xs)
    def neg(self,x):return self.mul(self.const(-1),x)
    def pow(self,x,n):
        if n==0:return self.one
        if n==1:return x
        if x==self.zero:return self.zero
        if x==self.one:return self.one
        return self.make('power',[x,n])
    def inv(self,x):
        assert x!=self.zero
        if x==self.one:return self.one
        return self.make('inverse',x)
    def diff(self,k,name):
        key=(k,name)
        if key in self.dc:return self.dc[key]
        op,d=self.nodes[k]['op'],self.nodes[k]['data']
        if op=='rational':v=self.zero
        elif op=='variable':v=self.one if d==name else self.zero
        elif op=='add':v=self.add(*(self.diff(i,name) for i in d))
        elif op=='multiply':v=self.add(*(self.mul(self.diff(i,name),*(d[:j]+d[j+1:])) for j,i in enumerate(d)))
        elif op=='power':v=self.mul(self.const(d[1]),self.pow(d[0],d[1]-1),self.diff(d[0],name))
        elif op=='inverse':v=self.neg(self.mul(self.diff(d,name),self.pow(self.inv(d),2)))
        else:raise ValueError(op)
        self.dc[key]=v;return v
    def evaluate(self,values,p):
        out=[]
        for n in self.nodes:
            op,d=n['op'],n['data']
            if op=='rational':v=d[0]*pow(d[1],-1,p)
            elif op=='variable':v=values[d]
            elif op=='add':v=sum(out[i] for i in d)
            elif op=='multiply':
                v=1
                for i in d:v=v*out[i]%p
            elif op=='power':v=pow(out[d[0]],d[1],p)
            elif op=='inverse':v=pow(out[d],-1,p)
            else:raise ValueError(op)
            out.append(v%p)
        return out

def jacobian_polynomial(C,matrix):
    def mul(P,Q):
        out={}
        for e,v in P.items():
            for f,w in Q.items():
                g=tuple(a+b for a,b in zip(e,f));out[g]=C.add(out.get(g,C.zero),C.mul(v,w))
        return out
    out={}
    for perm in permutations(range(4)):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4))
        term={(0,0,0,0):C.const(sign)}
        for i,j in enumerate(perm):
            term=mul(term,{tuple(v['exponent']):v['coefficient_node'] for v in matrix[i][j]})
        for e,v in term.items():out[e]=C.add(out.get(e,C.zero),v)
    return out

def build():
    srcpath=CONTACT/'contact_forms_global_residue.json'
    src=json.loads(srcpath.read_text());forms=json.loads((CONTACT/'contact_forms_residue_system.json').read_text())
    chosen=json.loads((CONTACT/'contact_forms_nonzero_witness.json').read_text())['selected_ideal_columns']
    regchosen=json.loads((CONTACT/'contact_forms_regularity_witness.json').read_text())['selected_columns']
    O=DAG(src['scalar_nodes']);C=DAG();t=C.var('t');ti=C.inv(t)
    r,s=C.var('r'),C.var('s')
    weights={}
    for prefix,basis in [('rho',QBASE),('mu',QBASE),('A',ABASE),('B',BBASE),('g2_',mons(4,True))]:
        weights.update((prefix+str(i),yd(e)) for i,e in enumerate(basis))
    hats={name:C.var(name) for name in weights if name not in ['mu0','A0']}
    hats['mu0']=C.neg(C.add(r,C.mul(hats['mu1'],C.pow(r,2)),hats['mu2'],C.mul(s,hats['mu3']),C.mul(C.pow(s,2),hats['mu4'])))
    h_terms=[]
    for prefix,basis in [('A',ABASE),('B',BBASE)]:
        for j,e in enumerate(basis):
            if prefix=='A' and j==0:continue
            h_terms.append(C.mul(hats[prefix+str(j)],C.pow(r,e[1]),C.pow(s,e[3])))
    hats['A0']=C.neg(C.add(*h_terms))
    pairs={}
    def pmul(a,b):return C.add(C.mul(a[0],b[0]),C.mul(t,a[1],b[1])),C.add(C.mul(a[0],b[1]),C.mul(a[1],b[0]))
    def ppow(a,n):
        v=(C.one,C.zero)
        while n:
            if n&1:v=pmul(v,a)
            a=pmul(a,a);n//=2
        return v
    def conv(k):
        if k in pairs:return pairs[k]
        op,d=O.nodes[k]['op'],O.nodes[k]['data']
        if op=='rational':v=(C.const(Fraction(*d)),C.zero)
        elif op=='variable':
            if d in weights:
                degree=weights[d];base=C.mul(hats[d],C.pow(ti,(degree+1)//2))
                v=(C.zero,base) if degree%2 else (base,C.zero)
            elif d=='alpha':v=(C.zero,C.one)
            else:v=(C.var(d),C.zero)
        elif op=='add':
            ps=[conv(i) for i in d];v=(C.add(*(a for a,b in ps)),C.add(*(b for a,b in ps)))
        elif op=='multiply':
            v=(C.one,C.zero)
            for i in d:v=pmul(v,conv(i))
        elif op=='power':v=ppow(conv(d[0]),d[1])
        elif op=='inverse':
            a,b=conv(d);den=C.inv(C.add(C.pow(a,2),C.neg(C.mul(t,C.pow(b,2)))))
            v=C.mul(a,den),C.neg(C.mul(b,den))
        else:raise ValueError(op)
        pairs[k]=v;return v
    def pure(k,parity):
        a,b=conv(k)
        assert (a if parity else b)==C.zero,('mixed/unexpected parity',k,parity)
        return b if parity else a
    # Derivatives are taken in original coordinates BEFORE substituting hats.
    variables=src['incidence_variable_order'];eqs=src['incidence_equation_nodes']
    oldJ=[[O.diff(eq,v) for v in variables] for eq in eqs]
    colbits=[int(v.startswith('B') or v=='alpha') for v in variables]
    Jbar=[[pure(k,colbits[j]) for j,k in enumerate(row)] for row in oldJ]
    basis=[tuple(e) for e in forms['socle_basis']];bits=[yd(e)%2 for e in basis]
    rowbits=[yd(forms['ideal_product_columns'][j]['multiplier_exponent'])%2 for j in chosen]+[0]
    oldrows=copy.deepcopy(src['determinant_frames']['T9']['first_219_sparse_rows'])
    jac=jacobian_polynomial(O,forms['normalization_jacobian_matrix'])
    oldrows.append([[i,jac[e]] for i,e in enumerate(basis) if e in jac])
    Tbar=[]
    for i,row in enumerate(oldrows):
        Tbar.append([[j,C.mul(pure(k,rowbits[i]^bits[j]),ti if rowbits[i] and bits[j] else C.one)] for j,k in row])
    L=[]
    for i,slot in enumerate(forms['canonical_one_form']['components']):
        parity=1 if i<8 else 0
        assert all(bits[j]==parity for j,k in slot['socle_coefficient_nodes'])
        L.append({'parameter':slot['parameter'],'entries':[[j,pure(k,0)] for j,k in slot['socle_coefficient_nodes']]})
    # D10 is also transported by row/column diagonal alpha factors.
    rows10=src['determinant_frames']['D10']['basis'];rb10=[yd(e)%2 for e in rows10]
    allcb=[]
    for degree in [2,3,4,4]:allcb.extend(yd(e)%2 for e in mons(10-degree))
    cb10=[allcb[j] for j in regchosen]
    Dbar=[]
    for j,col in enumerate(src['determinant_frames']['D10']['sparse_columns']):
        Dbar.append([[i,C.mul(pure(k,rb10[i]^cb10[j]),ti if rb10[i] and cb10[j] else C.one)] for i,k in col])
    operands=[{'source_component':v['source_component'],'x_degree':v['x_degree'],
               'P_node':pure(v['P_coefficient_node'],0),'target_node':pure(v['target_coefficient_node'],0)}
              for v in src['coefficient_obligations']]
    lf=src['localization']['factors']
    opens={n:pure(lf[n],0) for n in ['Delta_node','beta_node','G_w_at_point_node']}
    packet={'schema':'point-scaled-actual-current-v1','coefficient_field':'Q(lambda,r,s)',
        'variables':[v for v in variables if v not in ['mu0','A0','alpha']]+['t'],
        'scalar_nodes':C.nodes,'quadratic_cover':'alpha^2=t; old coefficient c_e=alpha^(-Ydegree(e))*hat(c_e)',
        'eliminated_hat_nodes':{'mu0':hats['mu0'],'A0':hats['A0']},
        'Jbar':Jbar,'Jbar_order':'Original 46-variable Jacobian, with all B columns and the alpha column divided by alpha after substitution.',
        'Hbar':'The first44 rows and first45 columns of Jbar.',
        'Tbar_sparse_rows':Tbar,'Tbar_size':220,'sigma_rhs':{'nonzero_entries':[[219,96]]},
        'Tbar_cubic_sign_rowbits':[int(forms['ideal_product_columns'][j]['form_index']==1) for j in chosen]+[1],
        'L_components':L,'Dbar10_sparse_columns':Dbar,'Dbar10_size':286,
        'Dbar10_cubic_sign_colbits':[int(j>=165 and j<285) for j in regchosen],
        'operand_pairs':operands,'open_nodes':opens,
        'density_scalar_node':t,
        'full_open':'t*Delta*beta*G_w*det(Jbar)*det(Tbar)*det(Dbar10) != 0',
        'density_formula':'Fbar=sum_j Kbar_(10+j)*L_j, where Kbar is the signed cofactor nullvector of Hbar and L_j=dot(component_j,sigma).',
        'actual_source_formula':'M_i=Fbar*P_i/(t*det(Jbar)); no canonical-form chain-rule term was dropped.',
        'global_solve_evaluation':'Solve [Hbar; hbar_alpha*qbar-qbar_alpha*hbar] v=e_last. This45x45 determinant is det(Jbar), a unit on the full open, including in a product algebra. Then M_i=(sum_j v_(10+j)*L_j)*P_i/t. No merely nonzero component pivot is chosen.',
        'factor_identities':{'J':'J=alpha^9*det(Jbar)','K_even_column':'K_j=alpha^8*Kbar_j',
            'K_B_column':'K_j=alpha^7*Kbar_j','eta_A':'eta_A=alpha^(-1)*L_A','eta_B':'eta_B=L_B',
            'f':'f=alpha^7*Fbar','delta9_alpha_exponent':sum(rowbits)+sum(bits),
            'D10_alpha_exponent':sum(rb10)+sum(cb10)},
        'structural_checks':{'all_46_by_46_J_entries_have_required_parity':True,
            'all_T9_and_D10_entries_factor_by_recorded_row_column_parity':True,
            'all_nine_P_and_target_entries_are_even':True,'source_derivatives_taken_before_coordinate_substitution':True},
        'source_packet_sha256':hashlib.sha256(srcpath.read_bytes()).hexdigest(),
        'input_hashes':{name:hashlib.sha256((CONTACT/name).read_bytes()).hexdigest() for name in
            ['contact_forms_global_residue.json','contact_forms_residue_system.json',
             'contact_forms_nonzero_witness.json','contact_forms_regularity_witness.json']},
        'full_trace_evaluated':False,'full_certificate_proved':False}
    return packet,(O,C,oldJ,oldrows,pairs,conv,weights,hats,forms,src)

def evaluate_operands(packet,values,p,check_full_open=True):
    """Evaluate all nine operands using one45x45 solve and one residue solve.

    This does not take a trace. The caller must supply a point (or later a
    quotient-algebra implementation) and separately enforce the44 equations.
    No cofactor determinant or contact-polynomial determinant is expanded.
    """
    import flint
    C=DAG(packet['scalar_nodes']);v=C.evaluate(values,p)
    rows=[[v[k] for k in row] for row in packet['Jbar']]
    augmented=[row[:45] for row in rows[:44]]+[
        [(rows[45][45]*rows[44][j]-rows[44][45]*rows[45][j])%p for j in range(45)]]
    tangent_matrix=flint.nmod_mat(augmented,p).solve(flint.nmod_mat([[0]]*44+[[1]],p))
    tangent=[int(tangent_matrix[j,0]) for j in range(45)]
    den=v[packet['density_scalar_node']]
    if den==0:raise ValueError('A required quadratic-cover coordinate is zero')
    T=[[0]*220 for _ in range(220)]
    for i,row in enumerate(packet['Tbar_sparse_rows']):
        for j,k in row:T[i][j]=v[k]
    sigma=flint.nmod_mat(T,p).solve(flint.nmod_mat([[0]]*219+[[96]],p))
    if check_full_open:
        if any(v[k]==0 for k in packet['open_nodes'].values()):
            raise ValueError('An original non-determinantal open factor vanishes')
        D=[[0]*286 for _ in range(286)]
        for j,col in enumerate(packet['Dbar10_sparse_columns']):
            for i,k in col:D[i][j]=v[k]
        if int(flint.nmod_mat(D,p).det())==0:
            raise ValueError('The selected degree-ten regularity determinant vanishes')
    L=[sum(v[k]*int(sigma[j,0]) for j,k in slot['entries'])%p for slot in packet['L_components']]
    scale=sum(tangent[10+j]*L[j] for j in range(16))*pow(den,-1,p)%p
    return [scale*v[o['P_node']]%p for o in packet['operand_pairs']]

def controls(packet,state,count=3,p=101):
    import flint
    O,C,oldJ,oldrows,pairs,conv,weights,hats,forms,src=state
    rng=random.Random(6106);results=[]
    def dense(rows,values,n):
        M=[[0]*n for _ in rows]
        for i,row in enumerate(rows):
            for j,k in row:M[i][j]=values[k]
        return flint.nmod_mat(M,p)
    def cofactors(M):
        return [((-1)**j*int(flint.nmod_mat([[row[k] for k in range(45) if k!=j] for row in M],p).det()))%p for j in range(45)]
    for attempt in range(50):
        hats_values={v:rng.randrange(p) for v in packet['variables']};alpha=rng.randrange(1,p)
        hats_values.update(lam=1,r=2,s=3,t=alpha*alpha%p)
        new=C.evaluate(hats_values,p)
        oldvals={name:new[node]*pow(pow(alpha,degree,p),-1,p)%p for name,(node,degree) in
                 ((name,(hats[name],degree)) for name,degree in weights.items())}
        oldvals.update(lam=1,r=2,s=3,alpha=alpha)
        old=O.evaluate(oldvals,p)
        for k,(a,b) in pairs.items():assert old[k]==(new[a]+alpha*new[b])%p
        TJ=dense(oldrows,old,220);TB=dense(packet['Tbar_sparse_rows'],new,220)
        J=flint.nmod_mat([[old[k] for k in row] for row in oldJ],p)
        JB=flint.nmod_mat([[new[k] for k in row] for row in packet['Jbar']],p)
        if int(TJ.det())==0 or int(J.det())==0:continue
        rhs=flint.nmod_mat([[0]]*219+[[96]],p);tau=TJ.solve(rhs);sigma=TB.solve(rhs)
        K=cofactors([[old[k] for k in row[:45]] for row in oldJ[:44]])
        KB=cofactors([[new[k] for k in row[:45]] for row in packet['Jbar'][:44]])
        eta=[sum(old[k]*int(tau[j,0]) for j,k in slot['socle_coefficient_nodes'])%p for slot in forms['canonical_one_form']['components']]
        L=[sum(new[k]*int(sigma[j,0]) for j,k in slot['entries'])%p for slot in packet['L_components']]
        f=sum(K[10+j]*eta[j] for j in range(16))%p;fb=sum(KB[10+j]*L[j] for j in range(16))%p
        assert int(J.det())==pow(alpha,9,p)*int(JB.det())%p
        assert f==pow(alpha,7,p)*fb%p
        source=[]
        for pair,oldpair in zip(packet['operand_pairs'],src['coefficient_obligations']):
            a=f*old[oldpair['P_coefficient_node']]*pow(int(J.det()),-1,p)%p
            b=fb*new[pair['P_node']]*pow(hats_values['t']*int(JB.det())%p,-1,p)%p
            assert a==b;source.append(a)
        try:solved_source=evaluate_operands(packet,hats_values,p)
        except ValueError:continue
        assert solved_source==source
        results.append({'alpha':alpha,'modulus':p,'all_nine_source_values_equal':True,
                        'augmented_solve_evaluation_matches_independent_cofactors':True,
                        'all_original_open_factors_nonzero':True,
                        'circuit_node_identities_checked':len(pairs),'on_contact_target':False})
        if len(results)==count:break
    assert len(results)==count
    return results

def main():
    start=time.monotonic();packet,state=build();tests=controls(packet,state)
    path=HERE/'point_scaled_current.json';path.write_text(json.dumps(packet,separators=(',',':'))+'\n')
    receipt={'status':'PASS','scalar_nodes':len(packet['scalar_nodes']),'variables':len(packet['variables']),
        'actual_source_operands':9,'exact_circuit_parity_and_matrix_factor_checks':packet['structural_checks'],
        'modular_reproduction_controls':tests,'witness_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope':'Exact coefficient/derivative circuit transport and row-column factor identities, with independent direct matrix controls. Controls are not contact solutions or traces. No full determinant is expanded into the contact polynomial ring.',
        'full_trace_evaluated':False,'full_certificate_proved':False,'seconds':time.monotonic()-start}
    (HERE/'point_scaled_current_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
