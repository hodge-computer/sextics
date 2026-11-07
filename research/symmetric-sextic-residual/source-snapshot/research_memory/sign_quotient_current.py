#!/usr/bin/env python3
"""Exact current transport for the eight disjoint B-pivot sign quotients.

No exceptional stratum is discarded. Source operands are transported, not
replaced by a simpler but inequivalent canonical-form formula.
"""
from pathlib import Path
import hashlib,json,random,time
from fractions import Fraction
import point_scaled_current as P
HERE=Path(__file__).resolve().parent

def build(old,j):
    assert 0<=j<8
    C=P.DAG();z=C.var('z');zi=C.inv(z);pairs={}
    def mul(a,b):return C.add(C.mul(a[0],b[0]),C.mul(z,a[1],b[1])),C.add(C.mul(a[0],b[1]),C.mul(a[1],b[0]))
    def power(a,n):
        out=C.one,C.zero
        while n:
            if n&1:out=mul(out,a)
            a=mul(a,a);n//=2
        return out
    def conv(k):
        if k in pairs:return pairs[k]
        op,d=old['scalar_nodes'][k]['op'],old['scalar_nodes'][k]['data']
        if op=='rational':v=C.const(Fraction(*d)),C.zero
        elif op=='variable':
            if d.startswith('A'):v=C.zero,C.var(d)
            elif d.startswith('B'):
                index=int(d[1:]);v=(C.zero,C.zero) if index<j else (C.zero,C.one if index==j else C.var(d))
            else:v=C.var(d),C.zero
        elif op=='add':
            vv=[conv(i) for i in d];v=C.add(*(a for a,b in vv)),C.add(*(b for a,b in vv))
        elif op=='multiply':
            v=C.one,C.zero
            for i in d:v=mul(v,conv(i))
        elif op=='power':v=power(conv(d[0]),d[1])
        elif op=='inverse':
            a,b=conv(d);den=C.inv(C.add(C.pow(a,2),C.neg(C.mul(z,C.pow(b,2)))))
            v=C.mul(a,den),C.neg(C.mul(b,den))
        else:raise ValueError(op)
        pairs[k]=v;return v
    def pure(k,bit):
        a,b=conv(k);assert (a if bit else b)==C.zero,(j,k,bit)
        return b if bit else a
    def fact(k,rb,cb):return C.mul(pure(k,rb^cb),zi if rb and cb else C.one)
    J=[]
    for rowi,row in enumerate(old['Jbar']):
        J.append([fact(k,int(rowi==45),int(10<=coli<26)) for coli,k in enumerate(row)])
    T=[[[coli,pure(k,old['Tbar_cubic_sign_rowbits'][rowi])] for coli,k in row]
       for rowi,row in enumerate(old['Tbar_sparse_rows'])]
    D=[[[rowi,pure(k,old['Dbar10_cubic_sign_colbits'][coli])] for rowi,k in col]
       for coli,col in enumerate(old['Dbar10_sparse_columns'])]
    L=[{'parameter':v['parameter'],'entries':[[i,pure(k,0)] for i,k in v['entries']]} for v in old['L_components']]
    operands=[dict(v,P_node=pure(v['P_node'],1),target_node=pure(v['target_node'],0)) for v in old['operand_pairs']]
    opens={name:pure(k,0) for name,k in old['open_nodes'].items()}
    density=C.mul(C.var('t'),z)
    variables=[v for v in old['variables'] if not(v.startswith('B') and int(v[1:])<=j)]+['z']
    packet={'schema':'disjoint-B-pivot-current-v1','pivot_index':j,'variables':variables,
        'stratum':f'B0=...=B{j-1}=0, B{j}!=0' if j else 'B0!=0',
        'substitution':f'hatB{j}=b, b^2=z; all hatA_i=b*A_i; hatB_i=b*B_i for i>{j}; earlier hatB_i=0',
        'scalar_nodes':C.nodes,'Jbar':J,'Tbar_sparse_rows':T,'Tbar_size':220,
        'sigma_rhs':{'nonzero_entries':[[219,96]]},'L_components':L,
        'Dbar10_sparse_columns':D,'Dbar10_size':286,'operand_pairs':operands,'open_nodes':opens,
        'density_scalar_node':density,
        'full_open':'t*z*Delta*beta*G_w*det(J2)*det(T2)*det(D2) != 0',
        'actual_source_formula':'M_i=F2*P2_i/(t*z*det(J2)); evaluate with one globally invertible45x45 augmented incidence solve and one T2 solve.',
        'factor_identities':{'Jbar':'Jbar=b^17*det(J2)','Kbar_cubic_column':'Kbar_j=b^15*K2_j',
            'sigma':'sigma=b^(-1)*sigma2','L':'L=b^(-1)*L2','Fbar':'Fbar=b^14*F2','Pbar':'Pbar=b*P2'},
        'coverage':'Eight strata are disjoint and cover B!=0, which the original full Jacobian open implies. None is asserted empty.',
        'trace_rule':'Sum unnormalized traces and degrees over all eight quotient strata, then divide. Original algebra has four times their total degree.',
        'full_trace_evaluated':False,'full_certificate_proved':False}
    return packet,C,conv,pairs

def control(old,new,C,pairs,count=2):
    rng=random.Random(60101);p=101;results=[]
    j=new['pivot_index']
    for attempt in range(30):
        values={v:rng.randrange(p) for v in new['variables']};b=rng.randrange(1,p)
        values.update(lam=1,r=2,s=3,t=rng.randrange(1,p),z=b*b%p)
        oldvals={v:values[v] for v in old['variables'] if not v.startswith(('A','B'))}
        for v in old['variables']:
            if v.startswith('A'):oldvals[v]=b*values[v]%p
            elif v.startswith('B'):
                i=int(v[1:]);oldvals[v]=0 if i<j else b if i==j else b*values[v]%p
        oldvals.update(lam=1,r=2,s=3)
        try:a=P.evaluate_operands(old,oldvals,p);bb=P.evaluate_operands(new,values,p)
        except (ValueError,ZeroDivisionError):continue
        assert a==bb
        results.append({'modulus':p,'all_nine_operands_equal':True,'all_original_opens_checked':True,
                        'on_contact_target':False})
        if len(results)==count:break
    return results

def main():
    start=time.monotonic();source=HERE/'point_scaled_current.json';old=json.loads(source.read_text())
    reports=[]
    for j in range(8):
        new,C,conv,pairs=build(old,j)
        tests=control(old,new,C,pairs,count=2 if j==0 else 1)
        report={'pivot_index':j,'variables':len(new['variables']),'scalar_nodes':len(C.nodes),
                'exact_parity_factor_checks':'PASS','controls':tests,
                'controls_absent_do_not_prove_stratum_empty':True}
        if j==0:
            path=HERE/'b0_quotient_current.json';path.write_text(json.dumps(new,separators=(',',':'))+'\n')
            report['exported_witness_sha256']=hashlib.sha256(path.read_bytes()).hexdigest()
        reports.append(report)
    out={'status':'PASS','all_eight_strata_structurally_transported':True,'strata':reports,
        'point_current_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope':'Exact quadratic-extension circuit transformations and row/column factor identities. Finite-field controls are operand evaluations, not target roots or traces. All eight strata remain required.',
        'full_trace_evaluated':False,'full_certificate_proved':False,'seconds':time.monotonic()-start}
    (HERE/'sign_quotient_current_receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
