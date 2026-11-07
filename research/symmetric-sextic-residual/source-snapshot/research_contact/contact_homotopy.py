#!/usr/bin/env python3
"""Numerical contact continuation for the exact protected symmetric sextic.

The optional numerical output is a candidate only. No exact solution, lift,
trace identity, or final certificate is inferred by this program.
"""
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json, hashlib, argparse, time
import numpy as np
import scipy.linalg as la

HERE=Path(__file__).resolve().parent
CIRCUIT=HERE/'contact_target_circuit.json'
QBASE=[(2,0,0,0),(0,2,0,0),(0,0,2,0),(0,0,1,1),(0,0,0,2)]
ABASE=[(3,0,0,0),(0,3,0,0),(1,0,2,0),(1,0,1,1),
       (1,0,0,2),(0,1,2,0),(0,1,1,1),(0,1,0,2)]
BBASE=[(2,0,1,0),(2,0,0,1),(0,2,1,0),(0,2,0,1),
       (0,0,3,0),(0,0,2,1),(0,0,1,2),(0,0,0,3)]
AB=(1,1,0,0)
def mons(d):
    return sorted(e for e in product(range(d+1),repeat=4)
                  if sum(e)==d and (e[2]+e[3])%2==0)
M2,M4,M6=mons(2),mons(4),mons(6)
I2,I4,I6=({e:i for i,e in enumerate(ms)} for ms in [M2,M4,M6])
assert len(M4)==19 and len(M6)==44
QIND=np.array([I2[e] for e in QBASE])
def tensor(left,right,output):
    ix={e:i for i,e in enumerate(output)}
    a=np.zeros((len(output),len(left),len(right)))
    for i,e in enumerate(left):
        for j,f in enumerate(right):a[ix[tuple(x+y for x,y in zip(e,f))],i,j]=1
    return a
T22=tensor(M2,M2,M4)
T24=tensor(M2,M4,M6)
TAA=tensor(ABASE,ABASE,M6)
TBB=tensor(BBASE,BBASE,M6)
def mul(T,a,b):return np.einsum('kij,i,j->k',T,a,b,optimize=False)
def coef_as_fraction(d,lam=Fraction(1)):
    nodes=d['nodes']
    @lru_cache(None)
    def evaluate(k):
        op,x=nodes[k]['op'],nodes[k]['data']
        if op=='rational':return Fraction(*x)
        if op=='variable':
            assert x=='lam';return lam
        if op=='add':return sum(map(evaluate,x),Fraction())
        if op=='multiply':
            a=Fraction(1)
            for i in x:a*=evaluate(i)
            return a
        if op=='power':return evaluate(x[0])**x[1]
        if op=='inverse':return 1/evaluate(x)
        raise ValueError(op)
    blocks=[]
    for power,ms in [(2,M2),(1,M4),(0,M6)]:
        p={tuple(z['exponent'][:4]):evaluate(z['coefficient_node'])
           for z in d['polynomials']['G'] if z['exponent'][4]==power}
        blocks.append([p.get(e,Fraction()) for e in ms])
    return blocks

class Model:
    def __init__(self,lam=Fraction(1)):
        self.circuit=json.loads(CIRCUIT.read_text())
        self.exact=coef_as_fraction(self.circuit,lam)
        self.h2,self.h4,self.target=[np.array(list(map(float,b))) for b in self.exact]
    def unpack(self,x):
        q=np.zeros(6,dtype=x.dtype);q[QIND]=x[:5]
        b=np.zeros(6,dtype=x.dtype);b[QIND]=x[5:10];b[I2[AB]]=1
        return q,b,x[10:18],x[18:26],x[26:45]
    def evaluate(self,x,jacobian=True):
        q,b,A,B,v=self.unpack(x)
        q2=mul(T22,q,q)
        hq=mul(T22,self.h2,q)
        y=mul(T24,q,q2)-mul(T24,self.h2,q2)+mul(T24,q,self.h4)\
          +mul(TAA,A,A)-mul(TBB,B,B)+mul(T24,b,v)
        if not jacobian:return y
        d=3*q2-2*hq+self.h4
        J=np.concatenate((np.einsum('kij,j->ki',T24,d)[:,QIND],
                          np.einsum('kij,j->ki',T24,v)[:,QIND],
                          2*np.einsum('kij,j->ki',TAA,A),
                          -2*np.einsum('kij,j->ki',TBB,B),
                          np.einsum('kij,i->kj',T24,b)),axis=1)
        return y,J
    def delta(self,x):
        z=x[5]*x[6];return (1-z)*(1-3*z)*(1-2*z)**3

def track(model,seed,free=0,max_steps=4000):
    rng=np.random.default_rng(seed)
    x=rng.integers(-6,7,45).astype(complex)/4
    x[free]=Fraction(1,4)
    initial=x.copy();y0=model.evaluate(x,False)
    active=np.array([i for i in range(45) if i!=free])
    gamma=np.exp(1j*rng.uniform(.3,2.5))
    t,step=0.,.01
    rejects=0;accepted=0;log=[]
    def path(t):
        den=(1-t)*gamma+t
        return ((1-t)*gamma*y0+t*model.target)/den,\
               gamma*(model.target-y0)/(den*den)
    for attempt in range(max_steps):
        if t>=1:break
        step=min(step,1-t)
        y,dy=path(t)
        _,J=model.evaluate(x)
        try:dx=la.solve(J[:,active],dy,check_finite=False)
        except la.LinAlgError:return None,{'seed':seed,'error':'predictor singular','t':t}
        candidate=x.copy();candidate[active]+=step*dx
        target,_=path(t+step)
        good=False
        for it in range(12):
            f,Jc=model.evaluate(candidate);f-=target
            residual=float(np.max(np.abs(f)))
            if residual<2e-10:
                good=True;break
            try:cor=la.solve(Jc[:,active],f,check_finite=False)
            except la.LinAlgError:break
            candidate[active]-=cor
            if not np.all(np.isfinite(candidate)) or np.max(np.abs(candidate))>1e8:break
        correction=np.max(np.abs(candidate-x))
        prediction=np.max(np.abs(step*dx))
        if not good or correction>max(3,8*prediction):
            step*=.5;rejects+=1
            if step<1e-8:return None,{'seed':seed,'error':'step underflow','t':t,'max_x':float(np.max(np.abs(x)))}
            continue
        x=candidate;t+=step;accepted+=1
        if it<4:step=min(.035,step*1.3)
        elif it>7:step*=.7
        if accepted%20==0 or t>=1:
            row={'t':t,'step':step,'residual':residual,'iterations':it,'max_x':float(np.max(np.abs(x)))}
            log.append(row);print(json.dumps({'seed':seed,**row}),flush=True)
    f,J=model.evaluate(x)
    receipt={'seed':seed,'free_index':free,'free_value':[.25,0.],
        'gamma':[gamma.real,gamma.imag],'accepted_steps':accepted,'rejected_steps':rejects,
        't':t,'residual_inf':float(np.max(np.abs(f-model.target))),
        'condition_number':float(np.linalg.cond(J[:,active])),
        'delta':[model.delta(x).real,model.delta(x).imag],
        'candidate':[[z.real,z.imag] for z in x],
        'initial':[[z.real,z.imag] for z in initial],'path_log':log,
        'circuit_sha256':hashlib.sha256(CIRCUIT.read_bytes()).hexdigest(),
        'scope':'Numerical candidate only; not an exact contact or certificate.'}
    return (x if t>=1 else None),receipt

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seed',type=int,default=42)
    ap.add_argument('--attempts',type=int,default=3);args=ap.parse_args()
    model=Model()
    for seed in range(args.seed,args.seed+args.attempts):
        x,r=track(model,seed)
        (HERE/f'contact_homotopy_{seed}.json').write_text(json.dumps(r,indent=2)+'\n')
        print(json.dumps({k:v for k,v in r.items() if k not in ['candidate','initial','path_log']}),flush=True)
        if x is not None:return
if __name__=='__main__':main()
