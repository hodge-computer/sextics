"""All S3xS3 invariant degree-six denominators over a selected prime field.
First solve AD=N(F), then retain ALL first-equation kernel corrections.
Reject D multiples of F. Test unrestricted normalized second equation modF.
This is a modular research screen; it does not prove nonexistence over C.
"""
import geometry_annihilator_search as a
import geometry_primitive_search as s
import numpy as np
import itertools, time, json, argparse
from pathlib import Path

def main():
 ar=argparse.ArgumentParser();ar.add_argument('--prime',type=int,default=11);ar.add_argument('--max',type=int,default=0);args=ar.parse_args();p=args.prime;t0=time.time()
 F,A,NB,DB,kernels,eligible=a.ann(6,p)
 r=len(eligible);k=len(kernels)
 cols=[];types=[]
 for i,(Di,Ni,_,_) in enumerate(eligible):
  for j in range(i,r):
   Dj,Nj,_,_=eligible[j];v=a.bilinear(Di,Nj,F,p)
   if i!=j:v=s.add(v,a.bilinear(Dj,Ni,F,p),p)
   cols.append(v);types.append(('b',i,j))
  for j,K in enumerate(kernels):cols.append(a.bilinear(Di,K,F,p));types.append(('c',i,j))
 # All actual coefficient equations, row-reduced in parameter-monomial space.
 rows={}
 for j,col in enumerate(cols):
  for e,c in col.items():rows.setdefault(e,{})[j]=c
 piv,_=a.relations(list(rows.values()),p)
 eqs=[P for P,_ in piv.values()];m=len(eqs)
 B=np.zeros((r,r,m),dtype=np.int64);C=np.zeros((r,m,k),dtype=np.int64)
 for n,P in enumerate(eqs):
  for idx,c in P.items():
   typ,i,j=types[idx]
   if typ=='b':B[i,j,n]=c
   else:C[i,n,j]=c
 print(json.dumps({'prime':p,'eligibleD':r,'normal_kernel':k,'independent_second_equations':m}),flush=True)
 def consistent(t):
  lhs=np.tensordot(t,C,axes=(0,0))%p
  rhs=-np.einsum('i,j,ijn->n',t,t,B)%p
  M=np.column_stack((lhs,rhs));row=0
  for col in range(k):
   nz=np.nonzero(M[row:,col])[0]
   if not len(nz):continue
   q=row+int(nz[0]);M[[row,q]]=M[[q,row]]
   M[row]=(M[row]*pow(int(M[row,col]),-1,p))%p
   fac=M[:,col].copy();fac[row]=0
   M=(M-fac[:,None]*M[row][None,:])%p
   row+=1
   if row==m:break
  return bool(not np.any(M[row:,-1])),row
 n=0;hits=[];illegal=0
 for lead in range(r):
  for tail in itertools.product(range(p),repeat=r-lead-1):
   t=np.array((0,)*lead+(1,)+tail,dtype=np.int64)
   ok,rank=consistent(t);n+=1
   if ok:
    D={}
    for i,x in enumerate(t):D=s.add(D,s.scale(eligible[i][0],int(x),p),p)
    bad=not s.reduce_F(D,F,p)
    if bad:illegal+=1
    else:
     hit={'t':t.tolist(),'rank':rank,'D_terms':[[e,c] for e,c in D.items()]};hits.append(hit)
     print(json.dumps({'LEGAL_HIT':hit}),flush=True)
   if n%1000==0:print(json.dumps({'tested':n,'legal_hits':len(hits),'seconds':round(time.time()-t0,2)}),flush=True)
   if args.max and n>=args.max:break
  if args.max and n>=args.max:break
 result={'prime':p,'degree':6,'eligibleD':r,'kernelN':k,'independent_equations':m,'projective_denominators_tested':n,'illegal_hits':illegal,'legal_hits':hits,'seconds':time.time()-t0}
 print(json.dumps(result),flush=True)
 Path(__file__).resolve().with_name(f'geometry_complete_sextic_screen_{p}.json').write_text(json.dumps(result,indent=2))
if __name__=='__main__':main()
