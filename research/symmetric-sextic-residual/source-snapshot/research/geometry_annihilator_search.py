import geometry_primitive_search as s
import itertools,json,time
from pathlib import Path

def symbasis(d,p):
 out={}
 for e in s.degree_monomials(6,d):
  if sum(e[3:])%2:continue
  c=tuple(sorted(e[:3]))+tuple(sorted(e[3:]))
  out.setdefault(c,{})[e]=1
 return list(sorted(out.items()))

def relations(columns,p):
 pivots={};rels=[]
 for j,col in enumerate(columns):
  v=col.copy();r={j:1}
  while v:
   k=min(v)
   if k not in pivots:
    inv=pow(v[k],-1,p);v=s.scale(v,inv,p);r=s.scale(r,inv,p)
    pivots[k]=(v,r);break
   b,br=pivots[k];c=v[k]
   v=s.add(v,s.scale(b,-c,p),p);r=s.add(r,s.scale(br,-c,p),p)
  else:rels.append(r)
 return pivots,rels

def combo_polys(coefs,basis,p):
 P={}
 for i,c in coefs.items():P=s.add(P,s.scale(basis[i],c,p),p)
 return P

def combo_N(coefs,basis,p):
 N=[{} for _ in range(6)]
 for i,c in coefs.items():
  for j in range(6):N[j]=s.add(N[j],s.scale(basis[i][j],c,p),p)
 return N

def action(P,N,p):
 out={}
 for i in range(6):out=s.add(out,s.mul(s.deriv(P,i,p),N[i],p),p)
 return out

def bilinear(D,N,F,p):
 div={}
 for i in range(6):div=s.add(div,s.deriv(N[i],i,p),p)
 return s.reduce_F(s.add(s.mul(D,div,p),s.scale(action(D,N,p),-1,p),p),F,p)

def ann(d,p):
 F,A,*_=s.data(p);NB=s.basis_N(d+1,p);DB=symbasis(d,p)
 columns=[action(F,N,p) for name,N in NB]+[s.scale(s.mul(A,D,p),-1,p) for name,D in DB]
 piv,rels=relations(columns,p);n=len(NB)
 eligible=[];nker=[]
 for r in rels:
  nc={i:c for i,c in r.items() if i<n};dc={i-n:c for i,c in r.items() if i>=n}
  N=combo_N(nc,[N for _,N in NB],p)
  if dc:eligible.append((combo_polys(dc,[D for _,D in DB],p),N,dc,nc))
  else:nker.append(N)
 return F,A,NB,DB,nker,eligible

def main():
 import argparse
 a=argparse.ArgumentParser();a.add_argument('--prime',type=int,default=37);a.add_argument('--degree',type=int,default=6);args=a.parse_args();p=args.prime;d=args.degree
 t=time.time();F,A,NB,DB,nker,elig=ann(d,p)
 print(json.dumps({'degree':d,'prime':p,'num_numerator_columns':len(NB),'num_denominator_columns':len(DB),'normal_kernel_dimension':len(nker),'eligible_denominator_dimension':len(elig),'seconds':time.time()-t}),flush=True)
 for j,(D,N,dc,nc) in enumerate(elig):
  print(json.dumps({'ann_basis':j,'D_terms':[(e,c if c<=p//2 else c-p) for e,c in sorted(D.items())],'ncoef':nc}),flush=True)
 if len(elig)>0:
  polys={}
  for i,(Di,Ni,_,_) in enumerate(elig):
   for j in range(i,len(elig)):
    Dj,Nj,_,_=elig[j]
    z=bilinear(Di,Nj,F,p)
    if i!=j:z=s.add(z,bilinear(Dj,Ni,F,p),p)
    for e,c in z.items():polys.setdefault(e,{})[(i,j)]=c
  pp,rr=relations([{(i,j):c for (i,j),c in P.items()} for P in polys.values()],p)
  equations=[P for P,repr in pp.values()]
  print(json.dumps({'canonical_numerator_only':True,'independent_quadratic_conditions':len(equations),'quadratic_conditions': [[(ij,c if c<=p//2 else c-p) for ij,c in sorted(P.items())] for P in equations]}),flush=True)
  result={'warning':'Quadratic conditions here use the selected numerator section only. Use geometry_complete_sextic_screen.py to include every first-equation kernel correction.','prime':p,'degree':d,'N_basis_names':[name for name,N in NB],'D_basis_names':[e for e,D in DB],'eligible':[{'D':[(e,c) for e,c in D.items()],'N':[[[e,c] for e,c in z.items()] for z in N],'D_coeff':dc,'N_coeff':nc} for D,N,dc,nc in elig],'quadratic_conditions':[[[ij,c] for ij,c in P.items()] for P in equations]}
  Path(__file__).resolve().with_name(f'geometry_annihilator_{d}_{p}.json').write_text(json.dumps(result,indent=2))
if __name__=='__main__':main()
