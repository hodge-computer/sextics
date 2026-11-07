"""Fixed-denominator q=1 search on exact symmetric sextic.
Uses both normalized equations, preserving the arbitrary F*Q remainder.
The S3 x S3 averaging reduction is complete for the tested invariant D.
Finite-field inconsistency is a screen, not by itself a rational obstruction.
"""
import itertools, json, time, argparse
from pathlib import Path

ZERO=(0,)*6

def add(a,b,p):
 c=a.copy()
 for e,v in b.items():
  z=(c.get(e,0)+v)%p
  if z:c[e]=z
  elif e in c:del c[e]
 return c

def scale(a,c,p):return {e:v*c%p for e,v in a.items() if v*c%p}
def mul(a,b,p):
 c={}
 for e,u in a.items():
  for f,v in b.items():
   g=tuple(e[i]+f[i] for i in range(6))
   c[g]=(c.get(g,0)+u*v)%p
 return {e:v for e,v in c.items() if v}
def power(a,n,p):
 b={ZERO:1}
 for _ in range(n):b=mul(a,b,p)
 return b

def deriv(a,i,p):
 c={}
 for e,v in a.items():
  if e[i]:
   f=list(e);f[i]-=1;f=tuple(f)
   c[f]=v*e[i]%p
 return c

def mon(i):
 e=list(ZERO);e[i]=1
 return {tuple(e):1}

def degree_monomials(n,d):
 if n==1:
  yield (d,)
 else:
  for i in range(d+1):
   for e in degree_monomials(n-1,d-i):yield (i,)+e

def permute(a,perm):
 c={}
 for e,v in a.items():
  f=[0]*6
  for i in range(6):f[perm[i]]=e[i]
  c[tuple(f)]=v
 return c

def canonical(e,block):
 if block==0:return (e[0],)+tuple(sorted(e[1:3]))+tuple(sorted(e[3:]))
 return tuple(sorted(e[:3]))+(e[3],)+tuple(sorted(e[4:]))

def basis_N(deg,p):
 result=[]
 for block in [0,3]:
  polys={}
  for e in degree_monomials(6,deg):
   if sum(e[3:])%2 != (1 if block==0 else 0):continue
   c=canonical(e,block)
   polys.setdefault(c,{})[e]=1
  for key,P in sorted(polys.items()):
   N=[{} for _ in range(6)]
   for i in range(block,block+3):
    perm=list(range(6));perm[block],perm[i]=perm[i],perm[block]
    N[i]=permute(P,perm)
   result.append((f'{block}:{key}',N))
 return result

def reduce_F(P,F,p):
 # Lex leading term 7 X0^6, strictly lower X0 degree elsewhere.
 lead=(6,0,0,0,0,0);inv=pow(F[lead],-1,p)
 tail={e:v for e,v in F.items() if e!=lead}
 P=P.copy()
 todo={e for e in P if e[0]>=6}
 while todo:
  e=max(todo);todo.remove(e)
  a=P.pop(e,0)
  if not a:continue
  m=(e[0]-6,)+e[1:]
  c=-a*inv%p
  for f,v in tail.items():
   g=tuple(m[i]+f[i] for i in range(6));z=(P.get(g,0)+c*v)%p
   if z:
    P[g]=z
    if g[0]>=6:todo.add(g)
   elif g in P:del P[g]
 return P

def system_columns(F,A,D,deg,p):
 Fs=[deriv(F,i,p) for i in range(6)];Ds=[deriv(D,i,p) for i in range(6)]
 basis=basis_N(deg+1,p)
 columns=[]
 for name,N in basis:
  normal={};div={};nd={}
  for i in range(6):
   normal=add(normal,mul(N[i],Fs[i],p),p)
   div=add(div,deriv(N[i],i,p),p)
   nd=add(nd,mul(N[i],Ds[i],p),p)
  residual=reduce_F(add(mul(D,div,p),scale(nd,-1,p),p),F,p)
  col={(0,)+e:v for e,v in normal.items()}
  col.update({(1,)+e:v for e,v in residual.items()})
  columns.append(col)
 target={(0,)+e:v for e,v in mul(A,D,p).items()}
 return basis,columns,target

def solve_columns(columns,target,p):
 pivots={};rank=0;kernel=0
 for j,col in enumerate(columns):
  v=col.copy();repr={j:1}
  while v:
   k=min(v)
   if k not in pivots:
    inv=pow(v[k],-1,p)
    v={e:a*inv%p for e,a in v.items()}
    repr={e:a*inv%p for e,a in repr.items()}
    pivots[k]=(v,repr);rank+=1;break
   b,br=pivots[k];c=v[k]
   for e,a in b.items():
    z=(v.get(e,0)-c*a)%p
    if z:v[e]=z
    elif e in v:del v[e]
   for e,a in br.items():
    z=(repr.get(e,0)-c*a)%p
    if z:repr[e]=z
    elif e in repr:del repr[e]
  else:kernel+=1
 v=target.copy();sol={}
 while v:
  k=min(v)
  if k not in pivots:return {'consistent':False,'rank':rank,'nullity':kernel,'obstruction_row':k,'obstruction_value':v[k]}
  b,br=pivots[k];c=v[k]
  for e,a in b.items():
   z=(v.get(e,0)-c*a)%p
   if z:v[e]=z
   elif e in v:del v[e]
  for e,a in br.items():
   z=(sol.get(e,0)+c*a)%p
   if z:sol[e]=z
   elif e in sol:del sol[e]
 return {'consistent':True,'rank':rank,'nullity':kernel,'solution':sol}

def data(p):
 z=[mon(i) for i in range(6)]
 QX={};QY={};U={};V={};SX={};SY={}
 for i in range(3):
  U=add(U,power(z[i],6,p),p);V=add(V,power(z[3+i],6,p),p)
  SX=add(SX,z[i],p);SY=add(SY,z[3+i],p)
  for j in range(i+1,3):
   QX=add(QX,mul(z[i],z[j],p),p);QY=add(QY,mul(z[3+i],z[3+j],p),p)
 C1=mul(power(QX,2,p),QY,p);C2=mul(QX,power(QY,2,p),p)
 F=add(scale(add(U,V,p),7,p),add(scale(C1,5,p),scale(C2,10,p),p),p)
 A={(1,)*6:1}
 return F,A,QX,QY,U,V,SX,SY,C1,C2

def candidates(p,mode):
 F,A,QX,QY,U,V,SX,SY,C1,C2=data(p)
 out=[('1',0,{ZERO:1})]
 quadrics=[('QX',QX),('QY',QY),('SX2',power(SX,2,p)),('SY2',power(SY,2,p))]
 for k in [1,-1,2,-2,3,-3,5,-5]:quadrics.append((f'QX{ k:+}QY',add(QX,scale(QY,k,p),p)))
 for name,P in quadrics:out.append((name,2,P))
 for nx,X in quadrics[:4]:
  for ny,Y in quadrics[:4]:
   if nx<=ny:out.append((f'{nx}*{ny}',4,mul(X,Y,p)))
 out.extend([('U',6,U),('V',6,V),('QXQY',4,mul(QX,QY,p)),('QX3',6,power(QX,3,p)),('QY3',6,power(QY,3,p))])
 if mode=='extended':
  for k in [1,-1,2,-2,3,-3]:
   out.append((f'U{k:+}V',6,add(U,scale(V,k,p),p)))
  for k in [-6,-3,-2,-1,0,1,2,3,6]:
   coupling=add(scale(C1,5,p),scale(C2,10,p),p)
   out.append((f'7U{k:+}C',6,add(scale(U,7,p),scale(coupling,k,p),p)))
  for k in [-3,-2,-1,0,1,2,3]:
   out.append((f'EXF{k:+}EYF',6,add(add(scale(U,42,p),scale(V,42*k,p),p),add(scale(C1,20+10*k,p),scale(C2,20+40*k,p),p),p)))
  out.extend([('QX2QY2',8,mul(power(QX,2,p),power(QY,2,p),p)),('QX*U',8,mul(QX,U,p)),('QY*U',8,mul(QY,U,p)),('QX*V',8,mul(QX,V,p)),('QY*V',8,mul(QY,V,p))])
 seen=set()
 for name,deg,D in out:
  key=tuple(sorted(D.items()))
  if not D or key in seen:continue
  seen.add(key)
  yield name,deg,D

def main():
 arg=argparse.ArgumentParser();arg.add_argument('--prime',type=int,default=37);arg.add_argument('--mode',default='basic');arg.add_argument('--name',default='');arg.add_argument('--output',required=True)
 args=arg.parse_args();p=args.prime;F,A,*_=data(p)
 results=[]
 for name,deg,D in candidates(p,args.mode):
  if args.name and args.name not in name:continue
  t=time.time();basis,cols,target=system_columns(F,A,D,deg,p)
  r=solve_columns(cols,target,p);r.update({'denominator':name,'degree':deg,'prime':p,'ncols':len(cols),'seconds':round(time.time()-t,3)})
  print(json.dumps({k:v for k,v in r.items() if k!='solution'}),flush=True)
  if r['consistent']:r['basis']=[name for name,_ in basis]
  results.append(r);Path(args.output).write_text(json.dumps(results,indent=2))
if __name__=='__main__':main()
