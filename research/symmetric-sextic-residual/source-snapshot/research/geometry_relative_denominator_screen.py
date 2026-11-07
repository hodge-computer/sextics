import geometry_primitive_search as s
import geometry_annihilator_search as a
import itertools,time,json
from pathlib import Path

def parity(seq):return sum(seq[i]>seq[j] for i in range(len(seq)) for j in range(i+1,len(seq)))%2

def orbit_canonical(e,block,chars):
 chunks=([e[0]],[*e[1:3]],[*e[3:]]) if block==0 else ([*e[:3]],[e[3]],[*e[4:]])
 ch=(False,chars[0],chars[1]) if block==0 else (chars[0],False,chars[1])
 sign=1;key=[]
 for es,c in zip(chunks,ch):
  if c and len(set(es))<len(es):return None,0
  if c and parity(es):sign=-sign
  key.extend(sorted(es))
 return tuple(key),sign

def char_basis(deg,chars,yp,p):
 result=[]
 for block in [0,3]:
  groups={}
  for e in s.degree_monomials(6,deg):
   if sum(e[3:])%2!=((1 if block==0 else 0)+yp)%2:continue
   key,c=orbit_canonical(e,block,chars)
   if key is not None:groups.setdefault(key,{})[e]=c%p
  for key,P in sorted(groups.items()):
   N=[{} for _ in range(6)]
   for i in range(block,block+3):
    perm=list(range(6));perm[block],perm[i]=perm[i],perm[block]
    N[i]=s.scale(s.permute(P,perm),-1 if (i!=block and chars[block//3]) else 1,p)
   result.append((f'{block}:{key}',N))
 return result

def candidates(p):
 F,A,QX,QY,U,V,SX,SY,C1,C2=s.data(p);z=[s.mon(i) for i in range(6)]
 PX=PY=DX=DY={s.ZERO:1}
 for i in range(3):PX=s.mul(PX,z[i],p);PY=s.mul(PY,z[3+i],p)
 for i in range(3):
  for j in range(i+1,3):
   DX=s.mul(DX,s.add(z[i],s.scale(z[j],-1,p),p),p)
   DY=s.mul(DY,s.add(z[3+i],s.scale(z[3+j],-1,p),p),p)
 basics=[('SX',SX,1,(0,0),0),('SY',SY,1,(0,0),1),('PX',PX,3,(0,0),0),('PY',PY,3,(0,0),1),('DX',DX,3,(1,0),0),('DY',DY,3,(0,1),1),('SXQX-PX',s.add(s.mul(SX,QX,p),s.scale(PX,-1,p),p),3,(0,0),0),('SYQY-PY',s.add(s.mul(SY,QY,p),s.scale(PY,-1,p),p),3,(0,0),1)]
 for item in basics:yield item
 for i,xx in enumerate(basics):
  nx,X,dx,cx,yx=xx
  for ny,Y,dy,cy,yy in basics[i:]:
   if dx+dy>6:continue
   yield nx+'*'+ny,s.mul(X,Y,p),dx+dy,tuple((cx[k]+cy[k])%2 for k in range(2)),(yx+yy)%2
 for nx,X,dx,cx,yx in basics:
  if dx==3:
   for nq,Q in [('QX',QX),('QY',QY)]:yield nx+'*'+nq,s.mul(X,Q,p),5,cx,yx

def main():
 p=37;F,A,*_=s.data(p);results=[]
 for name,D,d,chars,yp in candidates(p):
  t=time.time();NB=char_basis(d+1,chars,yp,p);cols=[]
  for _,N in NB:
   nr=a.action(F,N,p);dr=a.bilinear(D,N,F,p)
   col={(0,)+e:c for e,c in nr.items()};col.update({(1,)+e:c for e,c in dr.items()});cols.append(col)
  target={(0,)+e:c for e,c in s.mul(A,D,p).items()}
  r=s.solve_columns(cols,target,p);r.update({'name':name,'degree':d,'characters':chars,'Y_parity':yp,'prime':p,'ncols':len(cols),'seconds':time.time()-t})
  results.append(r)
  print(json.dumps({k:v for k,v in r.items() if k!='solution'}),flush=True)
 Path(__file__).resolve().with_name('geometry_relative_denominator_screen_37.json').write_text(json.dumps(results,indent=2))
if __name__=='__main__':main()
