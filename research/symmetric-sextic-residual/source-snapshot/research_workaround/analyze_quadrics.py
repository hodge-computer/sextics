"""Eliminate all numerator-kernel parameters linearly, over Q."""
from pathlib import Path
from flint import fmpq,fmpq_mat
import json,time,argparse

HERE=Path(__file__).resolve().parent

def analyze(degree):
    started=time.time()
    packet=json.loads((HERE/f'degree{degree}_exact_second_equations.json').read_text())
    types=packet['types'];eqs=[{j:fmpq(c) for j,c in row} for row in packet['equations']]
    ci=[j for j,t in enumerate(types) if t[0]=='c']
    qi=[j for j,t in enumerate(types) if t[0]=='b']
    order=ci+qi
    M=fmpq_mat([[row.get(j,0) for j in order] for row in eqs])
    rr,rank=M.rref()
    pure=[];mixedrank=0
    for i in range(rank):
        if any(rr[i,j] for j in range(len(ci))):mixedrank+=1;continue
        pure.append({tuple(types[qi[j]][1:]):rr[i,len(ci)+j] for j in range(len(qi)) if rr[i,len(ci)+j]})
    squares=[]
    for row in pure:
        if len(row)==1:
            (i,j),c=next(iter(row.items()))
            if i==j:squares.append(i)
    # A square-zero parameter is zero over any field. Substitute these zeros
    # and row-reduce again to expose further square-zero parameters.
    forced=set(squares)
    while True:
        surviving=[j for j in range(len(qi)) if not set(types[qi[j]][1:])&forced]
        if not surviving:break
        P=fmpq_mat([[row.get(tuple(types[qi[j]][1:]),0) for j in surviving] for row in pure])
        pr,pk=P.rref()
        gained=set()
        for i in range(pk):
            nz=[j for j in range(P.ncols()) if pr[i,j]]
            if len(nz)==1:
                a,b=types[qi[surviving[nz[0]]]][1:]
                if a==b:gained.add(a)
        if gained<=forced:break
        forced|=gained
    out={'status':'EXACT_NECESSARY_QUADRICS','degree':degree,'denominator_parameters':packet['D_parameters'],
         'kernel_parameters':packet['kernel_parameters'],'equation_rank':rank,'mixed_rank':mixedrank,
         'pure_quadrics_rank':len(pure),'square_zero_parameters':sorted(forced),
         'all_denominator_parameters_forced_zero':len(forced)==packet['D_parameters'],
         'pure_quadrics':[[[list(ij),str(c)] for ij,c in sorted(row.items())] for row in pure],
         'seconds':time.time()-started,'full_certificate_proved':False}
    (HERE/f'degree{degree}_pure_quadrics.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='pure_quadrics'}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--degree',type=int,default=6);a=p.parse_args();analyze(a.degree)
