#!/usr/bin/env python3
"""Resource-bounded F4 experiment, using an adjacent portable msolve binary.

The actual coefficient system comes from the pinned original-target packet.
This is a preliminary specialized ideal computation, not a trace certificate.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import resource
import subprocess
import time
import flint
from finite_modular_groebner import system

HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--binary',type=Path)
    ap.add_argument('--tag',default='p37_raw')
    ap.add_argument('--prime',type=int,default=37)
    ap.add_argument('--lam',type=int,default=1);ap.add_argument('--r',type=int,default=2);ap.add_argument('--s',type=int,default=3)
    ap.add_argument('--point-elimination',action='store_true');ap.add_argument('--alpha-resultant',action='store_true')
    ap.add_argument('--opens',action='store_true')
    ap.add_argument('--branch',choices=['full','bnzero','q2zero'],default='full')
    ap.add_argument('--quotient-elimination',action='store_true');ap.add_argument('--ab-free',action='store_true')
    ap.add_argument('--f4sat',action='store_true')
    ap.add_argument('--eliminate',type=int,default=0)
    ap.add_argument('--seconds',type=int,default=180)
    ap.add_argument('--memory-mib',type=int,default=3072)
    ap.add_argument('--threads',type=int,default=1)
    ap.add_argument('--max-pairs',type=int,default=5000)
    ap.add_argument('--reset-hash',type=int,default=0)
    args=ap.parse_args()
    if args.binary is None:
        found=list((HERE/'finite_msolve_0.11.0').rglob('msolve'))
        assert len(found)==1, found
        args.binary=found[0]
    binary=args.binary.resolve()
    order='quotient_first' if args.eliminate else 'contact'
    names,polys,sha=system(args.prime,args.lam,args.r,args.s,args.point_elimination,args.opens,'degrevlex',args.alpha_resultant,order,args.branch,args.quotient_elimination,args.ab_free)
    saturation=None
    if args.f4sat:
        assert args.opens and args.quotient_elimination and args.alpha_resultant and args.ab_free and args.branch=='full'
        assert not args.eliminate
        oldnames=names;keep=[j for j,n in enumerate(names) if not n.startswith('inv')]
        names=[names[j] for j in keep]
        assert len(names)==26 and len(polys)==31
        ctx=flint.nmod_mpoly_ctx.get(tuple(names),args.prime,'degrevlex')
        moved=[]
        for f in polys[:26]:
            g=ctx.constant(0)
            for e,c in f.to_dict().items():
                assert all(not e[j] for j in range(len(e)) if j not in keep)
                g+=ctx.term(int(c),tuple(e[j] for j in keep))
            moved.append(g)
        V=dict(zip(names,ctx.gens()));r=args.r;s=args.s
        q0=r+V['mu0']+r*r*V['mu1'];q2=V['mu2']+s*V['mu3']+s*s*V['mu4']
        aa=[V[f'A{i}'] for i in range(8)];bb=[V[f'B{i}'] for i in range(8)]
        a0=aa[0]+r**3*aa[1];a2=aa[2]+s*aa[3]+s*s*aa[4]+r*aa[5]+r*s*aa[6]+r*s*s*aa[7]
        b0=bb[0]+s*bb[1]+r*r*bb[2]+r*r*s*bb[3];b2=bb[4]+s*bb[5]+s*s*bb[6]+s**3*bb[7]
        an=q2*a0-q0*a2;bn=q2*b0-q0*b2;z=V['mu0']*V['mu1']
        saturation=(1-z)*(1-2*z)*(1-3*z)*an*bn
        polys=moved+[saturation]
    inp=HERE/f'finite_msolve_{args.tag}.ms';out=HERE/f'finite_msolve_{args.tag}.out';log=HERE/f'finite_msolve_{args.tag}.log'
    text=','.join(names)+'\n'+str(args.prime)+'\n'+',\n'.join(map(str,polys))+'\n'
    inp.write_text(text)
    command=[str(binary),'-v','2','-g','2','-t',str(args.threads),'-m',str(args.max_pairs),'-f',str(inp),'-o',str(out)]
    if args.eliminate:command+=['-e',str(args.eliminate)]
    if args.f4sat:command+=['-S']
    if args.reset_hash:command+=['-u',str(args.reset_hash)]
    def limit():resource.setrlimit(resource.RLIMIT_AS,(args.memory_mib*1024**2,)*2)
    started=time.monotonic()
    receipt={'tag':args.tag,'modulus':args.prime,'base_parameters':[args.lam,args.r,args.s],'branch':args.branch,
             'variables':len(names),'equations':len(polys),'input_terms':sum(map(len,polys)),
             'max_input_degree':int(max(f.total_degree() for f in polys)),
             'source_sha256':sha,'input_sha256':hashlib.sha256(text.encode()).hexdigest(),
             'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),
             'block_elimination_count':args.eliminate,'time_limit_seconds':args.seconds,'memory_limit_mib':args.memory_mib,
             'max_pairs_per_matrix':args.max_pairs,'threads':args.threads,
             'reset_hash_every_n_steps':args.reset_hash,
             'quotient_variables_eliminated':args.quotient_elimination,'alpha_eliminated':args.alpha_resultant,'AB_free_point_equation':args.ab_free,
             'f4sat':args.f4sat,'saturation_formula':'(1-z)*(1-2*z)*(1-3*z)*aN*bN' if saturation is not None else None,
             'saturation_sha256':hashlib.sha256(str(saturation).encode()).hexdigest() if saturation is not None else None,
             'command':command,
             'full_regularity_localization_included':False,'generic_flatness_proved':False,'traces_computed':False}
    print(json.dumps({'phase':'starting',**receipt}),flush=True)
    with log.open('w') as f:
        try:
            done=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,timeout=args.seconds,preexec_fn=limit)
            receipt['exit_code']=done.returncode
            receipt['status']='FINISHED' if done.returncode==0 else 'PROCESS_FAILED'
        except subprocess.TimeoutExpired:receipt['status']='TIME_LIMIT'
    receipt['seconds']=time.monotonic()-started
    receipt['output_bytes']=out.stat().st_size if out.exists() else 0
    receipt['scope']='Specialized preliminary ideal computation. No full localized finite algebra, generic degree, or trace identity is certified.'
    (HERE/f'finite_msolve_{args.tag}_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
