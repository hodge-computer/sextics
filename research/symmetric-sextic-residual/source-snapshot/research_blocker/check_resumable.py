#!/usr/bin/env python3
"""Complete-basis and ideal-preserving restart checks on small exact systems."""
from pathlib import Path
import argparse
import hashlib
import json
import resource
import signal
import subprocess
import time
import sympy as S
from packed_f4 import write,header,rows
from neogb_solver import NativeF4

HERE=Path(__file__).resolve().parent

def canon(fs,p):return sorted(tuple(sorted((e,int(c)%p) for e,c in f.items() if int(c)%p)) for f in fs)
def expressions(fs,variables):return [sum(c*S.prod(x**k for x,k in zip(variables,e)) for e,c in f.items()) for f in fs]

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--build-receipt',type=Path,default=HERE/'resumable_build_receipt.json')
    parser.add_argument('--output-receipt',type=Path,default=HERE/'resumable_validation_receipt.json')
    parser.add_argument('--compare-binary',type=Path)
    args=parser.parse_args()
    build=json.loads(args.build_receipt.read_text());binary=Path(build['binary'])
    folder=HERE/'vendor'/('resumable_checks_'+build['binary_sha256'][:12]);folder.mkdir(exist_ok=True)
    original=NativeF4(HERE/'vendor/libneogb_original.so')
    x,y,z,w=S.symbols('x y z w')
    cases=[('quadratic',(x,y),[x*x+y*y-1,x-y],37),
           ('nonreduced',(x,y),[x*x,x*y,y*y],101),
           ('empty',(x,y),[x*x,y-x,x*y-1,x*y],37),
           ('positive_dimension',(x,y,z),[x*y-z*z,x*x-y*z],101),
           ('mixed_cubic',(x,y,z),[x*x+y*z+1,y*y+x*z+2,z*z+x*y+3],65537),
           ('degree_fall',(x,y,z),[x*x*y+x*z+y,y*y*z+y*x+z,z*z*x+z*y+x],1073741827),
           ('cyclic4',(x,y,z,w),[x+y+z+w,x*y+y*z+z*w+w*x,x*y*z+y*z*w+z*w*x+w*x*y,x*y*z*w-1],101)]
    results=[];restart_result=None;started=time.monotonic()
    for name,variables,polynomials,p in cases:
        inputs=[{e:int(c)%p for e,c in S.Poly(f,*variables,modulus=p).terms()} for f in polynomials]
        reference=S.groebner(polynomials,*variables,modulus=p,order='grevlex')
        expected=canon([dict(f.terms()) for f in reference.polys],p)
        inp=folder/(name+'.hcf');out=folder/(name+'_complete.hcf')
        write(inp,[str(v) for v in variables],p,inputs)
        assert canon(rows(inp),p)==canon(inputs,p)
        command=[str(binary),'--input',str(inp),'--output',str(out),'--pairs','2','--info','0']
        run=subprocess.run(command,capture_output=True,text=True,timeout=45)
        (folder/(name+'.log')).write_text(run.stderr+run.stdout)
        assert run.returncode==0,(name,run.returncode,run.stderr,run.stdout)
        native_summary=json.loads(run.stdout.splitlines()[-1])
        assert native_summary['unit_ideal']==(name=='empty')
        assert header(out)['complete'] and canon(rows(out),p)==expected,name
        _,old_basis=original.solve(inputs,len(variables),p,pairs=2,reset=1)
        assert canon(old_basis,p)==expected,name
        if args.compare_binary:
            comparison=folder/(name+'_comparison.hcf')
            comparison_run=subprocess.run([str(args.compare_binary),'--input',str(inp),'--output',str(comparison),
                                           '--pairs','2','--info','0'],capture_output=True,text=True,timeout=45)
            assert comparison_run.returncode==0,(name,comparison_run.stderr)
            assert canon(rows(comparison),p)==expected,name
        results.append({'case':name,'prime':p,'native_complete_basis_matches_original_and_SymPy':True,
                        'basis_polynomials':header(out)['generators'],'basis_terms':header(out)['terms'],
                        'runtime_cpu_report':next(l for l in run.stderr.splitlines() if l.startswith('[native]'))})
        if name=='cyclic4':
            checkpoint=folder/'cyclic4_partial.hcf';unused=folder/'cyclic4_should_not_complete.hcf'
            run=subprocess.run([str(binary),'--input',str(inp),'--output',str(unused),'--checkpoint',str(checkpoint),
                    '--round-budget','1','--pairs','1','--info','0'],capture_output=True,text=True,timeout=45)
            (folder/'cyclic4_checkpoint.log').write_text(run.stderr+run.stdout)
            assert run.returncode==75,(run.returncode,run.stderr,run.stdout)
            meta=header(checkpoint);assert not meta['complete'] and meta['original_generators']==len(inputs)
            partial=list(rows(checkpoint));assert canon(partial[:len(inputs)],p)==canon(inputs,p)
            for f in expressions(partial,variables):assert reference.reduce(f)[1]==0
            resumed=folder/'cyclic4_resumed.hcf'
            rerun=subprocess.run([str(binary),'--input',str(checkpoint),'--output',str(resumed),'--pairs','2','--info','0'],
                                  capture_output=True,text=True,timeout=45)
            (folder/'cyclic4_resumed.log').write_text(rerun.stderr+rerun.stdout)
            assert rerun.returncode==0,(rerun.returncode,rerun.stderr,rerun.stdout)
            assert header(resumed)['complete'] and canon(rows(resumed),p)==expected
            restart_result={'forced_exit_code':75,'checkpoint_header':meta,
                            'original_prefix_exactly_preserved':True,
                            'every_partial_row_independently_reduces_to_zero_in_original_ideal':True,
                            'resumed_complete_basis_matches_direct_original_and_SymPy':True,
                            'checkpoint_sha256':hashlib.sha256(checkpoint.read_bytes()).hexdigest()}
    assert restart_result
    # A real asynchronous signal requests work only through the safe-boundary
    # flag.  The first F4 boundary guarantees the handler is already installed.
    variables=S.symbols('s0:7');p=101
    cyclic=[sum(S.prod(variables[(j+k)%7] for k in range(d)) for j in range(7)) for d in range(1,7)]
    cyclic.append(S.prod(variables)-1)
    inputs=[{e:int(c)%p for e,c in S.Poly(f,*variables,modulus=p).terms()} for f in cyclic]
    sig_input=folder/'signal_input.hcf';sig_checkpoint=folder/'signal_checkpoint.hcf';sig_output=folder/'signal_complete.hcf'
    write(sig_input,[str(v) for v in variables],p,inputs)
    def limit():resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
    proc=subprocess.Popen([str(binary),'--input',str(sig_input),'--output',str(sig_output),
                           '--checkpoint',str(sig_checkpoint),'--pairs','1','--info','0'],
                          stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,preexec_fn=limit)
    observed=[]
    while True:
        line=proc.stderr.readline();observed.append(line)
        if line.startswith('[progress]'):
            proc.send_signal(signal.SIGUSR1);break
        assert line,('process ended before signal-safe boundary',proc.poll())
    try:stdout,stderr=proc.communicate(timeout=10)
    except subprocess.TimeoutExpired:
        proc.kill();proc.communicate();raise
    assert proc.returncode==75,(proc.returncode,stdout,''.join(observed)+stderr)
    signal_header=header(sig_checkpoint);assert not signal_header['complete']
    assert canon(list(rows(sig_checkpoint))[:len(inputs)],p)==canon(inputs,p)
    receipt={'status':'PASS','binary':str(binary),'binary_sha256':build['binary_sha256'],
             'build_receipt_sha256':hashlib.sha256(args.build_receipt.read_bytes()).hexdigest(),
             'additional_packed_driver_comparison':str(args.compare_binary) if args.compare_binary else None,
             'cases':results,'restart_test':restart_result,
             'signal_checkpoint_test':{'signal':'SIGUSR1','exit_code':75,'original_prefix_preserved':True,
                                       'header':signal_header,'handler_performs_only_sig_atomic_t_assignment':True},
             'unit_ideal_diagnostic_checked':True,'seconds':time.monotonic()-started,
             'scope':'Small complete-basis comparisons and an independently checked ideal-preserving partial restart. No target quotient or trace has been computed.'}
    args.output_receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
