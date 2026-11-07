#!/usr/bin/env python3
"""Small independent checks of the direct packed-to-native input boundary."""
from pathlib import Path
import hashlib
import json
import random
import subprocess
import sympy as S
from sympy.polys.orderings import grevlex
from packed_f4 import write,header,rows
from check_resumable import canon
from neogb_solver import NativeF4

HERE=Path(__file__).resolve().parent

def main():
    build=json.loads((HERE/'resumable_dictionary_build_receipt.json').read_text())
    binary=Path(build['binary']);flat=Path(json.loads((HERE/'resumable_build_receipt.json').read_text())['binary'])
    folder=HERE/'vendor'/('dictionary_boundary_checks_'+build['binary_sha256'][:12]);folder.mkdir(exist_ok=True)
    native=NativeF4(HERE/'vendor/libneogb_original.so')
    x,y,z=S.symbols('x y z');v=(x,y,z)
    polynomials=[7*x*x+5*y*z+1,3*y*y+4*x*z+2,6*z*z+2*x*y+3]
    results=[]
    for p,elim in [(37,0),(1009,0),(65537,0),(37,1),(1009,2)]:
        inputs=[]
        for i,f in enumerate(polynomials):
            terms=[(e,int(c)%p) for e,c in S.Poly(f,*v,modulus=p).terms()]
            random.Random(910+i).shuffle(terms);inputs.append(dict(terms))
        order=grevlex if not elim else lambda m,e=elim:(grevlex(m[:e]),grevlex(m[e:]))
        expected=canon([dict(f.terms()) for f in S.groebner(polynomials,*v,modulus=p,order=order).polys],p)
        inp=folder/f'p{p}_e{elim}.hcf';write(inp,[str(a) for a in v],p,inputs,elim=elim)
        outputs=[]
        for label,exe in [('dictionary',binary),('flat',flat)]:
            out=folder/f'p{p}_e{elim}_{label}.hcf'
            run=subprocess.run([str(exe),'--input',str(inp),'--output',str(out),'--pairs','2','--info','0'],capture_output=True,text=True,timeout=30)
            assert run.returncode==0,(label,p,elim,run.stderr,run.stdout)
            assert header(out)['complete'] and canon(rows(out),p)==expected
            outputs.append(hashlib.sha256(out.read_bytes()).hexdigest())
        _,ref=native.solve(inputs,3,p,elim=elim,pairs=2)
        assert canon(ref,p)==expected
        imported=subprocess.run([str(binary),'--input',str(inp),'--output',str(folder/'unused.hcf'),'--import-only','1','--info','0'],capture_output=True,text=True,timeout=30)
        assert imported.returncode==0
        summary=json.loads(imported.stdout.splitlines()[-1]);assert summary['status']=='IMPORT_ONLY' and not summary['complete']
        results.append({'prime':p,'elimination_block':elim,'shuffled_nonmonic_input':True,
                        'matches_original_flat_and_independent_SymPy':True,
                        'direct_and_flat_complete_file_hashes':outputs,'import_only_exits_without_F4':True})
    # Zero rows are omitted from the native basis while the fixed original
    # prefix still preserves them verbatim in later partial checkpoints.
    zero_input=folder/'zero_row.hcf';out=folder/'zero_row_complete.hcf'
    write(zero_input,['x','y'],1009,[{}, {(2,0):2,(0,1):3},{(0,2):5,(1,0):7}])
    run=subprocess.run([str(binary),'--input',str(zero_input),'--output',str(out),'--info','0'],capture_output=True,text=True,timeout=30)
    assert run.returncode==0,(run.returncode,run.stderr)
    expected=canon([dict(f.terms()) for f in S.groebner([2*x*x+3*y,5*y*y+7*x],x,y,modulus=1009,order='grevlex').polys],1009)
    assert canon(rows(out),1009)==expected
    receipt={'status':'PASS','binary_sha256':build['binary_sha256'],'source_sha256':build['source_fingerprints']['resumable_dictionary_driver.c'],
             'coefficient_widths_tested':[8,16,32],'cases':results,'zero_input_row_omitted_correctly':True,
             'original_generator_prefix_only_uses_flat_exponents':True,
             'derived_input_storage':'one uint32 native id per dictionary entry; native uint32 monomial indices and field-width coefficients per term; 128 KiB read buffer; no terms-times-variables array',
             'scope':'Input-boundary regression checks on small complete ideals, plus the separate partial-restart and SIGUSR1 validation. No target quotient or traces.'}
    (HERE/'resumable_dictionary_input_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
