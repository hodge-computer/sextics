#!/usr/bin/env python3
"""Bind successful compilations to endpoint axioms and kernel object replay."""
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import subprocess
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
REPO=ROOT/'sextics/formal/lean'


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    started=time.monotonic()
    bindir=ROOT/'toolchains/lean-4.33.1-linux/bin'
    env=os.environ.copy()
    env['PATH']=str(bindir)+os.pathsep+env['PATH']
    env['LD_PRELOAD']=str(ROOT/'runtime_compat/own_exe_path.so')
    lake=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=REPO,env=env,text=True).strip()
    prior=[ROOT/('proof_attempt'+str(i)) for i in range(5,1,-1)]+[ROOT/'proof_attempt']
    env['LEAN_PATH']=os.pathsep.join([str(HERE)]+list(map(str,prior))+[lake])
    expected={
        'MonodromyImageSpanning':{
            'WeightedSexticMonodromy.orbitImageSpan_stable',
            'WeightedSexticMonodromy.orbitImageSpan_eq_top',
            'WeightedSexticMonodromy.finite_spanning_subset_of_span_eq_top',
            'WeightedSexticMonodromy.exists_finite_translates_rightInverse',
            'WeightedSexticMonodromy.exists_finite_translates_rightInverse_of_picardLefschetz'},
        'SymmetricPrime':{
            'SymmetricPrime.sectionConstant_not_mem_square',
            'SymmetricPrime.planeSection_irreducible',
            'SymmetricPrime.univariateF_monic',
            'SymmetricPrime.specialization_is_planeSection',
            'SymmetricPrime.target_irreducible',
            'SymmetricPrime.target_prime'},
    }
    records=[]
    for module,endpoints in expected.items():
        source=HERE/(module+'.lean');obj=HERE/(module+'.olean')
        compile_receipt=HERE/(module+'_compile_receipt.json')
        compiled=json.loads(compile_receipt.read_text())
        assert compiled['status']=='PASS' and compiled['exit_code']==0
        assert compiled['source_sha256']==digest(source)
        assert compiled['object_sha256']==digest(obj)
        text=source.read_text()
        assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b',text)
        assert not re.search(r'^\s*axiom\s',text,re.M)
        log=HERE/'compilation_logs'/(module+'.log')
        axioms={n:[a.strip() for a in aa.split(',') if a.strip()]
                for n,aa in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log.read_text(),re.S)}
        assert set(axioms)==endpoints
        assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
        command=['flock',str(ROOT/'lean_compile.lock'),'leanchecker','-v',module]
        replay=subprocess.run(command,cwd=REPO,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        checker_log=HERE/'compilation_logs'/(module+'_leanchecker.log')
        checker_log.write_text(replay.stdout)
        assert replay.returncode==0,replay.stdout
        assert 'replaying '+module in replay.stdout
        records.append({'module':module,'status':'PASS','source_sha256':digest(source),
            'object_sha256':digest(obj),'compile_receipt_sha256':digest(compile_receipt),
            'compiler_log_sha256':digest(log),'endpoint_axioms':axioms,
            'checker_exit_code':replay.returncode,'checker_log_sha256':digest(checker_log),
            'checker_command':command,'no_sorry_or_new_axioms':True})
        print(module+': bound compilation, endpoint axioms, and kernel replay PASS',flush=True)
    receipt={'status':'PASS','toolchain':subprocess.check_output(['lean','--version'],cwd=REPO,env=env,text=True).strip(),
        'compiler_binary_sha256':digest(bindir/'lean'),'checker_binary_sha256':digest(bindir/'leanchecker'),
        'audit_script_sha256':digest(Path(__file__)),
        'import_bindings':{name:{'source_sha256':digest(ROOT/'proof_attempt'/(name+'.lean')),
                                 'object_sha256':digest(ROOT/'proof_attempt'/(name+'.olean'))}
                           for name in ('ProjectorCore','HodgeTarget','SymmetricReflections')},
        'modules':records,'serialized_with':'lean_compile.lock',
        'checker_scope':'leanchecker replayed each new module against its imported environment using the same Lean kernel. Imported dependencies were not replayed with --fresh; this is not an external proof checker.',
        'mathematical_scope':'Monodromy module derives finite jointly surjective translated images and a linear section from explicit geometric-input hypotheses. SymmetricPrime proves unconditional primality of the exact protected HodgeSubmission.F. Neither module proves geometric support or the final HasCertificate.',
        'target_prime_proved':True,'geometric_support_proved':False,'full_certificate_proved':False,
        'seconds':time.monotonic()-started}
    (HERE/'monodromy_prime_kernel_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','seconds':receipt['seconds'],'target_prime_proved':True,
                      'full_certificate_proved':False}),flush=True)


if __name__=='__main__':main()
