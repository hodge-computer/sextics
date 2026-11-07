#!/usr/bin/env python3
"""Extend the previously saved partial-proof package without rewriting history.

Large-file hashing and ZIP creation are streamed. Only selected resumable
checkpoints are included; historical measurements and hashes are retained.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,time,zipfile
from packed_f4 import header

HERE=Path(__file__).resolve().parent

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

def copy(source,destination):
    source=Path(source);destination=Path(destination)
    destination.parent.mkdir(parents=True,exist_ok=True)
    if source.stat().st_size>=64*1024**2:
        if destination.exists():destination.unlink()
        try:os.link(source,destination)
        except OSError:shutil.copy2(source,destination)
    else:shutil.copy2(source,destination)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--package',type=Path,required=True)
    ap.add_argument('--basis',type=Path,required=True)
    ap.add_argument('--additional-basis',type=Path,action='append',default=[])
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();start=time.monotonic()
    package=args.package.resolve();basis=args.basis.resolve();output=args.output.resolve()
    assert package.is_dir() and basis.is_file()
    assert basis.parent==HERE
    selected_header=header(basis);state=basis.with_suffix(basis.suffix+'.state')
    bases=[basis]+[p.resolve() for p in args.additional_basis]
    assert len(bases)==len(set(bases))
    assert all(p.is_file() and p.parent==HERE for p in bases)
    states={p.with_suffix(p.suffix+'.state') for p in bases}
    assert all(p.is_file() for p in states)
    history=package/'PREVIOUS_MEMORY_COMPUTATION.txt'
    if not history.exists():shutil.copy2(package/'README.txt',history)
    previous_manifest=package/'PREVIOUS_MEMORY_PACKAGE_SHA256.json'
    if not previous_manifest.exists():shutil.copy2(package/'PACKAGE_SHA256.json',previous_manifest)
    old=json.loads(previous_manifest.read_text())
    protected='a51532e0442d72e8ce95d6728390fac0f719287d1cf20020701625bc1b5409d9'
    assert sha(package/'HodgeTarget.lean')==protected
    for path in package.glob('*.lean'):
        entry=old[path.name];expected=entry if isinstance(entry,str) else entry['sha256']
        assert sha(path)==expected

    destination=package/'research_blocker';destination.mkdir(exist_ok=True)
    omitted=[]
    for source in sorted(HERE.iterdir()):
        if not source.is_file() or '.tmp.' in source.name:continue
        if source.stat().st_size>=64*1024**2 and source not in bases:
            omitted.append({'file':source.name,'bytes':source.stat().st_size,'sha256':sha(source)})
            continue
        if source.name.endswith('.hcf.state') and source not in states:continue
        copy(source,destination/source.name)
    assert (destination/basis.name).is_file()
    if state.exists():assert (destination/state.name).is_file()
    assert all((destination/p.name).is_file() for p in bases+list(states))

    # Corresponding sources and licenses for the exact native binaries used.
    vendor=HERE/'vendor';target=destination/'vendor'
    for source in sorted((vendor/'msolve-0.11.0/src/neogb').glob('*')):
        if source.is_file():copy(source,target/'msolve-0.11.0/src/neogb'/source.name)
    for rel in ['msolve-0.11.0/src/msolve/streams.h','msolve-0.11.0/COPYING',
                'gmp-6.3.0/gmp.h','gmp-6.3.0/gmp-h.in',
                'msolve-v0.11.0.tar.gz','gmp-6.3.0.tar.xz']:
        copy(vendor/rel,target/rel)
    for source in (vendor/'gmp-6.3.0').glob('COPYING*'):
        if source.is_file():copy(source,target/'gmp-6.3.0'/source.name)
    for source in vendor.glob('libneogb_*.so'):copy(source,target/source.name)
    copy(vendor/'inspect_f4_state',target/'inspect_f4_state')
    used=['resumable_f7c3aa9b48eb8cae','resumable_5a57547469400e16','resumable_c88c65dfa299f4db',
          'openmp_88974186e92805c0','symbol_profile_dd5f742c96c6e820',
          'reducer_cache_da45de22dae5b9cb','divisor_index_03d4bfb8eda3ba46']
    for name in used:
        source=vendor/name
        assert source.is_dir()
        shutil.copytree(source,target/name,dirs_exist_ok=True,
                        ignore=shutil.ignore_patterns('__pycache__','*.pyc'))

    run_names=['finite_g2block','finite_beta_g2first','compact_two_rhs',
               'sparse32_core_first','sparse32_core_resume','sparse32_state_first',
               'sparse32_state_continuation','sparse32_openmp_continuation',
               'sparse32_jacobian_openmp','sparse32_jacobian_retry',
               'sparse32_symbol_profile','sparse32_cache_continuation',
               'sparse32_divisor_index_match','sparse32_divisor_continuation']
    runs=[]
    for name in run_names:
        path=HERE/(name+'_receipt.json')
        if path.exists():
            d=json.loads(path.read_text())
            runs.append({k:v for k,v in d.items() if k not in ['samples','command']})
    record={'schema':'symmetric-sextic-blocker-continuation-v1',
        'status':'PARTIAL_RESEARCH_AND_CHECKPOINT; FINAL_THEOREM_UNPROVED',
        'protected_target_sha256':protected,'previous_Lean_sources_unchanged':51,
        'new_Lean_modules':0,'finite_quotient_independently_verified':False,
        'full_source_traces_evaluated':False,'full_certificate_proved':False,
        'canonical_source_pushforward_normalization_or_correction_proved':False,
        'field_specialization':{'prime':37,'lambda':1,'r':2,'s':3},
        'selected_packed_basis':{'file':'research_blocker/'+basis.name,
            'bytes':basis.stat().st_size,'sha256':sha(basis),'header':selected_header},
        'selected_native_state':{'file':'research_blocker/'+state.name,
            'bytes':state.stat().st_size,'sha256':sha(state)} if state.exists() else None,
        'additional_selected_checkpoints':[
            {'file':'research_blocker/'+p.name,'bytes':p.stat().st_size,
             'sha256':sha(p),'header':header(p),
             'native_state_file':'research_blocker/'+p.name+'.state',
             'native_state_sha256':sha(p.with_suffix(p.suffix+'.state'))}
            for p in bases[1:]],
        'older_large_intermediate_checkpoints_not_duplicated_in_download':omitted,
        'historical_measurements_and_parent_hashes_retained':True,
        'reset_flag_operational_explanation_corrected':True,
        'current_sparse_input':{'variables':38,'equations':38,'terms':585,'degree':3},
        'runs':runs}
    (package/'blocker_computation_receipt.json').write_text(json.dumps(record,indent=2)+'\n')
    summary=(
        'LATEST CHECKPOINT AND PROOF STATUS\n'
        '==================================\n'
        'The final protected theorem is UNPROVED. No full source trace has been evaluated.\n'
        f'Saved packed data: research_blocker/{basis.name}\n'
        f'Native complete flag: {selected_header["complete"]}; independently verified basis: False.\n'
        f'Rows: {selected_header["generators"]:,}; terms: {selected_header["terms"]:,}; '
        f'monomials: {selected_header["monomials"]:,}.\n'
        f'Pending-queue sidecar included: {state.exists()}.\n'
        'See blocker_computation_receipt.json for measurements and exact hashes.\n'
        f'Additional resumable routes included: {len(bases)-1}.\n'
        'Only selected large checkpoints are duplicated in this download; earlier\n'
        'run logs, receipts and parent checkpoint hashes are retained.\n\n')
    (package/'README.txt').write_text(summary+(HERE/'README.txt').read_text())

    # Remove runtime caches inherited from previous development packages.
    for cache in package.rglob('__pycache__'):
        if cache.is_dir():shutil.rmtree(cache)
    manifest={str(p.relative_to(package)):sha(p) for p in sorted(package.rglob('*'))
              if p.is_file() and p!=package/'PACKAGE_SHA256.json'}
    (package/'PACKAGE_SHA256.json').write_text(json.dumps(manifest,indent=2)+'\n')
    temporary=output.with_name(output.name+'.tmp')
    with zipfile.ZipFile(temporary,'w',zipfile.ZIP_DEFLATED,compresslevel=3,allowZip64=True) as z:
        for p in sorted(package.rglob('*')):
            if p.is_file():z.write(p,str(p.relative_to(package.parent)))
    with zipfile.ZipFile(temporary) as z:
        assert z.testzip() is None
        count=len(z.infolist())
    os.replace(temporary,output)
    receipt={'status':'PASS','package':str(package),'zip':str(output),'files':count,
        'bytes':output.stat().st_size,'sha256':sha(output),'manifest_entries':len(manifest),
        'zip_CRC_check_passed':True,'protected_target_unchanged':True,
        'latest_checkpoint_complete':selected_header['complete'],
        'full_trace_evaluated':False,'full_certificate_proved':False,
        'seconds':time.monotonic()-start}
    (HERE.parent/'blocker_package_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
