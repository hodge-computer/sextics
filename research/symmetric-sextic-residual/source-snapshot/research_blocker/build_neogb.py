#!/usr/bin/env python3
"""Build the pinned original and compacting finite-field F4 cores locally.

Requires the official msolve-v0.11.0 and GMP-6.3.0 source trees under vendor/.
No privileged install, binary rewriting, or external publication is performed.
"""
from pathlib import Path
import argparse, ctypes, difflib, hashlib, json, re, shutil, subprocess

HERE=Path(__file__).resolve().parent
VENDOR=HERE/'vendor'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--audit',action='store_true')
    args=parser.parse_args()
    original=VENDOR/'msolve-0.11.0/src/neogb'
    patched=VENDOR/'neogb_patched'
    shutil.copytree(original,patched,dirs_exist_ok=True)
    (VENDOR/'msolve').mkdir(exist_ok=True)
    shutil.copy2(original.parent/'msolve/streams.h',VENDOR/'msolve/streams.h')
    original_h=(original/'hash.c').read_text()
    original_f=(original/'f4.c').read_text()
    assert sha(original/'hash.c')=='1cae7cab02e7a2ed35a997f391c087e6e3ff4150ec221181ff4209da2b8df3fe'
    assert sha(original/'f4.c')=='a545ffd5e4117c4cc3cba421d64d7145fa295c0befc45d5fd5d0b735b5a031a5'
    (patched/'hash.c').write_text(original_h+'\n'+(HERE/'compact_hash.c').read_text())
    start='''    while (!done) {
        rrt = realtime();'''
    changed='''    uint64_t hc_round = 0;
    while (!done) {
        ++hc_round;
        rrt = realtime();'''
    assert original_f.count(start)==1
    f=original_f.replace(start,changed)
    needle='''        done = preprocessing(mat, bs, md);'''
    replacement='''        if (fc > 0 && md->trace_level == NO_TRACER && md->reset_ht > 0
                && md->reset_ht != INT32_MAX
                && (hc_round % (uint64_t)md->reset_ht) == 0) {
            hc_compact_basis_hash_table(bs, md);
        }

        done = preprocessing(mat, bs, md);'''
    assert f.count(needle)==1
    (patched/'f4.c').write_text(f.replace(needle,replacement))
    diff=''
    for name in ['hash.c','f4.c']:
        diff+=''.join(difflib.unified_diff((original/name).read_text().splitlines(True),
                   (patched/name).read_text().splitlines(True),
                   fromfile='a/src/neogb/'+name,tofile='b/src/neogb/'+name))
    (HERE/'msolve_compact_hash.patch').write_text(diff)
    # The complete upstream configure script needs m4, which this environment
    # lacks. Prepare its public header from the official template for the
    # independently checked installed 64-bit, nail-free GMP ABI.
    gmp_lib=Path('/usr/lib/x86_64-linux-gnu/libgmp.so.10.5.0')
    gmp=ctypes.CDLL(str(gmp_lib))
    assert ctypes.c_int.in_dll(gmp,'__gmp_bits_per_limb').value==64
    assert ctypes.sizeof(ctypes.c_ulong)==8
    header=(VENDOR/'gmp-6.3.0/gmp-h.in').read_text()
    for k,v in {'GMP_LIMB_BITS':'64','GMP_NAIL_BITS':'0',
                'DEFN_LONG_LONG_LIMB':'/* #undef _LONG_LONG_LIMB */',
                'LIBGMP_DLL':'0','CC':'gcc','CFLAGS':'-O2'}.items():
        header=header.replace('@'+k+'@',v)
    assert not re.findall(r'@[A-Z_0-9]+@',header)
    (VENDOR/'gmp-6.3.0/gmp.h').write_text(header)
    builds=[]
    targets=[('original',original,False),('compact',patched,False)]
    if args.audit:targets.append(('compact_audit',patched,True))
    for name,src,audit in targets:
        output=VENDOR/('libneogb_'+name+'.so')
        command=['gcc','-O2','-fPIC','-shared','-D_GNU_SOURCE',
                 '-I'+str(VENDOR/'gmp-6.3.0')]
        if audit:command+=['-DHC_COMPACT_AUDIT=1']
        command+=['-o',str(output),str(src/'gb.c'),str(gmp_lib),'-lm']
        log=VENDOR/('neogb_compile_'+name+'.log')
        with log.open('w') as stream:
            subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT,check=True)
        ctypes.CDLL(str(output))
        builds.append({'name':name,'command':command,'sha256':sha(output),
                       'exact_reference_audit_enabled':audit})
    receipt={'upstream_tag':'v0.11.0','upstream_tree':'cc044551f8e202d00691990fd3fd0b1226a88ea2',
             'upstream_archive_sha256':sha(VENDOR/'msolve-v0.11.0.tar.gz'),
             'gmp_template_archive_sha256':sha(VENDOR/'gmp-6.3.0.tar.xz'),
             'patch_sha256':sha(HERE/'msolve_compact_hash.patch'),
             'scope':'Only ordinary finite-field, signature-free, NO_TRACER F4 path is modified.',
             'builds':builds}
    (HERE/'neogb_build_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)

if __name__=='__main__':main()
