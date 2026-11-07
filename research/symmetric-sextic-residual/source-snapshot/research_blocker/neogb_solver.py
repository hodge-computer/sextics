#!/usr/bin/env python3
"""Exact finite-field F4 adapter with streamed JSON-lines basis export.

Uses the pinned native neogb API. A completed solver output still requires
independent ideal/basis verification before being called a certificate.
"""
from pathlib import Path
from contextlib import contextmanager
import argparse, ctypes as C, hashlib, json, re, time

HERE=Path(__file__).resolve().parent
I32=C.c_int32
IP=C.POINTER(I32)

def parse_ms(path):
    lines=[s.strip() for s in Path(path).read_text().splitlines() if s.strip() and not s.lstrip().startswith('#')]
    names=[s.strip() for s in lines[0].rstrip(',').split(',')]
    assert len(set(names))==len(names)
    assert all(re.fullmatch(r'[A-Za-z_]\w*',n) for n in names)
    p=int(lines[1].rstrip(',')); index={n:i for i,n in enumerate(names)}
    polys=[]
    for raw in ''.join(lines[2:]).split(','):
        if not raw.strip():continue
        s=raw.replace(' ','')
        assert not any(c in s for c in '()/;')
        terms={}
        for term in re.findall(r'[+-]?[^+-]+',s):
            c=-1 if term.startswith('-') else 1
            e=[0]*len(names)
            for atom in term.lstrip('+-').split('*'):
                if re.fullmatch(r'\d+',atom):c*=int(atom)
                else:
                    match=re.fullmatch(r'([A-Za-z_]\w*)(?:\^(\d+))?',atom)
                    assert match,atom
                    e[index[match[1]]]+=int(match[2] or 1)
            e=tuple(e);terms[e]=(terms.get(e,0)+c)%p
        polys.append({e:c for e,c in terms.items() if c})
    return names,p,polys

class NativeF4:
    def __init__(self,path):
        self.path=Path(path).resolve()
        self.lib=C.CDLL(str(self.path))
        self.lib.export_f4.argtypes=[C.c_void_p,IP,C.POINTER(IP),C.POINTER(IP),
            C.POINTER(C.c_void_p),IP,IP,C.c_void_p,C.c_uint32]+[I32]*12
        self.lib.export_f4.restype=C.c_int64
        self.lib.free_f4_julia_result_data.argtypes=[C.c_void_p,C.POINTER(IP),
            C.POINTER(IP),C.POINTER(C.c_void_p),C.c_int64,C.c_int64]
        self.libc=C.CDLL(None)
    def stats(self):
        out={}
        for n in ['hc_compact_calls','hc_compact_removed','hc_compact_shrinks']:
            try:out[n]=C.c_uint64.in_dll(self.lib,n).value
            except ValueError:pass
        return out
    @contextmanager
    def export(self,polys,n,p,pairs=64,reset=1,info=0,elim=0):
        terms=[(e,c%p) for f in polys for e,c in f.items() if c%p]
        lens=(I32*len(polys))(*(len(f) for f in polys))
        exp=(I32*(len(terms)*n))(*(v for e,c in terms for v in e))
        coeff=(I32*len(terms))(*(c for e,c in terms))
        count=I32();blen=IP();bexp=IP();bcf=C.c_void_p()
        start=time.monotonic();before=self.stats()
        total=self.lib.export_f4(C.cast(self.libc.malloc,C.c_void_p),C.byref(count),
            C.byref(blen),C.byref(bexp),C.byref(bcf),lens,exp,coeff,p,
            0,elim,n,len(polys),14,1,pairs,reset,2,1,0,info)
        assert total>=0 and count.value>=0
        cptr=C.cast(bcf,IP)
        def rows():
            offset=0
            for i in range(count.value):
                f={}
                for j in range(blen[i]):
                    idx=offset+j
                    e=tuple(int(bexp[idx*n+k]) for k in range(n))
                    c=int(cptr[idx])%p
                    if c:f[e]=c
                offset+=blen[i]
                yield f
            assert offset==total
        metadata={'basis_polynomials':count.value,'terms':int(total),
            'seconds':time.monotonic()-start,
            'compaction':{k:v-before.get(k,0) for k,v in self.stats().items()}}
        try:yield metadata,rows()
        finally:self.lib.free_f4_julia_result_data(C.cast(self.libc.free,C.c_void_p),
                     C.byref(blen),C.byref(bexp),C.byref(bcf),count.value,p)
    def solve(self,polys,n,p,**kwargs):
        with self.export(polys,n,p,**kwargs) as (metadata,rows):
            return metadata,list(rows)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--input',type=Path,required=True)
    ap.add_argument('--library',type=Path,default=HERE/'vendor/libneogb_compact.so')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--pairs',type=int,default=64)
    ap.add_argument('--reset',type=int,default=1)
    ap.add_argument('--elim',type=int,default=0)
    ap.add_argument('--info',type=int,default=2)
    args=ap.parse_args()
    names,p,polys=parse_ms(args.input)
    native=NativeF4(args.library)
    with native.export(polys,len(names),p,pairs=args.pairs,reset=args.reset,
                       info=args.info,elim=args.elim) as (meta,rows):
        with args.output.open('w') as stream:
            stream.write(json.dumps({'schema':'sparse-finite-field-basis-v1',
                'variables':names,'prime':p,'order':'grevlex' if not args.elim else 'block-grevlex',
                'elimination_block':args.elim,**meta})+'\n')
            for f in rows:stream.write(json.dumps([[list(e),c] for e,c in f.items()])+'\n')
    meta.update({'input_sha256':hashlib.sha256(args.input.read_bytes()).hexdigest(),
                'library_sha256':hashlib.sha256(args.library.read_bytes()).hexdigest(),
                'basis_file_sha256':hashlib.sha256(args.output.read_bytes()).hexdigest(),
                'basis_independently_verified':False,'full_trace_evaluated':False})
    args.output.with_suffix('.receipt.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps(meta),flush=True)

if __name__=='__main__':main()
