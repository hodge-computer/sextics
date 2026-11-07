#!/usr/bin/env python3
"""Portable dictionary format for native F4 input, checkpoints and final bases.

Header <8s6I4Q (64 bytes): magic, version, flags, nvars, prime, order,
elimination block, ngens, nmonomials, nterms, original-generator prefix length.
Flags: 0 incomplete checkpoint; 1 completed native basis; 2 input generators.
Then nmonomials*nvars little-endian uint16 exponents. Each row has a uint64
length followed by (uint32 dictionary ID,uint32 coefficient) pairs.
"""
from pathlib import Path
import argparse
import array
import hashlib
import json
import struct
import sys

HEADER=struct.Struct('<8s6I4Q')
PAIR=struct.Struct('<II')
LENGTH=struct.Struct('<Q')

def write(path,names,p,polys,flags=2,elim=0):
    path=Path(path);dictionary={}
    for f in polys:
        for e,c in f.items():
            if c%p:
                assert len(e)==len(names) and min(e)>=0 and max(e)<=65535 and sum(e)<=65535
                if e not in dictionary:dictionary[e]=len(dictionary)
    terms=sum(sum(c%p!=0 for c in f.values()) for f in polys)
    assert len(dictionary)<2**32 and 2<=p<2**31
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('wb') as stream:
        stream.write(HEADER.pack(b'HCF4PK01',1,flags,len(names),p,0,elim,len(polys),len(dictionary),terms,len(polys)))
        for e in dictionary:stream.write(struct.pack('<'+'H'*len(names),*e))
        for f in polys:
            selected=[(e,c%p) for e,c in f.items() if c%p]
            stream.write(LENGTH.pack(len(selected)))
            for e,c in selected:stream.write(PAIR.pack(dictionary[e],c))
    meta={'schema':'packed-native-f4-v1','variables':names,'prime':p,'flags':flags,
          'generators':len(polys),'monomials':len(dictionary),'terms':terms,'original_generators':len(polys),
          'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'complete':flags==1,
          'basis_independently_verified':False}
    path.with_suffix(path.suffix+'.json').write_text(json.dumps(meta,indent=2)+'\n')
    return meta

def header(path):
    with Path(path).open('rb') as f:data=f.read(HEADER.size)
    magic,version,flags,n,p,order,elim,ngens,nmon,terms,noriginal=HEADER.unpack(data)
    assert magic==b'HCF4PK01' and version==1 and order==0 and noriginal<=ngens
    return {'version':version,'flags':flags,'complete':flags==1,'variables':n,'prime':p,
            'order':'grevlex' if not elim else 'block-grevlex','elimination_block':elim,
            'generators':ngens,'monomials':nmon,'terms':terms,'original_generators':noriginal}

def rows(path):
    meta=header(path);n=meta['variables'];dictionary=array.array('H')
    with Path(path).open('rb') as f:
        f.seek(HEADER.size);dictionary.fromfile(f,meta['monomials']*n)
        if sys.byteorder!='little':dictionary.byteswap()
        count=0
        for _ in range(meta['generators']):
            length,=LENGTH.unpack(f.read(8));row={}
            for _ in range(length):
                idx,c=PAIR.unpack(f.read(8));assert idx<meta['monomials'] and 0<c<meta['prime']
                e=tuple(dictionary[idx*n:(idx+1)*n]);row[e]=(row.get(e,0)+c)%meta['prime'];count+=1
            yield {e:c for e,c in row.items() if c}
        assert count==meta['terms'] and not f.read(1)

def main():
    ap=argparse.ArgumentParser();sub=ap.add_subparsers(dest='command',required=True)
    pack=sub.add_parser('pack');pack.add_argument('input',type=Path);pack.add_argument('output',type=Path)
    inspect=sub.add_parser('inspect');inspect.add_argument('input',type=Path)
    export=sub.add_parser('export');export.add_argument('input',type=Path);export.add_argument('output',type=Path)
    args=ap.parse_args()
    if args.command=='pack':
        from neogb_solver import parse_ms
        names,p,polys=parse_ms(args.input);print(json.dumps(write(args.output,names,p,polys),indent=2))
    elif args.command=='inspect':print(json.dumps(header(args.input),indent=2))
    else:
        with args.output.open('w') as stream:
            stream.write(json.dumps(header(args.input))+'\n')
            for f in rows(args.input):stream.write(json.dumps([[list(e),c] for e,c in f.items()])+'\n')

if __name__=='__main__':main()
