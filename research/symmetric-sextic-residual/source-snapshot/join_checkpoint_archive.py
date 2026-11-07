#!/usr/bin/env python3
"""Reassemble the exact large archive from its six verified download parts."""
from pathlib import Path
import argparse,hashlib,json,os


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--parts-dir',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    manifest=json.loads((Path(__file__).resolve().parent/'parts_manifest.json').read_text())
    output=args.output or args.parts_dir/manifest['complete_archive_file']
    temporary=output.with_name(output.name+'.assembling')
    if output.exists() or temporary.exists():
        raise FileExistsError('Choose a fresh output path; an output or temporary file already exists')
    total=hashlib.sha256();count=0
    try:
        with temporary.open('xb') as dest:
            for part in manifest['parts']:
                name=part['file_name']
                if Path(name).name!=name:raise ValueError('Part name must be a basename')
                digest=hashlib.sha256();length=0
                with (args.parts_dir/name).open('rb') as source:
                    for block in iter(lambda:source.read(8*1024**2),b''):
                        dest.write(block);digest.update(block);total.update(block)
                        length+=len(block);count+=len(block)
                if length!=part['bytes'] or digest.hexdigest()!=part['sha256']:
                    raise ValueError('Part checksum/length mismatch: '+name)
                print('Verified '+name,flush=True)
        if count!=manifest['complete_archive_bytes'] or total.hexdigest()!=manifest['complete_archive_sha256']:
            raise ValueError('Combined archive checksum/length mismatch')
        if output.exists():raise FileExistsError(output)
        os.replace(temporary,output)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise
    print('Verified complete archive: '+str(output))
    print('Proof status: unfinished research; the target theorem is unproved.')


if __name__=='__main__':main()
