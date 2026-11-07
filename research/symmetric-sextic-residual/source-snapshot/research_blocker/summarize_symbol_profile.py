#!/usr/bin/env python3
"""Summarize measured work in one target F4 batch, without a speedup claim."""
from pathlib import Path
import argparse,hashlib,json,re


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('log',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    content=args.log.read_text()
    lines=[s for s in content.splitlines() if s.startswith('[symbol_profile]')]
    if not lines:raise ValueError('No completed profile record; do not infer timings from a partial batch')
    tokens=dict(re.findall(r'(\w+)=([^\s]+)',lines[-1]))
    stats={k:float(v) if k.endswith('_seconds') else int(v) if v.isdecimal() else v
           for k,v in tokens.items()}
    total=stats['lookup_ns']+stats['materialization_ns']
    assert total>0
    rec={'schema':'actual-target-symbolic-profile-v1',
         'log_file':args.log.name,'log_sha256':hashlib.sha256(args.log.read_bytes()).hexdigest(),
         'measured_regions':stats,
         'lookup_share_of_two_regions':stats['lookup_ns']/total,
         'materialization_share_of_two_regions':stats['materialization_ns']/total,
         'scope':'Process-local timings of exact reducer lookup and multiplied-polynomial row construction. Excludes initial S-pair construction and outer symbolic bookkeeping. Includes profiling overhead.',
         'full_basis_computed':False,'full_source_trace_evaluated':False,
         'speedup_measured':False}
    args.output.write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps(rec,indent=2))


if __name__=='__main__':main()
