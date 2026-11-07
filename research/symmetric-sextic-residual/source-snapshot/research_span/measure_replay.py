#!/usr/bin/env python3
"""Run one finite checker in a fresh child and record Linux peak RSS."""
from pathlib import Path
import argparse
import hashlib
import json
import resource
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('script',type=Path)
    args = ap.parse_args()
    script = args.script.resolve()
    output = HERE/'contact'/('root_'+script.stem)
    start = time.monotonic()
    with output.with_suffix('.log').open('w') as log:
        process = subprocess.run([sys.executable,str(script)],stdout=log,stderr=subprocess.STDOUT)
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    receipt = {
        'status':'PASS' if process.returncode == 0 else 'FAIL',
        'script':str(script),
        'script_sha256':hashlib.sha256(script.read_bytes()).hexdigest(),
        'exit_code':process.returncode,
        'wall_seconds':time.monotonic()-start,
        'user_cpu_seconds':usage.ru_utime,
        'system_cpu_seconds':usage.ru_stime,
        'peak_resident_KiB':usage.ru_maxrss,
        'peak_resident_MiB':usage.ru_maxrss/1024,
        'platform':sys.platform,
        'scope':'Peak resident memory of this single fresh child, measured by getrusage on Linux.'
    }
    output.with_suffix('.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(output.with_suffix('.log').read_text())
    print(json.dumps(receipt,indent=2))
    raise SystemExit(process.returncode)


if __name__ == '__main__': main()
