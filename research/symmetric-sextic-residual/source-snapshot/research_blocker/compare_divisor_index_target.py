#!/usr/bin/env python3
"""Check the matched target-batch checkpoint and report measured timings."""
from pathlib import Path
import hashlib,json,re,subprocess

HERE=Path(__file__).resolve().parent


def main():
    baseline=json.loads((HERE/'sparse32_symbol_profile_receipt.json').read_text())
    indexed=json.loads((HERE/'sparse32_divisor_index_match_receipt.json').read_text())
    assert baseline['status']==indexed['status']=='PARTIAL_BASIS_CHECKPOINT'
    for field in ['input_sha256','input_native_state_sha256','requested_threads','requested_round_budget']:
        assert baseline[field]==indexed[field],field
    assert baseline['requested_round_budget']==1
    for r in [baseline,indexed]:
        command=r['command'];assert command[command.index('--pairs')+1]=='128'
    left=baseline['outputs']['checkpoint'];right=indexed['outputs']['checkpoint']
    assert left['sha256']==right['sha256'] and left['bytes']==right['bytes']
    assert left['header']==right['header']
    subprocess.run(['cmp','-s',str(HERE/left['file']),str(HERE/right['file'])],check=True)
    old=json.loads((HERE/'sparse32_symbol_profile_analysis.json').read_text())['measured_regions']
    logfile=HERE/'sparse32_divisor_index_match.log';content=logfile.read_text()
    lines=[s for s in content.splitlines() if s.startswith('[divisor_index]')]
    assert len(lines)==1,lines
    fields=dict(re.findall(r'(\w+)=([^\s]+)',lines[0]))
    new={k:float(v) if k.endswith('_seconds') else int(v) if v.isdecimal() else v
         for k,v in fields.items()}
    assert old['lookup_calls']==new['queries']
    for field in ['materialized_rows','materialized_terms']:assert old[field]==new[field]
    rounds=lambda text:[float(x) for x in re.findall(r'^\s*([0-9]+\.[0-9]+)\s*\|\s*[0-9]+\.[0-9]+\s*$',text,re.M)]
    old_rounds=rounds((HERE/'sparse32_symbol_profile.log').read_text())
    new_rounds=rounds(content)
    assert len(old_rounds)==len(new_rounds)==1
    rec={'schema':'matched-target-divisor-index-comparison-v1','status':'PASS',
         'input_checkpoint_sha256':baseline['input_sha256'],
         'input_native_state_sha256':baseline['input_native_state_sha256'],
         'output_checkpoint_byte_identical':True,'output_checkpoint_sha256':left['sha256'],
         'byte_comparison':'cmp -s exited 0; SHA256 and byte counts also match',
         'output_bytes':left['bytes'],'complete_basis':False,
         'matrix_batch_seconds':{'original_profiled_scan':old_rounds[0],'divisor_index':new_rounds[0],
                                 'observed_ratio':old_rounds[0]/new_rounds[0]},
         'lookup_seconds':{'original_profiled_scan':old['lookup_seconds'],'divisor_index':new['lookup_seconds'],
                           'observed_ratio':old['lookup_seconds']/new['lookup_seconds']},
         'original_profile':old,'divisor_index_profile':new,
         'peak_rss_kib':{'original_profiled_scan':baseline['peak_rss_kib'],'divisor_index':indexed['peak_rss_kib']},
         'log_sha256':hashlib.sha256(logfile.read_bytes()).hexdigest(),
         'scope':'One matched target batch, same native input state, 128 pairs and four threads. Timings include profiling overhead and are not a full-solve speedup or completion-time prediction.',
         'full_source_trace_evaluated':False,'full_certificate_proved':False}
    (HERE/'divisor_index_target_comparison.json').write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps(rec,indent=2))


if __name__=='__main__':main()
