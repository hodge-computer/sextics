#!/usr/bin/env python3
"""Collect already measured incomplete routes; no inference of dimension."""
from pathlib import Path
import argparse,json,subprocess

HERE=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--primary-tag',required=True)
    args=ap.parse_args()
    routes=[]
    for label,tag in [('small_open_core',args.primary_tag),('jacobian_witness','sparse32_jacobian_retry')]:
        receipt=json.loads((HERE/(tag+'_receipt.json')).read_text())
        assert receipt['status']=='PARTIAL_BASIS_CHECKPOINT'
        packed=receipt['outputs']['checkpoint'];state=receipt['outputs']['native_state']
        progress=json.loads(subprocess.check_output([str(HERE/'vendor/inspect_f4_state'),str(HERE/state['file'])]))
        routes.append({'route':label,'tag':tag,'receipt':tag+'_receipt.json',
                       'checkpoint':packed,'native_state':state,'progress':progress,
                       'peak_rss_kib':receipt['peak_rss_kib'],
                       'address_space_limit_mib':receipt['address_space_limit_mib'],
                       'execution_seconds':receipt['seconds']})
    record={'schema':'blocker-current-outcome-v1','status':'BLOCKER_NOT_COMPLETED',
            'exact_target':'HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A',
            'specialization':{'prime':37,'lambda':1,'r':2,'s':3},
            'routes':routes,'full_source_traces_evaluated':0,'new_Lean_theorems':0,
            'finite_quotient_completed_and_independently_verified':False,
            'source_coefficient_identity_proved':False,'full_certificate_proved':False,
            'no_completion_fraction_or_time_estimate':'Pending pairs can grow; term and row counts do not measure percent completion.',
            'next_mathematical_gates':[
                'Complete and verify a suitable finite algebra with every required open condition.',
                'Evaluate actual traces and establish the characteristic-zero source identity, adjusting the contact form if comparisons fail.',
                'Perform legal denominator clearing and the verifier bridge, then prove the protected Lean statement.']}
    (HERE/'latest_computation_status.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))


if __name__=='__main__':main()
