#!/usr/bin/env python3
"""Summarize actual quotient-computation receipts without inferring traces."""
from pathlib import Path
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
TAGS=['p37_delta','p5_delta','p37_reduced_f4sat','p65537_reduced_f4sat',
      'p37_reduced_regular','p37_reduced_hashreset']

def main():
    jobs=[]
    for tag in TAGS:
        path=HERE/f'finite_msolve_{tag}_receipt.json'
        if not path.exists():
            jobs.append({'tag':tag,'status':'NO_FINISHED_RECEIPT'});continue
        r=json.loads(path.read_text())
        logpath=HERE/f'finite_msolve_{tag}.log'
        log=logpath.read_text() if logpath.exists() else ''
        matrices=[]
        for m in re.finditer(r'^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+x\s+(\d+)\s+',log,re.M):
            degree,selected,pending,rows,columns=map(int,m.groups())
            matrices.append({'selected_degree':degree,'selected_pairs':selected,
                             'pending_pairs':pending,'rows':rows,'columns':columns})
        r.pop('saturation_polynomial',None)
        if matrices:
            r['largest_observed_matrix']=max(matrices,key=lambda q:q['rows']*q['columns'])
            r['matrix_with_most_rows']=max(matrices,key=lambda q:q['rows'])
            r['matrix_with_most_columns']=max(matrices,key=lambda q:q['columns'])
            r['last_observed_matrix']=matrices[-1]
        if 'command' not in r:
            r['command_reconstructed_from_receipt']=['msolve','-v','2','-g','2','-t',str(r.get('threads',1)),
              '-m',str(r.get('max_pairs_per_matrix',5000)),'-f',f'finite_msolve_{tag}.ms','-o',f'finite_msolve_{tag}.out']
        r['diagnostic_lines']=[line for line in log.splitlines()
                               if any(w in line for w in ['failed','Error:','segmentation fault'])]
        r['log_sha256']=hashlib.sha256(log.encode()).hexdigest()
        r['receipt_file']=path.name
        jobs.append(r)
    completed=[r['tag'] for r in jobs if r.get('exit_code')==0 and r.get('output_bytes',0)>0]
    if completed:raise RuntimeError('A solver output now exists; inspect it before issuing a negative status summary: '+repr(completed))
    finished=all(r.get('status')!='NO_FINISHED_RECEIPT' for r in jobs)
    generic_path=HERE/'contact_generic_g2_audit.json'
    generic=json.loads(generic_path.read_text()) if generic_path.exists() else None
    rhs=json.loads((HERE/'finite_target_rhs.json').read_text())
    result={
      'status':'TRACE_COMPUTATION_NOT_COMPLETED' if finished else 'COMPUTATION_IN_PROGRESS',
      'target':'symmetric-sextic-residual',
      'engines':{'msolve':'0.11.0','FLINT':'3.6.0','python_flint':'0.9.0'},
      'basis_computed':False,'quotient_dimension':None,'multiplication_matrices_computed':False,
      'trace_values':[None]*9,'trace_identities_proved':0,'full_certificate_proved':False,
      'base_specialization':{'lambda':1,'r':2,'s':3},
      'exact_preprocessing':{
        'g2_linear_elimination':{'removed_variables':19,'contact_variables_remaining':26,
          'contact_equations_remaining':25,'common_denominator':'(1-z)*(1-2*z)*(1-3*z), z=mu0*mu1',
          'all_target_pivots_checked_modulo':[5,37,65537],
          'independent_characteristic_zero_audit':generic},
        'alpha_elimination':{'formula':'alpha=-aN/bN','open':'bN != 0',
          'omitted_bN_zero_locus_accounted_for':False,
          'point_equation':'P=q2*aN^2+q0*bN^2; replaced by the A/B-free G3 modulo the contact equations',
          'eliminated_jacobian_factor':'Je=q2*bN*J'}},
      'required_targets_at_specialization':rhs['coefficient_targets'],
      'solver_runs':jobs,
      'native_flint_experiments':{
        'raw_mod37_200_generator_limit':'Incomplete generating set; not a Groebner basis.',
        'raw_mod37_5000_generator_limit':'External 180-second timeout; no completed basis.',
        'alpha_eliminated_lex_mod37':'Bounded Buchberger stopped without completing a basis.',
        'q2_zero_branch_mod37':'Reached 2000 generators at degree5 without completing a basis or proving the unit ideal.'},
      'limits':[
        'No dimension or degree of the target quotient has been established.',
        'Partial F4 matrices and incomplete generating sets are not multiplication matrices or traces.',
        'The reduced bN-open experiment omits a residual stratum whose generic absence has not been proved.',
        'The experiments localize the stated cheap chart factors, not the complete determinant product S of the target finite algebra.',
        'Specialized modular computations alone would not prove the characteristic-zero rational-function identities without specialization and reconstruction justification.',
        'Characteristic5 kills the target couplings and is a special Fermat fibre.',
        'Solver failure does not prove a trace identity false or a certificate nonexistent.']}
    (HERE/'finite_computation_status.json').write_text(json.dumps(result,indent=2)+'\n')
    lines=['FINITE TRACE COMPUTATION STATUS',result['status'],'',
       'No target quotient basis, quotient dimension, multiplication matrix, or trace value has been obtained.',
       'All nine requested source trace identities remain unproved. No trace value is asserted to be zero.','',
       'Exact preprocessing:',
       '- Removed all 19 g2 coefficients by checked linear elimination on D != 0; the independent generic characteristic-zero audit passed.',
       '- Eliminated alpha on bN != 0 and used the A/B-free point polynomial. The residual bN=0 stratum remains unresolved.','',
       'Actual solver outcomes:']
    for r in jobs:
        text=f"- {r['tag']}: {r.get('status')}, exit={r.get('exit_code')}, seconds={r.get('seconds')}."
        if r.get('largest_observed_matrix'):
            m=r['largest_observed_matrix'];text+=f" Largest observed sparse F4 matrix: {m['rows']} x {m['columns']} at selected degree {m['selected_degree']}."
        lines.append(text)
        for diagnostic in r.get('diagnostic_lines',[]):lines.append('  Diagnostic: '+diagnostic)
    lines += ['', 'The required normalized coefficient vector at (lambda,r,s)=(1,2,3), modulo37, is',
              '[0,18,31,6,0; 0,1,6,0]. These are TARGETS, not computed source traces.',
              'The unnormalized test would be Trace(M_i) - dim(A)*target_i = 0; dim(A) is unknown.','',
              'The JSON status preserves exact input hashes, solver arguments, limits, receipts and diagnostic references.',
              'The source scripts and .ms inputs are portable; the vendor binary and downloaded headers need not be bundled.',
              'Use Python3 with python-flint0.9.0 / FLINT3.6.0 and pass an msolve0.11.0 executable with --binary.', '',
              'Scope: bounded research computations. No Lean HasCertificate proof and no claim of mathematical impossibility.']
    (HERE/'finite_computation_status.txt').write_text('\n'.join(lines)+'\n')
    print(json.dumps({'status':result['status'],'runs':len(jobs),'trace_identities_proved':0,'quotient_dimension':None}))

if __name__=='__main__':main()
