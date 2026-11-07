#!/usr/bin/env python3
"""Generate an optional, separately applicable used-column insertion patch.

This never edits the vendor tree or the independent compaction patch/build.
"""
from pathlib import Path
from hashlib import sha256
import difflib
import json

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'vendor/msolve-0.11.0'

def modified_sources():
    helper=(HERE/'selective_columns.c').read_text()
    paths=['src/neogb/hash.c','src/neogb/convert.c','src/neogb/f4.c']
    original={name:(SOURCE/name).read_text() for name in paths}
    modified=dict(original)
    anchor='static inline void insert_in_basis_hash_table_pivots('
    assert original[paths[0]].count(anchor)==1
    modified[paths[0]]=original[paths[0]].replace(anchor,helper+'\n'+anchor,1)
    start=original[paths[1]].index('static void convert_sparse_matrix_rows_to_basis_elements(')
    end=original[paths[1]].index('static void convert_sparse_matrix_rows_to_basis_elements_use_sht(',start)
    body=original[paths[1]][start:end]
    body=body.replace('static void convert_sparse_matrix_rows_to_basis_elements(',
                      'static void hc_convert_sparse_matrix_rows_to_basis_elements(',1)
    assert body.count('        md_t *st\n')==1
    body=body.replace('        md_t *st\n','        md_t *st,\n        const int used_columns_only\n',1)
    call='    switch_hcm_data_to_basis_hash_table(hcm, bht, mat, sht);'
    assert body.count(call)==1
    body=body.replace(call,'''    if (used_columns_only) {
        hc_switch_used_columns_to_basis_hash_table(hcm, bht, mat, sht, st);
    } else {
        switch_hcm_data_to_basis_hash_table(hcm, bht, mat, sht);
    }''',1)
    wrapper='''static void convert_sparse_matrix_rows_to_basis_elements(
        const int sort,
        mat_t *mat,
        bs_t *bs,
        ht_t *bht,
        const ht_t * const sht,
        md_t *st
        )
{
    hc_convert_sparse_matrix_rows_to_basis_elements(
            sort, mat, bs, bht, sht, st, 0);
}

'''
    modified[paths[1]]=original[paths[1]][:start]+body+wrapper+original[paths[1]][end:]
    oldcall='''        convert_sparse_matrix_rows_to_basis_elements(
                -1, mat, bs, ht, sht, md);'''
    assert original[paths[2]].count(oldcall)==1
    newcall='''        hc_convert_sparse_matrix_rows_to_basis_elements(
                -1, mat, bs, ht, sht, md,
                md->fc > 0 && md->trace_level == NO_TRACER
                    && md->use_signatures == 0);'''
    modified[paths[2]]=original[paths[2]].replace(oldcall,newcall,1)
    return original,modified

def main():
    original,modified=modified_sources()
    patch=''.join(''.join(difflib.unified_diff(original[p].splitlines(True),modified[p].splitlines(True),
                     fromfile='a/'+p,tofile='b/'+p)) for p in original)
    path=HERE/'msolve_selective_columns.patch';path.write_text(patch)
    receipt={'status':'OPTIONAL_PATCH_GENERATED','patch_sha256':sha256(path.read_bytes()).hexdigest(),
        'helper_sha256':sha256((HERE/'selective_columns.c').read_bytes()).hexdigest(),
        'original_sources':{p:sha256(t.encode()).hexdigest() for p,t in original.items()},
        'modified_sources':{p:sha256(t.encode()).hexdigest() for p,t in modified.items()},
        'activation':'Only compute_new_elements in ordinary positive-characteristic, NO_TRACER, signature-free core_f4.',
        'other_callers':'The original converter wrapper still performs blanket insertion. Trace, saturation and final reduction callers are unchanged.',
        'source_tree_modified':False,'compaction_patch_modified':False,
        'correctness_gate':'Independent storage invariants and completed-basis differential checks are required before production use.'}
    (HERE/'finite_selective_patch_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
