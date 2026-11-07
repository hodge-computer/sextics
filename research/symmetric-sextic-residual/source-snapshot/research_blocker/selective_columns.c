/* Optional used-column insertion for ordinary msolve 0.11.0 F4 rounds.
 * Added by OpenAI ChatGPT, 2026-11-07.
 * GPL-2.0-or-later, as part of the modified msolve source.
 * The original converter remains available for tracing, saturation, final
 * reduction, and every caller outside ordinary compute_new_elements.
 */
uint64_t hc_used_column_calls = 0;
uint64_t hc_used_column_candidates = 0;
uint64_t hc_used_column_selected = 0;

static inline void hc_switch_used_columns_to_basis_hash_table(
    hi_t *hcm,
    ht_t *bht,
    const mat_t *mat,
    const ht_t * const sht,
    const md_t *md
    )
{
    const len_t start = mat->ncl, end = mat->nc;
    if (end < start || mat->ncr != end - start || bht == sht) abort();
    const len_t candidates = end - start;
    uint8_t *used = calloc((size_t)candidates, sizeof(uint8_t));
    if (!used && candidates) abort();
    len_t count = 0;

    /* Mark before mutating hcm or the surviving sparse rows. */
    for (len_t k = 0; k < mat->np; ++k) {
        const hm_t *row = mat->tr[k];
        if (!row) abort();
        for (len_t j = OFFSET; j < OFFSET + row[LENGTH]; ++j) {
            const hi_t col = row[j];
            if (col < start || col >= end) abort();
            if (!used[col - start]) {
                used[col - start] = 1;
                ++count;
            }
        }
    }
    while (bht->esz - bht->eld < count) enlarge_hash_table(bht);

    /* The original code inserts this whole interval.  Here only entries
     * subsequently read by a surviving row receive primary hash indices. */
    for (len_t i = start; i < end; ++i) {
        if (!used[i - start]) continue;
        const hi_t old = hcm[i];
        if (old == 0 || old >= sht->eld) abort();
#if PARALLEL_HASHING
        hcm[i] = check_insert_in_hash_table(sht->ev[old], sht->hd[old].val, bht);
#else
        hcm[i] = insert_in_hash_table(sht->ev[old], bht);
#endif
    }
    free(used);
    ++hc_used_column_calls;
    hc_used_column_candidates += candidates;
    hc_used_column_selected += count;
    if (md->info_level > 1) {
        fprintf(VERBSTREAM, "[columns] selected %u of %u; primary live %lu\n",
                count, candidates, (unsigned long)bht->eld);
        fflush(VERBSTREAM);
    }
}
