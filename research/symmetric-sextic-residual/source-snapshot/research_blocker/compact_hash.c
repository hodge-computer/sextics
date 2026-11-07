/* In-place ordinary-F4 hash compaction for msolve 0.11.0.
 * Added by OpenAI ChatGPT, 2026-11-07, for this computation.
 * Distributed under GPL-2.0-or-later, as part of the modified msolve source.
 * This routine is used only when trace_level == NO_TRACER.
 * Retain every non-null basis row and every pending pair lcm.
 * Polynomial coefficients and monomial exponent vectors are unchanged.
 */
uint64_t hc_compact_calls = 0;
uint64_t hc_compact_removed = 0;
uint64_t hc_compact_shrinks = 0;
static void hc_compact_basis_hash_table(bs_t *bs, md_t *md)
{
    ht_t *ht = bs->ht;
    ps_t *ps = md->ps;
    const hl_t old_eld = ht->eld, old_esz = ht->esz;
    const len_t evl = ht->evl;
    const double started = realtime();
    hl_t k, kept = 1;
    len_t i, j;

#ifdef HC_COMPACT_AUDIT
    /* Test builds retain every referenced vector for exact post-checking. */
    size_t audit_refs = ps->ld;
    for (i = 0; i < bs->ld; ++i)
        if (bs->hm[i]) audit_refs += bs->hm[i][LENGTH];
    exp_t *audit = malloc(audit_refs * evl * sizeof(exp_t));
    if (!audit && audit_refs) abort();
    size_t ai = 0;
    for (i = 0; i < bs->ld; ++i) {
        hm_t *row = bs->hm[i];
        if (!row) continue;
        for (j = OFFSET; j < OFFSET + row[LENGTH]; ++j) {
            memcpy(audit + ai * evl, ht->ev[row[j]], evl * sizeof(exp_t));
            ++ai;
        }
    }
    for (i = 0; i < ps->ld; ++i) {
        memcpy(audit + ai * evl, ht->ev[ps->p[i].lcm], evl * sizeof(exp_t));
        ++ai;
    }
    if (ai != audit_refs) abort();
#endif

    /* idx is scratch metadata; no matrix is live at this call boundary. */
    for (k = 1; k < old_eld; ++k) ht->hd[k].idx = 0;
    for (i = 0; i < bs->ld; ++i) {
        hm_t *row = bs->hm[i];
        if (row == NULL) continue;
        for (j = OFFSET; j < OFFSET + row[LENGTH]; ++j) {
            if (row[j] == 0 || row[j] >= old_eld) abort();
            ht->hd[row[j]].idx = 1;
        }
    }
    for (i = 0; i < ps->ld; ++i) {
        if (ps->p[i].lcm == 0 || ps->p[i].lcm >= old_eld) abort();
        ht->hd[ps->p[i].lcm].idx = 1;
    }
    /* Increasing old indices produce new indices <= their old indices. */
    for (k = 1; k < old_eld; ++k)
        if (ht->hd[k].idx) ht->hd[k].idx = (ind_t)kept++;

    /* Rewrite all live references before compacting the metadata itself. */
    for (i = 0; i < bs->ld; ++i) {
        hm_t *row = bs->hm[i];
        if (row == NULL) continue;
        for (j = OFFSET; j < OFFSET + row[LENGTH]; ++j)
            row[j] = ht->hd[row[j]].idx;
    }
    for (i = 0; i < ps->ld; ++i)
        ps->p[i].lcm = ht->hd[ps->p[i].lcm].idx;

    /* Monotonic compaction cannot overwrite a future source vector. */
    exp_t *base = ht->ev[0];
    for (k = 1; k < old_eld; ++k) {
        const ind_t dest = ht->hd[k].idx;
        if (!dest) continue;
        if (dest > k) abort();
        memmove(base + (hl_t)dest * evl, base + k * evl,
                (size_t)evl * sizeof(exp_t));
        const exp_t *e = base + (hl_t)dest * evl;
        hd_t d = {0};
        for (j = 0; j < evl; ++j) d.val += ht->rn[j] * e[j];
        d.sdm = generate_short_divmask(e, ht);
        d.deg = e[0] + (ht->ebl ? e[ht->ebl] : 0);
        ht->hd[dest] = d;
    }
    ht->eld = kept;

    hl_t target = 1024;
    while (target < 2 * kept) target *= 2;
    if (target <= old_esz / 2) {
        exp_t *new_base = realloc(base, (size_t)target * evl * sizeof(exp_t));
        if (new_base == NULL) abort();
        base = new_base;
        exp_t **new_ev = realloc(ht->ev, (size_t)target * sizeof(exp_t *));
        if (new_ev == NULL) abort();
        ht->ev = new_ev;
        hd_t *new_hd = realloc(ht->hd, (size_t)target * sizeof(hd_t));
        if (new_hd == NULL) abort();
        ht->hd = new_hd;
        hi_t *new_map = realloc(ht->hmap, (size_t)(2 * target) * sizeof(hi_t));
        if (new_map == NULL) abort();
        ht->hmap = new_map;
        ht->esz = target;
        ht->hsz = 2 * target;
        ++hc_compact_shrinks;
    }
    for (k = 0; k < ht->esz; ++k) ht->ev[k] = base + k * evl;
    memset(ht->hmap, 0, (size_t)ht->hsz * sizeof(hi_t));
    const hi_t mask = (hi_t)(ht->hsz - 1);
    for (k = 1; k < kept; ++k) {
        hi_t pos = ht->hd[k].val;
        hl_t probe;
        for (probe = 0; probe < ht->hsz; ++probe) {
            pos = (pos + (hi_t)probe) & mask;
            if (!ht->hmap[pos]) break;
        }
        if (probe == ht->hsz) abort();
        ht->hmap[pos] = (hi_t)k;
    }
    ++md->num_rht;
    ++hc_compact_calls;
    hc_compact_removed += old_eld - kept;
    md->rht_rtime += realtime() - started;
#ifdef HC_COMPACT_AUDIT
    ai = 0;
    for (i = 0; i < bs->ld; ++i) {
        hm_t *row = bs->hm[i];
        if (!row) continue;
        for (j = OFFSET; j < OFFSET + row[LENGTH]; ++j) {
            if (memcmp(audit + ai * evl, ht->ev[row[j]], evl * sizeof(exp_t))) abort();
            ++ai;
        }
    }
    for (i = 0; i < ps->ld; ++i) {
        if (memcmp(audit + ai * evl, ht->ev[ps->p[i].lcm], evl * sizeof(exp_t))) abort();
        ++ai;
    }
    if (ai != audit_refs) abort();
    free(audit);
#endif
    if (md->info_level > 1) {
        fprintf(VERBSTREAM, "[compact] live %lu -> %lu; capacity %lu -> %lu; secondary capacity %lu\n",
                (unsigned long)old_eld, (unsigned long)kept,
                (unsigned long)old_esz, (unsigned long)ht->esz,
                (unsigned long)md->ht->esz);
        fflush(VERBSTREAM);
    }
}
