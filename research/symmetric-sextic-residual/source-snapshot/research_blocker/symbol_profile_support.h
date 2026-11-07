/* Profile-only instrumentation for the frozen, serial symbolic-preprocessing
 * loop in the OpenMP msolve build. GPL-2.0-or-later.
 * These process-local counters do not enter md_t or any checkpoint format.
 */
#ifndef SYMBOL_PROFILE_SUPPORT_H
#define SYMBOL_PROFILE_SUPPORT_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static uint64_t symbol_profile_lookup_calls;
static uint64_t symbol_profile_lookup_hits;
static uint64_t symbol_profile_lookup_misses;
static uint64_t symbol_profile_leading_positions;
static uint64_t symbol_profile_full_tests;
static uint64_t symbol_profile_lookup_ns;
static uint64_t symbol_profile_materialization_ns;
static uint64_t symbol_profile_rows;
static uint64_t symbol_profile_terms;

static inline uint64_t symbol_profile_now(void)
{
    struct timespec value;
    if (clock_gettime(CLOCK_MONOTONIC, &value)) {
        perror("symbol_profile clock_gettime");
        abort();
    }
    return (uint64_t)value.tv_sec * UINT64_C(1000000000)
        + (uint64_t)value.tv_nsec;
}

static void symbol_profile_emit(const char *phase)
{
    fprintf(stderr,
        "[symbol_profile] phase=%s lookup_calls=%llu lookup_hits=%llu "
        "lookup_misses=%llu leading_positions=%llu full_divisibility_tests=%llu "
        "materialized_rows=%llu materialized_terms=%llu lookup_ns=%llu "
        "materialization_ns=%llu lookup_seconds=%.9f materialization_seconds=%.9f\n",
        phase,
        (unsigned long long)symbol_profile_lookup_calls,
        (unsigned long long)symbol_profile_lookup_hits,
        (unsigned long long)symbol_profile_lookup_misses,
        (unsigned long long)symbol_profile_leading_positions,
        (unsigned long long)symbol_profile_full_tests,
        (unsigned long long)symbol_profile_rows,
        (unsigned long long)symbol_profile_terms,
        (unsigned long long)symbol_profile_lookup_ns,
        (unsigned long long)symbol_profile_materialization_ns,
        (double)symbol_profile_lookup_ns / 1e9,
        (double)symbol_profile_materialization_ns / 1e9);
    fflush(stderr);
}
#endif
