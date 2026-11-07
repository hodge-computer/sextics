# Correction: the ordinary F4 path does not execute the reset option

The pinned msolve 0.11.0 source accepts and prints the `-u1` setting, but ordinary finite-field `core_f4` does not consult `reset_ht` and does not call `reset_hash_table`. The complete source has only one call to that function: inside `f4sat_trace_application_test_phase` in `modular.c`. Inspection of `core_f4` in the downloaded static binary agrees with the source. The three source snapshots used in the earlier memory analysis match the complete official source byte for byte.

Consequently, descriptions of the earlier ordinary runs as operating with hash regeneration enabled need this correction. They used the configured option, but that option did not trigger basis-hash compaction in those runs. All recorded timings, measured peak RSS, memory limits, matrix logs, and failure diagnostics remain unchanged. The analysis of the reset function's nominal allocations also remains correct; it describes a function that was not on this execution path. A comparison of `-u0` and `-u1` alone is therefore not a meaningful compaction experiment for these ordinary runs.

The adjacent JSON receipt contains source hashes, official source URLs, the two definition/call locations, and the pinned binary and disassembly hashes. This is a source-path audit, not a finite-algebra or trace certificate.
