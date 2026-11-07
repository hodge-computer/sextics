#!/usr/bin/env python3
"""Append this trace-computation continuation to the retained complete package.

Run after the solver status record is final. This packages evidence; it does
not evaluate a trace or certify the target theorem.
"""
from pathlib import Path
import hashlib
import json
import shutil
import zipfile

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parent
PACKAGE = WORKSPACE / "symmetric_sextic_contact_repair_20261106"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert PACKAGE.is_dir()
    assert (HERE / "finite_computation_status.json").is_file(), "Wait for the final solver record"
    prior_readme = PACKAGE / "PREVIOUS_CONTACT.txt"
    if not prior_readme.exists():
        shutil.copy2(PACKAGE / "README.txt", prior_readme)
    shutil.copy2(HERE / "TRACE_RESULTS.txt", PACKAGE / "README.txt")

    research = PACKAGE / "research_trace"
    research.mkdir(exist_ok=True)
    suffixes = {".py", ".json", ".txt", ".log", ".ms"}
    for source in sorted(HERE.iterdir()):
        if source.is_file() and source.suffix in suffixes:
            shutil.copy2(source, research / source.name)
    for name in ["ContactIncidenceElimination.lean", "ContactIncidenceElimination.olean",
                 "contact_elimination_lean_receipt.json"]:
        shutil.copy2(HERE / name, PACKAGE / name)

    audit = json.loads((PACKAGE / "contact_elimination_lean_receipt.json").read_text())
    assert audit["status"] == "PASS"
    assert sha(PACKAGE / "ContactIncidenceElimination.lean") == audit["source_sha256"]
    assert sha(PACKAGE / "ContactIncidenceElimination.olean") == audit["object_sha256"]
    assert sha(research / "contact_alpha_elimination.json") == audit["companion_circuit_sha256"]
    assert sha(research / "contact_alpha_elimination_receipt.json") == audit["companion_binding_receipt_sha256"]
    assert len(list(PACKAGE.glob("*.lean"))) == 51
    assert sha(PACKAGE / "HodgeTarget.lean") == "a51532e0442d72e8ce95d6728390fac0f719287d1cf20020701625bc1b5409d9"

    record = {
        "scope": "Exact reductions and recorded attempts; no individual full trace evaluated",
        "requested_coefficient_traces": 9,
        "individual_full_trace_values_evaluated": 0,
        "exact_relation_between_requested_traces": "C2*T14-C1*T23=0",
        "remaining_top_moment": "m=<alpha U>; its value is unknown",
        "quotient_degree_known": False,
        "complete_quotient_basis_available": False,
        "source_match_proved": False,
        "full_certificate_proved": False,
        "retained_lean_modules": 51,
        "new_lean_module": "ContactIncidenceElimination",
        "new_lean_audit": "contact_elimination_lean_receipt.json",
        "prior_50_modules": "Retained unchanged; previous package manifest was verified before this update",
        "prior_axiom_reports": 784,
        "new_endpoint_axiom_reports": len(audit["endpoint_axioms"]),
        "solver_status_record": "research_trace/finite_computation_status.json",
        "normalization_warning": "eta_R is not proved to contain the required inverse of Gamma_* Gamma^* or the exact source correction",
    }
    (PACKAGE / "trace_computation_receipt.json").write_text(json.dumps(record, indent=2) + "\n")

    manifest = {str(p.relative_to(PACKAGE)): sha(p)
                for p in sorted(PACKAGE.rglob("*"))
                if p.is_file() and p.name != "PACKAGE_SHA256.json"}
    (PACKAGE / "PACKAGE_SHA256.json").write_text(json.dumps(manifest, indent=2) + "\n")
    archive = PACKAGE.with_suffix(".zip")
    with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in sorted(PACKAGE.rglob("*")):
            if p.is_file():
                z.write(p, str(p.relative_to(PACKAGE.parent)))
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None
        archived_count = len(z.namelist())
    result = {"archive": str(archive), "files": archived_count,
              "bytes": archive.stat().st_size, "sha256": sha(archive),
              "individual_full_trace_values_evaluated": 0, "full_certificate_proved": False}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
