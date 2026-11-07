#!/usr/bin/env python3
"""Replay, audit axioms, and run leanchecker for the alpha-elimination module."""
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parent
REPO = WORKSPACE / "sextics/formal/lean"
MODULE = "ContactIncidenceElimination"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    env = os.environ.copy()
    bindir = WORKSPACE / "toolchains/lean-4.33.1-linux/bin"
    env["PATH"] = str(bindir) + os.pathsep + env["PATH"]
    env["LD_PRELOAD"] = str(WORKSPACE / "runtime_compat/own_exe_path.so")
    lake = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=REPO, env=env, text=True).strip()
    env["LEAN_PATH"] = os.pathsep.join([str(HERE), lake])
    source = HERE / (MODULE + ".lean")
    obj = HERE / (MODULE + ".olean")
    source_text = source.read_text()
    assert not re.search(r"\b(sorry|admit|native_decide|unsafe)\b", source_text)
    assert not re.search(r"^\s*axiom\s", source_text, re.M)
    started = time.monotonic()
    compiler = subprocess.run(["flock", str(WORKSPACE / "lean_compile.lock"), "lean", "-j1", "-M4096",
                               "-R", str(HERE), "-o", str(obj), str(source)], cwd=REPO, env=env,
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    compile_log = HERE / "contact_elimination_lean.log"
    compile_log.write_text(compiler.stdout)
    assert compiler.returncode == 0, compiler.stdout
    axioms = {name: [x.strip() for x in a.split(",") if x.strip()]
              for name, a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", compiler.stdout, re.S)}
    assert set(axioms) == {MODULE + "." + n for n in (
        "eliminated_jacobian_factor", "alpha_elimination", "residual_aN_zero")}
    assert all(set(a) <= {"propext", "Classical.choice", "Quot.sound"} for a in axioms.values())
    print("Fresh compilation and endpoint axiom audit passed.", flush=True)
    checker = subprocess.run(["flock", str(WORKSPACE / "lean_compile.lock"), "leanchecker", "-v", MODULE],
                             cwd=REPO, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    checker_log = HERE / "contact_elimination_leanchecker.log"
    checker_log.write_text(checker.stdout)
    assert checker.returncode == 0, checker.stdout
    assert "replaying " + MODULE in checker.stdout
    receipt = {
        "status": "PASS", "module": MODULE,
        "toolchain": subprocess.check_output(["lean", "--version"], cwd=REPO, env=env, text=True).strip(),
        "source_sha256": digest(source), "object_sha256": digest(obj),
        "compiler_binary_sha256": digest(bindir / "lean"),
        "checker_binary_sha256": digest(bindir / "leanchecker"),
        "compiler_exit_code": compiler.returncode, "compiler_log_sha256": digest(compile_log),
        "checker_exit_code": checker.returncode, "checker_log_sha256": digest(checker_log),
        "endpoint_axioms": axioms,
        "no_sorry_or_new_axioms": True,
        "compile_memory_limit_mib": 4096,
        "serialized_with": "lean_compile.lock",
        "checker_scope": "leanchecker replayed every declaration in this object against its imported environment. It is the same Lean kernel, not an external verifier, and imported dependencies were not replayed with --fresh.",
        "companion_binding_receipt_sha256": digest(HERE / "contact_alpha_elimination_receipt.json"),
        "companion_circuit_sha256": digest(HERE / "contact_alpha_elimination.json"),
        "scope": "Universal exact alpha-elimination equivalence, Jacobian chain-rule factor, and honest residual-stratum implication. Actual protected-chart coefficient binding and A/B-free ideal witness are separately exact Python checks. No trace value or final HasCertificate is asserted.",
        "source_trace_proved": False,
        "full_certificate_proved": False,
        "seconds": time.monotonic() - started,
    }
    (HERE / "contact_elimination_lean_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2), flush=True)


if __name__ == "__main__":
    main()
