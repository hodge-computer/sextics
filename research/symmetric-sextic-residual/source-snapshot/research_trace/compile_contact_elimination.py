#!/usr/bin/env python3
from pathlib import Path
import os
import subprocess

here = Path(__file__).resolve().parent
workspace = here.parent
repo = workspace / "sextics/formal/lean"
env = os.environ.copy()
env["PATH"] = str(workspace / "toolchains/lean-4.33.1-linux/bin") + os.pathsep + env["PATH"]
env["LD_PRELOAD"] = str(workspace / "runtime_compat/own_exe_path.so")
lake_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=repo, env=env, text=True).strip()
env["LEAN_PATH"] = os.pathsep.join([str(here), str(workspace / "proof_attempt4"), lake_path])
module = "ContactIncidenceElimination"
result = subprocess.run(["flock", str(workspace / "lean_compile.lock"), "lean", "-j1", "-M4096",
                         "-R", str(here), "-o", str(here / (module + ".olean")),
                         str(here / (module + ".lean"))], cwd=repo, env=env,
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(here / "contact_elimination_lean.log").write_text(result.stdout)
print(result.stdout)
raise SystemExit(result.returncode)
