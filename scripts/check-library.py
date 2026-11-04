#!/usr/bin/env python3
"""Build/replay changed shared Lean modules and recheck their accepted applications."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import yaml

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/proposals"))
from check import module_order, strip_comments
from sandbox import verify


def verification_plan(root, changed):
    """Select shared dependents and maintained solves affected by a tree diff."""
    lean = root / "formal/lean"
    sources = {
        p.relative_to(lean).with_suffix("").as_posix().replace("/", "."): p
        for p in lean.rglob("*.lean")
        if ".lake" not in p.relative_to(lean).parts
    }
    imports = {
        name: set(re.findall(r"^import\s+([^\n]+)", strip_comments(p.read_text()), re.M))
        for name, p in sources.items()
    }
    imports = {
        name: {item for line in lines for item in line.split()} for name, lines in imports.items()
    }
    affected = {
        Path(p).relative_to("formal/lean").with_suffix("").as_posix().replace("/", ".")
        for p in changed
        if p.startswith("formal/lean/") and p.endswith(".lean")
    }
    verifier_changed = any(
        p.startswith("scripts/proposals/") or
        p in ("scripts/check-library.py", ".github/solve-policy.json")
        for p in changed
    )
    if verifier_changed or any(
        p.startswith("formal/lean/") and not p.endswith(".lean") for p in changed
    ):
        affected.update(sources)
    while True:
        expanded = affected | {name for name, deps in imports.items() if deps & affected}
        if expanded == affected:
            break
        affected = expanded
    modules = sorted(affected & sources.keys())
    applications = []
    for receipt in sorted((root / "data").glob("*/acceptance.json")):
        folder = receipt.parent
        files = {p.name: p.read_bytes() for p in folder.glob("*.lean")}
        _, used = module_order(files)
        prefix = f"data/{folder.name}/"
        direct = any(
            p.startswith(prefix) and
            (p.endswith(".lean") or Path(p).name in ("instance.rec", "proof.json", "witness.json"))
            for p in changed
        )
        if direct or verifier_changed or (set(used) | {"HodgeComputer.Verify"}) & affected:
            applications.append(folder.name)
    return {"modules": modules, "instances": applications}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True)
    parser.add_argument("--plan", action="store_true")
    parser.add_argument("--phase", choices=("all", "shared", "applications"), default="all")
    parser.add_argument("--shard", default="1/1", help="Application shard, numbered from 1")
    args = parser.parse_args()
    changed = subprocess.check_output(
        ["git", "diff", "--name-only", args.base, "HEAD"], cwd=ROOT, text=True
    ).splitlines()
    plan = verification_plan(ROOT, changed)
    if args.plan:
        jobs = []
        if plan["modules"]:
            jobs.append({"phase": "shared", "shard": "1/1"})
        count = min(8, len(plan["instances"]))
        jobs.extend({"phase": "applications", "shard": f"{i+1}/{count}"} for i in range(count))
        print(json.dumps({**plan, "matrix": {"include": jobs}}))
        return
    shard, shards = map(int, args.shard.split("/"))
    if not 1 <= shard <= shards:
        parser.error("Expected --shard INDEX/COUNT with 1 <= INDEX <= COUNT")
    lean = ROOT / "formal/lean"
    modules = plan["modules"] if args.phase != "applications" else []
    if modules:
        subprocess.run(["lake", "build", *modules], cwd=lean, check=True)
        for module in modules:
            subprocess.run(["lake", "env", "leanchecker", "--verbose", module], cwd=lean, check=True)
    selected = plan["instances"][shard-1::shards] if args.phase != "shared" else []
    policy = json.loads((ROOT / ".github/solve-policy.json").read_text())
    applications = 0
    for instance_id in selected:
        folder = ROOT / "data" / instance_id
        files = {p.name: p.read_bytes() for p in folder.glob("*.lean")}
        if (folder / "witness.json").exists():
            files["witness.json"] = (folder / "witness.json").read_bytes()
        order, used = module_order(files)
        with tempfile.TemporaryDirectory(prefix="hodge-library-") as temporary:
            verify(
                ROOT,
                files,
                yaml.safe_load((folder / "instance.rec").read_text()),
                json.loads((folder / "proof.json").read_text()),
                order,
                used,
                policy,
                Path(temporary),
            )
        applications += 1
        print(f"Checked protected application: {folder.name}", flush=True)
    print(
        f"Replayed {len(modules)} shared modules and checked {applications} accepted applications."
    )


if __name__ == "__main__":
    main()
