#!/usr/bin/env python3
"""Regression checks for new-solve routing and maintenance verification scope."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


library = load("check_library", ROOT / "scripts/check-library.py")
classifier = load("classify", ROOT / "scripts/proposals/classify.py")


class MaintenanceChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.write("formal/lean/HodgeComputer/Verify.lean", "")
        self.write("formal/lean/HodgeComputer/Helper.lean", "import HodgeComputer.Verify\n")
        for instance in ("first", "second"):
            self.write(f"data/{instance}/acceptance.json", "{}")
            self.write(f"data/{instance}/Solution.lean", "import HodgeTarget\n")

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def plan(self, *changes):
        return library.verification_plan(self.root, changes)

    def test_shared_contract_rechecks_all_existing_solves(self):
        plan = self.plan("formal/lean/HodgeComputer/Verify.lean")
        self.assertEqual(plan["instances"], ["first", "second"])
        self.assertEqual(plan["modules"], ["HodgeComputer.Helper", "HodgeComputer.Verify"])

    def test_source_target_manifest_and_witness_edits_recheck_the_instance(self):
        for name in ("Solution.lean", "Helper.lean", "instance.rec", "proof.json", "witness.json"):
            with self.subTest(name=name):
                self.assertEqual(self.plan("data/first/" + name)["instances"], ["first"])

    def test_editorial_and_attribution_edits_do_not_require_lean(self):
        self.assertEqual(self.plan("data/first/solution.md", "data/first/acceptance.json"),
                         {"modules": [], "instances": []})

    def test_verifier_edit_rechecks_existing_solves(self):
        self.assertEqual(self.plan("scripts/proposals/Audit.lean")["instances"], ["first", "second"])

    def test_shared_build_includes_dependencies_of_affected_instances(self):
        self.write("data/first/Solution.lean", "import HodgeTarget\nimport HodgeComputer.Helper\n")
        self.assertEqual(library.required_modules(self.root, ["first"], []),
                         ["HodgeComputer.Helper", "HodgeComputer.Verify"])

    def test_each_affected_instance_has_its_own_job(self):
        instances = [f"instance-{i}" for i in range(66)]
        jobs = library.verification_jobs({"modules": ["HodgeComputer.Verify"], "instances": instances})
        self.assertEqual(len(jobs), 67)
        self.assertEqual([job["instance"] for job in jobs if job["phase"] == "applications"], instances)
        self.assertEqual(library.verification_jobs({"modules": [], "instances": []}), [])

    def test_import_only_umbrellas_do_not_replay_entire_subtrees(self):
        self.write("formal/lean/HodgeComputer/Verify.lean", "def example : Nat := 0\n")
        self.write("formal/lean/HodgeComputer.lean", "/- umbrella -/\nimport HodgeComputer.Verify\n")
        self.assertEqual(library.replay_modules(self.root,
            ["HodgeComputer", "HodgeComputer.Helper", "HodgeComputer.Verify"]),
            ["HodgeComputer.Verify"])

    def test_candidate_receipt_does_not_turn_a_new_solve_into_maintenance(self):
        def git(*args):
            return subprocess.check_output(["git", *args], cwd=self.root, stderr=subprocess.DEVNULL).decode().strip()
        git("init", "-q")
        git("config", "user.name", "CI fixture")
        git("config", "user.email", "ci@example.invalid")
        git("add", ".")
        git("commit", "-qm", "Base")
        base = git("rev-parse", "HEAD")
        self.write("data/first/Solution.lean", "import HodgeTarget\n-- maintained\n")
        git("add", ".")
        git("commit", "-qm", "Existing solve maintenance")
        previous = classifier.ROOT
        classifier.ROOT = self.root
        self.addCleanup(setattr, classifier, "ROOT", previous)
        self.assertEqual(classifier.classify(base, git("rev-parse", "HEAD")), "maintenance")
        self.write("data/new/acceptance.json", "{}")
        self.write("data/new/Solution.lean", "import HodgeTarget\n")
        git("add", ".")
        git("commit", "-qm", "New solve with a candidate receipt")
        self.assertEqual(classifier.classify(base, git("rev-parse", "HEAD")), "solve")


if __name__ == "__main__":
    unittest.main()
