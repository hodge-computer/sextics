#!/usr/bin/env python3
"""Check immutable-solve routing and parallel shared-library verification."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


library = load("check_library", ROOT / "scripts/check-library.py")
classifier = load("classify", ROOT / "scripts/proposals/classify.py")
checker = load("proposal_check", ROOT / "scripts/proposals/check.py")


class MaintenanceChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.write("formal/lean/HodgeComputer/Verify.lean", "")
        self.write("formal/lean/HodgeComputer/Helper.lean", "import HodgeComputer.Verify\n")
        for instance in ("first", "second"):
            self.write(f"data/{instance}/acceptance.json", json.dumps({
                "formalAcceptance": True, "instanceId": instance}))
            self.write(f"data/{instance}/Solution.lean", "import HodgeTarget\n")
            self.write(f"data/{instance}/proof.json", json.dumps({
                "schemaVersion": 2, "instanceId": instance, "theorem": "Submission.certificate"}))
            self.write(f"data/{instance}/solution.md", "# Original explanation\n")
            self.write(f"data/{instance}/witness.json", "{}")
            self.write(f"data/{instance}/instance.rec", f"id: {instance}\nq: 1\nF: X0**6\nA: X0**5*Y0\n")

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

    def test_only_shared_lean_changes_schedule_library_jobs(self):
        self.assertEqual(self.plan("data/first/Solution.lean", "data/first/witness.json",
                                   "data/first/solution.md", "data/first/acceptance.json",
                                   "scripts/proposals/Audit.lean"),
                         {"modules": [], "instances": []})

    def test_shared_helper_change_selects_only_its_applications(self):
        self.write("data/first/Solution.lean", "import HodgeTarget\nimport HodgeComputer.Helper\n")
        self.assertEqual(self.plan("formal/lean/HodgeComputer/Helper.lean"),
                         {"modules": ["HodgeComputer.Helper"], "instances": ["first"]})

    def test_toolchain_change_rechecks_all_existing_solves(self):
        self.assertEqual(self.plan("formal/lean/lean-toolchain")["instances"], ["first", "second"])

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

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root,
                                       stderr=subprocess.DEVNULL).decode().strip()

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-qm", "Fixture change")
        return self.git("rev-parse", "HEAD")

    def initialize_git(self):
        self.git("init", "-q")
        self.git("config", "user.name", "CI fixture")
        self.git("config", "user.email", "ci@example.invalid")
        return self.commit()

    def test_accepted_proof_manifest_and_witness_edits_are_rejected(self):
        base = self.initialize_git()
        with patch.object(classifier, "ROOT", self.root), patch.object(checker, "ROOT", self.root):
            for name in ("Solution.lean", "proof.json", "witness.json"):
                with self.subTest(name=name):
                    self.write("data/first/" + name, "changed\n")
                    head = self.commit()
                    self.assertEqual(classifier.classify(base, head), "solve")
                    with self.assertRaisesRegex(ValueError, "may only add new solution files"):
                        checker.read_proposal(base, head, "contributor", {})
                    base = head
            (self.root / "data/first/Solution.lean").unlink()
            head = self.commit()
            self.assertEqual(classifier.classify(base, head), "solve")
            with self.assertRaisesRegex(ValueError, "may only add new solution files"):
                checker.read_proposal(base, head, "contributor", {})

    def test_adding_a_helper_to_an_accepted_solve_is_rejected(self):
        base = self.initialize_git()
        self.write("data/first/Helper.lean", "import HodgeTarget\n")
        head = self.commit()
        with patch.object(classifier, "ROOT", self.root), patch.object(checker, "ROOT", self.root):
            self.assertEqual(classifier.classify(base, head), "solve")
            with self.assertRaisesRegex(ValueError, "already has a merged proof"):
                checker.read_proposal(base, head, "contributor", {})

    def test_accepted_explanation_edits_remain_maintenance(self):
        base = self.initialize_git()
        self.write("data/first/solution.md", "# Updated explanation\n")
        head = self.commit()
        with patch.object(classifier, "ROOT", self.root):
            self.assertEqual(classifier.classify(base, head), "maintenance")

    def test_candidate_receipt_cannot_authorize_an_editorial_exemption(self):
        self.write("data/new/solution.md", "# Unaccepted explanation\n")
        base = self.initialize_git()
        self.write("data/new/acceptance.json", json.dumps({
            "formalAcceptance": True, "instanceId": "new"}))
        self.write("data/new/solution.md", "# Changed explanation\n")
        head = self.commit()
        with patch.object(classifier, "ROOT", self.root):
            self.assertEqual(classifier.classify(base, head), "solve")

    def test_new_solve_still_passes_structure_checks(self):
        self.write("data/new/instance.rec", "id: new\nq: 1\nF: X0**6\nA: X0**5*Y0\n")
        base = self.initialize_git()
        self.write("data/new/proof.json", json.dumps({
            "schemaVersion": 2, "instanceId": "new", "theorem": "Submission.certificate"}))
        self.write("data/new/solution.md", "# New solution\n")
        self.write("data/new/Solution.lean", "import HodgeTarget\n")
        head = self.commit()
        with patch.object(classifier, "ROOT", self.root), patch.object(checker, "ROOT", self.root):
            self.assertEqual(classifier.classify(base, head), "solve")
            rid, _, _, _ = checker.read_proposal(base, head, "contributor",
                                                {"maxFiles": 64, "maxBytes": 16 * 1024 * 1024})
            self.assertEqual(rid, "new")


if __name__ == "__main__":
    unittest.main()
