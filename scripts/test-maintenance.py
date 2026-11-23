#!/usr/bin/env python3
"""Regression checks for new-solve routing and maintenance verification scope."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/proposals"))


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

    def test_documentation_inside_the_library_requires_no_lean(self):
        self.assertEqual(self.plan("formal/lean/HodgeComputer/README.md"),
                         {"modules": [], "instances": []})

    def test_other_files_inside_the_library_recheck_everything(self):
        plan = self.plan("formal/lean/lakefile.toml")
        self.assertEqual(plan["instances"], ["first", "second"])
        self.assertEqual(plan["modules"], ["HodgeComputer.Helper", "HodgeComputer.Verify"])

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


class CombinedSolveProposalChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.policy = {"schemaVersion": 1, "mode": "live", "maxFiles": 996, "timeoutSeconds": 60, "memoryMb": 4096}
        self.write("formal/lean/HodgeComputer/Verify.lean", "def verifyMarker : Nat := 0\n")
        self.write("formal/lean/HodgeComputer/Constructions/Base.lean", "import HodgeComputer.Verify\ndef baseMarker : Nat := 1\n")
        self.write("formal/lean/HodgeComputer/Constructions/Dependent.lean", "import HodgeComputer.Constructions.Base\ndef depMarker : Nat := 2\n")
        self.write("formal/TECHNIQUES.md", "# Techniques\n")
        self.write("docs/01-certificates.md", "# Chapter 1\n")
        self.write("docs/overview.md", "# Overview\n")
        self.write("docs/index.json", json.dumps({
            "schemaVersion": 1,
            "overview": {"source": "docs/overview.md", "content": "docs/overview.html"},
            "pages": [{"id": "certificates", "source": "docs/01-certificates.md", "content": "docs/certificates.html"}],
        }))
        self.write("data/open/instance.rec", "id: open\nq: 1\nF: X0**6\nA: Y0**6\n")
        self.write("data/first/instance.rec", "id: first\nq: 1\nF: X0**6\nA: Y0**6\n")
        self.write("data/first/proof.json", json.dumps({"schemaVersion": 2, "instanceId": "first", "theorem": "Submission.certificate"}))
        self.write("data/first/acceptance.json", "{}")
        self.git("init", "-q")
        self.git("config", "user.name", "CI fixture")
        self.git("config", "user.email", "ci@example.invalid")
        self.git("add", ".")
        self.git("commit", "-qm", "Base")
        self.base = self.git("rev-parse", "HEAD")
        self.prev_check_root = checker.ROOT
        self.prev_class_root = classifier.ROOT
        checker.ROOT = self.root
        classifier.ROOT = self.root
        self.addCleanup(setattr, checker, "ROOT", self.prev_check_root)
        self.addCleanup(setattr, classifier, "ROOT", self.prev_class_root)

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, stderr=subprocess.DEVNULL).decode().strip()

    def add_minimal_solve(self, solution_body="import HodgeTarget\n"):
        self.write("data/open/proof.json", json.dumps({
            "schemaVersion": 2, "instanceId": "open", "theorem": "Submission.certificate",
        }))
        self.write("data/open/solution.md", "# Open proof\n\nDetails.\n")
        self.write("data/open/Solution.lean", solution_body)

    def commit_branch(self, name):
        self.git("checkout", "-q", "-B", name, self.base)

    def test_combined_solve_with_library_and_book_companions_accepted(self):
        self.commit_branch("combined-ok")
        self.add_minimal_solve(
            "import HodgeTarget\nimport HodgeComputer.Constructions.NewPkg.Helper\n"
        )
        self.write("formal/lean/HodgeComputer/Constructions/NewPkg/Helper.lean",
                   "import HodgeComputer.Constructions.Base\ndef helperVal : Nat := 3\n")
        self.write("formal/lean/HodgeComputer/Constructions/NewPkg/README.md", "# NewPkg\n")
        self.write("formal/TECHNIQUES.md", "# Techniques\n\nAdded NewPkg.\n")
        self.write("docs/01-certificates.md", "# Chapter 1\n\n## New section\n")
        self.git("add", ".")
        self.git("commit", "-qm", "Combined solve PR")
        head = self.git("rev-parse", "HEAD")
        self.assertEqual(classifier.classify(self.base, head), "solve")
        rid, metadata, files, instance, companions = checker.read_proposal(self.base, head, "alice", self.policy)
        self.assertEqual(rid, "open")
        self.assertEqual(metadata["instanceId"], "open")
        self.assertEqual(set(files), {"proof.json", "solution.md", "Solution.lean"})
        self.assertEqual(set(companions), {
            "formal/lean/HodgeComputer/Constructions/NewPkg/Helper.lean",
            "formal/lean/HodgeComputer/Constructions/NewPkg/README.md",
            "formal/TECHNIQUES.md",
            "docs/01-certificates.md",
        })
        lib_files = {
            checker.library_module_name(p): raw
            for p, raw in companions.items()
            if checker.companion_kind(p) == "library"
        }
        lib_order, lib_imports, staged = checker.library_module_order(self.root, lib_files)
        self.assertEqual(lib_order, ["HodgeComputer.Constructions.NewPkg.Helper"])
        self.assertEqual(lib_imports, ["HodgeComputer.Constructions.Base"])
        self.assertEqual(set(staged), {"HodgeComputer.Constructions.NewPkg.Helper"})

    def test_combined_solve_rejects_protected_paths(self):
        forbidden = [
            ("formal/lean/HodgeComputer/Verify.lean", "def verifyMarker : Nat := 1\n"),
            ("formal/lean/HodgeComputer.lean", "import HodgeComputer.Verify\n"),
            ("formal/lean/lakefile.toml", 'name = "HodgeTestbed"\n'),
            ("formal/lean/HodgeTestbed/Extra.lean", "def x : Nat := 0\n"),
            ("docs/certificates.html", "<h1>bad</h1>\n"),
            ("scripts/proposals/check.py", "# tampered\n"),
            ("CONTRIBUTING.md", "# tampered\n"),
            ("data/open/instance.rec", "id: open\nq: 1\nF: X0**6\nA: Y1**6\n"),
            ("data/first/Solution.lean", "import HodgeTarget\n"),
        ]
        for idx, (rel, content) in enumerate(forbidden):
            with self.subTest(path=rel):
                self.commit_branch(f"bad-{idx}")
                self.add_minimal_solve()
                self.write(rel, content)
                self.git("add", ".")
                self.git("commit", "-qm", f"Tamper {rel}")
                head = self.git("rev-parse", "HEAD")
                with self.assertRaises(ValueError):
                    checker.read_proposal(self.base, head, "alice", self.policy)

    def test_combined_solve_rejects_deletions_and_executable_modes(self):
        self.commit_branch("bad-delete")
        self.add_minimal_solve()
        (self.root / "formal/lean/HodgeComputer/Constructions/Dependent.lean").unlink()
        self.git("add", "-A")
        self.git("commit", "-qm", "Delete companion")
        with self.assertRaises(ValueError):
            checker.read_proposal(self.base, self.git("rev-parse", "HEAD"), "alice", self.policy)

        self.commit_branch("bad-exec")
        self.add_minimal_solve()
        p = self.write("formal/lean/HodgeComputer/Constructions/Exec.lean", "def x : Nat := 0\n")
        os.chmod(p, 0o755)
        self.git("add", ".")
        self.git("commit", "-qm", "Executable companion")
        with self.assertRaises(ValueError):
            checker.read_proposal(self.base, self.git("rev-parse", "HEAD"), "alice", self.policy)

    def test_library_module_order_security_and_dependents(self):
        # Modifying Base must pull unchanged Dependent into the sandbox rebuild order.
        order, ext, staged = checker.library_module_order(
            self.root,
            {"HodgeComputer.Constructions.Base": b"import HodgeComputer.Verify\ndef baseMarker : Nat := 9\n"},
        )
        self.assertEqual(order, [
            "HodgeComputer.Constructions.Base",
            "HodgeComputer.Constructions.Dependent",
        ])
        self.assertEqual(ext, ["HodgeComputer.Verify"])
        self.assertEqual(set(staged), set(order))

        # Banned tokens, disallowed imports, missing imports, and cycles are rejected.
        bad_cases = [
            {"HodgeComputer.Constructions.Bad": b"theorem t : True := by sorry\n"},
            {"HodgeComputer.Constructions.Bad": b"axiom cheat : False\n"},
            {"HodgeComputer.Constructions.Bad": b"import Proposal.Helper\ndef x : Nat := 0\n"},
            {"HodgeComputer.Constructions.Bad": b"import HodgeTarget\ndef x : Nat := 0\n"},
            {"HodgeComputer.Constructions.Bad": b"import HodgeComputer.Constructions.NoSuchModule\n"},
            {
                "HodgeComputer.Constructions.CycA": b"import HodgeComputer.Constructions.CycB\n",
                "HodgeComputer.Constructions.CycB": b"import HodgeComputer.Constructions.CycA\n",
            },
        ]
        for case in bad_cases:
            with self.subTest(case=list(case)):
                with self.assertRaises(ValueError):
                    checker.library_module_order(self.root, case)

        # A base core module importing a modified Constructions module must be rejected.
        self.write("formal/lean/HodgeComputer/Verify.lean", "import HodgeComputer.Constructions.Base\n")
        with self.assertRaises(ValueError):
            checker.library_module_order(
                self.root,
                {"HodgeComputer.Constructions.Base": b"def baseMarker : Nat := 10\n"},
            )

    def test_validate_book_index_and_companion_links(self):
        # Valid updated docs/index.json adding a brand-new book chapter passes.
        good_index = json.dumps({
            "schemaVersion": 1,
            "overview": {"source": "docs/overview.md", "content": "docs/overview.html"},
            "pages": [
                {"id": "certificates", "source": "docs/01-certificates.md", "content": "docs/certificates.html"},
                {"id": "new-chapter", "source": "docs/06-new.md", "content": "docs/new.html"},
            ],
        }).encode()
        checker.validate_book_index(good_index, self.root, {"docs/06-new.md"})

        # Missing source, bad HTML path, or duplicate page ID is rejected.
        bad_indices = [
            {"schemaVersion": 1, "overview": {"source": "docs/overview.md", "content": "docs/overview.html"},
             "pages": [{"id": "missing", "source": "docs/06-missing.md", "content": "docs/missing.html"}]},
            {"schemaVersion": 1, "overview": {"source": "docs/overview.md", "content": "docs/overview.html"},
             "pages": [{"id": "badhtml", "source": "docs/01-certificates.md", "content": "evil.html"}]},
            {"schemaVersion": 1, "overview": {"source": "docs/overview.md", "content": "docs/overview.html"},
             "pages": [
                 {"id": "dup", "source": "docs/01-certificates.md", "content": "docs/a.html"},
                 {"id": "dup", "source": "docs/01-certificates.md", "content": "docs/b.html"},
             ]},
        ]
        for payload in bad_indices:
            with self.subTest(payload=payload):
                with self.assertRaises(ValueError):
                    checker.validate_book_index(json.dumps(payload).encode(), self.root, set())

        # Companion library and book links in solution.md resolve cleanly via content.render extra_files.
        sys.path.insert(0, str(ROOT / "scripts"))
        content_mod = load("content_mod", ROOT / "scripts/content.py")
        html_out = content_mod.render(
            "# Proof\n\nUses [Helper](../../formal/lean/HodgeComputer/Constructions/NewPkg/Helper.lean) "
            "and [New Chapter](../../docs/06-new.md#section-one).\n",
            root=self.root,
            source_path=Path("data/open/solution.md"),
            extra_files=[
                Path("formal/lean/HodgeComputer/Constructions/NewPkg/Helper.lean"),
                Path("docs/06-new.md"),
            ],
        )
        self.assertIn("formal/lean/HodgeComputer/Constructions/NewPkg/Helper.lean", html_out)
        self.assertIn("docs/06-new.md#section-one", html_out)


if __name__ == "__main__":
    unittest.main()
