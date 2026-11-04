#!/usr/bin/env python3
"""Check that post-merge publication records credit without freezing proof sources."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('publish', ROOT/'scripts/proposals/publish.py')
publish = importlib.util.module_from_spec(spec)
spec.loader.exec_module(publish)


class CreditRecording(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.folder = self.root/'data/example'
        self.folder.mkdir(parents=True)
        self.pr = {'merged': True, 'base': {'ref': 'main', 'repo': {'full_name': publish.REPOSITORY}},
                   'merge_commit_sha': 'a'*40, 'user': {'login': 'contributor'},
                   'merged_at': '2026-01-01T00:00:00Z', 'html_url': f'https://github.com/{publish.REPOSITORY}/pull/12'}
        self.changes = [[{'status': 'added', 'filename': 'data/example/proof.json'}]]

    def call(self):
        def output(args, **kwargs):
            return json.dumps(self.changes if '/files?' in args[2] else self.pr).encode()
        with patch.object(publish, 'ROOT', self.root), patch.object(publish.subprocess, 'check_output', side_effect=output), patch.object(publish.subprocess, 'run'):
            publish.publish(12)

    def test_credit_is_small_and_survives_source_maintenance(self):
        self.call()
        path = self.folder/'acceptance.json'
        original = path.read_text()
        self.assertEqual(json.loads(original), {'schemaVersion': 2, 'githubLogin': 'contributor',
                         'acceptedAt': self.pr['merged_at'], 'pullRequest': {'number': 12, 'url': self.pr['html_url']}})
        (self.folder/'Solution.lean').write_text('-- maintained proof source\n')
        self.call()
        self.assertEqual(path.read_text(), original)

    def test_unmerged_pr_cannot_record_credit(self):
        self.pr['merged'] = False
        with self.assertRaises(ValueError):
            self.call()
        self.assertFalse((self.folder/'acceptance.json').exists())

    def test_modifying_an_existing_proof_does_not_award_new_credit(self):
        self.changes[0][0]['status'] = 'modified'
        self.call()
        self.assertFalse((self.folder/'acceptance.json').exists())

    def test_retry_does_not_replace_another_original_pr(self):
        path = self.folder/'acceptance.json'
        path.write_text(json.dumps({'pullRequest': {'number': 11}}))
        original = path.read_text()
        with self.assertRaises(ValueError):
            self.call()
        self.assertEqual(path.read_text(), original)


if __name__ == '__main__':
    unittest.main()
