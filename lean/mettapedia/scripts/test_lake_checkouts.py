#!/usr/bin/env python3
"""Regression tests for the non-mutating Lake dependency preflight."""

import importlib.util
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "checkouts", Path(__file__).with_name("check_lake_checkouts.py"))
checkouts = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(checkouts)


class CheckoutTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.checkout = self.root / ".lake/packages/example"
        self.url = "https://example.org/library.git"
        self.manifest = {"packages": [
            {"type": "git", "name": "example", "url": self.url},
        ]}
        self.write_manifest()

    def write_manifest(self):
        (self.root / "lake-manifest.json").write_text(json.dumps(self.manifest))

    def make_checkout(self):
        self.checkout.mkdir(parents=True)
        subprocess.run(["git", "init", "-q", str(self.checkout)], check=True)
        subprocess.run(["git", "-C", str(self.checkout), "remote", "add", "origin", self.url],
                       check=True)

    def test_missing_dependency_is_left_for_initial_checkout(self):
        self.assertEqual(checkouts.check_existing_checkouts(self.root), [])

    def test_existing_matching_checkout_is_accepted(self):
        self.make_checkout()
        self.assertEqual(checkouts.check_existing_checkouts(self.root), [])

    def test_changed_origin_is_reported_without_removing_content(self):
        self.make_checkout()
        marker = self.checkout / "retained"
        marker.write_text("preserve cached data")
        self.manifest["packages"][0]["url"] += "/changed"
        self.write_manifest()
        failures = checkouts.check_existing_checkouts(self.root)
        self.assertEqual(len(failures), 1)
        self.assertIn("cached origin differs", failures[0])
        self.assertEqual(marker.read_text(), "preserve cached data")

    def test_git_access_failure_is_not_treated_as_an_origin_change(self):
        self.make_checkout()
        with patch.object(checkouts, "git_output", side_effect=ValueError(
                "Git ownership or repository access check failed")):
            failures = checkouts.check_existing_checkouts(self.root)
        self.assertIn("Git ownership", failures[0])
        self.assertNotIn("origin differs", failures[0])
        self.assertTrue((self.checkout / ".git").is_dir())

    def test_git_ownership_rejection_preserves_the_checkout(self):
        self.make_checkout()
        environment = {
            "GIT_TEST_ASSUME_DIFFERENT_OWNER": "1",
            "GIT_CONFIG_COUNT": "1",
            "GIT_CONFIG_KEY_0": "safe.directory",
            "GIT_CONFIG_VALUE_0": "",
        }
        with patch.dict(os.environ, environment):
            failures = checkouts.check_existing_checkouts(self.root)
        self.assertEqual(len(failures), 1)
        self.assertIn("Git ownership", failures[0])
        self.assertTrue((self.checkout / ".git").is_dir())

    def test_quoted_package_name_uses_the_actual_directory(self):
        self.make_checkout()
        self.manifest["packages"][0]["name"] = "«example»"
        self.write_manifest()
        self.assertEqual(checkouts.check_existing_checkouts(self.root), [])


if __name__ == "__main__":
    unittest.main()
