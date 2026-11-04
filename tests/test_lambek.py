#!/usr/bin/env python3
"""Structural and syntactic verification tests for Lambek calculus."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class TestLambekCalculus(unittest.TestCase):
    def test_coq_files_exist_and_nonempty(self):
        for rel in ("01.v", "src/plus.v", "src/minus.v", "examples/example1.v", "examples/slash_backslash_examples.v"):
            path = os.path.join(ROOT, rel)
            self.assertTrue(os.path.isfile(path), f"Missing {path}")
            self.assertGreater(os.path.getsize(path), 0, f"Empty {path}")

    def test_documentation_exists(self):
        for rel in ("README.md", "documentation.md"):
            path = os.path.join(ROOT, rel)
            self.assertTrue(os.path.isfile(path), f"Missing {path}")
            self.assertGreater(os.path.getsize(path), 100)


if __name__ == "__main__":
    unittest.main()
