"""Reproduce delivery-check failures and verify that a complete register passes."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


CHECKER = Path(__file__).resolve().parents[1] / "scripts" / "check_requirements.py"
HEADER = "| ID | Requirement | Status | Evidence |\n| --- | --- | --- | --- |\n"
ISSUE_ROW = "| #1 | Foundation | Verified | [Proof](proof.md) |\n"
TASK_ROW = "| #1/A.1.1 | Hilbert spaces | Verified | [Proof](proof.md) |\n"


class RequirementsTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        docs = self.root / "docs"
        docs.mkdir()
        (docs / "proof.md").write_text("Verification artifact\n", encoding="utf-8")
        self.register = docs / "REQUIREMENTS.md"
        self.issues = self.root / "issues.json"
        self.pages = [
            [{"number": 2, "pull_request": {}, "body": None}],
            [{"number": 1, "state": "closed", "body": "| A.1.1 | Hilbert spaces | High |"}],
        ]

    def check(self, rows, *args):
        self.register.write_text(HEADER + rows, encoding="utf-8")
        self.issues.write_text(json.dumps(self.pages), encoding="utf-8")
        return subprocess.run(
            [sys.executable, str(CHECKER), str(self.issues), "--register", str(self.register), *args],
            capture_output=True, text=True, check=False,
        )

    def test_all_verified_with_closed_issue_and_pull_request(self):
        result = self.check(ISSUE_ROW + TASK_ROW)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Verified: 2", result.stdout)

    def test_each_unfinished_status_fails_delivery(self):
        for status in ("Partial", "Open", "Blocked"):
            with self.subTest(status=status):
                result = self.check((ISSUE_ROW + TASK_ROW).replace("Verified", status))
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn(f"#1/A.1.1: {status}", result.stderr)

    def test_verified_parent_cannot_cover_unfinished_task(self):
        result = self.check(ISSUE_ROW + TASK_ROW.replace("Verified", "Partial"))
        self.assertEqual(result.returncode, 2)
        self.assertIn("#1 cannot be Verified while #1/A.1.1 is Partial", result.stderr)

    def test_blocked_requirement_reports_the_recorded_action(self):
        reason = "Supply the retained archive. [Archive status](proof.md)"
        rows = ISSUE_ROW.replace("Verified", "Partial")
        rows += f"| #1/A.1.1 | Recover original logs | Blocked | {reason} |\n"
        result = self.check(rows)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn(f"#1/A.1.1: Blocked. {reason}", result.stderr)

    def test_missing_issue_task_and_hypothesis_fail_coverage(self):
        self.pages[1][0]["body"] += "\n**Hypothesis**: The example generalizes."
        self.pages[0].append({"number": 3, "state": "open", "body": ""})
        result = self.check(ISSUE_ROW)
        self.assertEqual(result.returncode, 2)
        for requirement_id in ("#3", "#1/A.1.1", "#1/H1"):
            self.assertIn(f"Missing registered requirement {requirement_id}", result.stderr)

    def test_previously_recorded_prose_requirements_cannot_disappear(self):
        previous = self.root / "previous.md"
        previous.write_text(HEADER + ISSUE_ROW + TASK_ROW
                            + "| #1/review | Review proof | Open | In discussion |\n",
                            encoding="utf-8")
        result = self.check(ISSUE_ROW + TASK_ROW, "--previous-register", str(previous))
        self.assertEqual(result.returncode, 2)
        self.assertIn("Missing registered requirement #1/review", result.stderr)

    def test_duplicate_and_unrecognized_status_fail_validation(self):
        result = self.check(ISSUE_ROW + TASK_ROW.replace("Verified", "Delayed") + TASK_ROW)
        self.assertEqual(result.returncode, 2)
        self.assertIn("invalid or duplicate ID", result.stderr)
        self.assertIn("needs a requirement, a valid status and evidence", result.stderr)

    def test_verified_status_requires_evidence_and_existing_local_targets(self):
        result = self.check(ISSUE_ROW.replace("[Proof](proof.md)", "Done")
                            + TASK_ROW.replace("proof.md", "missing.md"))
        self.assertEqual(result.returncode, 2)
        self.assertIn("#1 needs a link to its verification evidence", result.stderr)
        self.assertIn("#1/A.1.1 has invalid evidence link", result.stderr)

    def test_empty_github_response_fails_validation(self):
        self.pages = [[]]
        result = self.check(ISSUE_ROW + TASK_ROW)
        self.assertEqual(result.returncode, 2)
        self.assertIn("The GitHub response contains no issues", result.stderr)


if __name__ == "__main__":
    unittest.main()
