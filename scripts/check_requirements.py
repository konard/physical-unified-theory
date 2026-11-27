#!/usr/bin/env python3
"""Check repository requirements against the paginated GitHub Issues response."""

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit


ROW_ID = re.compile(r"#[1-9]\d*(?:/[A-Za-z0-9][A-Za-z0-9.-]*)?")
TASK = re.compile(r"^\|\s*([A-O]\.\d+\.\d+)\s*\|", re.MULTILINE)
HYPOTHESIS = re.compile(r"^\*\*Hypothesis\*\*:", re.MULTILINE)
STATUSES = {"Verified", "Partial", "Open", "Blocked"}
TABLE_HEADER = "| ID | Requirement | Status | Evidence |"
TABLE_DIVIDER = "| --- | --- | --- | --- |"
LINK = re.compile(r"\[[^\]]+\]\(([^)]+)\)")


def issue_requirements(pages):
    """Return issue, task and hypothesis IDs, including those from closed issues."""
    if not isinstance(pages, list) or not pages or not all(
        isinstance(page, list) for page in pages
    ):
        raise ValueError("Expected GitHub issue pages from gh api --paginate --slurp")

    required = set()
    for page in pages:
        for issue in page:
            if "pull_request" in issue:
                continue
            issue_id = f"#{issue['number']}"
            if not ROW_ID.fullmatch(issue_id) or issue_id in required:
                raise ValueError(f"Invalid or duplicate GitHub issue ID {issue_id}")
            required.add(issue_id)
            body = issue["body"] or ""
            required.update(f"{issue_id}/{task}" for task in TASK.findall(body))
            hypotheses = len(HYPOTHESIS.findall(body))
            required.update(f"{issue_id}/H{index}" for index in range(1, hypotheses + 1))
    if not required:
        raise ValueError("The GitHub response contains no issues")
    return required


def register_rows(markdown):
    """Read the Markdown tables used by the register."""
    rows = {}
    errors = []
    for line_number, line in enumerate(markdown.splitlines(), start=1):
        if not line.startswith("|") or line in {TABLE_HEADER, TABLE_DIVIDER}:
            continue
        cells = re.split(r"(?<!\\)\|", line)
        if len(cells) != 6 or cells[0] or cells[-1]:
            errors.append(f"Line {line_number} must have four table cells")
            continue

        requirement_id, requirement, status, evidence = (cell.strip() for cell in cells[1:-1])
        if not ROW_ID.fullmatch(requirement_id) or requirement_id in rows:
            errors.append(f"Line {line_number} has an invalid or duplicate ID {requirement_id!r}")
            continue
        rows[requirement_id] = status, evidence
        if not requirement or not evidence or status not in STATUSES:
            errors.append(f"{requirement_id} needs a requirement, a valid status and evidence")
    return rows, errors


def validate(register, pages, previous_register=None):
    """Return the register rows and problems with coverage or evidence."""
    rows, errors = register_rows(register.read_text(encoding="utf-8"))
    required = issue_requirements(pages)
    if previous_register is not None:
        previous_rows, previous_errors = register_rows(
            previous_register.read_text(encoding="utf-8")
        )
        errors.extend(f"Base register: {error}" for error in previous_errors)
        required.update(previous_rows)
    for requirement_id in sorted(required - rows.keys()):
        errors.append(f"Missing registered requirement {requirement_id}")

    repository = register.parent.parent.resolve()
    for requirement_id, (status, evidence) in rows.items():
        issue_id, _, _ = requirement_id.partition("/")
        if issue_id not in rows:
            errors.append(f"{requirement_id} requires a parent issue row {issue_id}")
        elif rows[issue_id][0] == "Verified" and status != "Verified":
            errors.append(f"{issue_id} cannot be Verified while {requirement_id} is {status}")

        links = LINK.findall(evidence)
        if status == "Verified" and not links:
            errors.append(f"{requirement_id} needs a link to its verification evidence")
        for link in links:
            target = urlsplit(link)
            if target.scheme == "https" and target.netloc:
                continue
            path = (register.parent / unquote(target.path)).resolve()
            if (target.scheme or target.netloc or not target.path
                    or not path.is_relative_to(repository) or not path.exists()):
                errors.append(f"{requirement_id} has invalid evidence link {link!r}")
    return rows, errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("issues", type=Path, help="JSON from gh api --paginate --slurp")
    parser.add_argument("--register", type=Path, default=Path("docs/REQUIREMENTS.md"))
    parser.add_argument("--previous-register", type=Path, help="Preserve IDs from the base branch")
    args = parser.parse_args()
    try:
        with args.issues.open(encoding="utf-8") as source:
            rows, errors = validate(args.register, json.load(source), args.previous_register)
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(f"Cannot check requirements: {error}", file=sys.stderr)
        return 2

    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 2

    counts = Counter(status for status, _ in rows.values())
    print("Requirement status | " + " | ".join(
        f"{status}: {counts[status]}" for status in sorted(STATUSES)
    ), flush=True)
    if counts["Verified"] == len(rows):
        return 0

    print("Requirements remain unverified. Deliver the work and record its evidence in "
          "docs/REQUIREMENTS.md to pass this check.", file=sys.stderr)
    for requirement_id, (status, evidence) in rows.items():
        if status == "Blocked":
            print(f"{requirement_id}: {status}. {evidence}", file=sys.stderr)
        elif status != "Verified":
            print(f"{requirement_id}: {status}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
