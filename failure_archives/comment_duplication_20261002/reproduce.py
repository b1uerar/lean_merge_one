#!/usr/bin/env python3
"""Replay archived merges and check their recorded comment duplication."""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import runpy


ARCHIVE = Path(__file__).resolve().parent


def comment_counts(source):
    return Counter(line.strip() for line in source.splitlines()
                   if line.lstrip().startswith("--"))


def replay(directory, project, timeout):
    report = json.loads((directory / "failure.json").read_text(encoding="utf-8"))
    options = dict(report["parameters"])
    if project is not None:
        options["project"] = str(project)
    if timeout is not None:
        options["timeout"] = timeout
    merge = runpy.run_path(str(ARCHIVE.parent.parent / "lean_merge.py"))["merge"]
    base = (directory / "base.lean").read_text(encoding="utf-8")
    donor = (directory / "donor.lean").read_text(encoding="utf-8")
    result = merge(base, donor, **options)
    output = result["content"]
    output_counts = comment_counts(output)
    input_maximum = comment_counts(base) | comment_counts(donor)
    duplicated = {
        text: {"input_maximum": input_maximum[text], "output": count}
        for text, count in output_counts.items()
        if count > input_maximum[text]
    }
    digest = hashlib.sha256(output.encode("utf-8")).hexdigest()
    expected = report["historical_output_sha256"]
    return {
        "case": directory.name,
        "verified": result["verified"],
        "matches_historical_output": digest == expected,
        "comment_anomaly_reproduced": bool(duplicated),
        "excess_comment_lines": sum(
            item["output"] - item["input_maximum"] for item in duplicated.values()),
        "passed": bool(result["verified"] and digest == expected and duplicated),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cases", nargs="*", help="case directory names; default: all five")
    parser.add_argument("--project", type=Path, help="override the recorded Lake project")
    parser.add_argument("--timeout", type=float, help="override timeout per merge")
    parser.add_argument("--jobs", type=int, default=1, help="parallel merges; default: 1")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    manifest = json.loads((ARCHIVE / "manifest.json").read_text(encoding="utf-8"))
    names = args.cases or [case["directory"] for case in manifest["cases"]]
    known = {case["directory"] for case in manifest["cases"]}
    if any(name not in known for name in names):
        parser.error("case names must appear in manifest.json")
    # Replays keep the archived evidence unchanged, including on worker failure.
    os.environ["LEAN_TOOL_FAILURE_ARCHIVE"] = "0"
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(replay, ARCHIVE / name, args.project, args.timeout)
                   for name in names]
        passed = True
        for name, future in zip(names, futures):
            try:
                result = future.result()
            except Exception as error:
                result = {"case": name, "passed": False, "error": str(error)}
            print(json.dumps(result, ensure_ascii=False), flush=True)
            passed = passed and result["passed"]
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
