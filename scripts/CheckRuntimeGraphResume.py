#!/usr/bin/env python3
"""Validate the graph/dispatch charge markers from RuntimeGraphCombinedSmoke.

Run only after successful execution of the unchanged Lean regression driver.
These checks cover its printed graph and dispatch fields, not additional cases.
"""
import json
from pathlib import Path
import re
import sys


def one(text, pattern, label):
    matches = re.findall(pattern, text, re.M)
    assert len(matches) == 1, f"Expected exactly one {label} marker"
    return matches[0]


def check(text):
    expected = [marker for i in range(1, 9) for marker in (f"START runtime case {i}", f"DONE runtime case {i}")]
    actual = [line for line in text.splitlines() if line.startswith(("START runtime case ", "DONE runtime case "))]
    assert actual == expected, "Missing, duplicate, or out-of-order runtime case markers"
    assert text.splitlines().count("PASS all eight runtime bodies") == 1
    assert len([line for line in text.splitlines() if line.startswith("PASS ")]) == 9
    graph = one(text, r"^PASS binary graph path/mask/full-state smoke; retained events=([0-9]+); stopping scans=([0-9]+); operations=([0-9]+)$", "graph")
    events, scans, operations = map(int, graph)
    assert events <= 27 and scans == 27 and operations > 0, "Invalid graph counts or operation charge"
    dispatch = one(text, r"^PASS binary empty/free/diagonal/direct/retained-endpoint dispatch smoke; charges=(\[[0-9, ]*\])$", "dispatch")
    charges = json.loads(dispatch)
    assert len(charges) == 5 and all(type(x) is int and x > 0 for x in charges), "Expected five positive dispatch charges"
    guesses = one(text, r"^PASS binary full original-input guess family; entries=([0-9]+); stopping scans=([0-9]+); operations=([0-9]+)$", "guess-family")
    entries, scans, operations = map(int, guesses)
    assert entries == 9 and scans == 243 and operations > 0, "Invalid guess-family counts or operation charge"


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python3 scripts/CheckRuntimeGraphCharges.py EXECUTION_LOG")
    check(Path(sys.argv[1]).read_text())
    print("PASS printed runtime graph and dispatch charge checks")
