#!/usr/bin/env python3
"""Check the exact source snapshot and its static integration coverage.

This does not elaborate Lean, audit axioms, replay the kernel or run programs.
Run from the repository root before the Lean gates.
"""
import hashlib
import json
from pathlib import Path
import re

paper = Path("Improved Upper Bounds for the Directed Flow-Cut Gap")
manifest = json.loads((paper / "verification/component-verification.json").read_text())
assert manifest["status"] == "UNVERIFIED"
assert manifest["source_snapshot"]["component_count"] == len(manifest["component_sources"])
for rel, expected in manifest["file_sha256"].items():
    p = Path(rel)
    assert p.is_file(), "Missing file: " + rel
    assert hashlib.sha256(p.read_bytes()).hexdigest() == expected, "File drift: " + rel
canonical = json.dumps(manifest["component_sources"], sort_keys=True, separators=(",", ":")).encode()
assert hashlib.sha256(canonical).hexdigest() == manifest["source_snapshot"]["sha256"]
actual = {p.relative_to(paper).as_posix() for p in (paper / "DirectedFlowCutGap").rglob("*.lean")}
assert actual == set(manifest["component_sources"]), "Component inventory mismatch"
modules = sorted(p[:-5].replace("/", ".") for p in actual)
root = (paper / "DirectedFlowCutGap.lean").read_text()
assert root == "".join("import " + m + "\n" for m in modules), "Root module index mismatch"
dependencies = {}
for rel in sorted(actual):
    text = (paper / rel).read_text()
    imported = re.findall(r"^import\s+([A-Za-z0-9_.]+)", text, re.M)
    owned = [m for m in imported if m.startswith("DirectedFlowCutGap.")]
    assert set(owned) <= set(modules), "Missing project dependency: " + rel
    dependencies[rel[:-5].replace("/", ".")] = owned
active, done = set(), set()
def visit(module):
    assert module not in active, "Import cycle: " + module
    if module in done:
        return
    active.add(module)
    for child in dependencies[module]:
        visit(child)
    active.remove(module)
    done.add(module)
for module in modules:
    visit(module)
replay = (paper / "verification/KernelReplay.lean").read_text()
targets = re.findall(r"^  replayFromImports `([A-Za-z0-9_.]+)$", replay, re.M)
assert targets == modules + ["DirectedFlowCutGap"], "Kernel replay coverage mismatch"
strict = manifest["strict_new_components_in_dependency_order"]
assert len(strict) == len(set(strict)) == len(manifest["added_components"])
assert set(strict) == set(manifest["added_components"])
positions = {"DirectedFlowCutGap." + n: i for i, n in enumerate(strict)}
for module, i in positions.items():
    assert all(dep not in positions or positions[dep] < i for dep in dependencies[module])
print(f"Static snapshot integrity passed: {len(modules)} component sources; Lean gates remain separate.")
