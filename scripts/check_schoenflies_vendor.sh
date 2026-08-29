#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

python3 - <<'PY'
import json
import re
from pathlib import Path

repo = Path.cwd()
source_root = repo / "Wikipedia"
compat_root = repo / "SchoenfliesCompat"
source_metadata = json.loads((source_root / "VENDOR.json").read_text())
compat_metadata = json.loads((compat_root / "VENDOR.json").read_text())

expected_source = {
    "schema": 1,
    "name": "jordan-schoenflies-closure",
    "upstream_repository": "https://github.com/plby/lean-proofs",
    "upstream_commit": "2b380d2f2476782f55181ff21174a744cdb783d1",
    "upstream_subdirectory": "src/latest",
    "entry_module": "Wikipedia.SchoenfliesTheorem.JordanSchoenflies",
    "lean_source_files": 134,
    "license": "Apache-2.0",
}
expected_compat = {
    "schema": 1,
    "name": "mathlib-graph-schoenflies-compat",
    "upstream_repository": "https://github.com/leanprover-community/mathlib4",
    "upstream_commit": "db584cd6d46c92f209a44c0f1c829460d327499d",
    "entry_modules": [
        "SchoenfliesCompat.Graph.Basic",
        "SchoenfliesCompat.Graph.Subgraph",
        "SchoenfliesCompat.Graph.Delete",
        "SchoenfliesCompat.Graph.Maps",
    ],
    "lean_source_files": 4,
    "license": "Apache-2.0",
    "pinned_mathlib_commit": "8a178386ffc0f5fef0b77738bb5449d50efeea95",
    "namespace": "SchoenfliesGraph",
}
for label, metadata, expected in (
    ("Schönflies source", source_metadata, expected_source),
    ("Schönflies compatibility", compat_metadata, expected_compat),
):
    for key, value in expected.items():
        if metadata.get(key) != value:
            raise SystemExit(
                f"{label} metadata mismatch for {key}: "
                f"expected {value!r}, found {metadata.get(key)!r}"
            )

expected_target = {"lean": "4.29.0", "mathlib": "v4.29.0"}
if source_metadata.get("compatibility") != expected_target:
    raise SystemExit("unexpected Schönflies source compatibility target")
if compat_metadata.get("compatibility") != expected_target:
    raise SystemExit("unexpected Schönflies graph compatibility target")

expected_upstream = {
    "lean": "4.33.0",
    "mathlib_commit": "db584cd6d46c92f209a44c0f1c829460d327499d",
}
if source_metadata.get("upstream_compatibility") != expected_upstream:
    raise SystemExit("unexpected Schönflies upstream compatibility metadata")
expected_namespaces = {
    "multigraph": "SchoenfliesGraph",
    "jordan_curve": "SchoenfliesJordanCurveTheorem",
}
if source_metadata.get("namespace_isolation") != expected_namespaces:
    raise SystemExit("unexpected Schönflies namespace-isolation metadata")

if (repo / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.29.0":
    raise SystemExit("lean-toolchain no longer matches the Schönflies compatibility target")
lakefile = (repo / "lakefile.lean").read_text()
if '"https://github.com/leanprover-community/mathlib4" @ "v4.29.0"' not in lakefile:
    raise SystemExit("lakefile mathlib pin no longer matches the compatibility target")
if (
    '"e442525a662e9e3beb8205b9fa1fc99509076ded" / "HOLLight-Lean"'
    not in " ".join(lakefile.split())
):
    raise SystemExit("HOL Light Jordan-curve dependency pin changed unexpectedly")
for license_path in (source_root / "LICENSE", compat_root / "LICENSE"):
    if not license_path.is_file():
        raise SystemExit(f"vendored Apache-2.0 license is missing: {license_path}")

def module_path(module: str) -> Path:
    return repo.joinpath(*module.split(".")).with_suffix(".lean")

local_prefixes = ("Wikipedia.", "SchoenfliesCompat.")
seen: set[str] = set()
stack = [source_metadata["entry_module"]]
while stack:
    module = stack.pop()
    if module in seen:
        continue
    seen.add(module)
    path = module_path(module)
    if not path.is_file():
        raise SystemExit(f"Schönflies vendor import is missing: {module} ({path})")
    for line in path.read_text().splitlines():
        stripped = line.strip()
        if stripped.startswith("public import "):
            dependencies = stripped.removeprefix("public import ").split()
        elif stripped.startswith("import "):
            dependencies = stripped.removeprefix("import ").split()
        else:
            continue
        stack.extend(dep for dep in dependencies if dep.startswith(local_prefixes))

actual_source = {
    ".".join(path.relative_to(repo).with_suffix("").parts)
    for path in source_root.rglob("*.lean")
}
actual_compat = {
    ".".join(path.relative_to(repo).with_suffix("").parts)
    for path in compat_root.rglob("*.lean")
}
actual = actual_source | actual_compat
if seen != actual:
    raise SystemExit(
        "Schönflies vendor closure mismatch\n"
        f"unreachable files: {sorted(actual - seen)}\n"
        f"missing files: {sorted(seen - actual)}"
    )
if len(actual_source) != source_metadata["lean_source_files"]:
    raise SystemExit(
        "Schönflies source file-count mismatch: expected "
        f"{source_metadata['lean_source_files']}, found {len(actual_source)}"
    )
if len(actual_compat) != compat_metadata["lean_source_files"]:
    raise SystemExit(
        "Schönflies compatibility file-count mismatch: expected "
        f"{compat_metadata['lean_source_files']}, found {len(actual_compat)}"
    )

for path in [*source_root.rglob("*.lean"), *compat_root.rglob("*.lean")]:
    text = path.read_text()
    for forbidden in (
        "import Mathlib\n",
        "import Mathlib.Combinatorics.Graph.Basic",
        "import Mathlib.Combinatorics.Graph.Subgraph",
        "import Mathlib.Combinatorics.Graph.Delete",
        "import Mathlib.Combinatorics.Graph.Maps",
    ):
        if forbidden in text:
            raise SystemExit(f"non-isolated Schönflies import in {path}: {forbidden}")
    for lineno, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if stripped.startswith("import ") or stripped.startswith("public import "):
            continue
        if re.search(r"\bGraph\b", line):
            raise SystemExit(
                f"unisolated root Graph token in {path}:{lineno}: {line.strip()}"
            )

for relative in (
    Path("JordanCurveTheorem.lean"),
    Path("JordanCurveTheorem/Regions.lean"),
    Path("SchoenfliesTheorem/JordanClosed.lean"),
):
    path = source_root / relative
    text = path.read_text()
    if "namespace JordanCurveTheorem" in text:
        raise SystemExit(f"unisolated JordanCurveTheorem namespace in {path}")
    for lineno, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if stripped.startswith("import ") or stripped.startswith("public import "):
            continue
        if re.search(r"(?<!Wikipedia\.)\bJordanCurveTheorem\.", line):
            raise SystemExit(
                f"unisolated JordanCurveTheorem reference in {path}:{lineno}: "
                f"{line.strip()}"
            )

basic = (compat_root / "Graph/Basic.lean").read_text()
if "structure SchoenfliesGraph" not in basic or "structure Graph" in basic:
    raise SystemExit("Schoenflies multigraph base is not namespace-isolated")

print(
    "PASS: pinned Jordan–Schönflies metadata, licenses, 4.29 compatibility, "
    "namespace isolation, minimal imports, and exact "
    f"{len(actual_source)}+{len(actual_compat)}-module closure."
)
PY
