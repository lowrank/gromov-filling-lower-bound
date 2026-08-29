#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_dir"

python3 - <<'PY'
import json
from pathlib import Path

repo = Path.cwd()
source_root = repo / "ClassificationOfSurfaces"
metadata_path = source_root / "VENDOR.json"
metadata = json.loads(metadata_path.read_text())

expected = {
    "schema": 1,
    "name": "classification-of-surfaces-eval-closure",
    "upstream_commit": "e3c7230fe78d7b056a415d9ecae6f77887046b32",
    "entry_module": "ClassificationOfSurfaces.EvalStatement",
    "lean_source_files": 131,
    "license": "Apache-2.0",
}
for key, value in expected.items():
    if metadata.get(key) != value:
        raise SystemExit(
            f"surface-vendor metadata mismatch for {key}: "
            f"expected {value!r}, found {metadata.get(key)!r}"
        )

compatibility = metadata.get("compatibility", {})
if compatibility != {"lean": "4.29.0", "mathlib": "v4.29.0"}:
    raise SystemExit(f"unexpected surface-vendor compatibility target: {compatibility!r}")

if (repo / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.29.0":
    raise SystemExit("lean-toolchain no longer matches the surface-vendor compatibility target")
if '"https://github.com/leanprover-community/mathlib4" @ "v4.29.0"' not in (
    repo / "lakefile.lean"
).read_text():
    raise SystemExit("lakefile mathlib pin no longer matches the surface-vendor compatibility target")
if not (source_root / "LICENSE").is_file():
    raise SystemExit("surface-vendor Apache-2.0 license is missing")

def module_path(module: str) -> Path:
    return repo.joinpath(*module.split(".")).with_suffix(".lean")

entry = metadata["entry_module"]
seen: set[str] = set()
stack = [entry]
while stack:
    module = stack.pop()
    if module in seen:
        continue
    seen.add(module)
    path = module_path(module)
    if not path.is_file():
        raise SystemExit(f"surface-vendor import is missing: {module} ({path})")
    for line in path.read_text().splitlines():
        if line.startswith("import "):
            stack.extend(
                dependency
                for dependency in line.removeprefix("import ").split()
                if dependency.startswith("ClassificationOfSurfaces.")
            )

actual = {
    ".".join(path.relative_to(repo).with_suffix("").parts)
    for path in source_root.rglob("*.lean")
}
if seen != actual:
    unreachable = sorted(actual - seen)
    missing = sorted(seen - actual)
    raise SystemExit(
        "surface-vendor closure mismatch\n"
        f"unreachable files: {unreachable}\n"
        f"missing files: {missing}"
    )
if len(actual) != metadata["lean_source_files"]:
    raise SystemExit(
        f"surface-vendor file-count mismatch: expected "
        f"{metadata['lean_source_files']}, found {len(actual)}"
    )

print(
    "PASS: pinned surface-vendor metadata, 4.29 compatibility, license, "
    f"and exact {len(actual)}-module transitive closure."
)
PY
