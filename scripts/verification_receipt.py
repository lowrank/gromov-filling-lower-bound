#!/usr/bin/env python3
"""Bind the complete proof/checker source set to a live axiom inventory."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOW = ["Classical.choice", "Quot.sound", "propext"]
SCHEMA = "gromov-source-receipt-v1"
AUDIT_COMMIT = "46024e005996495c65ef609368e11ab39c4222e3"
PROOF_DIRS = ("GromovFilling", "ClassificationOfSurfaces", "Wikipedia", "SchoenfliesCompat")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_object)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files(root):
    files = {"GromovFilling.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain"}
    for directory in PROOF_DIRS:
        require((root / directory).is_dir(), f"missing source directory: {directory}")
        files.update(str(p.relative_to(root)) for p in (root / directory).rglob("*.lean"))
    for directory in PROOF_DIRS[1:]:
        files.update(f"{directory}/{name}" for name in ("VENDOR.json", "VENDOR.md", "LICENSE"))
    for directory in ("scripts", ".github/workflows"):
        require((root / directory).is_dir(), f"missing checker directory: {directory}")
        files.update(str(p.relative_to(root)) for p in (root / directory).rglob("*")
                     if p.is_file() and p.suffix in (".py", ".sh", ".lean", ".yml", ".yaml"))
    for name in files:
        path = root / name
        require(path.is_file() and not path.is_symlink(), f"missing or symlinked bound file: {name}")
    return {name: digest(root / name) for name in sorted(files)}


def names_once(values, field):
    require(isinstance(values, list) and values, f"empty or malformed {field}")
    require(all(isinstance(x, str) and x for x in values), f"malformed {field}")
    require(len(values) == len(set(values)), f"duplicate {field}")
    return sorted(values)


def positive_inventory(data, root):
    require(data.get("schema") == "gromov-axiom-inventory-v1", "unknown audit schema")
    report = data["report"]
    require(report["root"] == "GromovFilling", "wrong audited root")
    require(report["ok"] is True and report["violations"] == [], "positive audit failed")
    require(sorted(report["allowed"]) == ALLOW, "changed axiom allowlist")
    require(set(report["axiomsUsed"]) <= set(ALLOW), "disallowed axiom")
    declarations = names_once(data["declarations"], "declarations")
    require(type(report["audited"]) is int and report["audited"] == len(declarations),
            "declaration count disagrees with inventory")
    modules = names_once(data["modules"], "modules")
    expected = ["GromovFilling"] + [str(p.relative_to(root).with_suffix("")).replace("/", ".")
                                    for p in (root / "GromovFilling").rglob("*.lean")]
    require(modules == sorted(expected), "compiled module inventory differs from source modules")
    return {"declarations": declarations, "modules": modules, "axioms_used": sorted(report["axiomsUsed"]),
            "allowed_axioms": ALLOW}


def negative_control(data):
    require(data.get("schema") == "gromov-axiom-inventory-v1", "unknown negative schema")
    report = data["report"]
    require(report["ok"] is False and report["root"] == "GromovFilling", "negative control passed")
    require(sorted(report["allowed"]) == ALLOW, "negative control changed allowlist")
    require(report["violations"] == [{"decl": "GromovFilling.auditTamper", "axioms": ["sorryAx"]}],
            "negative control did not reject the injected theorem for sorryAx")
    require("GromovFilling.auditTamper" in data["declarations"], "missing negative-control theorem")
    return {"declaration": "GromovFilling.auditTamper", "rejected_axiom": "sorryAx", "exit_code": 1}


def verify(receipt, positive, negative, root=ROOT):
    require(receipt.get("schema") == SCHEMA, "unknown receipt schema")
    require(re.fullmatch(r"[0-9a-f]{40}", receipt["candidate_commit"]) is not None,
            "candidate must be a full commit hash")
    files = source_files(root)
    require(set(files) == set(receipt["source_sha256"]), "bound file set differs (missing or extra file)")
    changed = [name for name in files if files[name] != receipt["source_sha256"][name]]
    require(not changed, f"bound file hash mismatch: {changed}")
    require(receipt["audit_tool_commit"] == AUDIT_COMMIT, "changed audit tool pin")
    require(receipt["toolchain"] == (root / "lean-toolchain").read_text().strip(), "toolchain metadata drift")
    require(receipt["dependencies"] == read_json(root / "lake-manifest.json"), "dependency metadata drift")
    require(receipt["inventory"] == positive_inventory(positive, root), "live declaration inventory drift")
    require(receipt["negative_control"] == negative_control(negative), "negative-control mismatch")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("create")
    create.add_argument("--output", type=Path, required=True)
    check = commands.add_parser("verify")
    check.add_argument("receipt", type=Path)
    for cmd in (create, check):
        cmd.add_argument("--positive", type=Path, required=True)
        cmd.add_argument("--negative", type=Path, required=True)
    args = parser.parse_args()
    positive, negative = read_json(args.positive), read_json(args.negative)
    if args.command == "create":
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        files = source_files(ROOT)
        tracked = subprocess.check_output(["git", "ls-tree", "-rz", "--name-only", "HEAD", "--", *files],
                                          cwd=ROOT).decode().split("\0")
        require(set(filter(None, tracked)) == set(files), "candidate has uncommitted bound files")
        subprocess.run(["git", "diff", "--quiet", "HEAD", "--", *files], cwd=ROOT, check=True)
        receipt = {"schema": SCHEMA, "candidate_commit": commit,
                   "source_sha256": files,
                   "inventory": positive_inventory(positive, ROOT),
                   "negative_control": negative_control(negative),
                   "audit_tool_commit": AUDIT_COMMIT,
                   "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
                   "dependencies": read_json(ROOT / "lake-manifest.json")}
        verify(receipt, positive, negative)
        args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    else:
        receipt = read_json(args.receipt)
        verify(receipt, positive, negative)
    print(f"PASS: source receipt binds {len(receipt['source_sha256'])} files and "
          f"{len(receipt['inventory']['declarations'])} distinct declarations.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
