#!/usr/bin/env python3
"""Mutation tests against a real accepted source receipt, outside the worktree."""

from copy import deepcopy
from pathlib import Path
import shutil
import sys
import tempfile

import verification_receipt as gate


def main():
    receipt, positive, negative = map(gate.read_json, sys.argv[1:])
    with tempfile.TemporaryDirectory(prefix="gromov-receipt-tamper-") as temp:
        root = Path(temp)
        for name in receipt["source_sha256"]:
            destination = root / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(gate.ROOT / name, destination)
        gate.verify(receipt, positive, negative, root)
        tested = []

        def reject(label, r=receipt, p=positive, n=negative):
            try:
                gate.verify(r, p, n, root)
            except (ValueError, KeyError, TypeError):
                tested.append(label)
                return
            raise AssertionError(f"mutation was accepted: {label}")

        source = root / "GromovFilling.lean"
        original = source.read_bytes()
        source.write_bytes(original + b"\n-- changed source\n")
        reject("changed source")
        source.unlink()
        reject("missing source")
        source.write_bytes(original)
        extra = root / "GromovFilling/UnexpectedModule.lean"
        extra.write_text("-- unreceipted module\n")
        reject("extra source")
        extra.unlink()

        changed = deepcopy(receipt)
        changed["source_sha256"].pop("scripts/verification_receipt.py")
        reject("omitted checker", r=changed)
        changed = deepcopy(positive)
        changed["declarations"].pop()
        changed["report"]["audited"] -= 1
        reject("missing declaration with adjusted count", p=changed)
        changed = deepcopy(positive)
        changed["declarations"][0] = "GromovFilling.unexpectedDeclaration"
        reject("unexpected declaration with unchanged count", p=changed)
        changed = deepcopy(positive)
        changed["declarations"][0] = changed["declarations"][1]
        reject("duplicate declaration", p=changed)
        changed = deepcopy(positive)
        changed["modules"].pop()
        reject("missing compiled module", p=changed)
        changed = deepcopy(positive)
        changed["report"]["axiomsUsed"].append("sorryAx")
        reject("disallowed live axiom", p=changed)
        changed = deepcopy(negative)
        changed["report"]["ok"] = True
        reject("negative control accepted", n=changed)
        changed = deepcopy(receipt)
        changed["candidate_commit"] = changed["candidate_commit"][:7]
        reject("abbreviated candidate", r=changed)
        gate.verify(receipt, positive, negative, root)
        print(f"PASS: receipt gate rejects {len(tested)} mutations: {', '.join(tested)}.")


if __name__ == "__main__":
    main()
