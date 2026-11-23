#!/usr/bin/env python3
"""Mutation controls for an actual annotated source-emission record."""

import copy
import json
from pathlib import Path
import sys

from qualify_inductive_m1 import validate_annotations


def check(records):
    validate_annotations(records)
    mutations = []

    def altered(name, edit):
        changed = copy.deepcopy(records)
        edit(changed)
        mutations.append((name, changed))

    altered("missing-source", lambda rows: rows.pop())
    altered("reordered-sources", lambda rows: rows.reverse())
    altered("wrong-judgment", lambda rows: rows[0].update(judgment="OtherJudgment"))
    altered("failed-erasure", lambda rows: rows[0].update(erasure_matches_source=False))
    altered("changed-type", lambda rows: rows[1].update(expected_type="different type"))
    altered("missing-annotation", lambda rows: rows[0].update(annotated_function=""))
    altered("extra-typing-permission", lambda rows: rows[0].update(typing_permissions=[0, 1, 2]))
    altered("boolean-row", lambda rows: rows[0].update(typing_permissions=[0, True]))
    altered("premature-cons-permission", lambda rows:
            rows[0]["computation_policies"][1].update(cons_certificate_accepted=True))
    altered("numeric-verdict", lambda rows:
            rows[0]["computation_policies"][0].update(nil_certificate_accepted=0))
    mutations.append(("malformed-record", [None, records[1]]))
    for name, mutated in mutations:
        try:
            validate_annotations(mutated)
        except RuntimeError:
            continue
        raise AssertionError(f"accepted altered annotation record: {name}")
    return len(mutations)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: test_inductive_annotations.py ANNOTATIONS.json")
    count = check(json.loads(Path(sys.argv[1]).read_text()))
    print(f"Annotated source intake: actual record accepted; {count} mutations refused")
