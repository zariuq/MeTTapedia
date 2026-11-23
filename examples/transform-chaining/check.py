"""Replay ordered composition, kernel receipts, and shared-source probabilities."""

import argparse
from fractions import Fraction
from itertools import product
import json
import math
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[1] / "lean" / "mettapedia"


def run(command, *, cwd=None, data=None, environment=None):
    proc = subprocess.run(command, cwd=cwd, input=data, env=environment, text=True,
                          capture_output=True, check=True)
    return proc.stdout, proc.stderr


def term(line):
    """Read one ground term in the example's symbol/number fragment."""
    stack = []
    roots = []
    for token in re.findall(r"\(|\)|[^\s()]+", line):
        if token == "(":
            stack.append([])
        elif token == ")":
            node = stack.pop()
            (stack[-1] if stack else roots).append(tuple(node))
        else:
            (stack[-1] if stack else roots).append(token)
    if stack or len(roots) != 1:
        raise ValueError(line)
    return roots[0]


def tagged(output, label):
    rows = [term(line)[1] for line in output.splitlines() if line.startswith(f"({label} ")]
    if len(rows) != 1:
        raise ValueError(f"expected one {label!r} in {output}")
    return rows[0]


def probability(clauses, weights):
    """Weighted model count of a disjunction of conjunctive leaf supports."""
    supports = frozenset(frozenset(clause) for clause in clauses)
    if not supports:
        return Fraction(0)
    if frozenset() in supports:
        return Fraction(1)
    source = min(set.union(set(), *supports))
    weight = weights[source]
    yes = probability([clause - {source} for clause in supports], weights)
    no = probability([clause for clause in supports if source not in clause], weights)
    return weight * yes + (1 - weight) * no


def world_reference(facts, weights, active):
    """Enumerate worlds and run the two base relations directly in each world."""
    total = Fraction(0)
    for bits in product((False, True), repeat=len(weights)):
        world = dict(zip(weights, bits))
        mass = math.prod(weights[key] if bit else 1 - weights[key] for key, bit in world.items())
        edges = [(rel, x, z) for _, rel, x, z, leaf in facts
                 if leaf[-1] in active and world[leaf[-1]]]
        if any(("father", middle, "carol") in edges for rel, x, middle in edges
               if rel == "mother" and x == "alice"):
            total += mass
    return total


def chainer_lineage(answer):
    marker, proof, claim, tv = answer
    _, rel, nxt, x, mid, z, left, right, left_source, right_source = claim
    _, rule, branches = proof
    connective, left_branch, right_leaf = branches
    call, left_rule, left_leaf = left_branch
    assert (marker, rel, nxt, proof[0], rule, connective, call, left_rule, tv[0]) == (
        ":", "mother", "father", "by", "compose-rule", "conjunction", "by", left, "STV")
    assert (left_leaf, right_leaf) == (left_source, right_source)
    return (x, mid, z, left, right), (left_leaf, right_leaf)


def check(args, work):
    source = (HERE / "compose.metta").read_text()
    env = dict(os.environ, CETTA_TRANSFORM_CURSOR_REFERENCE="0")
    cetta = [args.cetta, "--lang", "petta", "--profile", "extended"]
    ordinary, _ = run([*cetta, HERE / "compose.metta"], environment=env)
    family = tagged(ordinary, "prepared-family")
    route = tagged(ordinary, "prepared-route")
    assert len(family) == 2 and len(route) == 1 and tagged(ordinary, "reversed") == ()
    assert [row[4:6] for row in family] == [("l1", "r1"), ("l2", "r1")]
    assert family == tagged(ordinary, "ordinary-family") and route == tagged(ordinary, "ordinary-route")
    assert tagged(ordinary, "first-family") == family[0]

    tcalc, _ = run([args.cetta, "--lang", "tcalc", HERE / "compose.tcalc"])
    outcomes = [term(line)[1:] for line in tcalc.splitlines() if line.startswith("(outcome ")]
    assert len(outcomes) == 1 and "(finished true)" in tcalc
    derived = [row for row in outcomes[0] if row[0] == "holds" and isinstance(row[1], tuple)]
    expected = []
    for relation, answers in [(("then", "mother", "father"), family), (("then", "rail", "ferry"), route)]:
        for tag, x, mid, z, i, j, lp, rp, ls, rs in answers:
            assert tag == "witness"
            expected.append(("holds", relation, x, z, ("via", mid, ("leaf", i, lp, ls), ("leaf", j, rp, rs))))
    composed, = tagged(ordinary, "nested")
    assert composed == ("via", "west", expected[-1][-1], ("leaf", "r3", "bus-proof", "schedule"))
    expected.append(("holds", ("then", ("then", "rail", "ferry"), "bus"), "east", "pier", composed))
    assert sorted(derived, key=repr) == sorted(expected, key=repr)

    # Decode the actual tcalc child proofs and middle at the lowering boundary.
    kernel_rows = []
    for _, rel, x, z, (via, mid, left, right) in derived:
        if rel == ("then", "mother", "father"):
            assert via == "via" and left[0] == right[0] == "leaf"
            kernel_rows.append((x, mid, z, left[1], right[1], left[2], right[2], left[3], right[3]))
    assert sorted(kernel_rows) == sorted(row[1:] for row in family)
    damaged = list(kernel_rows[0])
    damaged[1] = "alice"
    swapped = list(kernel_rows[0])
    swapped[5:7] = reversed(swapped[5:7])
    forged_id = list(kernel_rows[0])
    forged_id[3] = "unissued"
    forged_source = list(kernel_rows[0])
    forged_source[7] = "independent-report"
    facts = [term(line) for line in (HERE / "compose.tcalc").read_text().splitlines() if line.startswith("(holds ")]
    requests = [("premise", rel, x, z, *leaf[1:]) for _, rel, x, z, leaf in facts]
    requests.extend(("check", "mother", "father", *fields)
                    for fields in [*kernel_rows, damaged, swapped, forged_id, forged_source])
    kernel_input = "".join("\t".join(fields) + "\n" for fields in requests)
    checked, _ = run(["lake", "env", "lean", "-DwarningAsError=true", "--run",
                      HERE / "CheckReceipts.lean"], cwd=LEAN, data=kernel_input)
    assert checked.splitlines() == ["accepted " + " ".join([i, j, ls, rs])
                                     for _, _, _, i, j, _, _, ls, rs in kernel_rows] + [
                                         "rejected", "rejected", "invalid-occurrence", "invalid-occurrence"]

    for ref in ("0", "1"):
        visible, _ = run([*cetta, HERE / "visibility.metta"],
                         environment=dict(env, CETTA_TRANSFORM_CURSOR_REFERENCE=ref))
        observed = tagged(visible, "snapshot-results")
        assert observed == (term("(yielded 0 alice bob carol l1 r1)"), term("(yielded 1 alice bob carol l2 r1)"))
        assert tagged(visible, "live-results") == (*observed, term("(yielded 2 alice bob carol l2 r2)"))

    upstream = args.chainer.resolve().with_suffix("")
    program = work / "lineage-with-import.metta"
    program.write_text(f"!(import! &self {upstream})\n" + (HERE / "lineage.metta").read_text())
    output, _ = run(["sh", args.petta_runner, program, "--silent"])
    weights = {"certain": Fraction(1), "report": Fraction(1, 2)}
    checkpoints = {}
    for phase in ("original", "replay", "retracted"):
        lineage = [chainer_lineage(row) for row in tagged(output, phase)]
        present = phase != "retracted"
        wanted = [(r[1:6], r[8:10]) for r in family] if present else []
        assert sorted(lineage) == sorted(wanted)
        mass = probability([support for _, support in lineage], weights)
        active = set(weights) if present else {"certain"}
        assert mass == world_reference(facts, weights, active) == (Fraction(1, 2) if present else 0)
        checkpoints[phase] = {"proofs": len(lineage), "mass": str(mass)}
    assert probability([["report"], ["other"]], {"report": Fraction(1, 2), "other": Fraction(1, 2)}) == Fraction(3, 4)

    counters = {}
    setup = source.split("!(reset-runtime-stats!)", 1)[0]
    for operation in ("ordinary", "compose"):
        for demand in ("collapse", "once"):
            measured = work / f"{operation}-{demand}.metta"
            measured.write_text(setup + f"!(reset-runtime-stats!)\n!(observed ({demand} ({operation} mother father alice carol)))\n")
            out, err = run([args.stats_cetta, *cetta[1:], "--emit-runtime-stats", measured], environment=env)
            assert tagged(out, "observed") == (family if demand == "collapse" else family[0])
            all_counts = {name: int(number) for name, number in re.findall(r"^runtime-counter (\S+) (\d+)$", err, re.M)}
            names = ("space-occurrence-cursor-row", "transform-cursor-scan-row", "scratch-arena-alloc-bytes",
                     "eval-arena-alloc-bytes", "transform-cursor-owned-bytes-peak")
            counts = {name: all_counts[name] for name in names}
            assert counts["scratch-arena-alloc-bytes"] > 0
            if operation == "compose":
                assert counts["transform-cursor-scan-row"] > 0 and all_counts["transform-direct-firing"] > 0
            counters[f"{operation}-{demand}"] = counts
    return {"materializer": checked.splitlines(), "snapshot_answers": 2, "live_answers": 3,
            "tcalc_derived_rows": len(derived), "chainer": checkpoints, "counters": counters}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__, epilog=(
        "Build the Lean module Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.TransformChain "
        "in the mettapedia Lake project before running the replay."))
    for option, help_text in (
        ("cetta", "CeTTa executable with the PeTTa extended and tcalc languages"),
        ("stats-cetta", "CeTTa executable built with runtime counters"),
        ("petta-runner", "SWI-PeTTa run.sh matching the chainer's dependency"),
        ("chainer", "upstream petta_chainer.metta (qualified with b0e24f9b)"),
        ("work-dir", "directory for the generated query and measurement inputs"),
    ):
        parser.add_argument("--" + option, required=True, type=Path, help=help_text)
    args = parser.parse_args()
    args.work_dir.mkdir(parents=True, exist_ok=True)
    print(json.dumps(check(args, args.work_dir), indent=2))
