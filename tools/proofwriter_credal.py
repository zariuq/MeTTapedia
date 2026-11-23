"""Measure certified marginal-only intervals on the ProofWriter depth-5 split.

ProofWriter supplies rules and logical labels. The existing simulated report
model supplies premise marginals and two precise posterior baselines. HiGHS
proposes endpoint certificates. Lean verifies each endpoint by exact rational
arithmetic and computes the work-limited projection curve.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import cache
import json
from math import prod
from pathlib import Path
import random
import subprocess
from time import perf_counter
from zipfile import ZipFile

from scipy.optimize import linprog

from pln_anytime_credal import conjunction, event, interval, packet as credal_packet
from pln_credal_certificates import linear_rows, pack_endpoint
from proofwriter_joint import literal, overlap_case, theory
from proofwriter_wm import OUTCOMES, distribution, evaluate, exchange, mixtures, packet, simulated_reports


CAPS = (0, 4, 8, 16, 32, 64, 128)


def propose_endpoint(request, rows, direction):
    support = request["evidence"]
    objective = [direction * bit for bit in conjunction(request["query"], support)]
    answer = linprog(objective, A_ub=rows or None, b_ub=[0] * len(rows) if rows else None,
                     A_eq=[list(map(int, support))], b_eq=[1], method="highs")
    if not answer.success:
        raise ValueError(f"Endpoint search failed: {answer.message}")

    def rational(value):
        return Q(float(value)).limit_denominator(1_000_000)

    beta = rational(answer.eqlin.marginals[0])
    multipliers = [-rational(value) for value in answer.ineqlin.marginals]
    return pack_endpoint(request, rows, direction, beta, multipliers, list(map(rational, answer.x)))


def prepare(marginals, query, evidence, caps):
    worlds = len(query)
    constraints = [interval(event(worlds, index), [True] * worlds, rate)
                   for index, rate in enumerate(marginals)]
    request = credal_packet(constraints, list(query), list(evidence), list(caps))
    rows = linear_rows(request)
    request["certificates"] = [propose_endpoint(request, rows, sign) for sign in (1, -1)]
    return request


def product_mass(mask, probabilities):
    return sum((prod(p if world & (1 << i) else 1 - p for i, p in enumerate(probabilities))
                for world, hit in enumerate(mask) if hit), Q(0))


def endpoints(raw):
    return tuple(Q(*value) for value in raw)


def verified(lean, request):
    result = exchange(lean, request)
    if "error" in result:
        raise ValueError(result["error"])
    return endpoints(result["sharp"]), result["projection"]


def diagnosis(archive, world_lean, credal_lean):
    record, question, (left, right) = overlap_case(archive)
    facts, rules = theory(record)
    q = literal(record["questions"][question]["representation"])
    program = {**packet(facts, rules, [q]), "includeScopes": True}
    scope, = evaluate(world_lean, program, [], [])["scopes"]
    ids = [list(facts)[index] for index in scope["coordinates"]]
    common, = left & right
    alternative, = left - right
    assert set(ids) == left | right
    given_proof = tuple(label in ("True", "Both") for label in scope["labels"])
    prior = (Q(3, 4),) * len(ids)
    result = {}
    for name, source, expected in (("required", common, (Q(1), Q(1))),
                                     ("alternative", alternative, (Q(2, 3), Q(1)))):
        query = event(len(given_proof), ids.index(source))
        request = prepare(prior, query, given_proof, CAPS)
        bound, stages = verified(credal_lean, request)
        assert bound == expected
        joint = conjunction(query, given_proof)
        independent = product_mass(joint, prior) / product_mass(given_proof, prior)
        fair = (Q(1, 2),) * len(ids)
        shared = (product_mass(joint, fair) + int(joint[-1])) / (
            product_mass(given_proof, fair) + int(given_proof[-1]))
        assert bound[0] <= independent <= bound[1] and bound[0] <= shared <= bound[1]
        result[name] = {"fact": source, "sharp": bound, "independent": independent,
                        "shared_reliability": shared, "projection": stages}
    bad = request["certificates"][0]["weights"]
    bad[0] = [-1, 1]
    assert "error" in exchange(credal_lean, request)
    no_proof = {key: value for key, value in request.items() if key != "certificates"}
    no_proof["constraints"][ids.index(common)] = interval(
        event(len(query), ids.index(common)), [True] * len(query), Q(0))
    assert exchange(credal_lean, no_proof)[-1]["interval"] is None
    return {"theory": record["id"], "question": question, **result, "zero_support_checked": True,
            "rejected_forged_certificate": True}


def benchmark(records, world_lean, credal_lean, seed, caps):
    totals = defaultdict(Counter)
    projection = defaultdict(Counter)
    scopes = Counter()
    rng = random.Random(seed)
    theories = 0

    @cache
    def solve(marginals, query):
        return verified(credal_lean, prepare(marginals, query, (True,) * len(query), caps))

    for record in records:
        theories += 1
        facts, rules = theory(record)
        questions = list(record["questions"].values())
        queries = [literal(q["representation"]) for q in questions]
        gold = [str(q["answer"]) for q in questions]
        _, ledger = simulated_reports(facts, rng)
        _, modes = ledger.posterior()
        weights = [component.mass for component in modes]
        laws = [component.probabilities for component in modes]
        marginals = tuple(sum(w * law[i] for w, law in zip(weights, laws, strict=True))
                          for i in range(len(facts)))
        encoded = {**packet(facts, rules, queries), "includeScopes": True}
        oracle = evaluate(world_lean, encoded, [(True,) * len(facts)], [*laws, marginals])
        assert oracle["labels"] == [gold], record["id"]
        for label, scope, *masses in zip(oracle["labels"][0], oracle["scopes"], *oracle["masses"], strict=True):
            index = OUTCOMES.index(label)
            exact = mixtures(masses[:-1], weights)[index]
            precise_independent = distribution(masses[-1])[index]
            scope_priors = tuple(marginals[i] for i in scope["coordinates"])
            n = len(scope_priors)
            scopes[n] += 1
            query = tuple(world_label == label for world_label in scope["labels"])
            assert product_mass(query, scope_priors) == precise_independent
            (lo, hi), stages = solve(scope_priors, query)
            assert 0 <= lo <= exact <= hi <= 1 and lo <= precise_independent <= hi
            width = hi - lo
            error_radius = max(precise_independent - lo, hi - precise_independent)
            for family in ("all", "multiple_sources" if n >= 2 else "at_most_one_source"):
                counts = totals[family]
                counts["queries"] += 1
                counts["sharp_points"] += int(width == 0)
                counts["vacuous"] += int(width == 1)
                counts["strict_half_threshold"] += int(hi < Q(1, 2) or Q(1, 2) < lo)
                counts["sensitive_half_threshold"] += int(
                    (lo < Q(1, 2) < hi) and precise_independent != Q(1, 2))
                counts["width_sum"] += width
                counts["independence_error_radius_sum"] += error_radius
                counts["worst_independence_error"] = max(counts["worst_independence_error"], error_radius)

            families = ["all"]
            if n >= 2:
                families.append("multiple_sources")
            if n >= 4:
                families.append("four_or_more_sources")
            previous = (Q(0), Q(1))
            for stage in stages:
                lower, upper = endpoints(stage["interval"])
                assert previous[0] <= lower <= lo <= hi <= upper <= previous[1]
                previous = lower, upper
                tight = lower == lo and upper == hi
                complete = stage["projectionComplete"]
                assert not complete or tight
                for family in families:
                    counts = projection[family, stage["pairsPerPivot"]]
                    counts["queries"] += 1
                    counts["width_sum"] += upper - lower
                    counts["sharp"] += int(tight)
                    counts["completed"] += int(complete)
                    counts["strict_half_threshold"] += int(upper < Q(1, 2) or Q(1, 2) < lower)

    def summarize(counts):
        count = counts["queries"]
        return {**counts, "mean_width": float(counts["width_sum"] / count)}

    return {
        "theories": theories, "seed": seed, "scope_counts": scopes,
        "unique_certificate_problems": solve.cache_info().misses,
        "sharp": {key: summarize(row) for key, row in totals.items()},
        "projection": {family: {budget: summarize(projection[family, budget]) for budget in caps}
                       for family in sorted({family for family, _ in projection})},
    }


def worker(root, module):
    command = ["lake", "env", "lean", "-M", "8192", "--run", f"Mettapedia/Examples/PLN/{module}.lean"]
    return subprocess.Popen(command, cwd=root, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--seed", type=int, default=19)
    parser.add_argument("--max-pairs-per-pivot", type=int, choices=CAPS, default=32)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1] / "lean/mettapedia"
    start = perf_counter()
    with ZipFile(args.archive) as archive, worker(root, "ProofWriterWorldModel") as world_lean, \
            worker(root, "AnytimeCredalReplay") as credal_lean:
        split = next(name for name in archive.namelist() if name.endswith("/OWA/depth-5/meta-test.jsonl"))
        controls = diagnosis(archive, world_lean, credal_lean)
        caps = tuple(cap for cap in CAPS if cap <= args.max_pairs_per_pivot)
        with archive.open(split) as records:
            replay = benchmark(map(json.loads, records), world_lean, credal_lean, args.seed, caps)
    if world_lean.returncode or credal_lean.returncode:
        raise RuntimeError("A Lean evaluator failed")
    print(json.dumps({"split": split, "diagnosis": controls, "benchmark": replay,
                      "seconds": round(perf_counter() - start, 3)}, indent=2, default=str))


if __name__ == "__main__":
    main()
