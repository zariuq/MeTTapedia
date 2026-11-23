#!/usr/bin/env python3
"""Execute the MeTTa controller and compare with independent finite sums."""

import argparse
from collections import Counter, defaultdict
import itertools
import math
from pathlib import Path
import random
import re
import subprocess


HERE = Path(__file__).resolve().parent
TRIPLES = tuple(itertools.product((0, 1), repeat=3))
BETAS = (0.0, 0.5, 1.0, 2.0, 4.0)
CHECKS = 0


def check(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise AssertionError(message)


def near(actual, expected, message):
    check(isinstance(actual, (int, float)) and math.isfinite(actual)
          and math.isclose(actual, expected, rel_tol=2e-10, abs_tol=2e-10),
          f"{message}: {actual!r} != {expected!r}")


def sexpr(value):
    if isinstance(value, (tuple, list)):
        return "(" + " ".join(map(sexpr, value)) + ")"
    return str(value)


def parse_output(text):
    tokens = re.findall(r"[()]|[^\s()]+", text)
    index = 0

    def parse():
        nonlocal index
        token = tokens[index]
        index += 1
        if token == "(":
            values = []
            while index < len(tokens) and tokens[index] != ")":
                values.append(parse())
            if index == len(tokens):
                raise AssertionError("Unclosed expression in runtime output")
            index += 1
            return tuple(values)
        if token == ")":
            raise AssertionError("Unexpected closing parenthesis in runtime output")
        if token.lower() in ("true", "false"):
            return token.lower() == "true"
        try:
            return int(token)
        except ValueError:
            try:
                return float(token)
            except ValueError:
                return token

    expressions = []
    while index < len(tokens):
        expressions.append(parse())
    return expressions


def utility(world, action):
    a, b, c = world
    target = (b ^ c, a ^ c, a ^ b ^ c)
    return sum(1 if x == y else -1 for x, y in zip(target, action))


def reference_policy(world, budget, beta):
    actions = [a for a in TRIPLES if sum(a) <= budget]
    # No stabilizing transformation shared with the MeTTa implementation.
    raw = [math.exp(beta * utility(world, a)) / 8.0 for a in actions]
    normalizer = math.fsum(raw)
    return [(weight / normalizer, a, utility(world, a))
            for weight, a in zip(raw, actions)]


def sample(policy, draw):
    for probability, action, _ in policy[:-1]:
        if draw < probability:
            return action
        draw -= probability
    return policy[-1][1]


def joint(budget, beta):
    return [(w, a, p / 8.0) for w in TRIPLES
            for p, a, _ in reference_policy(w, budget, beta)]


def mutual_information(histories, left, right):
    # Group projected pairs before summing, so this also works for coarse views.
    pairs, lm, rm = defaultdict(float), defaultdict(float), defaultdict(float)
    for w, a, p in histories:
        x, y = left(w, a), right(w, a)
        pairs[x, y] += p
        lm[x] += p
        rm[y] += p
    return math.fsum(p * math.log(p / (lm[x] * rm[y]))
                     for (x, y), p in pairs.items() if p > 0)


def readouts(histories, beta):
    reward = math.fsum(p * utility(w, a) for w, a, p in histories)
    kl = math.fsum(p * math.log(64.0 * p) for _, _, p in histories if p > 0)
    temporal = mutual_information(histories, lambda w, a: w, lambda w, a: a)
    cuts = [mutual_information(
        histories, lambda w, a: (w[i], a[i]),
        lambda w, a: tuple((w[j], a[j]) for j in range(3) if j != i))
        for i in range(3)]
    means = [math.fsum(p * (1 - 2 * (w + a)[i]) for w, a, p in histories)
             for i in range(6)]
    covariances = [abs(math.fsum(p * (1 - 2 * (w + a)[i])
                                      * (1 - 2 * (w + a)[j])
                                for w, a, p in histories) - means[i] * means[j])
                   for i, j in itertools.combinations(range(6), 2)]
    initial = defaultdict(float)
    for w, _, p in histories:
        initial[w] += p
    return dict(MeanUtility=reward, KLNats=kl, Objective=beta * reward - kl,
                PastFutureBits=temporal / math.log(2),
                MinUnitCutBits=min(cuts) / math.log(2),
                MaxPairCovariance=max(covariances),
                InitialDrift=max(abs(initial[w] - 0.125) for w in TRIPLES))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cetta", type=Path,
                        default=HERE.parents[2] / "hyperon/CeTTa/cetta")
    parser.add_argument("--program", type=Path,
                        help="Execute a self-contained controller file before the checks")
    args = parser.parse_args()
    program = [args.program.read_text()] if args.program else ["!(import! &self control.metta)"]

    def query(tag, index, expression):
        program.append(f"!({tag} {index} {expression})")

    cases = [(w, b, beta) for b in range(4) for beta in BETAS for w in TRIPLES]
    for i, (world, budget, beta) in enumerate(cases):
        policy = reference_policy(world, budget, beta)
        draws, cumulative = [0.0], 0.0
        for p, _, _ in policy:
            draws.append(cumulative + p / 2)
            cumulative += p
        draws.append(math.nextafter(1.0, 0.0))
        query("Policy", i, f"(tc:policy {sexpr(world)} {budget} {beta})")
        query("Samples", i,
              f"(let $p (tc:policy {sexpr(world)} {budget} {beta}) "
              f"(map-atom {sexpr(draws)} (|-> ($u) (tc:sample $p $u))))")

    settings = [(b, beta) for b in range(4) for beta in BETAS]
    for i, (budget, beta) in enumerate(settings):
        query("Joint", i, f"(tc:joint {budget} {beta})")
        query("Readouts", i, f"(tc:summary {budget} {beta})")
    query("Passive", 0, "(tc:passive-tilt 2 2.0)")
    invalid_actions = ((2, 0, 0), (-1, 0, 0), (0, 1), (0, 0, 0, 0))
    admissions = [(b, a) for b in range(4) for a in TRIPLES + invalid_actions]
    for i, (budget, action) in enumerate(admissions):
        query("Admission", i, f"(tc:admitted {budget} {sexpr(action)})")

    executions = [(w, b) for b in range(4) for w in TRIPLES]
    for i, (world, budget) in enumerate(executions):
        board, episode, draw = f"&run{i}", f"e{i}", (i + 0.5) / len(executions)
        program += [f"!(bind! {board} (new-space))",
                    f"!(tc:open {board} {episode} {sexpr(world)} {budget})",
                    f"!(add-atom {board} (Unrelated sentinel))"]
        query("Before", i, f"(collapse (match {board} $fact $fact))")
        query("Execute", i, f"(tc:step {board} {episode} 2.0 {draw})")
        query("After", i, f"(collapse (match {board} $fact $fact))")
        query("Replay", i, f"(tc:step {board} {episode} 2.0 {draw})")
        query("AfterReplay", i, f"(collapse (match {board} $fact $fact))")

    # Each attempt uses the same still-pending state; no failure may mutate it.
    program += ["!(bind! &negative (new-space))",
                "!(tc:open &negative n (0 0 1) 2)"]
    failures = (
        "(tc:execute &negative n (0 0 1) (1 1 1))",
        "(tc:execute &negative n (1 1 1) (0 0 0))",
        "(tc:execute &negative n (0 0 1) (2 0 0))",
        "(tc:step &negative n 2.0 -0.1)",
        "(tc:step &negative n 2.0 1.0)",
        "(tc:step &negative n -1.0 0.5)",
    )
    query("NegativeBefore", 0, "(collapse (match &negative $fact $fact))")
    for i, attempt in enumerate(failures):
        query("Refusal", i, attempt)
        query("NegativeAfter", i, "(collapse (match &negative $fact $fact))")
    program += ["!(bind! &no-actions (new-space))",
                "!(tc:open &no-actions none (0 0 0) -1)",
                "!(bind! &no-state (new-space))",
                "!(add-atom &no-state (Pending missing))",
                "!(add-atom &no-state (Sensors missing (0 0 0)))",
                "!(add-atom &no-state (ActuatorBudget missing 3))"]
    query("EmptyPolicy", 0, "(tc:step &no-actions none 2.0 0.5)")
    query("MissingResource", 0, "(tc:step &no-state missing 2.0 0.5)")
    query("MissingStillPending", 0,
          "(collapse (match &no-state (Pending $ep) $ep))")
    # A previously prepared action is rechecked after the permit changes.
    program += ["!(bind! &stale (new-space))",
                "!(tc:open &stale stale (0 0 1) 3)"]
    query("Prepared", 0, "(tc:sample (tc:policy (0 0 1) 3 2.0) 0.5)")
    program += ["!(remove-atom &stale (ActuatorBudget stale 3))",
                "!(add-atom &stale (ActuatorBudget stale 2))"]
    query("StaleBefore", 0, "(collapse (match &stale $fact $fact))")
    query("StaleExecute", 0, "(tc:execute &stale stale (0 0 1) (1 1 1))")
    query("StaleAfter", 0, "(collapse (match &stale $fact $fact))")
    program += ["!(bind! &await (new-space))"]
    query("Await", 0, "(tc:step &await awaiting 2.0 0.5)")
    program += ["!(add-atom &await (Sensors awaiting (0 0 0)))"]
    query("Await", 1, "(tc:step &await awaiting 2.0 0.5)")
    program += ["!(add-atom &await (ActuatorBudget awaiting 2))",
                "!(add-atom &await (ActuatorBudget awaiting 3))"]
    query("Ambiguous", 0, "(tc:step &await awaiting 2.0 0.5)")
    program += ["!(add-atom &await (Sensors awaiting (0 0 1)))"]
    query("Ambiguous", 1, "(tc:step &await awaiting 2.0 0.5)")
    query("CDFBoundaries", 0,
          "(let $p (tc:policy (0 0 0) 3 0.0) "
          "(map-atom (0.0 0.125 0.25 0.375 0.5 0.625 0.75 0.875) "
          "(|-> ($u) (tc:sample $p $u))))")
    # Coarse observations must aggregate histories before taking log ratios.
    query("ReadoutControl", 0,
          "(tc:mi (tc:joint 3 0.0) Past (tc:labels8) Past (tc:labels8))")
    query("ReadoutControl", 1,
          "(tc:mi (tc:joint 3 2.0) Blind (0) Future (tc:labels8))")

    completed = subprocess.run(
        [str(args.cetta.resolve()), "--lang", "petta", "--quiet", "-e", "\n".join(program)],
        cwd=HERE, text=True, capture_output=True, check=True)
    check(not completed.stderr.strip(), f"Unexpected runtime diagnostic: {completed.stderr}")
    outputs = defaultdict(list)
    for value in parse_output(completed.stdout):
        if isinstance(value, tuple) and len(value) == 3 and isinstance(value[0], str):
            outputs[value[0], value[1]].append(value[2])

    def result(tag, index):
        values = outputs[tag, index]
        check(len(values) == 1, f"{tag} {index}: expected one evaluated answer, got {values}")
        return values[0]

    rng = random.Random(17)
    sample_count = probability_count = 0
    for i, (world, budget, beta) in enumerate(cases):
        actual = result("Policy", i)
        expected = reference_policy(world, budget, beta)
        check(len(actual) == len(expected), "Policy lost or invented an action")
        near(math.fsum(row[0] for row in actual), 1.0, "Conditional normalization")
        for got, (p, action, u) in zip(actual, expected):
            check(got[1:] == (action, u), "Action identity or utility mismatch")
            near(got[0], p, "Conditional probability")
            probability_count += 1
        draws, cumulative = [0.0], 0.0
        for p, _, _ in expected:
            draws.append(cumulative + p / 2)
            cumulative += p
        draws.append(math.nextafter(1.0, 0.0))
        sampled = result("Samples", i)
        check(sampled == tuple(sample(expected, u) for u in draws), "CDF realization mismatch")
        sample_count += len(draws)
        # These are independent finite controls, not a replacement for the Gibbs theorem.
        objective = math.fsum(p * (beta * u - math.log(8 * p)) for p, _, u in actual)
        alternatives = [[float(j == k) for j in range(len(expected))]
                        for k in range(len(expected))]
        alternatives.append([1.0 / len(expected)] * len(expected))
        for _ in range(3):
            raw = [rng.random() for _ in expected]
            alternatives.append([q / math.fsum(raw) for q in raw])
        for q in alternatives:
            other = math.fsum(p * (beta * row[2] - math.log(8 * p))
                              for p, row in zip(q, expected) if p > 0)
            check(other <= objective + 2e-10, "A control policy beats the Gibbs objective")

    for i, (budget, beta) in enumerate(settings):
        expected, actual = joint(budget, beta), result("Joint", i)
        check(len(actual) == len(expected), "History support mismatch")
        near(math.fsum(h[2] for h in actual), 1.0, "History normalization")
        for got, (w, a, p) in zip(actual, expected):
            check(got[:2] == (w, a), "History endpoint mismatch")
            near(got[2], p, "History probability")
        summary = result("Readouts", i)
        check(summary[0] == "Summary", "Readout was not evaluated")
        fields = dict(summary[1:])
        check(fields["Budget"] == budget and fields["Beta"] == beta, "Readout parameters")
        for field, expected_value in readouts(expected, beta).items():
            near(fields[field], expected_value, field)
        if budget == 3:
            rho = math.tanh(beta)
            near(fields["MeanUtility"], 3 * rho, "Lean parity reward formula")
            near(fields["KLNats"], 3 * beta * rho - 3 * math.log(math.cosh(beta)),
                 "Lean parity KL formula")
            for w, a, p in actual:
                target = (w[1] ^ w[2], w[0] ^ w[2], w[0] ^ w[1] ^ w[2])
                density = math.prod(1 + rho * (1 if x == y else -1)
                                    for x, y in zip(a, target)) / 64
                near(p, density, "Lean noisy-parity density")
            def f(r):
                return math.fsum(t * math.log2(2 * t)
                                 for t in ((1 + r) / 2, (1 - r) / 2) if t > 0)
            near(fields["MinUnitCutBits"], 3 * f(rho) - f(rho * rho),
                 "Paper's spatial cut formula (numerical control)")

    passive = result("Passive", 0)
    passive_reference = [(w, a, math.exp(2 * utility(w, a)))
                         for w in TRIPLES for a in TRIPLES if sum(a) <= 2]
    total = math.fsum(p for _, _, p in passive_reference)
    check(len(passive) == len(passive_reference), "Passive history support mismatch")
    near(math.fsum(h[2] for h in passive), 1.0, "Passive normalization")
    for got, (w, a, p) in zip(passive, passive_reference):
        check(got[:2] == (w, a), "Passive support mismatch")
        near(got[2], p / total, "Passive probability")
    drift = readouts(passive, 2.0)["InitialDrift"]
    check(drift > 0.11, "The noncausal initial-law counterexample disappeared")

    for i, (budget, action) in enumerate(admissions):
        allowed = len(action) == 3 and all(x in (0, 1) for x in action) and sum(action) <= budget
        check(result("Admission", i) is allowed, "Admission predicate mismatch")
    for i, (world, budget) in enumerate(executions):
        action = sample(reference_policy(world, budget, 2.0), (i + 0.5) / len(executions))
        episode = f"e{i}"
        check(result("Execute", i) == ("Committed", action), "Execution choice mismatch")
        expected_state = Counter((
            ("Sensors", episode, world), ("ActuatorBudget", episode, budget),
            ("ActuatorState", episode, action),
            ("Executed", episode, world, action, utility(world, action)),
            ("Unrelated", "sentinel")))
        check(Counter(result("After", i)) == expected_state, "Wrong update, receipt or frame")
        before = Counter(result("Before", i))
        check(before[("Pending", episode)] == 1, "Fixture lacks linear request")
        check(result("Replay", i) == ("Refused", "Admission"), "Replay was admitted")
        check(Counter(result("AfterReplay", i)) == expected_state, "Replay changed state")
    before = Counter(result("NegativeBefore", 0))
    for i in range(len(failures)):
        expected_refusal = "Admission" if i < 3 else "PolicyInput"
        check(result("Refusal", i) == ("Refused", expected_refusal), "Wrong refusal outcome")
        check(Counter(result("NegativeAfter", i)) == before, "Refusal changed state")
    check(result("EmptyPolicy", 0) == ("Refused", "EmptyPolicy"), "Empty policy was executed")
    check(result("MissingResource", 0) == ("Refused", "Admission"), "Missing resource accepted")
    check(result("MissingStillPending", 0) == ("missing",), "Failed preparation consumed request")
    check(result("Prepared", 0) == (1, 1, 1), "Stale control prepared a different action")
    check(result("StaleExecute", 0) == ("Refused", "Admission"), "Stale permission accepted")
    check(Counter(result("StaleBefore", 0)) == Counter(result("StaleAfter", 0)),
          "Stale candidate changed state")
    check(result("Await", 0) == ("Unresolved", "Sensors"), "Missing sensor outcome")
    check(result("Await", 1) == ("Unresolved", "ActuatorBudget"), "Missing budget outcome")
    check(result("Ambiguous", 0) == ("Refused", "AmbiguousBudget"), "Ambiguous budget accepted")
    check(result("Ambiguous", 1) == ("Refused", "AmbiguousSensors"), "Ambiguous sensors accepted")
    check(result("CDFBoundaries", 0) == TRIPLES, "CDF boundary convention changed")
    near(result("ReadoutControl", 0), 3 * math.log(2), "A view's self-information")
    near(result("ReadoutControl", 1), 0.0, "A blind view's information")

    print(f"PASS: {CHECKS} checks; {len(cases)} conditional policies; "
          f"{probability_count} action probabilities; {sample_count} CDF draws; "
          f"{len(settings)} history laws and information readouts; "
          f"{len(executions)} executions and replays.")
    print(f"PASS: forbidden actions, stale observations, malformed actions, invalid policy inputs, "
          f"empty choices, stale permits and missing resources are refused without mutation; "
          f"missing observations remain unresolved.")
    print(f"PASS: global-tilt counterexample changes an initial probability by {drift:.12f}; "
          f"the causal controller preserves all eight initial probabilities.")


if __name__ == "__main__":
    main()
