"""Exact Lean inference for single-period CTV probe games.

The adapter receives only the harness statement emitter's rules, observed
facts, resolved labels, and queries. Roots without a declared mechanism use
Laplace estimates from resolved periods. Inference uses the exact factor
engine on each case. A case can contain a multiply connected directed acyclic
graph. Each declared head requires one two-sided conditional mechanism.
"""

from collections import Counter, deque
from fractions import Fraction
from graphlib import TopologicalSorter
from itertools import product
from pathlib import Path
import subprocess

from proofwriter_wm import exchange
from stochastic_inference_check import factor, ratio


def annotated(parse, statement):
    marker, name, atom, truth = parse(statement)
    if marker != ":":
        raise ValueError(f"Expected an annotated statement: {statement}")
    return name, atom, truth


def variable(atom, period):
    name, subject, time = atom
    if time != period or any(not isinstance(part, str) or part.startswith("$") for part in (name, subject)):
        raise ValueError(f"Expected a ground predicate and subject at {period}: {atom}")
    return name, subject


def rate(truth):
    tag, value, confidence = truth
    value = Fraction(value)
    if tag != "STV" or Fraction(confidence) != 1 or not 0 <= value <= 1:
        raise ValueError(f"Expected a declared exact conditional row: {truth}")
    return value


def dependencies(expression):
    if expression[0] == "Period" and expression[1:] == ["$t"]:
        return ()
    if expression[0] in ("And", "Or", "Not"):
        return tuple(dict.fromkeys(key for child in expression[1:] for key in dependencies(child)))
    return (variable(expression, "$t"),)


def condition(expression, assignment):
    head, *args = expression
    if head == "Period" and args == ["$t"]:
        return True
    if head == "And":
        return all(condition(child, assignment) for child in args)
    if head == "Or":
        return any(condition(child, assignment) for child in args)
    if head == "Not":
        child, = args
        return not condition(child, assignment)
    return assignment[variable(expression, "$t")]


class LeanProbeBackend:
    name = "lean-factors-learned-roots"
    replay_module = "Mettapedia/ProbabilityTheory/StochasticInference/JsonReplay.lean"

    def __init__(self):
        from probes import statements
        from supplynet.problog_backend import parse

        self.statements, self.parse = statements, parse
        self.process = None

    def begin(self, world, rates, history):
        self.rules = {}
        graph = TopologicalSorter()
        for text in self.statements.rules(world):
            _, implication, truth = annotated(self.parse, text)
            tag, body, head = implication
            ctv, given, otherwise = truth
            child = variable(head, "$t")
            if tag != "Implication" or ctv != "CTV" or child in self.rules:
                raise ValueError(f"Expected one two-sided mechanism per head: {text}")
            parents = dependencies(body)
            self.rules[child] = body, parents, rate(given), rate(otherwise)
            graph.add(child, *parents)
        self.order = list(graph.static_order())
        self.resolved = {}
        self.true, self.counts = Counter(), Counter()
        for period, observation in history:
            self.resolve(period, observation)
        root = Path(__file__).resolve().parents[1] / "lean/mettapedia"
        self.process = subprocess.Popen(["lake", "env", "lean", "-M", "8192", "--run", self.replay_module],
                                        cwd=root, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    def _facts(self, texts, period):
        facts = {}
        for text in texts:
            _, atom, truth = annotated(self.parse, text)
            if atom == ["Period", period] and rate(truth) == 1:
                continue
            key = variable(atom, period)
            value = rate(truth)
            if value not in (0, 1) or (key in facts and facts[key] != value):
                raise ValueError(f"Expected a consistent hard label: {text}")
            facts[key] = int(value)
        return facts

    def resolve(self, period, observation):
        statements = self.statements.observation_facts(observation)
        statements += self.statements.resolution_facts(period, observation)
        labels = self._facts(statements, period.name)
        if period.name in self.resolved:
            if self.resolved[period.name] != labels:
                raise ValueError(f"Conflicting resolved period {period.name}")
            return
        self.resolved[period.name] = labels
        self.true.update(labels)
        self.counts.update(labels.keys())

    def beliefs(self, observation, keys, budget):
        seen = self._facts(self.statements.observation_facts(observation), observation.period)
        queried = [variable(annotated(self.parse, self.statements.query(key))[1], observation.period)
                   for key in keys]
        names = list(dict.fromkeys([*self.order, *seen, *queried]))
        index = {name: i for i, name in enumerate(names)}
        base = []
        for name in names:
            if name not in self.rules:
                p = Fraction(self.true[name] + 1, self.counts[name] + 2)
                base.append(factor([index[name]], [1 - p, p]))
                continue
            body, parents, given, otherwise = self.rules[name]
            rows = []
            for values in product((False, True), repeat=len(parents)):
                p = given if condition(body, dict(zip(parents, values, strict=True))) else otherwise
                rows.extend([1 - p, p])
            base.append(factor([index[parent] for parent in parents] + [index[name]], rows))
        observations = [{"observe": {"id": "/".join((*name, observation.period)),
                                     "likelihood": factor([index[name]], [1 - value, value])}}
                        for name, value in seen.items()]
        queries = [{"probability": {"event": factor([index[name]], [0, 1])}} for name in queried]
        result = exchange(self.process, {"domains": [2] * len(names), "base": base,
                                         "operations": observations + queries})
        if not isinstance(result, list) or len(result) != len(observations) + len(queries):
            raise ValueError(f"Unexpected Lean reply: {result}")
        if any(reply != {"status": "recorded"} for reply in result[:len(observations)]):
            raise ValueError(f"Lean refused an observation: {result}")
        return {key: float(Fraction(*reply["value"]))
                for key, reply in zip(keys, result[len(observations):], strict=True)
                if reply["value"] is not None}

    def summary(self):
        return {"budgeted": False, "root_model": "Laplace from resolved labels"}

    def close(self):
        if self.process is not None:
            self.process.stdin.close()
            if self.process.wait() != 0:
                raise RuntimeError("The Lean evaluator failed")


class LeanPathBounds(LeanProbeBackend):
    """Anytime intervals for queried roots with disjoint observed paths.

    A transfer contracts one binary transition. Parsing and path discovery
    precede that budget. The round-robin order uses public paths only.
    """

    name = "lean-path-bounds-learned-roots"
    replay_module = "Mettapedia/Examples/PLN/DiagnosticPathReplay.lean"

    def begin(self, world, rates, history):
        super().begin(world, rates, history)
        self.transfers = 0
        for body, parents, given, otherwise in self.rules.values():
            if len(parents) != 1 or body != [*parents[0], "$t"] or not (0 < given < 1 and 0 < otherwise < 1):
                raise ValueError("Expected positive binary transitions along disjoint report paths")

    def beliefs(self, observation, keys, budget):
        from supplynet.game import Bounded

        roots = [variable(annotated(self.parse, self.statements.query(key))[1], observation.period)
                 for key in keys]
        if any(root in self.rules for root in roots):
            raise ValueError("Path intervals require a root query")
        seen = self._facts(self.statements.observation_facts(observation), observation.period)
        by_root = {root: [] for root in roots}
        owned = set()
        pending = deque()
        for terminal, reading in sorted(seen.items()):
            node = terminal
            scope, links = [], []
            while node in self.rules:
                scope.append(node)
                _, (parent,), given, otherwise = self.rules[node]
                links.append([ratio(otherwise), ratio(given)])
                node = parent
            if node not in by_root:
                continue
            if owned.intersection(scope):
                raise ValueError("Reports share a non-root variable")
            owned.update(scope)
            path = {"value": bool(reading), "links": links, "processed": 0}
            by_root[node].append(path)
            if links:
                pending.append(path)

        remaining = budget
        while remaining > 0 and pending:
            path = pending.popleft()
            path["processed"] += 1
            remaining -= 1
            if path["processed"] < len(path["links"]):
                pending.append(path)

        queries = [
            {"prior": ratio(Fraction(self.true[root] + 1, self.counts[root] + 2)),
             "reports": by_root[root]}
            for root in roots
        ]
        result = exchange(self.process, {"queries": queries, "budget": budget})
        if result.get("transfers") != budget - remaining or len(result.get("answers", [])) != len(keys):
            raise ValueError(f"Unexpected Lean path replay reply: {result}")
        self.transfers += result["transfers"]
        answers = {}
        for key, bounds in zip(keys, result["answers"], strict=True):
            if bounds is not None:
                lo, hi = (Fraction(*raw) for raw in bounds)
                answers[key] = Bounded((lo + hi) / 2, lo, hi)
        return answers

    def summary(self):
        return {"budgeted": True, "budget_unit": "binary likelihood transfer", "transfers": self.transfers,
                "root_model": "Laplace from resolved labels"}
