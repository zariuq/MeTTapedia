#!/usr/bin/env python3
"""Untrusted bounded article producer for application-only first-order rules.

Rule variables are fresh for each invocation. Ordered premises can determine
variables absent from the conclusion. Explicit node seeds supply choices such
as theorem premises or substitutions. Only a separate checker grants authority;
exhaustion of this search budget establishes neither refusal nor completeness.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path


@dataclass(frozen=True)
class Variable:
    scope: int
    name: str


class BudgetExhausted(Exception):
    pass


def parse_pattern(value, variables):
    if isinstance(value, dict) and set(value) == {"var"}:
        return variables[value["var"]]
    if not (isinstance(value, list) and len(value) == 2
            and isinstance(value[0], str) and isinstance(value[1], list)):
        raise ValueError("expected an application or declared variable")
    return value[0], tuple(parse_pattern(child, variables) for child in value[1])


def walk(term, assignments):
    while isinstance(term, Variable) and term in assignments:
        term = assignments[term]
    return term


def occurs(variable, term, assignments):
    term = walk(term, assignments)
    return (term == variable if isinstance(term, Variable)
            else any(occurs(variable, child, assignments) for child in term[1]))


def unify(first, second, before):
    assignments = before.copy()
    pending = [(first, second)]
    while pending:
        left, right = (walk(term, assignments) for term in pending.pop())
        if left == right:
            continue
        if isinstance(left, Variable):
            if occurs(left, right, assignments):
                return None
            assignments[left] = right
        elif isinstance(right, Variable):
            pending.append((right, left))
        elif left[0] != right[0] or len(left[1]) != len(right[1]):
            return None
        else:
            pending.extend(zip(left[1], right[1]))
    return assignments


def ground(term, assignments):
    term = walk(term, assignments)
    if isinstance(term, Variable):
        raise ValueError(f"undetermined rule argument: {term.name}")
    return [term[0], [ground(child, assignments) for child in term[1]]]


class Search:
    def __init__(self, rules, budget, depth):
        if budget < 0 or depth < 0:
            raise ValueError("budgets must be nonnegative")
        self.rules = {rule["id"]: rule for rule in rules}
        if len(self.rules) != len(rules):
            raise ValueError("duplicate rule identifier")
        self.index = {}
        for rule in rules:
            if len(set(rule["vars"])) != len(rule["vars"]):
                raise ValueError("duplicate rule variable")
            variables = {name: Variable(0, name) for name in rule["vars"]}
            conclusion = parse_pattern(rule["conclusion"], variables)
            if isinstance(conclusion, Variable):
                raise ValueError("a judgment needs an application head")
            for premise in rule["premises"]:
                parse_pattern(premise, variables)
            self.index.setdefault(conclusion[0], []).append(rule)
        self.budget, self.depth = budget, depth
        self.attempts = 0
        self.scope = 0

    def solve(self, goal, assignments, depth, seed=None):
        if depth < 0:
            raise BudgetExhausted("depth")
        goal_head = walk(goal, assignments)
        if isinstance(goal_head, Variable):
            raise ValueError("undetermined judgment head")
        candidates = ([self.rules[seed["rule"]]] if seed is not None
                      else self.index.get(goal_head[0], []))
        for rule in candidates:
            if self.attempts >= self.budget:
                raise BudgetExhausted("attempts")
            self.attempts += 1
            self.scope += 1
            variables = {name: Variable(self.scope, name) for name in rule["vars"]}
            after = unify(parse_pattern(rule["conclusion"], variables), goal, assignments)
            if after is None:
                continue
            seeds = [None] * len(rule["premises"])
            if seed is not None:
                if len(seed["arguments"]) != len(rule["vars"]):
                    raise ValueError("seed argument arity")
                seeds = seed.get("children", seeds)
                if len(seeds) != len(rule["premises"]):
                    raise ValueError("seed premise arity")
                for name, argument in zip(rule["vars"], seed["arguments"]):
                    after = unify(variables[name], parse_pattern(argument, {}), after)
                    if after is None:
                        break
                if after is None:
                    continue
            premises = [parse_pattern(p, variables) for p in rule["premises"]]

            def children(index, state, articles):
                if index == len(premises):
                    yield articles, state
                    return
                for article, updated in self.solve(premises[index], state, depth - 1, seeds[index]):
                    yield from children(index + 1, updated, articles + [article])

            for proofs, final in children(0, after, []):
                yield (rule["id"], [variables[name] for name in rule["vars"]], proofs), final

    def first(self, goal, seed=None):
        def finish(tree, state):
            rule, arguments, children = tree
            return {"rule": rule, "arguments": [ground(a, state) for a in arguments],
                    "children": [finish(child, state) for child in children]}
        try:
            for tree, state in self.solve(parse_pattern(goal, {}), {}, self.depth, seed):
                try:
                    return {"status": "candidate", "article": finish(tree, state), "attempts": self.attempts}
                except ValueError:
                    continue
            return {"status": "no-candidate", "attempts": self.attempts}
        except BudgetExhausted as error:
            return {"status": "budget-exhausted", "limit": str(error), "attempts": self.attempts}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--budget", type=int, required=True)
    parser.add_argument("--depth", type=int, default=256)
    args = parser.parse_args()
    document = json.loads(args.input.read_text())
    results = []
    for request in document["requests"]:
        search = Search(document["rules"], args.budget, args.depth)
        result = search.first(request["goal"], request.get("seed"))
        result.update(name=request["name"], goal=request["goal"])
        results.append(result)
        print(request["name"], result["status"], result["attempts"], flush=True)
    args.output.write_text(json.dumps({"results": results}, ensure_ascii=False) + "\n")
    return 0 if all(r["status"] == "candidate" for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
