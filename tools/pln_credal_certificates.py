"""Pack exact endpoint certificates for the Lean conditional-interval replay."""

from fractions import Fraction as Q

from pln_anytime_credal import conjunction, pair


def linear_rows(request):
    rows = []
    for reading in request["constraints"]:
        condition = reading["condition"]
        joint = conjunction(reading["event"], condition)
        lo, hi = Q(*reading["lower"]), Q(*reading["upper"])
        rows.append([lo * c - j for c, j in zip(condition, joint, strict=True)])
        rows.append([j - hi * c for c, j in zip(condition, joint, strict=True)])
    return rows


def pack_endpoint(request, rows, direction, beta, multipliers, witness):
    support = request["evidence"]
    objective = [direction * bit for bit in conjunction(request["query"], support)]
    # The remaining world coefficients are canceled by the nonnegativity rows.
    reduced_costs = [
        c - beta * s + sum(a * row[i] for a, row in zip(multipliers, rows, strict=True))
        for i, (c, s) in enumerate(zip(objective, support, strict=True))
    ]
    # Row order matches scaledAtoms. The two equality pairs are evidence
    # normalization and the query coordinate, in that order.
    weights = [*reduced_costs, *multipliers, max(-beta, Q(0)), max(beta, Q(0)),
               Q(direction < 0), Q(direction > 0)]
    return {"value": pair(direction * beta), "weights": list(map(pair, weights)),
            "witness": list(map(pair, witness))}
