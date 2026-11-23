"""Export hand-derived certificate controls for an independent harness."""

from copy import deepcopy
from fractions import Fraction as Q
import argparse
import json
from pathlib import Path
import subprocess

from pln_anytime_credal import conjunction, event, interval, packet, pair
from pln_credal_certificates import linear_rows, pack_endpoint


def sharp(request, lower, upper):
    rows = linear_rows(request)
    request["certificates"] = [
        pack_endpoint(request, rows, sign, sign * value, list(map(Q, multipliers)),
                      list(map(Q, witness)))
        for sign, (value, multipliers, witness) in zip((1, -1), (lower, upper), strict=True)
    ]
    return request


def fixtures():
    certain = [True] * 8
    common, left, right = (event(8, bit) for bit in range(3))
    either = [a or b for a, b in zip(left, right, strict=True)]
    proof = conjunction(common, either)
    rows = [interval(premise, certain, Q(3, 4)) for premise in (common, left, right)]
    high_witness = [Q(1, 4), 0, 0, 0, 0, 0, 0, Q(3, 4)]
    shared = sharp(packet(rows, proof, certain, []),
                   (Q(1, 2), [1, 0, 1, 0, 0, 0], [0, Q(1, 4), 0, 0, 0, 0, Q(1, 4), Q(1, 2)]),
                   (Q(3, 4), [0, 1, 0, 0, 0, 0], high_witness))
    yield "shared_prerequisite", shared, {"sharp": [[1, 2], [3, 4]]}

    diagnosis = sharp(packet(rows, left, proof, []),
                      (Q(2, 3), [1, Q(2, 3), 1, 0, 0, 0], [0, 0, Q(1, 3), 0, 0, Q(1, 3), 0, Q(2, 3)]),
                      (Q(1), [0] * 6, [Q(1, 3), 0, 0, 0, 0, 0, 0, 1]))
    yield "alternative_given_proof", diagnosis, {"sharp": [[2, 3], [1, 1]]}

    condition, query = event(4, 0), event(4, 1)
    witness = [0, Q(1, 4), 0, Q(3, 4)]
    sometimes_null = sharp(packet([interval(query, condition, Q(3, 4))], query, condition, []),
                           (Q(3, 4), [1, 0], witness), (Q(3, 4), [0, 1], witness))
    yield "regular_conditioning", sometimes_null, {"sharp": [[3, 4], [3, 4]]}

    fact, all_worlds, empty = event(2, 0), [True] * 2, [False] * 2
    row = interval(fact, all_worlds, Q(0))
    unsupported = packet([row], empty, fact, [])
    unsupported["refutation"] = {
        "weights": [pair(Q(w)) for w in [0, 0, 0, 1, 0, 1, 0, 0]],
        "consistencyWitness": [[1, 1], [0, 1]],
    }
    yield "unsupported_evidence", unsupported, {"status": "unsupported"}

    inconsistent = packet([row, interval(fact, all_worlds, Q(1))], empty, all_worlds, [])
    inconsistent["refutation"] = {
        "weights": [pair(Q(w)) for w in [0, 0, 0, 1, 1, 0, 0, 1, 0, 0]],
    }
    yield "inconsistent_constraints", inconsistent, {"status": "inconsistent"}

    wrong_bound = deepcopy(shared)
    wrong_bound["certificates"][0]["value"] = [3, 5]
    yield "tampered_bound", wrong_bound, {"accepted": False}

    wrong_witness = deepcopy(diagnosis)
    wrong_witness["certificates"][0]["witness"][7] = [1, 3]
    yield "tampered_witness", wrong_witness, {"accepted": False}

    wrong_support = deepcopy(unsupported)
    wrong_support["refutation"]["consistencyWitness"] = [[0, 1], [1, 1]]
    yield "tampered_consistency_witness", wrong_support, {"accepted": False}


def check(cases):
    root = Path(__file__).resolve().parents[1] / "lean/mettapedia"
    cmd = ["lake", "env", "lean", "-M", "8192", "--run", "Mettapedia/Examples/PLN/AnytimeCredalReplay.lean"]
    output = subprocess.run(cmd, cwd=root, check=True, text=True, stdout=subprocess.PIPE,
                            input="".join(json.dumps(case["packet"]) + "\n" for case in cases))
    for case, line in zip(cases, output.stdout.splitlines(), strict=True):
        expected = case["expected"]
        actual = json.loads(line)
        if expected.get("accepted") is False:
            assert "error" in actual, case["name"]
        else:
            assert all(actual.get(key) == value for key, value in expected.items()), (case["name"], actual)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Replay all controls through Lean first")
    args = parser.parse_args()
    cases = [{"name": name, "packet": request, "expected": expected}
             for name, request, expected in fixtures()]
    if args.check:
        check(cases)
    print(json.dumps({"version": 1, "cases": cases}, indent=2))


if __name__ == "__main__":
    main()
