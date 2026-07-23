#!/usr/bin/env python3
"""Generate and independently verify the compact program-discovery fixture."""

from __future__ import annotations

import argparse
import json
import sqlite3
import sys
from pathlib import Path
from typing import Any


SCHEMA = "oeis.program_discovery_conformance.v1"
PREFIX_PROGRAM_IDS = (
    "070cb36bbc3b3c1eae4d327b2d16007e95b9ebb01cadde574f66c35f3c276229",
    "0491610c80689e9d35f410a1767c85b3610957b02ad1f50ca964dc43533f0d61",
)
MULTI_TARGET_PROGRAM_ID = (
    "0720af3f484b690b7aeb61fabdbd20a6ce3caad8898b0b495558ad8b38ade763"
)
PARETO_SOURCE = "ac-nmt-n5-v5/world1/generation-2/feedback"
PARETO_TARGET = 34
COMPLEMENTARITY_TARGET = 42


class FixtureError(ValueError):
    pass


def _one(connection: sqlite3.Connection, query: str, parameters: tuple[Any, ...]) -> sqlite3.Row:
    row = connection.execute(query, parameters).fetchone()
    if row is None:
        raise FixtureError(f"fixture query returned no row: {query}")
    return row


def _program(connection: sqlite3.Connection, program_id: str) -> dict[str, Any]:
    row = _one(
        connection,
        "SELECT program_id,tokens_json,token_count FROM programs WHERE program_id=?",
        (program_id,),
    )
    return {
        "program_id": row["program_id"],
        "tokens": json.loads(row["tokens_json"]),
        "token_count": row["token_count"],
    }


def _observation(connection: sqlite3.Connection, program_id: str) -> dict[str, Any]:
    row = _one(
        connection,
        """
        SELECT observation_id,program_id,token_count,checker_runtime_units
        FROM observations
        WHERE logical_artifact_id=? AND anum=? AND program_id=?
        """,
        (PARETO_SOURCE, PARETO_TARGET, program_id),
    )
    return {
        "observation_id": row["observation_id"],
        "program_id": row["program_id"],
        "token_count": row["token_count"],
        "runtime": row["checker_runtime_units"],
    }


def build_fixture(corpus: Path, harness_root: Path) -> dict[str, Any]:
    sys.path.insert(0, str(harness_root))
    from oeis_pc_harness.dsl import eval_prefix, parse_program  # type: ignore[import-not-found]

    connection = sqlite3.connect(corpus)
    connection.row_factory = sqlite3.Row
    try:
        metadata = {
            row["key"]: row["value"]
            for row in connection.execute("SELECT key,value FROM metadata ORDER BY key")
        }
        if metadata.get("schema") != "oeis.program_corpus.sqlite.v1":
            raise FixtureError("unexpected program-corpus schema")

        shortest_rows = connection.execute(
            """
            SELECT program_id FROM observations
            WHERE logical_artifact_id=? AND anum=? AND is_shortest_exact=1
            ORDER BY program_id LIMIT 2
            """,
            (PARETO_SOURCE, PARETO_TARGET),
        ).fetchall()
        if len(shortest_rows) != 2:
            raise FixtureError("expected two authenticated shortest programs")
        same_target_programs = [
            _program(connection, str(row["program_id"])) for row in shortest_rows
        ]

        multi = _program(connection, MULTI_TARGET_PROGRAM_ID)
        multi_targets = [
            int(row["anum"])
            for row in connection.execute(
                "SELECT anum FROM program_sequence_edges WHERE program_id=? ORDER BY anum LIMIT 2",
                (MULTI_TARGET_PROGRAM_ID,),
            )
        ]
        if len(multi_targets) != 2:
            raise FixtureError("expected the broad program to cover two targets")

        shortest = _observation(connection, same_target_programs[0]["program_id"])
        fastest_id = str(
            _one(
                connection,
                """
                SELECT program_id FROM observations
                WHERE logical_artifact_id=? AND anum=? AND is_fastest_measured=1
                ORDER BY program_id LIMIT 1
                """,
                (PARETO_SOURCE, PARETO_TARGET),
            )["program_id"]
        )
        fastest = _observation(connection, fastest_id)
        pareto = [shortest, fastest]

        prefix_programs = [_program(connection, program_id) for program_id in PREFIX_PROGRAM_IDS]
        prefix_outputs = [
            eval_prefix(parse_program(program["tokens"]), 6, timeincr=100_000)
            for program in prefix_programs
        ]

        family_programs: dict[str, list[str]] = {}
        for row in connection.execute(
            """
            SELECT model_family,program_id FROM observations WHERE anum=?
            GROUP BY model_family,program_id ORDER BY model_family,program_id
            """,
            (COMPLEMENTARITY_TARGET,),
        ):
            family_programs.setdefault(str(row["model_family"]), []).append(
                str(row["program_id"])
            )
        required_families = [
            "ac-nmt-scaled-luong-bilstm",
            "tgad",
            "tree-neural-network",
        ]
        if sorted(family_programs) != sorted(required_families):
            raise FixtureError("unexpected family set at the complementarity target")
        ac = set(family_programs[required_families[0]])
        tgad = set(family_programs[required_families[1]])
        tree = set(family_programs[required_families[2]])

        repeated_id = shortest["observation_id"]
        fixture = {
            "schema": SCHEMA,
            "corpus_metadata": metadata,
            "two_programs_one_target": {
                "target": PARETO_TARGET,
                "programs": same_target_programs,
            },
            "one_program_two_targets": {
                "program": multi,
                "targets": multi_targets,
            },
            "exact_repetition": {
                "authenticated_observation_id": repeated_id,
                "occurrences": [repeated_id, repeated_id],
                "occurrence_count": 2,
                "distinct_observation_count": 1,
            },
            "shortest_fastest_disagreement": {
                "target": PARETO_TARGET,
                "source_lineage": PARETO_SOURCE,
                "shortest": shortest,
                "fastest": fastest,
            },
            "pareto_frontier": {
                "target": PARETO_TARGET,
                "members": pareto,
            },
            "finite_prefix_divergence": {
                "agreement_length": 4,
                "left": {**prefix_programs[0], "outputs": prefix_outputs[0]},
                "right": {**prefix_programs[1], "outputs": prefix_outputs[1]},
            },
            "family_complementarity": {
                "target": COMPLEMENTARITY_TARGET,
                "families": [
                    {
                        "name": name,
                        "target_coverage": 1,
                        "program_ids": family_programs[name],
                    }
                    for name in required_families
                ],
                "ac_plus_tgad_witness_union": len(ac | tgad),
                "ac_plus_tree_witness_union": len(ac | tree),
            },
        }
        validate_fixture(fixture)
        return fixture
    finally:
        connection.close()


def validate_fixture(value: dict[str, Any]) -> None:
    if value.get("schema") != SCHEMA:
        raise FixtureError("fixture schema mismatch")

    same_target = value["two_programs_one_target"]
    same_target_ids = [program["program_id"] for program in same_target["programs"]]
    if len(same_target_ids) != 2 or len(set(same_target_ids)) != 2:
        raise FixtureError("two-program fixture lost syntactic diversity")

    multi = value["one_program_two_targets"]
    if len(set(multi["targets"])) < 2:
        raise FixtureError("multi-target fixture lost target diversity")

    repeat = value["exact_repetition"]
    if len(repeat["occurrences"]) != repeat["occurrence_count"]:
        raise FixtureError("repetition occurrence count mismatch")
    if len(set(repeat["occurrences"])) != repeat["distinct_observation_count"]:
        raise FixtureError("repetition distinct count mismatch")

    disagreement = value["shortest_fastest_disagreement"]
    shortest = disagreement["shortest"]
    fastest = disagreement["fastest"]
    if not (
        shortest["program_id"] != fastest["program_id"]
        and shortest["token_count"] < fastest["token_count"]
        and shortest["runtime"] > fastest["runtime"]
    ):
        raise FixtureError("shortest/fastest disagreement is not strict")

    pareto = value["pareto_frontier"]["members"]
    if len(pareto) < 2:
        raise FixtureError("Pareto frontier is trivial")
    for left in pareto:
        for right in pareto:
            dominates = (
                right["token_count"] <= left["token_count"]
                and right["runtime"] <= left["runtime"]
                and (
                    right["token_count"] < left["token_count"]
                    or right["runtime"] < left["runtime"]
                )
            )
            if dominates:
                raise FixtureError("stored Pareto member is dominated")

    divergence = value["finite_prefix_divergence"]
    length = divergence["agreement_length"]
    left_outputs = divergence["left"]["outputs"]
    right_outputs = divergence["right"]["outputs"]
    if left_outputs[:length] != right_outputs[:length] or left_outputs == right_outputs:
        raise FixtureError("prefix fixture does not agree then diverge")

    complementarity = value["family_complementarity"]
    if {family["target_coverage"] for family in complementarity["families"]} != {1}:
        raise FixtureError("model-family target coverages differ")
    if complementarity["ac_plus_tgad_witness_union"] == complementarity["ac_plus_tree_witness_union"]:
        raise FixtureError("model-family witness unions do not differ")


def canonical_json(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--corpus", type=Path)
    parser.add_argument("--harness-root", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--verify", action="store_true")
    arguments = parser.parse_args()

    if arguments.verify:
        value = json.loads(arguments.output.read_text(encoding="utf-8"))
        validate_fixture(value)
        print(f"PASS {arguments.output}")
        return 0

    if arguments.corpus is None or arguments.harness_root is None:
        parser.error("--corpus and --harness-root are required when generating")
    expected = canonical_json(build_fixture(arguments.corpus, arguments.harness_root))
    if arguments.output.exists() and arguments.output.read_text(encoding="utf-8") != expected:
        raise FixtureError("refusing to overwrite a non-matching fixture")
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(expected, encoding="utf-8")
    print(f"PASS {arguments.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
