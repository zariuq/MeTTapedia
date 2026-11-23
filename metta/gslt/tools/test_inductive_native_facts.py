#!/usr/bin/env python3
"""Refusal controls using a genuine completed native-fact qualification.

The retained gate is the positive control. Mutations test join mistakes that can
survive a simple process-success or theorem-count check. These controls do not
replace the native gates' altered-proof and failed-publication tests.
"""

import argparse
from copy import deepcopy
import json
from pathlib import Path

from qualify_inductive_native_facts import (validate_native_records, validate_hol_record,
                                            validate_megalodon_profile, MM0_ROOTS)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("qualification", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = json.loads(args.qualification.read_text())
    if report.get("qualified") is not True or report.get("m1_qualified") is not False:
        raise RuntimeError("expected a completed component gate with M1 still open")
    binary = Path(report["binary"])
    original = [report["mm0"]["evidence"], report["megalodon"]["evidence"],
                report["hol_light"]["evidence"], report["megalodon_profile"]]

    def validate(records, mm0_expected=None):
        validate_native_records(*records[:2], binary, report["binary_sha256"],
                                report["mm0"]["statements"] if mm0_expected is None else mm0_expected,
                                report["megalodon"]["statements"])
        validate_hol_record(records[2], binary, report["binary_sha256"], report["hol_light"]["statements"])
        profile = records[3]
        validate_megalodon_profile(profile["compiler"], profile["carrier"], profile["evidence"],
                                   binary, report["binary_sha256"], profile["statements"])
        if profile.get("default_kernel_axioms_added") != 0 or \
                profile.get("full_source_definition_history_refinement") is not False:
            raise RuntimeError("Megalodon profile scope differs")

    validate(original)
    cases = []

    def refusal(name, mutate, reason, expected_mutate=None):
        records = deepcopy(original)
        mutate(records)
        expected = deepcopy(report["mm0"]["statements"])
        if expected_mutate is not None:
            expected_mutate(expected)
        try:
            validate(records, expected)
        except RuntimeError as error:
            if reason not in str(error):
                raise RuntimeError(f"{name}: refused for an unrelated reason: {error}") from error
            cases.append(dict(case=name, refused=True, reason=str(error)))
        else:
            raise RuntimeError(f"{name}: invalid join accepted")

    refusal("different-binary", lambda rows: rows[0]["input_sha256"].update({str(binary): "0" * 64}),
            "different binary")
    refusal("missing-prime-mode", lambda rows: rows[0]["native"].pop(), "coverage")
    refusal("missing-result-despite-count", lambda rows: rows[0]["native"][0]["results"].pop(), "packets")
    refusal("changed-accepted-statement", lambda rows: rows[0]["native"][0]["results"][2].update(value="(thm (F))"),
            "statements differ")
    refusal("dropped-premise-inventory", lambda rows: rows[0]["upstream_proof_dependencies"].update(
                naturalClosureElimination=[]), "assumption inventory")
    refusal("source-axiom-added", lambda rows: rows[0].update(source_axioms_added=1), "source axioms")
    refusal("imported-megalodon-axiom", lambda rows: rows[1]["runs"][0].update(imported_axioms=1), "coverage")
    refusal("different-recursion-theorem", lambda rows: rows[1]["roots"].update(nrRecursion="0" * 64),
            "identity differs")
    refusal("missing-megalodon-mode", lambda rows: rows[1]["runs"].pop(), "coverage")
    refusal("induction-renamed-elimination", lambda rows: rows[0]["upstream_proof_dependencies"].update(
                naturalClosureInduction=rows[0]["upstream_proof_dependencies"].pop("naturalClosureElimination")),
            "assumption inventory")
    refusal("ordinary-closure-profile", lambda rows: rows[0].update(
                profile="HOL natural closure: zero, successor, elimination"), "recursion profile")
    refusal("missing-induction-root", lambda rows: rows[0]["upstream_proof_dependencies"].pop(
                "naturalClosureInduction"), "assumption inventory")
    refusal("elimination-substituted-for-induction", lambda rows: rows[0]["native"][0]["results"][5].update(
                value=report["mm0"]["statements"]["naturalClosureElimination"]), "statements differ")

    def omit_induction_membership(rows):
        statement = rows[0]["native"][0]["results"][5]["value"]
        premise = " (im G (thm (naturalClosure A z s n)))"
        if statement.count(premise) != 1:
            raise RuntimeError("expected exactly one induction membership premise")
        rows[0]["native"][0]["results"][5]["value"] = statement.replace(premise, "", 1)

    refusal("induction-membership-omitted", omit_induction_membership, "statements differ")

    def revert_equality_index(rows):
        declaration = rows[0]["native"][0]["results"][2 + len(MM0_ROOTS)]["value"]
        index = "(eqc (tydef P)"
        if declaration.count(index) != 1:
            raise RuntimeError("expected exactly one defined-type equality index")
        rows[0]["native"][0]["results"][2 + len(MM0_ROOTS)]["value"] = declaration.replace(index, "(eqc A", 1)

    refusal("reverted-equality-index", revert_equality_index, "type-definition declaration differs")
    refusal("missing-type-definition-reference-refusal", lambda rows: rows[0]["reference_checks"].pop(4),
            "independent-reference coverage")
    refusal("reverted-type-definition-accepted", lambda rows: rows[0]["reference_checks"][4].update(
                returncode=0), "independent-reference coverage")
    refusal("missing-mm0-recursion-root", lambda rows: rows[0]["upstream_proof_dependencies"].pop(
                "holNaturalRecursion"), "assumption inventory")
    refusal("missing-mm0-constructor-separation", lambda rows: rows[0]["upstream_proof_dependencies"].pop(
                "holZeroNotSuccessor"), "assumption inventory")
    refusal("changed-mm0-recursion-statement", lambda rows: rows[0]["native"][0]["results"][
                2 + MM0_ROOTS.index("holNaturalRecursion")].update(value="(thm (F))"), "statements differ")
    refusal("missing-mm0-graph-refusal", lambda rows: rows[0]["reference_checks"].pop(),
            "independent-reference coverage")
    refusal("lost-mm0-infinity-dependency", lambda rows: rows[0]["upstream_proof_dependencies"][
                "holNaturalRecursion"].remove("inf"), "assumption scope")

    def reverse_recursion_arguments(rows):
        entry = rows[0]["native"][0]["results"][2 + MM0_ROOTS.index("holNaturalRecursion")]
        original = "(app (app f (app g n)) n)"
        if entry["value"].count(original) != 1:
            raise RuntimeError("expected exactly one primitive-recursion method call")
        entry["value"] = entry["value"].replace(original, "(app (app f n) (app g n))", 1)

    refusal("reversed-mm0-recursion-arguments", reverse_recursion_arguments, "statements differ")
    refusal("mm0-other-authored-carrier", lambda _: None, "authored interpretation",
            lambda expected: expected.update(authored_meaning="UnrelatedModel.all_models"))
    refusal("mm0-graph-comparison-omitted", lambda _: None, "authored interpretation",
            lambda expected: expected.pop("authored_graph_meaning"))
    refusal("mm0-selection-law-erased", lambda _: None, "authored interpretation",
            lambda expected: expected.update(meaning_scope="all models; arbitrary selection"))
    refusal("hol-different-binary", lambda rows: rows[2].update(binary_sha256="0" * 64), "different binary")
    refusal("hol-missing-carrier-infinity", lambda rows: rows[2]["roots"].pop(), "root inventory")
    refusal("hol-altered-typed-statement", lambda rows: rows[2]["roots"][0].update(statement="(thm () F)"),
            "typed statements")
    refusal("hol-primitive-infinity-substituted", lambda rows: rows[2]["roots"][-1].update(name="INFINITY_AX"),
            "root inventory")
    refusal("hol-repeated-assumption", lambda rows: rows[2]["source_axiom_nodes"].__setitem__(
                0, rows[2]["source_axiom_nodes"][1]), "assumption inventory")
    refusal("hol-extra-assumption", lambda rows: rows[2].update(source_axioms_added=1), "assumption inventory")
    refusal("hol-other-carrier", lambda rows: rows[2].update(meaning="UnrelatedModel.all_models"), "authored meaning")
    refusal("hol-missing-refusal-coverage", lambda rows: rows[2].update(native_refusals=2), "refusal coverage")
    refusal("hol-overclaimed-history", lambda rows: rows[2].update(full_source_definition_history_refinement=True),
            "definition-history")
    refusal("hol-component-claimed-m1", lambda rows: rows[2].update(m1_qualified=True), "component scope")
    refusal("megalodon-profile-missing-choice-option",
            lambda rows: rows[3]["evidence"]["selected_axioms"].pop(0),
            "optional theory qualification")
    refusal("megalodon-profile-claimed-m1",
            lambda rows: rows[3]["evidence"].update(m1_qualified=True),
            "optional theory qualification")
    refusal("megalodon-profile-missing-refusal",
            lambda rows: rows[3]["evidence"].update(refusal_controls=3),
            "optional theory qualification")
    refusal("megalodon-carrier-imported-axiom",
            lambda rows: rows[3]["carrier"].update(imported_axioms=1),
            "carrier qualification")
    refusal("megalodon-profile-default-axioms",
            lambda rows: rows[3].update(default_kernel_axioms_added=3),
            "profile scope")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(qualified=True, positive_controls=1,
                                         negative_controls=cases, m1_qualified=False), indent=2) + "\n")
    print(f"Native join: one genuine positive control and {len(cases)} refusals passed; M1 remains open.")


if __name__ == "__main__":
    main()
