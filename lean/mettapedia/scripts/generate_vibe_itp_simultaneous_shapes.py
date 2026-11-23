#!/usr/bin/env python3
"""Produce exact v2 schema instances using the existing restricted rule parser.

This untrusted producer does not establish rule soundness. Lean must check the
generated instance/intro lemmas and the separate specification-meaning proofs.
The original v1 generator, schemas and generated artifact remain unchanged.
"""
import argparse
from pathlib import Path

import generate_vibe_itp_rule_shapes as base


ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "Mettapedia/Languages/VibeITP/Presentation"
OUTPUT = OWNER / "SimultaneousRuleShapes.lean"


def generate():
    original = (OWNER / "Rules.lean").read_text()
    addition = (OWNER / "SimultaneousRules.lean").read_text()
    old_name = "def kernelRules : List FORule :="
    new_name = "def rulesV2 : List FORule := kernelRules ++ simultaneousRules"
    base.require(original.count(old_name) == 1 and addition.count(new_name) == 1,
                 "unexpected kernel package declarations")
    combined = original.replace(old_name, "def legacyKernelRules : List FORule :=") + "\n" + addition.replace(
        new_name, "def kernelRules : List FORule := legacyKernelRules ++ simultaneousRules")
    base.EXPECTED_NAMED = 128
    inventory = base.parse_inventory(combined, (OWNER / "Syntax.lean").read_text(),
                                     (OWNER.parent / "Spec/Basic.lean").read_text())
    names = inventory.groups["simultaneousRules"]
    base.require(len(names) == 16 and len(set(names)) == 16, "expected sixteen distinct v2 rules")
    output = ["""import Mettapedia.Languages.VibeITP.Presentation.SimultaneousRules
import Mettapedia.Languages.VibeITP.Presentation.Instances

/-! Exact v2 rule-instance shapes, generated from the actual schemas by
`scripts/generate_vibe_itp_simultaneous_shapes.py`. These are structural
instantiation and introduction laws, not specification soundness proofs. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
"""]
    declarations = base.declarations(addition)

    def helpers(expr):
        if isinstance(expr, str):
            return {expr} if expr in inventory.arities else set()
        if expr[0] == "mv":
            return set()
        found = {expr[0]}
        for child in expr[1:]:
            found |= helpers(child)
        return found

    def members(count):
        if not count:
            return "    simp only [List.not_mem_nil] at included\n"
        result = "    simp only [List.mem_cons, List.not_mem_nil, or_false] at included\n"
        if count == 1:
            return result + "    rcases included with rfl\n    assumption\n"
        return result + "    rcases included with " + " | ".join("rfl" for _ in range(count)) + " <;> assumption\n"

    for name in names:
        rule = inventory.rules[name]
        variables = [base.RENAMES.get(v, v) for v in rule.variables]
        arguments = "[" + ", ".join(variables) + "]"
        applied = " ".join(variables)
        parameters = f"({applied} : Pattern)" if variables else ""
        premises = [base.instantiate(p) for p in rule.premises]
        conclusion = base.parenthesized(base.instantiate(rule.conclusion))
        premise_list = "[" + ", ".join(base.render(p) for p in premises) + "]"
        unfolded = set().union(*(helpers(p) for p in (*rule.premises, rule.conclusion)))
        if unfolded & {"entryPattern", "pairPattern"}:
            unfolded |= {"cCons", "cNil"}
        if "fvarSym" in declarations[name].body:
            unfolded.add("fvarSym")
        simps = [name, "FORule.instPremises", "FORule.instConclusion", "FORule.bindings", "mkRule", "ab_apply"]
        if variables:
            simps += ["mv", "ab_fvar_hit"]
        if len(variables) > 1:
            simps.append("ab_fvar_miss")
        simps += sorted(unfolded)
        output.append(f"""theorem inst_{name} {parameters} :
    {name}.instPremises {arguments} = {premise_list} ∧
      {name}.instConclusion {arguments} = {conclusion} := by
  simp [{', '.join(simps)}]
""")
        implication = " → ".join("P " + base.parenthesized(p) for p in premises)
        if implication:
            implication += " → "
        quantifier = f"∀ {applied} : Pattern, " if variables else ""
        premise_args = " ".join("(premises _ (by simp))" for _ in premises)
        output.append(f"""theorem sound_{name} {{P : Pattern → Prop}}
    (sound : {quantifier}{implication}P {conclusion}) :
    ∀ args : List Pattern, args.length = {name}.vars.length →
      (∀ premise ∈ {name}.instPremises args, P premise) → P ({name}.instConclusion args) := by
  intro args length premises
  match args, length with
  | {arguments}, _ =>
      rw [(inst_{name} {applied}).1] at premises
      rw [(inst_{name} {applied}).2]
      exact sound {applied} {premise_args}
""")
        implicit = f"{{{applied} : Pattern}}" if variables else ""
        data = " ".join(f"(data_{v} : IsData {v})" for v in variables)
        hypotheses = " ".join(f"(premise{i} : FODerivable R {base.parenthesized(p)})"
                              for i, p in enumerate(premises))
        output.append(f"""theorem intro_{name} {{R : List FORule}} (member : {name} ∈ R) {implicit}
    {data} {hypotheses} : FODerivable R {conclusion} := by
  apply FODerivable.intro member {arguments} rfl
  · intro argument included
""" + members(len(variables)) + f"""  · exact (inst_{name} {applied}).2
  · rw [(inst_{name} {applied}).1]
    intro goal included
""" + members(len(premises)))
    output.append("end Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentation\n")
    return "\n".join(output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    options = parser.parse_args()
    generated = generate()
    if options.write:
        OUTPUT.write_text(generated)
    elif not OUTPUT.exists() or OUTPUT.read_text() != generated:
        raise SystemExit("simultaneous rule shapes differ from the current schemas")
    print("16 exact rule shapes generated" if options.write else "16 rule shapes match current schemas")
