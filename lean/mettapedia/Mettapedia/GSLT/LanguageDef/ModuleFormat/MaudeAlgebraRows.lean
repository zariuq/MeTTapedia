import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
import Mettapedia.Languages.Maude.Substitution

/-! The algebra row producer is checked against the independent raw source schemas.
Its rows preserve the selected declaration and the whole ground unit term.
Typed instances require the source sorting evidence. This is schema correspondence, not an executable normalizer or an
equation termination/coherence certificate. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation

open Mettapedia.Languages

theorem unit_ground_of_signature_check {signature : Maude.Signature} (valid : signature.check = true)
    {declaration : Maude.Operator} (member : declaration ∈ signature.operators)
    {unit : Maude.Term} (selected : declaration.attributes.identity = some unit) : unit.variables = [] := by
  simp only [Maude.Signature.check, Bool.and_eq_true, List.all_eq_true] at valid
  have formed := valid.2 declaration member
  rw [selected] at formed
  simp only [Bool.and_eq_true] at formed
  exact List.isEmpty_iff.mp formed.2.1.1

theorem algebraRows_sound {signature : Maude.Signature} (valid : signature.check = true)
    {declaration : Maude.Operator} (declared : declaration ∈ signature.operators)
    {law : AlgebraLaw} {row : Maude.Row} (produced : (law, row) ∈ algebraRows declaration)
    (assignment : Maude.Valuation) :
    Maude.AlgebraSchema signature (row.left.substitute assignment) (row.right.substitute assignment) := by
  cases law <;>
    by_cases associative : declaration.attributes.associative = true <;>
    by_cases commutative : declaration.attributes.commutative = true <;>
      cases selected : declaration.attributes.identity with
      | none =>
          simp [algebraRows, associative, commutative, selected] at produced
          all_goals
            subst row
            simp only [Maude.Term.substitute, List.map_cons, List.map_nil]
            first
            | exact .associative declared associative
            | exact .commutative declared commutative
      | some unit =>
          have unchanged := Maude.Term.substitute_ground assignment unit
            (unit_ground_of_signature_check valid declared selected)
          simp [algebraRows, associative, commutative, selected] at produced
          all_goals
            subst row
            simp only [Maude.Term.substitute, List.map_cons, List.map_nil]
            try rw [unchanged]
            first
            | exact .associative declared associative
            | exact .commutative declared commutative
            | exact .leftUnit declared selected
            | exact .rightUnit declared selected

private def assign (first second third : Maude.Term) : Maude.Valuation := fun name =>
  if name = "maude:axiom:X" then first else if name = "maude:axiom:Y" then second else
    if name = "maude:axiom:Z" then third else .var name

theorem algebraRows_cover {signature : Maude.Signature} (valid : signature.check = true)
    {left right : Maude.Term} (step : Maude.AlgebraSchema signature left right) :
    ∃ declaration ∈ signature.operators, ∃ law row assignment,
      (law, row) ∈ algebraRows declaration ∧ row.left.substitute assignment = left ∧
        row.right.substitute assignment = right := by
  cases step with
  | @associative declaration first second third declared associative =>
      let row : Maude.Row := ⟨declaration.id ++ ":assoc",
        [("maude:axiom:X", declaration.result), ("maude:axiom:Y", declaration.result), ("maude:axiom:Z", declaration.result)], [],
        .app declaration.id [.app declaration.id [.var "maude:axiom:X", .var "maude:axiom:Y"], .var "maude:axiom:Z"],
        .app declaration.id [.var "maude:axiom:X", .app declaration.id [.var "maude:axiom:Y", .var "maude:axiom:Z"]]⟩
      refine ⟨declaration, declared, .associative, row, assign first second third, ?_, ?_, ?_⟩
      · by_cases commutative : declaration.attributes.commutative = true <;>
          cases selected : declaration.attributes.identity <;>
            simp [algebraRows, associative, commutative, selected, row]
      · simp [row, Maude.Term.substitute, assign]
      · simp [row, Maude.Term.substitute, assign]
  | @commutative declaration first second declared commutative =>
      let row : Maude.Row := ⟨declaration.id ++ ":comm",
        [("maude:axiom:X", declaration.arguments.headD declaration.result),
         ("maude:axiom:Y", declaration.arguments.headD declaration.result)], [],
        .app declaration.id [.var "maude:axiom:X", .var "maude:axiom:Y"],
        .app declaration.id [.var "maude:axiom:Y", .var "maude:axiom:X"]⟩
      refine ⟨declaration, declared, .commutative, row, assign first second second, ?_, ?_, ?_⟩
      · by_cases associative : declaration.attributes.associative = true <;>
          cases selected : declaration.attributes.identity <;>
            simp [algebraRows, associative, commutative, selected, row]
      · simp [row, Maude.Term.substitute, assign]
      · simp [row, Maude.Term.substitute, assign]
  | @leftUnit declaration unit _ declared selected =>
      let row : Maude.Row := ⟨declaration.id ++ ":left-unit", [("maude:axiom:X", declaration.result)], [],
        .app declaration.id [unit, .var "maude:axiom:X"], .var "maude:axiom:X"⟩
      have unchanged := Maude.Term.substitute_ground (assign right right right) unit
        (unit_ground_of_signature_check valid declared selected)
      refine ⟨declaration, declared, .leftUnit, row, assign right right right, ?_, ?_, ?_⟩
      · by_cases associative : declaration.attributes.associative = true <;>
          by_cases commutative : declaration.attributes.commutative = true <;>
            simp [algebraRows, associative, commutative, selected, row]
      · simp [row, Maude.Term.substitute, assign, unchanged]
      · simp [row, Maude.Term.substitute, assign]
  | @rightUnit declaration unit _ declared selected =>
      let row : Maude.Row := ⟨declaration.id ++ ":right-unit", [("maude:axiom:X", declaration.result)], [],
        .app declaration.id [.var "maude:axiom:X", unit], .var "maude:axiom:X"⟩
      have unchanged := Maude.Term.substitute_ground (assign right right right) unit
        (unit_ground_of_signature_check valid declared selected)
      refine ⟨declaration, declared, .rightUnit, row, assign right right right, ?_, ?_, ?_⟩
      · by_cases associative : declaration.attributes.associative = true <;>
          by_cases commutative : declaration.attributes.commutative = true <;>
            simp [algebraRows, associative, commutative, selected, row]
      · simp [row, Maude.Term.substitute, assign, unchanged]
      · simp [row, Maude.Term.substitute, assign]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
