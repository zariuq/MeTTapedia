import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeAlgebraRows

/-! Commutativity swaps equal-domain arguments while retaining the result
sort. Associativity and an identity require the stronger closed-operation
shape. The generated equation uses domain-sorted variables. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCommutativeSortControls

open Mettapedia.Languages
open MaudeCompilation

def first : Maude.Operator := ⟨"first", "a", [], "S", {constructor := true}⟩
def second : Maude.Operator := ⟨"second", "b", [], "S", {constructor := true}⟩
def operation : Maude.Operator := ⟨"operation", "f", ["S", "S"], "T", {commutative := true}⟩
def signature : Maude.Signature := ⟨["S", "T"], [first, second, operation]⟩
def theory : Maude.Theory := ⟨"CommutativeDifferentResult", signature, [], []⟩

#guard signature.check
#guard theory.check
#guard (prepare theory).isOk
#guard (algebraRows operation).all (fun (_, row) => row.check signature)
#guard (algebraRows operation).all (fun (_, row) => row.formals == [("maude:axiom:X", "S"), ("maude:axiom:Y", "S")])
#guard !({signature with operators := [first, second, {operation with arguments := ["S", "T"]}]} : Maude.Signature).check
#guard !({signature with operators := [first, second, {operation with attributes := {associative := true}}]} : Maude.Signature).check
#guard !({signature with operators := [first, second,
  {operation with attributes := {identity := some (.app first.id [])}}]} : Maude.Signature).check

private theorem first_sorted : Maude.HasSort signature [] (.app first.id []) "S" :=
  .app (by simp [signature]) .nil

private theorem second_sorted : Maude.HasSort signature [] (.app second.id []) "S" :=
  .app (by simp [signature]) .nil

theorem commutative_different_result : Maude.Equivalent theory [] "T"
    (.app operation.id [.app first.id [], .app second.id []])
    (.app operation.id [.app second.id [], .app first.id []]) := by
  apply Maude.Equivalent.algebra
  exact ⟨.commutative (by simp [theory, signature]) rfl,
    .app (by simp [theory, signature]) (.cons first_sorted (.cons second_sorted .nil)),
    .app (by simp [theory, signature]) (.cons second_sorted (.cons first_sorted .nil))⟩

#print axioms commutative_different_result

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCommutativeSortControls
