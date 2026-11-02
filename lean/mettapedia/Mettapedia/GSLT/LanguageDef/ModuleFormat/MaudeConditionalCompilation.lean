import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
import Mettapedia.Languages.Maude.ConditionalMax

/-! Conditional source equations use the existing typed relation-query
premises. A bounded snapshot is generated per input, with exact source
equality evidence for every numeral comparison it contains. The bound's
coverage and module import/canonical-form certificates remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def equationRule? (signature : Maude.Signature) (row : Maude.Row) (index : Nat) : Option RewriteRule := do
  let premises ← conditions? signature row
  if row.inputsBound then
    pure {
      name := "maude:conditional-equation:" ++ toString index ++ ":" ++ row.name
      typeContext := context row
      premises := premises
      left := encode row.left
      right := encode row.right }
  else none

def prepare (theory : Maude.Theory) : Except String LanguageDef := do
  unless theory.check do throw "the source theory is ill-sorted"
  unless theory.signature.operators.all (fun declaration => !declaration.attributes.associative &&
      !declaration.attributes.commutative && declaration.attributes.identity.isNone) do
    throw "the conditional stage requires a separately certified algebra profile"
  let some rules := theory.equations.zipIdx.mapM (fun (row, index) => equationRule? theory.signature row index)
    | throw "a source equation requires a stronger binding producer"
  let language : LanguageDef := {
    name := theory.name ++ ":conditional-equations"
    types := theory.signature.sorts.map TypeDecl.plain
    terms := theory.signature.operators.map operator
    equations := []
    rewrites := rules }
  unless language.validate.isEmpty do throw "the generated conditional stage is invalid"
  pure language

def trueRow (left right : Nat) : GeneralPremise.ProviderRow := {
  relation := equalityRelation "Bool"
  values := [encode (Maude.ConditionalMax.le (Maude.ConditionalMax.numeral left) (Maude.ConditionalMax.numeral right)),
    encode Maude.ConditionalMax.truth] }

def comparisonPairs (bound : Nat) : List (Nat × Nat) :=
  (List.range (bound + 1)).flatMap fun left =>
    ((List.range (bound + 1)).filter (fun right => decide (left ≤ right))).map fun right => (left, right)

def provider (bound : Nat) : GeneralPremise.ProviderSnapshot := {
  signatures := [⟨equalityRelation "Bool", [.base "Bool", .base "Bool"], [.input, .input]⟩]
  rows := (comparisonPairs bound).map fun pair => trueRow pair.1 pair.2 }

theorem comparisonPairs_iff (bound left right : Nat) :
    (left, right) ∈ comparisonPairs bound ↔ left ≤ bound ∧ right ≤ bound ∧ left ≤ right := by
  simp only [comparisonPairs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨first, firstWithin, second, ⟨secondWithin, ordered⟩, rfl, rfl⟩
    exact ⟨by omega, by omega, ordered⟩
  · rintro ⟨firstWithin, secondWithin, ordered⟩
    exact ⟨left, by omega, right, ⟨by omega, ordered⟩, rfl, rfl⟩

theorem comparison_source_equality (bound left right : Nat)
    (member : (left, right) ∈ comparisonPairs bound) :
    Maude.Equivalent Maude.Examples.conditional [] "Bool"
      (Maude.ConditionalMax.le (Maude.ConditionalMax.numeral left) (Maude.ConditionalMax.numeral right))
      Maude.ConditionalMax.truth := by
  have ordered := ((comparisonPairs_iff bound left right).mp member).2.2
  simpa only [if_pos ordered] using Maude.ConditionalMax.comparison_equivalent left right

def plan (language : LanguageDef) (bound : Nat) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile ⟨language, [], provider bound⟩
    {sites := .all, includeDerivedEquations := false}

#print axioms comparison_source_equality

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ConditionalCompilation
