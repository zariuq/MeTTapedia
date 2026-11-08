import Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQuery

/-!
# Effective constant reads in the current intrinsic query owner

This is the executable leaf boundary used by constant admission: completed
singleton, non-Undefined replies only. The current query's primitive rule
precedes declaration lookup. Ordinary symbols instead read the complete
ordered, occurrence-fresh declaration list. It is not replaced by an
annotation oracle or by the older query-policy model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaEffectiveQueryLeaves

open Mettapedia.Logic.LP (unifyTotal)
open Mettapedia.Languages.MeTTa.PeTTa
open IntrinsicTypeFacts (TypeTerm Declaration named undefinedType primitiveType)
open IndependentTypeOutput (Supply Path Result row)

/-- Noncomplete queries decline admission, as do zero, multiple or
Undefined answers. This does not identify their source outcomes. -/
def completedSingleton : Result → Option TypeTerm
  | some [type] => if StableIntrinsicTypeQuery.isUndefined type then none else some type
  | _ => none

def effective (library : List Declaration) (supply : Supply) (fuel : Nat)
    (path : Path) (subject : TypeTerm) : Option TypeTerm :=
  completedSingleton (StableIntrinsicTypeQuery.run library supply fuel path subject none)

theorem accepted_is_complete_singleton (result : Result) (type : TypeTerm) :
    completedSingleton result = some type ↔
      result = some [type] ∧ StableIntrinsicTypeQuery.isUndefined type = false := by
  cases result with
  | none => simp [completedSingleton]
  | some replies =>
      cases replies with
      | nil => simp [completedSingleton]
      | cons first rest =>
          cases rest with
          | cons second tail => simp [completedSingleton]
          | nil =>
              cases undefined : StableIntrinsicTypeQuery.isUndefined first <;>
                simp_all [completedSingleton] <;> aesop

theorem actual_symbol_query (library : List Declaration) (supply : Supply)
    (fuel : Nat) (path : Path) (name : String) :
    StableIntrinsicTypeQuery.run library supply (fuel + 1) path (named name) none =
      some (let rows := IndependentTypeOutput.declarations library supply path (named name)
        if rows.isEmpty then [undefinedType] else rows) := by
  simp [StableIntrinsicTypeQuery.run, StableIntrinsicTypeQuery.step,
    StableIntrinsicTypeQuery.candidates, IndependentTypeOutput.isVariable,
    IndependentTypeOutput.literal, primitiveType, IndependentTypeOutput.elements,
    IndependentTypeOutput.select, named]

theorem actual_bool_query (library : List Declaration) (supply : Supply)
    (fuel : Nat) (path : Path) (value : Bool) :
    StableIntrinsicTypeQuery.run library supply (fuel + 1) path (.const (.boolean value)) none =
      some [named "Bool"] := by
  simp [StableIntrinsicTypeQuery.run, StableIntrinsicTypeQuery.step,
    StableIntrinsicTypeQuery.candidates, IndependentTypeOutput.isVariable,
    IndependentTypeOutput.literal, primitiveType, IndependentTypeOutput.select]

theorem effective_bool_ignores_authored_rows (library : List Declaration) (supply : Supply)
    (fuel : Nat) (path : Path) (value : Bool) :
    effective library supply (fuel + 1) path (.const (.boolean value)) = some (named "Bool") := by
  rw [effective, actual_bool_query]
  rfl

theorem actual_arrow_bool_mgu_rejected (fields : List TypeTerm) :
    unifyTotal [(row (named "->" :: fields), named "Bool")] = none := by
  rw [unifyTotal.eq_def (σ := IntrinsicTypeFacts.signature)]
  rfl

namespace Controls

def numberArrow : TypeTerm := row [named "->", named "Number", named "Number"]
def falseTruthRow : Declaration :=
  ⟨0, .symbol "true", row [named "->", .var 0, named "Number"]⟩

theorem ordinary_function_keeps_complete_effective_type :
    effective [⟨0, .symbol "inc", numberArrow⟩] IndependentTypeOutput.freshSupply 1 [] (named "inc") =
      some numberArrow := by
  cbv
  congr 2
  funext index
  fin_cases index <;> rfl

theorem authored_truth_arrow_cannot_replace_effective_bool :
    effective [falseTruthRow] IndependentTypeOutput.freshSupply 1 [] (.const (.boolean true)) =
      some (named "Bool") := effective_bool_ignores_authored_rows _ _ 0 _ _

theorem unfinished_empty_and_undefined_all_decline_admission :
    completedSingleton none = none ∧ completedSingleton (some []) = none ∧
      completedSingleton (some [undefinedType]) = none := by cbv

theorem ordered_overload_is_not_first_selected :
    effective [⟨0, .symbol "inc", numberArrow⟩, ⟨1, .symbol "inc", named "Bool"⟩]
      IndependentTypeOutput.freshSupply 1 [] (named "inc") = none := by cbv

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaEffectiveQueryLeaves
