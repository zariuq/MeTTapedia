import Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQueryCompletion
import Mettapedia.Logic.LP.ConjunctiveUnification

/-!
# Queries of ground uninterpreted data

Admission is local to the symbols actually present in the value. Unrelated
overloaded declarations are permitted. The structural schema below is used
only under `GroundUninterpreted`; it is not a typing rule for open terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StableGroundTypeQueries

open Mettapedia.Logic.LP
open IntrinsicTypeFacts (Scalar signature TypeTerm Declaration named primitiveType undefinedType)
open IndependentTypeOutput (Path Supply Query row freshRows freshSupply declarations collect)
open StableIntrinsicTypeQuery (run step candidates functions)

def GroundUninterpreted (library : List Declaration) : TypeTerm → Prop
  | .var _ => False
  | .const (.symbol name) => ∀ declaration ∈ library, declaration.subject ≠ .symbol name
  | .const _ => True
  | .app _ children => ∀ index, GroundUninterpreted library (children index)

def groundSchema : TypeTerm → TypeTerm
  | .var name => .var name
  | .const scalar => (primitiveType scalar).getD undefinedType
  | .app arity children => .app arity (fun index => groundSchema (children index))

theorem admitted_is_ground (library : List Declaration) (value : TypeTerm)
    (admitted : GroundUninterpreted library value) : value.isGround := by
  induction value with
  | var name => exact admitted.elim
  | const scalar => trivial
  | app arity children ih => exact fun index => ih index (admitted index)

theorem schema_is_ground (library : List Declaration) (value : TypeTerm)
    (admitted : GroundUninterpreted library value) : (groundSchema value).isGround := by
  induction value with
  | var name => exact admitted.elim
  | const scalar => cases scalar <;> trivial
  | app arity children ih => exact fun index => ih index (admitted index)

theorem no_head_declarations (library : List Declaration) (supply : Supply) (path : Path)
    (value : TypeTerm) (admitted : GroundUninterpreted library value) :
    declarations library supply path value = [] := by
  cases value with
  | var name => exact admitted.elim
  | app arity children => rfl
  | const scalar =>
    cases scalar with
    | number _ | string _ | boolean _ => rfl
    | symbol name =>
      apply List.flatMap_eq_nil_iff.mpr
      intro declaration present
      simp [admitted declaration present]

theorem no_function_derivations (library : List Declaration) (supply : Supply) (query : Query)
    (path : Path) (values : List TypeTerm) (required : Option TypeTerm)
    (admitted : ∀ value ∈ values, GroundUninterpreted library value) :
    functions library supply query path values required = some [] := by
  cases values with
  | nil => rfl
  | cons first rest =>
    simp only [functions, no_head_declarations library supply path first (admitted first (by simp)), collect]

theorem freshRows_singleton (query : Query) (path : Path) (position : Nat) (values : List TypeTerm)
    (children : ∀ value ∈ values, ∀ index,
      query (0 :: index :: path) value none = some [groundSchema value]) :
    freshRows query path position values = some [values.map groundSchema] := by
  induction values generalizing position with
  | nil => rfl
  | cons first rest ih =>
    simp [freshRows, children first (by simp) position,
      ih (position + 1) (fun value member index => children value (List.mem_cons_of_mem _ member) index)]

theorem row_map_ofFn (arity : Nat) (children : Fin arity → TypeTerm) :
    row ((List.ofFn children).map groundSchema) = .app arity (fun index => groundSchema (children index)) := by
  simp only [row, List.length_map, List.length_ofFn, Term.app.injEq, true_and]
  apply (Fin.heq_fun_iff (by simp)).mpr
  intro index
  simp

/-- A sufficient source-size budget produces exactly one actual type, in
the presence of arbitrary declarations outside the value's symbol support. -/
theorem fresh_singleton (library : List Declaration) (supply : Supply) (fuel : Nat) :
    ∀ (path : Path) (value : TypeTerm), GroundUninterpreted library value → value.size ≤ fuel →
      run library supply fuel path value none = some [groundSchema value] := by
  induction fuel with
  | zero =>
    intro path value _ enough
    have positive := value.size_pos
    omega
  | succ fuel ih =>
    intro path value admitted enough
    cases value with
    | var name => exact admitted.elim
    | const scalar =>
      cases scalar with
      | number text | string text | boolean text =>
        simp [run, StableIntrinsicTypeQuery.step, candidates, IndependentTypeOutput.isVariable, IndependentTypeOutput.literal,
          primitiveType, IndependentTypeOutput.select, groundSchema]
      | symbol name =>
        have empty := no_head_declarations library supply path (.const (.symbol name)) admitted
        simp [run, StableIntrinsicTypeQuery.step, candidates, IndependentTypeOutput.isVariable, IndependentTypeOutput.literal,
          primitiveType, IndependentTypeOutput.elements, empty, IndependentTypeOutput.select, groundSchema]
    | app arity children =>
      have each : ∀ value ∈ List.ofFn children, GroundUninterpreted library value := by
        intro value member
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
        exact admitted index
      have computed : freshRows (run library supply fuel) (4 :: path) 0 (List.ofFn children) =
          some [(List.ofFn children).map groundSchema] := by
        apply freshRows_singleton
        intro value member position
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
        apply ih _ _ (admitted index)
        have smaller := Term.size_subterm (ts := children) index
        omega
      have noFunctions := no_function_derivations library supply (run library supply fuel)
        path (List.ofFn children) none each
      simp [run, StableIntrinsicTypeQuery.step, candidates, IndependentTypeOutput.isVariable, IndependentTypeOutput.literal,
        IndependentTypeOutput.elements, noFunctions, IndependentTypeOutput.allowsRow,
        IndependentTypeOutput.structural, computed, groundSchema]
      simp only [row, List.length_ofFn, Term.app.injEq, true_and]
      apply (Fin.heq_fun_iff (by simp)).mpr
      intro index
      simp

end Mettapedia.Languages.MeTTa.PeTTa.StableGroundTypeQueries
