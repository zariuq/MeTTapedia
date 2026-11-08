import Mettapedia.Languages.MeTTa.PeTTa.StableGroundTypeQueries
import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutputSpineRecursive

/-! Bound return queries for ground uninterpreted values. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StableGroundTypeQueries

open Mettapedia.Logic.LP
open IntrinsicTypeFacts (signature TypeTerm Declaration named primitiveType undefinedType)
open IndependentTypeOutput (Path Query row freshSupply structural)
open IndependentTypeOutput.Resolution (argumentsResolved arguments_eq_resolved)
open IndependentTypeOutput.Structural (FieldsApart fieldVariables)
open IndependentTypeOutput.SpineRecursive (bindFields bindFields_vector match_proper_row)
open Mettapedia.Logic.LP.ConjunctiveUnification (applyTerm_of_isGround)

theorem ground_fields_apart (path : Path) (position : Nat) (term : TypeTerm) (ground : term.isGround) :
    FieldsApart path position term := by
  intro later follows name occurs
  have empty := (Term.isGround_iff_freeVars_empty term).mp ground
  simp [empty] at occurs

theorem fieldVariables_range (path : Path) (position count : Nat) :
    fieldVariables path position count =
      (List.range' position count).map (fun index => (.var (freshSupply (3 :: path) index) : TypeTerm)) := by
  induction count generalizing position with
  | zero => rfl
  | succ count ih => simp only [fieldVariables, List.range'_succ, List.map_cons, ih]

theorem row_apply (store : Subst signature) (items : List TypeTerm) :
    store.applyTerm (row items) = row (items.map store.applyTerm) := by
  simp only [row, Subst.applyTerm, Term.app.injEq, List.length_map, true_and]
  apply (Fin.heq_fun_iff (List.length_map store.applyTerm).symm).mpr
  intro index
  simp

/-- The actual fresh field matcher initializes the known ground requirements,
then the existing argument owner reads the resulting source/target pairs. -/
theorem structural_ground_entry (query : Query) (path : Path) (items targets : List TypeTerm)
    (lengths : items.length = targets.length)
    (subjects : ∀ item ∈ items, item.isGround) (types : ∀ target ∈ targets, target.isGround) :
    structural freshSupply query path items (some (row targets)) =
      argumentsResolved query (4 :: path) 0 (items.zip targets) (row targets) := by
  have apart : ∀ target ∈ targets, FieldsApart path 0 target :=
    fun target present => ground_fields_apart path 0 target (types target present)
  have fields : (List.range items.length).map
      (fun index => (Term.var (freshSupply (3 :: path) index) : TypeTerm)) =
      fieldVariables path 0 items.length := by
    simpa only [List.range_eq_range'] using (fieldVariables_range path 0 items.length).symm
  simp only [structural]
  rw [fields, lengths, match_proper_row path 0 targets apart]
  dsimp only
  rw [arguments_eq_resolved, row_apply, bindFields_vector path 0 targets apart]
  have unchanged : items.map (bindFields path 0 targets).applyTerm = items := by
    conv_rhs => rw [← List.map_id items]
    apply List.map_congr_left
    intro item member
    exact applyTerm_of_isGround _ (subjects item member)
  change argumentsResolved query (4 :: path) 0
    ((items.zip (fieldVariables path 0 targets.length)).map
      (Prod.map (bindFields path 0 targets).applyTerm (bindFields path 0 targets).applyTerm)) (row targets) = _
  rw [← List.zip_map, unchanged, bindFields_vector path 0 targets apart]

/-- Singleton child queries retain singleton multiplicity through the actual
matcher. Each successful refinement leaves all remaining ground fields fixed. -/
theorem resolved_ground_singleton (query : Query) (path : Path) (position : Nat)
    (pending : List (TypeTerm × TypeTerm)) (result : TypeTerm)
    (groundPairs : ∀ pair ∈ pending, pair.1.isGround ∧ pair.2.isGround)
    (groundResult : result.isGround)
    (children : ∀ pair ∈ pending, ∀ index,
      query (0 :: index :: path) pair.1 (some pair.2) = some [pair.2]) :
    argumentsResolved query path position pending result = some [result] := by
  induction pending generalizing position with
  | nil => rw [argumentsResolved]
  | cons pair rest ih =>
    rcases pair with ⟨subject, formal⟩
    rw [argumentsResolved]
    split
    · exact ih (position + 1)
        (fun pair member => groundPairs pair (List.mem_cons_of_mem _ member))
        (fun pair member index => children pair (List.mem_cons_of_mem _ member) index)
    · rw [children (subject, formal) List.mem_cons_self position]
      obtain ⟨refinement, accepted⟩ := unifyTotal_complete
        (σ := signature) (equations := [(formal, formal)])
        ⟨Subst.id signature, by
          intro pair member
          cases List.mem_singleton.mp member
          rfl⟩
      simp only [IndependentTypeOutput.collect, accepted, bind, Option.bind, Option.pure_def]
      have unchanged : rest.map (fun pair => (refinement.applyTerm pair.1, refinement.applyTerm pair.2)) = rest := by
        conv_rhs => rw [← List.map_id rest]
        apply List.map_congr_left
        intro pair member
        have both := groundPairs pair (List.mem_cons_of_mem _ member)
        simp only [applyTerm_of_isGround refinement both.1, applyTerm_of_isGround refinement both.2, Prod.mk.eta]
        rfl
      rw [unchanged, applyTerm_of_isGround refinement groundResult]
      rw [ih (position + 1)
        (fun pair member => groundPairs pair (List.mem_cons_of_mem _ member))
        (fun pair member index => children pair (List.mem_cons_of_mem _ member) index)]
      rfl

theorem zip_ground_schemas (items : List TypeTerm) :
    items.zip (items.map groundSchema) = items.map (fun value => (value, groundSchema value)) := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp [ih]

/-- Rechecking the type established at entry returns exactly one continuation
through the real bound-query traversal, not through a fresh-query shortcut. -/
theorem bound_own_singleton (library : List Declaration) (fuel : Nat) :
    ∀ (path : Path) (value : TypeTerm), GroundUninterpreted library value → value.size ≤ fuel →
      StableIntrinsicTypeQuery.run library freshSupply fuel path value (some (groundSchema value)) =
        some [groundSchema value] := by
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
        simp [StableIntrinsicTypeQuery.run, StableIntrinsicTypeQuery.step,
          StableIntrinsicTypeQuery.candidates, StableIntrinsicTypeQuery.isUndefined,
          IndependentTypeOutput.isVariable, IndependentTypeOutput.literal, primitiveType,
          IndependentTypeOutput.select, IndependentTypeOutput.matched, groundSchema,
          named, unifyTotal, Subst.id, Subst.applyTerm, Option.toList]
        rfl
      | symbol name =>
        have empty := no_head_declarations library freshSupply path (.const (.symbol name)) admitted
        simp [StableIntrinsicTypeQuery.run, StableIntrinsicTypeQuery.step,
          StableIntrinsicTypeQuery.candidates, StableIntrinsicTypeQuery.isUndefined,
          IndependentTypeOutput.isVariable, IndependentTypeOutput.literal, primitiveType,
          IndependentTypeOutput.elements, empty, IndependentTypeOutput.select,
          IndependentTypeOutput.matched, groundSchema, named, undefinedType]
    | app arity children =>
      let items := List.ofFn children
      have each : ∀ value ∈ items, GroundUninterpreted library value := by
        intro value member
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
        exact admitted index
      have sourceGround : ∀ value ∈ items, value.isGround :=
        fun value member => admitted_is_ground library value (each value member)
      have targetGround : ∀ type ∈ items.map groundSchema, type.isGround := by
        intro type member
        obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
        exact schema_is_ground library value (each value present)
      have shape : row (items.map groundSchema) = groundSchema (.app arity children) :=
        row_map_ofFn arity children
      have computed : structural freshSupply (StableIntrinsicTypeQuery.run library freshSupply fuel)
          path items (some (groundSchema (.app arity children))) = some [groundSchema (.app arity children)] := by
        rw [← shape, structural_ground_entry _ _ _ _ (by simp) sourceGround targetGround, zip_ground_schemas]
        apply resolved_ground_singleton
        · intro pair member
          obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
          exact ⟨sourceGround value present, schema_is_ground library value (each value present)⟩
        · rw [shape]
          exact schema_is_ground library _ admitted
        · intro pair member position
          obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
          apply ih _ _ (each value present)
          obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
          have smaller := Term.size_subterm (ts := children) index
          omega
      have noFresh := no_function_derivations library freshSupply
        (StableIntrinsicTypeQuery.run library freshSupply fuel) path items none each
      have noBound := no_function_derivations library freshSupply
        (StableIntrinsicTypeQuery.run library freshSupply fuel) path items
        (some (groundSchema (.app arity children))) each
      simp only [items] at computed noFresh noBound
      change structural freshSupply (StableIntrinsicTypeQuery.run library freshSupply fuel)
        path (List.ofFn children) (some (.app arity (fun index => groundSchema (children index)))) =
        some [.app arity (fun index => groundSchema (children index))] at computed
      change StableIntrinsicTypeQuery.functions library freshSupply
        (StableIntrinsicTypeQuery.run library freshSupply fuel) path (List.ofFn children)
        (some (.app arity (fun index => groundSchema (children index)))) = some [] at noBound
      simp only [StableIntrinsicTypeQuery.run, StableIntrinsicTypeQuery.step,
        StableIntrinsicTypeQuery.candidates, StableIntrinsicTypeQuery.isUndefined,
        IndependentTypeOutput.isVariable, IndependentTypeOutput.literal,
        IndependentTypeOutput.elements, IndependentTypeOutput.allowsRow, groundSchema]
      rw [noBound, noFresh]
      simp only [Bool.false_eq_true, ↓reduceIte, bind, Option.bind, Option.pure_def,
        List.isEmpty_nil, Bool.true_and, Bool.false_and, List.nil_append]
      rw [computed]

end Mettapedia.Languages.MeTTa.PeTTa.StableGroundTypeQueries
