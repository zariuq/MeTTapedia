import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryRank

/-!
# Bounded iteration of completed fresh-insertion phases

The private worker records each actual phase count and stops on a completed
zero phase. Its allowance counts phases, not evaluator instructions. Failure
or insufficient allowance refuses; it is never returned as a zero result.
No rollback of externally published effects is licensed by this model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryIteration

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveRegionProvenance
open FlatQueryRowCodec FlatQueryDomainInvariant FiniteNestedQuerySource FiniteNestedQueryCompletion FiniteNestedQueryRank
open NamedSpaces

variable {Value : Type} [DecidableEq Value]

def iterate {codec : Codec Value} {names : Inventory String} (queries : List (Query codec names))
    (head : FlatQueryOutputDomain.Head codec names) (target : Handle) (bindings : Subst) :
    Nat → Effects.State → Option (Effects.State × List Nat)
  | 0, _ => none
  | allowance + 1, before => do
      let first ← run queries head target bindings before
      if first.2.length = 0 then some (first.1, [0])
      else
        let later ← iterate queries head target bindings allowance first.1
        return (later.1, first.2.length :: later.2)

theorem complete {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (data : DataHead head) (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (before : Effects.State) (rows : List Atom) (allowance : Nat)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain queries before)
    (covered : Covered queries bindings) (snapshot : before.read target = some rows)
    (enough : rank domain head rows < allowance) :
    ∃ after counts, iterate queries head target bindings allowance before = some (after, counts) := by
  induction allowance generalizing before rows with
  | zero => omega
  | succ allowance ih =>
      obtain ⟨next, answers, first⟩ := run_complete domain queries queries (fun _ member => member)
        head data constants target bindings before rows bound valid covered snapshot
      by_cases quiet : answers.length = 0
      · exact ⟨next, [0], by simp only [iterate, first, bind, Option.bind, if_pos quiet]⟩
      · obtain ⟨nextRows, nextRead, balance⟩ := run_balance domain queries queries (fun _ member => member)
          head constants target bindings before next rows answers bound valid snapshot first
        have nextValid := run_preserves domain queries queries (fun _ member => member)
          head constants target bindings before next answers bound valid first
        obtain ⟨after, counts, later⟩ := ih next nextRows nextValid nextRead (by omega)
        exact ⟨after, answers.length :: counts, by
          simp only [iterate, first, bind, Option.bind, if_neg quiet, later]
          rfl⟩

theorem catalogue_allowance {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (data : DataHead head) (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (before : Effects.State) (rows : List Atom)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain queries before)
    (covered : Covered queries bindings) (snapshot : before.read target = some rows) :
    ∃ after counts, iterate queries head target bindings (domain.card ^ head.2.cells.length + 1) before = some (after, counts) := by
  apply complete domain queries head data constants target bindings before rows _ bound valid covered snapshot
  have subset : rank domain head rows ≤ (catalogue domain head).card := Finset.card_le_card Finset.sdiff_subset
  have size : (catalogue domain head).card = domain.card ^ head.2.cells.length := by
    simp [catalogue, FlatQueryOutputDomain.catalogue_card]
  omega

omit [DecidableEq Value] in
theorem count_trace {codec : Codec Value} {names : Inventory String}
    (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (target : Handle) (bindings : Subst) (allowance : Nat) (before after : Effects.State) (counts : List Nat)
    (completed : iterate queries head target bindings allowance before = some (after, counts)) :
    ∃ positive, counts = positive ++ [0] ∧ (∀ count ∈ positive, 0 < count) ∧ counts.length ≤ allowance := by
  induction allowance generalizing before after counts with
  | zero => cases completed
  | succ allowance ih =>
      obtain ⟨first, _, tail⟩ := Option.bind_eq_some_iff.mp completed
      split at tail
      next quiet =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj tail)
        exact ⟨[], rfl, by simp, by simp⟩
      next productive =>
        obtain ⟨later, continued, same⟩ := Option.bind_eq_some_iff.mp tail
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        obtain ⟨positive, countsEq, nonzero, length⟩ := ih first.1 later.1 later.2 continued
        refine ⟨first.2.length :: positive, by simp [countsEq], ?_, by simp only [List.length_cons]; omega⟩
        intro count member
        rcases List.mem_cons.mp member with same | member
        · subst count; omega
        · exact nonzero count member

theorem saturated {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (allowance : Nat) (before after : Effects.State) (counts : List Nat)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain queries before)
    (completed : iterate queries head target bindings allowance before = some (after, counts)) :
    FreshNestedQuerySource.SaturatedAt after target head.1 (queries.map Query.leg) bindings := by
  induction allowance generalizing before after counts with
  | zero => cases completed
  | succ allowance ih =>
      obtain ⟨first, phase, tail⟩ := Option.bind_eq_some_iff.mp completed
      split at tail
      next quiet =>
        have empty : first.2 = [] := List.length_eq_zero_iff.mp quiet
        have done := quiet_is_saturated domain queries head constants target bindings before first.1 bound valid
          (phase.trans (congrArg some (Prod.ext rfl empty)))
        have resultState : first.1 = after := (Prod.mk.inj (Option.some.inj tail)).1
        simpa only [done.1, resultState] using done.2
      next productive =>
        obtain ⟨later, continued, same⟩ := Option.bind_eq_some_iff.mp tail
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        exact ih first.1 later.1 later.2
          (run_preserves domain queries queries (fun _ member => member) head constants target bindings before first.1 first.2 bound valid phase)
          continued

theorem balance {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (target : Handle) (bindings : Subst) (allowance : Nat) (before after : Effects.State) (rows : List Atom) (counts : List Nat)
    (bound : BindingsInDomain codec names domain bindings) (valid : ViewsInDomain domain queries before)
    (snapshot : before.read target = some rows)
    (completed : iterate queries head target bindings allowance before = some (after, counts)) :
    ∃ result, after.read target = some result ∧ rank domain head result + counts.sum = rank domain head rows := by
  induction allowance generalizing before after rows counts with
  | zero => cases completed
  | succ allowance ih =>
      obtain ⟨first, phase, tail⟩ := Option.bind_eq_some_iff.mp completed
      obtain ⟨middleRows, middleRead, firstBalance⟩ := run_balance domain queries queries (fun _ member => member)
        head constants target bindings before first.1 rows first.2 bound valid snapshot phase
      split at tail
      next quiet =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj tail)
        exact ⟨middleRows, middleRead, by simpa [quiet] using firstBalance⟩
      next productive =>
        obtain ⟨later, continued, same⟩ := Option.bind_eq_some_iff.mp tail
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        obtain ⟨result, reading, laterBalance⟩ := ih first.1 later.1 middleRows later.2
          (run_preserves domain queries queries (fun _ member => member) head constants target bindings before first.1 first.2 bound valid phase)
          middleRead continued
        exact ⟨result, reading, by simp only [List.sum_cons]; omega⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryIteration
