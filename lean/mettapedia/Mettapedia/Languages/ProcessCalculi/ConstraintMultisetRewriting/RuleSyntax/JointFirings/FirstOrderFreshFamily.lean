import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Independent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Logic.LP.PrivateVariableRenaming
import Mathlib.Data.Nat.Pairing

/-!
# Jointly fresh namespaces for a finite first-order family

Each member gets its own pairing-indexed slot namespace. A single
substitution realizes arbitrary independent assignments to every namespace.
Ground incoming information is fixed by every such substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FirstOrderFreshFamily

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)

variable {signature : LPSignature} (slots : signature.vars ≃ ℕ)

def opening (index : ℕ) : Subst signature :=
  fun slot => .var (slots.symm (Nat.pair index (slots slot)))

def combine (requested : ℕ → Subst signature) : Subst signature :=
  fun slot =>
    let address := Nat.unpair (slots slot)
    requested address.1 (slots.symm address.2)

theorem combine_opening (requested : ℕ → Subst signature) (index : ℕ) (term : Term signature) :
    (combine slots requested).applyTerm ((opening slots index).applyTerm term) =
      (requested index).applyTerm term := by
  induction term with
  | var slot => simp [Subst.applyTerm, combine, opening]
  | const value => rfl
  | app symbol terms ih => simp only [Subst.applyTerm, ih]

def Requested (requested : ℕ → Subst signature) (indices : Finset ℕ) (assignment : Subst signature) : Prop :=
  ∀ index ∈ indices, ∀ term : Term signature,
    assignment.applyTerm ((opening slots index).applyTerm term) = (requested index).applyTerm term

variable {O : Type*} {P : Program (Terms (Term signature))}

abbrev X := frames (FirstOrder.action signature)
abbrev E := ext (FirstOrder.action signature)
abbrev M := OneMember (FirstOrder.action signature) O P

/-- A finite family realizes any already requested namespaces and every new member independently. -/
theorem realized (family : List (ℕ × M (O := O) (P := P)))
    (distinct : (family.map Prod.fst).Nodup)
    (correct : ∀ entry ∈ family, entry.2.opening = opening slots entry.1)
    (requested : ℕ → Subst signature) (past : Finset ℕ)
    (apart : ∀ index ∈ past, index ∉ family.map Prod.fst) :
    Realized X PUnit.unit (family.map Prod.snd) (Requested slots requested past) := by
  induction family generalizing requested past with
  | nil =>
    exact ⟨combine slots requested, fun index _ term => combine_opening slots requested index term⟩
  | cons entry rest ih =>
    obtain ⟨index, member⟩ := entry
    have unique := List.nodup_cons.mp distinct
    have laterCorrect : ∀ entry ∈ rest, entry.2.opening = opening slots entry.1 :=
      fun entry inside => correct entry (List.mem_cons_of_mem _ inside)
    change ∀ h : Subst signature,
      Realized X PUnit.unit (rest.map Prod.snd)
        (fun u => Requested slots requested past u ∧
          ∀ term ∈ member.rule.terms,
            u.applyTerm (member.opening.applyTerm term) = h.applyTerm term)
    intro h
    have laterApart : ∀ i ∈ insert index past, i ∉ rest.map Prod.fst := by
      intro i inside inRest
      rcases Finset.mem_insert.mp inside with rfl | inPast
      · exact unique.1 inRest
      · exact apart i inPast (List.mem_cons_of_mem _ inRest)
    have later := ih unique.2 laterCorrect (Function.update requested index h) (insert index past) laterApart
    refine Realized.mono X (rest.map Prod.snd) (fun u solved => ?_) later
    refine ⟨?_, ?_⟩
    · intro i inside term
      have different : i ≠ index := by
        intro same
        exact apart i inside (by simp [same])
      simpa only [Function.update_of_ne different] using
        solved i (Finset.mem_insert_of_mem inside) term
    · intro term _
      rw [correct (index, member) List.mem_cons_self]
      simpa using solved index (Finset.mem_insert_self _ _) term

/-- The incoming ground state imposes no competing names on these private openings. -/
theorem fresh (knowledge : EquationStore (Term signature)) (present : Finset O) (label : O → Term signature)
    (family : List (ℕ × M (O := O) (P := P)))
    (distinct : (family.map Prod.fst).Nodup)
    (correct : ∀ entry ∈ family, entry.2.opening = opening slots entry.1)
    (ground : ∀ term, (⟨PUnit.unit, knowledge, present, label⟩ : State (Terms (Term signature)) O).Mentions term →
      term.isGround) :
    Bag.Fresh X (⟨PUnit.unit, knowledge, present, label⟩ : State (Terms (Term signature)) O)
      (⟨PUnit.unit, family.map Prod.snd⟩ : Bag O E P PUnit.unit) := by
  intro b g
  cases b
  have all := realized slots family distinct correct (fun _ => Subst.id signature) ∅
    (fun _ inside => False.elim (Finset.notMem_empty _ inside))
  refine Realized.mono X (family.map Prod.snd) (fun u _ term mentioned => ?_) all
  change u.applyTerm ((Subst.id signature).applyTerm term) = g.applyTerm term
  rw [Subst.applyTerm_id, FirstOrder.ground_fixed u term (ground term mentioned),
    FirstOrder.ground_fixed g term (ground term mentioned)]

/-- Reopening retains an original opening inside its private namespace. -/
structure Reopened (slots : signature.vars ≃ ℕ) (O : Type*) (P : Program (Terms (Term signature))) where
  index : ℕ
  member : M (O := O) (P := P)
  inner : Subst signature
  opening_eq : member.opening = (opening slots index).comp inner
  realizes : ∀ h : Subst signature, ∃ u : Subst signature,
    ∀ term ∈ member.rule.terms, u.applyTerm (inner.applyTerm term) = h.applyTerm term

theorem realized_composed (family : List (Reopened slots O P))
    (distinct : (family.map Reopened.index).Nodup)
    (requested : ℕ → Subst signature) (past : Finset ℕ)
    (apart : ∀ index ∈ past, index ∉ family.map Reopened.index) :
    Realized X PUnit.unit (family.map Reopened.member) (Requested slots requested past) := by
  induction family generalizing requested past with
  | nil =>
    exact ⟨combine slots requested, fun index _ term => combine_opening slots requested index term⟩
  | cons entry rest ih =>
    have unique := List.nodup_cons.mp distinct
    change ∀ h : Subst signature,
      Realized X PUnit.unit (rest.map Reopened.member)
        (fun u => Requested slots requested past u ∧
          ∀ term ∈ entry.member.rule.terms,
            u.applyTerm (entry.member.opening.applyTerm term) = h.applyTerm term)
    intro h
    obtain ⟨inner, realizes⟩ := entry.realizes h
    have laterApart : ∀ i ∈ insert entry.index past, i ∉ rest.map Reopened.index := by
      intro i inside inRest
      rcases Finset.mem_insert.mp inside with rfl | inPast
      · exact unique.1 inRest
      · exact apart i inPast (List.mem_cons_of_mem _ inRest)
    have later := ih unique.2 (Function.update requested entry.index inner) (insert entry.index past) laterApart
    refine Realized.mono X (rest.map Reopened.member) (fun u solved => ?_) later
    refine ⟨?_, ?_⟩
    · intro i inside term
      have different : i ≠ entry.index := by
        intro same
        exact apart i inside (by simp [same])
      simpa only [Function.update_of_ne different] using solved i (Finset.mem_insert_of_mem inside) term
    · intro term mentioned
      rw [entry.opening_eq, Subst.applyTerm_comp]
      have prescribed := solved entry.index (Finset.mem_insert_self _ _) (entry.inner.applyTerm term)
      have value : u.applyTerm ((opening slots entry.index).applyTerm (entry.inner.applyTerm term)) =
          inner.applyTerm (entry.inner.applyTerm term) := by simpa using prescribed
      exact value.trans (realizes term mentioned)

theorem fresh_composed (knowledge : EquationStore (Term signature)) (present : Finset O)
    (label : O → Term signature) (family : List (Reopened slots O P))
    (distinct : (family.map Reopened.index).Nodup)
    (ground : ∀ term, (⟨PUnit.unit, knowledge, present, label⟩ : State (Terms (Term signature)) O).Mentions term →
      term.isGround) :
    Bag.Fresh X (⟨PUnit.unit, knowledge, present, label⟩ : State (Terms (Term signature)) O)
      (⟨PUnit.unit, family.map Reopened.member⟩ : Bag O E P PUnit.unit) := by
  intro b g
  cases b
  have all := realized_composed slots family distinct (fun _ => Subst.id signature) ∅
    (fun _ inside => False.elim (Finset.notMem_empty _ inside))
  refine Realized.mono X (family.map Reopened.member) (fun u _ term mentioned => ?_) all
  change u.applyTerm ((Subst.id signature).applyTerm term) = g.applyTerm term
  rw [Subst.applyTerm_id, FirstOrder.ground_fixed u term (ground term mentioned),
    FirstOrder.ground_fixed g term (ground term mentioned)]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FirstOrderFreshFamily
