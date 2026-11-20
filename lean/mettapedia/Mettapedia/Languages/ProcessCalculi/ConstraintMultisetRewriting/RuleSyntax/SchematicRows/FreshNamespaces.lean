import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FirstOrderFreshFamily
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# Independent private namespaces above a retained source prefix

The prefix retains arbitrary caller unknowns, not only ground source values.
Pairing separates each independently opened rule or datum above that prefix.
A single substitution realizes all requested private assignments while keeping
the caller's values on every term whose variables lie below the bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.FreshNamespaces

open Mettapedia.Logic.LP

variable {signature : LPSignature} (slots : signature.vars ≃ Nat)

def opening (bound index : Nat) : Subst signature :=
  fun name => .var (slots.symm (bound + Nat.pair index (slots name)))

def combine (bound : Nat) (caller : Subst signature) (requested : Nat → Subst signature) : Subst signature :=
  fun name => if slots name < bound then caller name else
    let address := Nat.unpair (slots name - bound)
    requested address.1 (slots.symm address.2)

theorem combine_opening (bound : Nat) (caller : Subst signature) (requested : Nat → Subst signature)
    (index : Nat) (term : Term signature) :
    (combine slots bound caller requested).applyTerm ((opening slots bound index).applyTerm term) =
      (requested index).applyTerm term := by
  induction term with
  | var name =>
    have above : ¬ bound + Nat.pair index (slots name) < bound := by omega
    simp [Subst.applyTerm, opening, combine, above]
  | const value => rfl
  | app symbol children ih => simp only [Subst.applyTerm, ih]

variable [DecidableEq signature.vars]

theorem source_agrees (bound : Nat) (caller : Subst signature) (requested : Nat → Subst signature)
    (term : Term signature) (below : ∀ name ∈ term.freeVars, slots name < bound) :
    (combine slots bound caller requested).applyTerm term = caller.applyTerm term := by
  apply Subst.applyTerm_congr
  intro name member
  exact if_pos (below name member)

theorem opening_avoids_source (bound index : Nat) (term sourceTerm : Term signature)
    (below : ∀ name ∈ sourceTerm.freeVars, slots name < bound) :
    Disjoint ((opening slots bound index).applyTerm term).freeVars sourceTerm.freeVars := by
  apply Finset.disjoint_left.mpr
  intro name inOpened inSource
  obtain ⟨original, _, inImage⟩ := (Subst.mem_freeVars_applyTerm.mp inOpened)
  have same : name = slots.symm (bound + Nat.pair index (slots original)) :=
    Term.mem_freeVars_var.mp inImage
  have low := below name inSource
  rw [same, Equiv.apply_symm_apply] at low
  omega

open OneFrame (Terms frames ext)
open JointFirings

abbrev X := frames (FirstOrder.action signature)
abbrev E := ext (FirstOrder.action signature)

def Keeps (bound : Nat) (caller assignment : Subst signature) : Prop :=
  ∀ term : Term signature, (∀ name ∈ term.freeVars, slots name < bound) →
    assignment.applyTerm term = caller.applyTerm term

def Requested (bound : Nat) (requested : Nat → Subst signature) (past : Finset Nat)
    (assignment : Subst signature) : Prop :=
  ∀ index ∈ past, ∀ term : Term signature,
    assignment.applyTerm ((opening slots bound index).applyTerm term) = (requested index).applyTerm term

variable {O : Type*} {P : Program (Terms (Term signature))}

theorem realized (bound : Nat) (caller : Subst signature)
    (family : List (Nat × OneMember (FirstOrder.action signature) O P))
    (distinct : (family.map Prod.fst).Nodup)
    (correct : ∀ entry ∈ family, entry.2.opening = opening slots bound entry.1)
    (requested : Nat → Subst signature) (past : Finset Nat)
    (apart : ∀ index ∈ past, index ∉ family.map Prod.fst) :
    Realized X PUnit.unit (family.map Prod.snd)
      (fun assignment => Keeps slots bound caller assignment ∧ Requested slots bound requested past assignment) := by
  induction family generalizing requested past with
  | nil =>
    exact ⟨combine slots bound caller requested,
      fun term below => source_agrees slots bound caller requested term below,
      fun index _ term => combine_opening slots bound caller requested index term⟩
  | cons entry rest ih =>
    obtain ⟨index, member⟩ := entry
    have unique := List.nodup_cons.mp distinct
    change ∀ locals : Subst signature,
      Realized X PUnit.unit (rest.map Prod.snd) (fun assignment =>
        (Keeps slots bound caller assignment ∧ Requested slots bound requested past assignment) ∧
          ∀ term ∈ member.rule.terms,
            assignment.applyTerm (member.opening.applyTerm term) = locals.applyTerm term)
    intro locals
    have laterCorrect : ∀ entry ∈ rest, entry.2.opening = opening slots bound entry.1 :=
      fun entry inside => correct entry (List.mem_cons_of_mem _ inside)
    have laterApart : ∀ i ∈ insert index past, i ∉ rest.map Prod.fst := by
      intro i inside inRest
      rcases Finset.mem_insert.mp inside with rfl | inPast
      · exact unique.1 inRest
      · exact apart i inPast (List.mem_cons_of_mem _ inRest)
    have later := ih unique.2 laterCorrect (Function.update requested index locals) (insert index past) laterApart
    apply Realized.mono X (rest.map Prod.snd) (fun assignment solved => ?_) later
    refine ⟨⟨solved.1, ?_⟩, ?_⟩
    · intro i inside term
      have different : i ≠ index := by
        intro same
        exact apart i inside (by simp [same])
      simpa only [Function.update_of_ne different] using
        solved.2 i (Finset.mem_insert_of_mem inside) term
    · intro term _
      rw [correct (index, member) List.mem_cons_self]
      simpa using solved.2 index (Finset.mem_insert_self _ _) term

theorem fresh (bound : Nat) (knowledge : EquationStore (Term signature)) (present : Finset O)
    (label : O → Term signature)
    (family : List (Nat × OneMember (FirstOrder.action signature) O P))
    (distinct : (family.map Prod.fst).Nodup)
    (correct : ∀ entry ∈ family, entry.2.opening = opening slots bound entry.1)
    (below : ∀ term, (⟨PUnit.unit, knowledge, present, label⟩ : RuleSyntax.State (Terms (Term signature)) O).Mentions term →
      ∀ name ∈ term.freeVars, slots name < bound) :
    Bag.Fresh X (⟨PUnit.unit, knowledge, present, label⟩ : RuleSyntax.State (Terms (Term signature)) O)
      (⟨PUnit.unit, family.map Prod.snd⟩ : Bag O E P PUnit.unit) := by
  intro b caller
  cases b
  have all := realized slots bound caller family distinct correct (fun _ => Subst.id signature) ∅
    (fun _ inside => False.elim (Finset.notMem_empty _ inside))
  exact Realized.mono X (family.map Prod.snd) (fun assignment kept term mentioned => by
    change assignment.applyTerm ((Subst.id signature).applyTerm term) = caller.applyTerm term
    rw [Subst.applyTerm_id]
    exact kept.1 term (below term mentioned)) all

#print axioms combine_opening
#print axioms source_agrees
#print axioms opening_avoids_source
#print axioms realized
#print axioms fresh

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.FreshNamespaces
