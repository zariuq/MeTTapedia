import Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPreservation
import Mettapedia.Logic.LP.UnificationOccurs

/-!
# Actual unifier clashes refute destination-source solutions

An occurs-check failure is justified by finite-term source mathematics.
Interrupted work is not a clash and is not assigned an empty source meaning.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)
open EagerDFS

theorem encode_read (model : Destination.Environment) (term : Atom) :
    Destination.encode (Destination.read model term) =
      Mettapedia.Logic.LP.Subst.applyTerm model (Destination.encode term) :=
  Destination.encode_decode _

theorem occurs_encode (name : String) (term : Atom) (present : name ∈ atomFreeVars term) :
    (Destination.encode term).occursIn name = true := by
  cases term with
  | var other =>
      simp only [atomFreeVars,List.mem_singleton] at present
      subst other
      simp [Destination.encode,Mettapedia.Logic.LP.Term.occursIn]
  | symbol => simp [atomFreeVars] at present
  | grounded => simp [atomFreeVars] at present
  | expression items =>
      obtain ⟨item,member,inside⟩ := Unifying.mem_freeVars_expression.mp present
      have childOccurs := occurs_encode name item inside
      obtain ⟨index,atIndex⟩ := List.mem_iff_get.mp member
      simp only [Destination.encode,Mettapedia.Logic.LP.Term.occursIn,List.any_eq_true]
      refine ⟨index,by simp,?_⟩
      simpa only [← atIndex,List.get_eq_getElem,Fin.getElem_fin] using childOccurs
termination_by sizeOf term
decreasing_by
  subst term
  simp_wf
  exact Nat.lt_trans (List.sizeOf_lt_of_mem member) (by omega)

theorem occurs_forbids_model (model : Destination.Environment) (name : String) (items : List Atom)
    (occurs : Unifying.occurs name (.expression items) = true) :
    Destination.read model (.var name) ≠ Destination.read model (.expression items) := by
  intro equal
  have encoded := congrArg Destination.encode equal
  rw [encode_read,encode_read] at encoded
  simp only [Destination.encode] at encoded
  have absent := Mettapedia.Logic.LP.unifies_var_app_occurs_false model name items.length
    (fun index => Destination.encode items[index]) encoded
  have present : name ∈ atomFreeVars (.expression items) := by
    simpa only [Unifying.occurs,List.contains_iff_mem] using occurs
  have yes := occurs_encode name (.expression items) present
  simp only [Destination.encode] at yes
  rw [yes] at absent
  cases absent

theorem unifyLists_refutes_model (unifier : Subst → Atom → Atom → Unifying.Unified)
    (validAfter : ∀ bindings bound left right, Unifying.Idempotent bindings →
      unifier bindings left right = .ok bound → Unifying.Idempotent bound)
    (keeps : ∀ bindings bound left right, Unifying.Idempotent bindings →
      unifier bindings left right = .ok bound → ∀ model,
        Destination.Solves model (presentation bindings) → Destination.read model left = Destination.read model right →
          Destination.Solves model (presentation bound))
    (refutes : ∀ bindings left right, Unifying.Idempotent bindings →
      unifier bindings left right = .clash → ∀ model,
        Destination.Solves model (presentation bindings) → Destination.read model left ≠ Destination.read model right) :
    ∀ (left right : List Atom) (bindings : Subst), Unifying.Idempotent bindings →
      Unifying.unifyLists unifier bindings left right = .clash → ∀ model,
        Destination.Solves model (presentation bindings) → left.map (Destination.read model) ≠ right.map (Destination.read model) := by
  intro left
  induction left with
  | nil =>
      intro right bindings valid clashed model old equal
      cases right with
      | nil => cases clashed
      | cons => simp at equal
  | cons first rest ih =>
      intro right bindings valid clashed model old equal
      cases right with
      | nil => simp at equal
      | cons other others =>
          simp only [List.map_cons,List.cons.injEq] at equal
          cases head : unifier bindings first other with
          | clash => exact refutes bindings first other valid head model old equal.1
          | exhausted => simp [Unifying.unifyLists,head] at clashed
          | ok middle =>
              rw [Unifying.unifyLists,head,Unifying.Unified.ok_andThen] at clashed
              exact ih others middle (validAfter bindings middle first other valid head) clashed model
                (keeps bindings middle first other valid head model old equal.1) equal.2

theorem unifyTerms_refutes_model (fuel : Nat) :
    ∀ (bindings : Subst) (left right : Atom), Unifying.Idempotent bindings →
      Unifying.unifyTerms fuel bindings left right = .clash → ∀ model,
        Destination.Solves model (presentation bindings) → Destination.read model left ≠ Destination.read model right := by
  induction fuel with
  | zero => intro bindings left right valid clashed; cases clashed
  | succ fuel ih =>
      intro bindings left right valid clashed model old equal
      have resolvedEqual : Destination.read model (Unifying.resolve bindings left) =
          Destination.read model (Unifying.resolve bindings right) :=
        (absorbs_of_solves model bindings old left).trans
          (equal.trans (absorbs_of_solves model bindings old right).symm)
      unfold Unifying.unifyTerms at clashed
      generalize leftView : Unifying.resolve bindings left = resolvedLeft at clashed
      generalize rightView : Unifying.resolve bindings right = resolvedRight at clashed
      cases resolvedLeft with
      | var name =>
          cases resolvedRight with
          | var other =>
              simp only at clashed
              split at clashed <;> cases clashed
          | symbol other => simp [Unifying.occurs,atomFreeVars] at clashed
          | grounded value => simp [Unifying.occurs,atomFreeVars] at clashed
          | expression items =>
              simp only at clashed
              split at clashed
              · rename_i occurs
                exact occurs_forbids_model model name items occurs (by simpa only [leftView,rightView] using resolvedEqual)
              · cases clashed
      | symbol name =>
          cases resolvedRight with
          | var other => simp [Unifying.occurs,atomFreeVars] at clashed
          | symbol other =>
              simp only at clashed
              split at clashed
              · cases clashed
              · rename_i different
                apply different
                simpa [leftView,rightView,Destination.read,Destination.encode,Destination.decode] using resolvedEqual
          | grounded => simp [leftView,rightView,Destination.read,Destination.encode,Destination.decode] at resolvedEqual
          | expression => simp [leftView,rightView,Destination.read,Destination.encode,Destination.decode] at resolvedEqual
      | grounded value =>
          cases resolvedRight with
          | var other => simp [Unifying.occurs,atomFreeVars] at clashed
          | symbol => simp [leftView,rightView,Destination.read,Destination.encode,Destination.decode] at resolvedEqual
          | grounded other =>
              simp only at clashed
              split at clashed
              · cases clashed
              · rename_i different
                apply different
                simpa [leftView,rightView,Destination.read,Destination.encode,Destination.decode] using resolvedEqual
          | expression => simp [leftView,rightView,Destination.read,Destination.encode,Destination.decode] at resolvedEqual
      | expression items =>
          cases resolvedRight with
          | var other =>
              simp only at clashed
              split at clashed
              · rename_i occurs
                exact occurs_forbids_model model other items occurs (by simpa only [leftView,rightView] using resolvedEqual.symm)
              · cases clashed
          | symbol => simp [leftView,rightView,Destination.read,Destination.encode,Destination.decode] at resolvedEqual
          | grounded => simp [leftView,rightView,Destination.read,Destination.encode,Destination.decode] at resolvedEqual
          | expression others =>
              simp only at clashed
              have equalItems : items.map (Destination.read model) = others.map (Destination.read model) := by
                simpa only [leftView,rightView,read_expression,Atom.expression.injEq] using resolvedEqual
              exact unifyLists_refutes_model (Unifying.unifyTerms fuel)
                (fun bindings bound left right valid unified => (Unifying.unifyTerms_sound fuel bindings bound left right valid unified).1)
                (unifyTerms_keeps_model fuel) ih items others bindings valid clashed model old equalItems

theorem clashed_has_no_source_solution (fuel : Nat) (bindings : Subst) (left right : Atom)
    (valid : Unifying.Idempotent bindings)
    (clashed : Unifying.unifyTerms fuel bindings left right = .clash) :
    ¬∃ model, Destination.Solves model (presentation bindings) ∧ Destination.read model left = Destination.read model right := by
  rintro ⟨model,old,equal⟩
  exact unifyTerms_refutes_model fuel bindings left right valid clashed model old equal

end Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation
