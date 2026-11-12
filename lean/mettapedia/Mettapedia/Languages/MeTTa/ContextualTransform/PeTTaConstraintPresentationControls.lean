import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanConstraintAdmission
import Lean.Elab.Tactic.Cbv

/-!
# Positive and negative controls for the source binding bridge

The source solver, runtime substitution and finite-term unifier are executed
separately. An unserved budget remains distinct from a source contradiction.
Raw shadowed list entries are not substituted for first-lookup semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstraintPresentationControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS
open UnifyingConstraintPresentation
open OutputPlan.ConstraintAdmission

def x : Atom := .var "x"
def y : Atom := .var "y"
def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def shadow : Subst := [("x",a),("x",b)]

theorem source_presentation_retains_shadow_key_occurrences :
    presentation shadow = [(x,a),(x,a)] := by decide +kernel

theorem first_binding_readback_is_preserved :
    Destination.read (environment shadow) x = a := by
  rw [read_environment]
  decide +kernel

theorem actual_graph_and_raw_conjunction_differ :
    (Destination.resolve (presentation shadow)).isSome = true ∧
      (Destination.resolve [(x,a),(x,b)]).isSome = false := by
  constructor
  · have solved : Destination.Solves (environment [("x",a)]) (presentation shadow) := by
      rw [source_presentation_retains_shadow_key_occurrences]
      simp only [Destination.Solves,List.mem_cons,List.not_mem_nil,or_false,or_self,forall_eq]
      rw [read_environment,read_environment]
      decide +kernel
    obtain ⟨model,computed⟩ := Destination.resolve_complete ⟨environment [("x",a)],solved⟩
    rw [computed]
    rfl
  · have refused : Destination.resolve [(x,a),(x,b)] = none := by
      apply (Destination.resolve_none_iff _).mpr
      rintro ⟨model,solved⟩
      have one := solved (x,a) (by simp)
      have two := solved (x,b) (by simp)
      have impossible := one.symm.trans two
      simp [a,b,Destination.read,Destination.encode,Destination.decode] at impossible
    rw [refused]
    rfl

theorem zero_unifier_budget_is_not_source_refusal :
    Unifying.unifyTerms 0 [] x a = .exhausted ∧
      (Destination.refine [] x a).isSome = true := by
  constructor
  · rfl
  · have computed := actual_source_refine [] [] [("x",a)] x a
      (by intro model; rfl) (by simp [Unifying.Idempotent,Subst.lookup]) (by decide +kernel)
    rw [computed]
    rfl

theorem cyclic_equation_refuses_in_both_representations :
    Unifying.unify [] x (.expression [.symbol "f",x]) = .clash ∧
      Destination.refine [] x (.expression [.symbol "f",x]) = none := by
  constructor
  · decide +kernel
  · exact actual_source_refusal [] [] x (.expression [.symbol "f",x])
      (by intro model; rfl) (by simp [Unifying.Idempotent,Subst.lookup]) (by decide +kernel)

theorem unresolved_binding_chain_is_not_idempotent :
    ¬Unifying.Idempotent [("x",y),("y",a)] := by
  intro valid
  have invalid := valid "x" y (by rfl) "y" (by simp [y,atomFreeVars])
  change some a = none at invalid
  cases invalid

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstraintPresentationControls
