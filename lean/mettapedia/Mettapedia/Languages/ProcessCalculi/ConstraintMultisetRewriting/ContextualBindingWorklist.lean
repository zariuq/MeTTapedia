import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingCase
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidualContext
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidSolver

/-!
# Executable contextual binding over an equation worklist

The driver normalizes rigid equations, searches the queue for a recoverable
distinct-variable binding, and applies that binding to every retained
equation. Both orientations are tried. Fuel exhaustion, repeated spines and
unrecovered dependencies leave inspectable residuals; only a proved rigid
clash is refuted here. Fresh-helper imitation and pruning have their own
frame-changing cases and are not silently replaced by this binding pass.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklist

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {declaration : V → MetaArity S}

abbrev TermBinding {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S declaration) Γ sort) :=
  {answer : Assignment declaration declaration // ContextualFrameUnifier.Principal [(left, right)] answer}

def ofCase {Γ : Ctx S} {sort : S.Srt}
    {left right : Term (signature S declaration) Γ sort}
    (binding : ContextualBindingCase.Case left right) : TermBinding left right :=
  ⟨ContextualBinding.answer binding.chosen binding.body, binding.principal⟩

def tryLeft {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S declaration) Γ sort) : Option (TermBinding left right) :=
  (ContextualBindingCase.tryLeft left right).map ofCase

def swap {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S declaration) Γ sort}
    (binding : TermBinding right left) : TermBinding left right := ⟨binding.val, by
  constructor
  · intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    exact (binding.property.sound _ (List.mem_singleton_self _)).symm
  · intro Next next candidate solved
    apply binding.property.factors next candidate
    intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    exact (solved _ (List.mem_singleton_self _)).symm⟩

def tryTerms {Γ : Ctx S} {sort : S.Srt} (left right : Term (signature S declaration) Γ sort) :
    Option (TermBinding left right) :=
  (ContextualBindingCase.tryTerms left right).map ofCase

structure Update (problem : Problem declaration) where
  answer : Assignment declaration declaration
  remaining : Problem declaration
  valid : Reduction problem answer remaining

/-- The actual selected equation and both retained portions of its queue. -/
structure Selection (problem : Problem declaration) where
  context : Ctx S
  sort : S.Srt
  left : Term (signature S declaration) context sort
  right : Term (signature S declaration) context sort
  binding : ContextualBindingCase.Case left right
  before : Problem declaration
  after : Problem declaration
  split : problem = before ++ (observe left, observe right) :: after

def Selection.update {problem : Problem declaration} (selection : Selection problem) : Update problem :=
  ⟨ContextualBinding.answer selection.binding.chosen selection.binding.body,
    mapProblem (ContextualBinding.answer selection.binding.chosen selection.binding.body)
      (selection.before ++ selection.after), by
      have principal := of_principal_prefix selection.binding.principal selection.after
      have valid := principal.keep_left selection.before
      exact Eq.mpr (congrArg (fun problem => Reduction problem
        (ContextualBinding.answer selection.binding.chosen selection.binding.body)
        (mapProblem (ContextualBinding.answer selection.binding.chosen selection.binding.body)
          (selection.before ++ selection.after))) selection.split)
        (by simpa only [observeProblem, observe, mapProblem, List.map_append,
          List.map_cons, List.map_nil, List.cons_append, List.nil_append] using valid)⟩

def Selection.append {problem : Problem declaration} (selection : Selection problem)
    (extra : Problem declaration) : Selection (problem ++ extra) where
  context := selection.context
  sort := selection.sort
  left := selection.left
  right := selection.right
  binding := selection.binding
  before := selection.before
  after := selection.after ++ extra
  split := (congrArg (fun problem => problem ++ extra) selection.split).trans (by
    simp only [List.append_assoc, List.cons_append])

def Selection.prepend {problem : Problem declaration} (selection : Selection problem)
    (equation : Equation (Observation S declaration)) : Selection (equation :: problem) where
  context := selection.context
  sort := selection.sort
  left := selection.left
  right := selection.right
  binding := selection.binding
  before := equation :: selection.before
  after := selection.after
  split := congrArg (List.cons equation) selection.split

def selectEquation (equation : Equation (Observation S declaration)) : Option (Selection [equation]) := by
  rcases equation with ⟨⟨Γ, sort, left⟩, ⟨Δ, result, right⟩⟩
  by_cases contexts : Γ = Δ
  · subst Δ
    by_cases sorts : sort = result
    · subst result
      exact (ContextualBindingCase.tryTerms left right).map fun binding =>
        ⟨Γ, sort, left, right, binding, [], [], rfl⟩
    · exact none
  · exact none

def tryEquation (equation : Equation (Observation S declaration)) : Option (Update [equation]) :=
  (selectEquation equation).map Selection.update

def select : (problem : Problem declaration) → Option (Selection problem)
  | [] => none
  | equation :: rest =>
      match selectEquation equation with
      | some selection => some (selection.append rest)
      | none => (select rest).map fun selection => selection.prepend equation

def choose (problem : Problem declaration) : Option (Update problem) :=
  (select problem).map Selection.update

def identity (problem : Problem declaration) : Update problem := ⟨generator declaration, problem, by
  constructor
  · intro Next next candidate solved
    simpa only [Assignment.compose_identity_right] using solved
  · intro Next next candidate solved
    exact ⟨candidate, solved, fun identity => (instantiate_generator candidate identity).symm⟩⟩

inductive Result (problem : Problem declaration)
  | residual (update : Update problem)
  | refuted (proof : ∀ {Next : Type} (next : Next → MetaArity S)
      (candidate : Assignment declaration next), ¬ Models candidate problem)

def run : Nat → (problem : Problem declaration) → Result problem
  | 0, problem => .residual (identity problem)
  | fuel + 1, problem =>
      match computed : ContextualRigidSolver.normalize problem with
      | none => .refuted fun _ candidate => ContextualRigidSolver.refused_has_no_solution computed candidate
      | some normalized =>
          let normalizedProof := ContextualRigidSolver.normalization_reduction computed
          match choose normalized with
          | none => .residual ⟨generator declaration, normalized, normalizedProof⟩
          | some update =>
              let first := normalizedProof.compose update.valid
              match run fuel update.remaining with
              | .residual last => .residual
                  ⟨Assignment.compose last.answer (Assignment.compose update.answer (generator declaration)),
                    last.remaining, first.compose last.valid⟩
              | .refuted impossible => .refuted fun next candidate solved => by
                  obtain ⟨residual, restSolved, _⟩ := first.complete next candidate solved
                  exact impossible next residual restSolved

omit [DecidableEq V] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] in
theorem completed_sound {problem : Problem declaration} (update : Update problem)
    (finished : update.remaining = []) : Models update.answer problem := by
  have reduced := update.valid
  rw [finished] at reduced
  exact reduced.finished_sound

omit [DecidableEq V] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] in
theorem retained_factorization {problem : Problem declaration} (update : Update problem)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment declaration next)
    (solved : Models candidate problem) :
    ∃ residual : Assignment declaration next, Models residual update.remaining ∧
      ∀ identity, candidate identity = instantiate residual (update.answer identity) :=
  update.valid.complete next candidate solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklist
