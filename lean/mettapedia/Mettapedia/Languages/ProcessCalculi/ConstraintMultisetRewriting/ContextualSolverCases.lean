import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingWorklist
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedSelfPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedImitation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedFlexPair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexive

/-!
# Inspectable solver choices retain their actual equation and frame operation

A root case contains the existing terms, declaration identities, parameter
maps and recovered binding used by its concrete solver operation. A located
choice additionally retains the exact queue prefix and suffix. Performing
that choice uses the existing frame updates and maps every retained equation.
The data contains no assumed progress or completeness theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverCases

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V : Type} [DecidableEq V] {source : V → MetaArity S}

inductive RootCase (S : Signature) {V : Type} [DecidableEq V] (source : V → MetaArity S) :
    Equation (Observation S source) → Type
  | reflexive {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort) :
      RootCase S source (observe term, observe term)
  | binding {Γ : Ctx S} {sort : S.Srt} {left right : Term (signature S source) Γ sort}
      (recovered : ContextualBindingCase.Case left right) : RootCase S source (observe left, observe right)
  | imitation (identity : V) {Γ : Ctx S} (rho : Ren S (source identity).1 Γ)
      (operator : S.Op (source identity).2) (fields : Args (signature S source) (S.arity operator) Γ) :
      RootCase S source
        (observe (rename (S := signature S source) rho (generator source identity)),
          observe (Term.op (.inl operator) fields))
  | selfPair (identity : V) {Γ : Ctx S} (left right : Ren S (source identity).1 Γ) (different : left ≠ right) :
      RootCase S source
        (observe (rename (S := signature S source) left (generator source identity)),
          observe (rename (S := signature S source) right (generator source identity)))
  | flexPair (first second : V) (different : first ≠ second) (sorts : (source first).2 = (source second).2)
      {Γ : Ctx S} (left : Ren S (source first).1 Γ) (right : Ren S (source second).1 Γ) :
      RootCase S source
        (observe (rename (S := signature S source) left (generator source first)),
          observe (rename (S := signature S source) right (generator source second)))
  | reverse {equation : Equation (Observation S source)} (original : RootCase S source (equation.2, equation.1)) :
      RootCase S source equation

def RootCase.perform : {equation : Equation (Observation S source)} → RootCase S source equation →
    ContextualFrameUpdate.Update [equation]
  | _, .reflexive term => ContextualReflexive.discharge term
  | _, .binding recovered =>
      ⟨V, inferInstance, source, ContextualBinding.answer recovered.chosen recovered.body, [], by
        simpa only [observeProblem, observe, List.map_cons, List.map_nil, List.append_nil, mapProblem] using
          of_principal_prefix recovered.principal []⟩
  | _, .imitation identity rho operator fields => ContextualNamedImitation.apply source identity rho operator fields []
  | _, .selfPair identity left right _ => ContextualNamedSelfPair.apply source identity left right []
  | _, .flexPair first second different sorts left right =>
      ContextualNamedFlexPair.apply source first second different sorts left right []
  | _, .reverse original => original.perform.swap

structure Choice (problem : Problem source) where
  before : Problem source
  equation : Equation (Observation S source)
  selected : RootCase S source equation
  after : Problem source
  split : problem = before ++ equation :: after

def RootCase.locate {equation : Equation (Observation S source)} (selected : RootCase S source equation)
    (before after : Problem source) : Choice (before ++ equation :: after) :=
  ⟨before, equation, selected, after, rfl⟩

def Choice.perform {problem : Problem source} (choice : Choice problem) : ContextualFrameUpdate.Update problem :=
  let updated := (choice.selected.perform.keep_right choice.after).keep_left choice.before
  ⟨updated.Variables, updated.equality, updated.declaration, updated.answer, updated.remaining, by
    exact Eq.mpr (congrArg (fun equations => Reduction equations updated.answer updated.remaining) choice.split)
      updated.valid⟩

def Choice.prepend {problem : Problem source} (choice : Choice problem)
    (equation : Equation (Observation S source)) : Choice (equation :: problem) where
  before := equation :: choice.before
  equation := choice.equation
  selected := choice.selected
  after := choice.after
  split := congrArg (List.cons equation) choice.split

def Choice.append {problem : Problem source} (choice : Choice problem) (extra : Problem source) : Choice (problem ++ extra) where
  before := choice.before
  equation := choice.equation
  selected := choice.selected
  after := choice.after ++ extra
  split := (congrArg (fun equations => equations ++ extra) choice.split).trans (by
    simp only [List.append_assoc, List.cons_append])

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSolverCases
