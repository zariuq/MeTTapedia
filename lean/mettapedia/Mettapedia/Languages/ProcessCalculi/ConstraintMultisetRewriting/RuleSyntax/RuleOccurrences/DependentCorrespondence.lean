import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Dependent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Correspondences

/-!
# The dependent full step restricted to a program and the candidate, as an operational correspondence

`dependent_full_eq` is an equality of transition relations through the maps `Dependent.toState` and
`holding`. In the form of `GSLT.IndexedOperational.OperationalCorrespondence`:

* **`dependentCorrespondence`**. Source: the dependent full step restricted to the fresh openings of
  a program `P`. Target: the candidate with ambient program `P`. A dependent state is related to the
  candidate state with the same four fields that holds no rule. Each step is one step, both ways.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface (Frames)
open LogicOverTheStep.StepSpan (Succ)
open FragmentsOfTheStep.TransitionMaps (theoryOf)
open _root_.Mettapedia.GSLT.IndexedOperational (OperationalCorrespondence)

universe uR uZ

variable {Head : Type} {rules : Rules Head} {O : Type} [DecidableEq O] {L : Type}
  [UniverseLevel.LevelOrder L] {levels : LevelModel rules L} {P : Program (Dependent.Terms rules)}
  {R : Type uR} [DecidableEq R] {Z : Type uZ}

/-- **The dependent full step restricted to a program and the candidate with that program ambient,
as an operational correspondence**: a dependent state is related to the candidate state with the
same fields that holds no rule. -/
def dependentCorrespondence (code : R → Rule (Dependent.Terms rules)) (zone : R → Z) :
    OperationalCorrespondence
      (theoryOf (Interface.DependentFull.State rules O) (Succ (Dependent.dependentOn levels P)))
      (theoryOf (RState (Dependent.Terms rules) O R (Rule (Dependent.Terms rules)) Z)
        (Succ (rstep (frames levels) O R Dependent.helperExtensions (ofRules Z) P).toStep)) where
  related s u := u = holding (Dependent.toState s) ∅ code zone
  readStep := by
    rintro origin current next rfl moved
    obtain ⟨t, rfl, -⟩ := holding_closed R (frames levels) Dependent.helperExtensions
      (offers_empty code) zone moved
    exact .inr ⟨Dependent.ofState t,
      (dependent_full_eq code zone origin (Dependent.ofState t)).mpr moved, rfl⟩
  forward := by
    rintro origin after current rfl moved
    have step := (dependent_full_eq (levels := levels) (P := P) code zone origin after).mp moved
    exact ⟨_, path_of_run (Relation.ReflTransGen.single step), rfl⟩

#print axioms dependentCorrespondence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
