import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
import MettaHyperonFull.Minimal.Interpreter

/-!
# Function operators must be evaluated

The published `interpret_function` algorithm evaluates a function operator
under the selected arrow type before evaluating its arguments.  This is not
an eliminable administrative step: recursive `%Undefined%` consistency is
not transitive, so a compatible earlier overload can add an observable type
constraint even though that overload was inapplicable to the call arguments.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaOperatorHeadEvaluationCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation
open Spec.Type.RuntimeRefinement

private def selectedArrow : Atom :=
  .expression [.symbol "->", Atom.undefinedType, Atom.atomType, .var "t"]

private def earlierArrow : Atom :=
  .expression [.symbol "->", .symbol "A", Atom.atomType, .symbol "A"]

private def beforeHead : Bindings :=
  ⟨[("q", .var "t")], []⟩

private def afterHead : Bindings :=
  ⟨[("t", .symbol "A"), ("q", .var "t")], []⟩

private def modelA : String → Atom := fun name =>
  if name = "q" ∨ name = "t" then .symbol "A" else .var name

private def modelB : String → Atom := fun name =>
  if name = "q" ∨ name = "t" then .symbol "B" else .var name

/-- The selected arrow and the earlier overload have a successful recursive
type match.  The nested undefined formal is gradual, while the return match
adds `t = A` to the already visible equation `q = t`. -/
theorem head_type_match_adds_constraint :
    CorePlusR2TypeMatchRel selectedArrow earlierArrow
      beforeHead afterHead := by
  constructor
  · refine ⟨modelA, ⟨?_, by simp [afterHead]⟩⟩
    intro name value member
    rcases List.mem_cons.mp member with ⟨rfl, rfl⟩ | member
    · simp [modelA, applyTypeValuation]
    · have : name = "q" ∧ value = .var "t" := by simpa [afterHead] using member
      rcases this with ⟨rfl, rfl⟩
      simp [modelA, applyTypeValuation]
  · intro valuation
    constructor
    · intro outputSatisfied
      have tEqualsA : valuation "t" = .symbol "A" := by
        simpa [applyTypeValuation] using
          outputSatisfied.1 "t" (.symbol "A") (by simp [afterHead])
      have qEqualsT : valuation "q" = valuation "t" := by
        simpa [applyTypeValuation] using
          outputSatisfied.1 "q" (.var "t") (by simp [afterHead])
      constructor
      · refine ⟨?_, by simp [beforeHead]⟩
        intro name value member
        have : name = "q" ∧ value = .var "t" := by
          simpa [beforeHead] using member
        rcases this with ⟨rfl, rfl⟩
        simpa [applyTypeValuation] using qEqualsT
      · simp [selectedArrow, earlierArrow, CorePlusR2TypeConsistent,
          ReducedTypeConsistent, ReducedTypeListConsistent,
          applyTypeValuation, Atom.undefinedType, Atom.atomType, tEqualsA]
    · rintro ⟨inputSatisfied, consistent⟩
      have qEqualsT : valuation "q" = valuation "t" := by
        simpa [applyTypeValuation] using
          inputSatisfied.1 "q" (.var "t") (by simp [beforeHead])
      have tEqualsA : valuation "t" = .symbol "A" := by
        simpa [selectedArrow, earlierArrow, CorePlusR2TypeConsistent,
          ReducedTypeConsistent, ReducedTypeListConsistent,
          applyTypeValuation, Atom.undefinedType, Atom.atomType] using
            consistent
      refine ⟨?_, by simp [afterHead]⟩
      intro name value member
      rcases List.mem_cons.mp member with ⟨rfl, rfl⟩ | member
      · simpa [applyTypeValuation] using tEqualsA
      · have : name = "q" ∧ value = .var "t" := by
          simpa [afterHead] using member
        rcases this with ⟨rfl, rfl⟩
        simpa [applyTypeValuation] using qEqualsT

/-- The successful head match is not observationally neutral at the caller's
`q` variable.  The input admits `q = B`; every output model forces `q = A`. -/
theorem head_type_match_not_binding_neutral :
    ¬BindingTheoryEquivAt ["q"] beforeHead afterHead := by
  intro equivalence
  have beforeSatisfied : TypeBindingSatisfied modelB beforeHead := by
    simp [modelB, beforeHead, TypeBindingSatisfied, applyTypeValuation]
  obtain ⟨afterModel, afterSatisfied, agrees⟩ :=
    equivalence.leftToRight modelB beforeSatisfied
  have qEqualsT : afterModel "q" = afterModel "t" := by
    simpa [applyTypeValuation] using
      afterSatisfied.1 "q" (.var "t") (by simp [afterHead])
  have tEqualsA : afterModel "t" = .symbol "A" := by
    simpa [applyTypeValuation] using
      afterSatisfied.1 "t" (.symbol "A") (by simp [afterHead])
  have qEqualsB : afterModel "q" = .symbol "B" := by
    simpa [modelB] using (agrees "q" (by simp)).symm
  rw [qEqualsT, tEqualsA] at qEqualsB
  simp at qEqualsB

/-- Negative boundary: the same input theory really is observationally
neutral with itself, isolating the added head constraint as the cause. -/
example : BindingTheoryEquivAt ["q"] beforeHead beforeHead :=
  BindingTheoryEquivAt.refl ["q"] beforeHead

end Mettapedia.Languages.MeTTa.HE.LeaTTaOperatorHeadEvaluationCounterexample
