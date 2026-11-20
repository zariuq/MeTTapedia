import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.SourceNativeBags
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedExample

/-!
# Native readings of equal answers retain distinct source origins

The two source equations have equal bodies and equal returned values. Their
rigid index words remain different, each has an actual native execution
reading, and their answer bag has two occurrences. An incorrect value has
no certified native reading of that class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SourceNativeControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting Hosting.Alternatives
open RuleSyntax.StepWeb
open Hosting.Alternatives.Controls (N D dupP q3 dupP_plain)
open Counted.Example (q3_unopened)

noncomputable local instance : DecidableEq (Set (Term MSig [] ())) := Classical.decEq _

theorem two_origins_native (occupied : Finset ℕ) (fuel : RuleName → ℕ) :
    ([.eqn 0,.ret] : List RuleName) ≠ [.eqn 1,.ret] ∧
      SourceNativeReadouts.NativeShows (D := D) N dupP q3 [.eqn 0,.ret] occupied (csym "one") ∧
      SourceNativeReadouts.NativeShows (D := D) N dupP q3 [.eqn 1,.ret] occupied (csym "one") := by
  obtain ⟨_,_,_,_,_,left,right,_⟩ := Counted.Example.written_twice_answers
  refine ⟨by decide,?_,?_⟩
  · apply (SourceNativeReadouts.classAnswer_iff_native (D := D) N dupP_plain q3 trivial q3_unopened
      [.eqn 0,.ret] occupied fuel (csym "one")).mp
    rw [left]
    exact Set.mem_singleton _
  · apply (SourceNativeReadouts.classAnswer_iff_native (D := D) N dupP_plain q3 trivial q3_unopened
      [.eqn 1,.ret] occupied fuel (csym "one")).mp
    rw [right]
    exact Set.mem_singleton _

theorem native_answer_bag (occupied : Finset ℕ) (fuel : RuleName → ℕ) :
    ({[.eqn 0,.ret],[.eqn 1,.ret]} : Multiset (List RuleName)).map
        (SourceNativeBags.answers (D := D) N dupP q3 occupied) =
      {{csym "one"},{csym "one"}} := by
  obtain ⟨_,_,_,_,_,left,right,_⟩ := Counted.Example.written_twice_answers
  have mapped := congrArg
    (fun read : List RuleName → Set (Term MSig [] ()) =>
      ({[.eqn 0,.ret],[.eqn 1,.ret]} : Multiset (List RuleName)).map read)
    (SourceNativeBags.answers_eq_class (D := D) N dupP_plain q3 trivial q3_unopened occupied fuel)
  have assembled : ({[.eqn 0,.ret],[.eqn 1,.ret]} : Multiset (List RuleName)).map
      (classAnswer (D := D) N dupP q3) =
      ({{csym "one"},{csym "one"}} : Multiset (Set (Term MSig [] ()))) := by
    simp [left,right]
  exact mapped.trans assembled

theorem support_loses_a_native_answer_occurrence (occupied : Finset ℕ) (fuel : RuleName → ℕ) :
    (({[.eqn 0,.ret],[.eqn 1,.ret]} : Multiset (List RuleName)).map
      (SourceNativeBags.answers (D := D) N dupP q3 occupied)).card = 2 ∧
    (({[.eqn 0,.ret],[.eqn 1,.ret]} : Multiset (List RuleName)).map
      (SourceNativeBags.answers (D := D) N dupP q3 occupied)).toFinset.card = 1 := by
  rw [native_answer_bag occupied fuel]
  simp

theorem wrong_value_refused (occupied : Finset ℕ) (fuel : RuleName → ℕ) :
    ¬ SourceNativeReadouts.NativeShows (D := D) N dupP q3 [.eqn 0,.ret] occupied (csym "two") := by
  intro shown
  obtain ⟨_,_,_,_,_,left,_,_⟩ := Counted.Example.written_twice_answers
  have source := (SourceNativeReadouts.classAnswer_iff_native (D := D) N dupP_plain q3 trivial q3_unopened
    [.eqn 0,.ret] occupied fuel (csym "two")).mpr shown
  rw [left] at source
  have different : (csym "two" : Term MSig [] ()) ≠ csym "one" := by decide
  exact different (Set.mem_singleton_iff.mp source)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.SourceNativeControls
