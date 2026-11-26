import Mettapedia.GSLT.Core.EnumerableSteps
import Mettapedia.GSLT.Core.Reducts
import Mettapedia.GSLT.LanguageDef.RewritingUniversality
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations

/-!
# Classes of languages

A language presents a GSLT: patterns modulo its equations, closed under contexts and equivalence, with
its reference steps between equivalent representatives (`theoryOf`). Where a language lies among the
semantic and computability classes is read off what it presents:

* a language without equations, collections or algebra declarations presents equality, so its theory
  is a rewriting system and its steps are the reference steps (`equationFree`, `stepModulo_iff_step`);
* a language without rules has no steps (`stepFree`);
* a language whose premises never ask the step has computable successor lists, so decidable steps, when
  its relation environment is computable on codes (`successors_of_noStepPremises`,
  `decidable_of_noStepPremises`);
* the steps of every language are enumerable when its relation environment is computable on codes
  (`EnumerableSteps.referenceSteps_enumerable`), every recursively enumerable relation on numbers is the
  step relation of a language (`RewritingUniversality.re_iff_steps`), and so some language has steps that
  are not decidable (`undecidable_steps`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageClasses

open Mettapedia.Computability
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.EngineCoded
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.ComputabilityClasses
open Mettapedia.GSLT.EnumerableSteps

/-! ## The theory a language presents -/

/-- **The GSLT a language presents**: patterns modulo its equations, and its reference steps between
equivalent representatives. -/
def theoryOf (relEnv : RelationEnv) (language : LanguageDef) : GSLT.{0} where
  Term := Pattern
  equations := Mettapedia.OSLF.MeTTaIL.ReferenceStep.equivalentSetoid relEnv language
  rewrites := Mettapedia.OSLF.MeTTaIL.ReferenceStep.StepModulo relEnv language
  rewrites_resp_left := fun {_ _ target} same moved => by
    obtain ⟨redex, contractum, before, step, after⟩ := moved
    exact ⟨target, ⟨redex, contractum, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ same) before, step,
      after⟩, Relation.EqvGen.refl _⟩
  rewrites_resp_right := fun moved same => by
    obtain ⟨redex, contractum, before, step, after⟩ := moved
    exact ⟨redex, contractum, before, step, Relation.EqvGen.trans _ _ _ after same⟩

/-- **A language without equations presents equality**, so its theory is a rewriting system. -/
theorem equationFree {relEnv : RelationEnv} {language : LanguageDef} (free : language.isEquationFree = true) :
    Reducts.EquationFree ⟨theoryOf relEnv language⟩ := fun _ _ equivalent =>
  (equivalent_iff_eq_of_isEquationFree (relEnv := relEnv) free).mp equivalent

/-- The steps of a language without equations are its reference steps. -/
theorem stepModulo_iff_step {relEnv : RelationEnv} {language : LanguageDef} (free : language.isEquationFree = true)
    {source target : Pattern} : StepModulo relEnv language source target ↔ Step relEnv language source target := by
  constructor
  · rintro ⟨redex, contractum, before, step, after⟩
    rw [(equivalent_iff_eq_of_isEquationFree (relEnv := relEnv) free).mp before,
      ← (equivalent_iff_eq_of_isEquationFree (relEnv := relEnv) free).mp after]
    exact step
  · exact fun step => ⟨source, target, Relation.EqvGen.refl _, step, Relation.EqvGen.refl _⟩

/-- **A language without rules has no steps.** -/
theorem stepFree {relEnv : RelationEnv} {language : LanguageDef} (noRules : language.rewrites = []) :
    StaticPart.StepFree ⟨theoryOf relEnv language⟩ := by
  rintro _ _ ⟨_, _, _, ⟨_, valid⟩, _⟩
  cases valid with
  | rule found _ _ => simp [noRules] at found

/-! ## Languages whose premises never ask the step -/

/-- Whether a premise asks the step itself. -/
def asksStep : Premise → Bool
  | .congruence _ _ => true
  | .scopedStep _ => true
  | .forAll _ _ body => asksStep body
  | _ => false

/-- No premise of any rule asks the step. -/
def NoStepPremises (language : LanguageDef) : Prop :=
  ∀ rule ∈ language.rewrites, ∀ premise ∈ rule.premises, asksStep premise = false

theorem questionsOf_eq_nil (sites : Pattern) :
    ∀ (premise : Premise) (bindings : Bindings), asksStep premise = false → questionsOf sites bindings premise = []
  | .freshness _, _, _ => rfl
  | .relationQuery _ _, _, _ => rfl
  | .congruence _ _, _, asks => by simp [asksStep] at asks
  | .scopedStep _, _, asks => by simp [asksStep] at asks
  | .forAll collection parameter body, bindings, asks => by
      simp only [questionsOf]
      cases collectionElements (bindings.lookup collection) with
      | none => rfl
      | some elements =>
          simp only
          rw [List.flatMap_eq_nil_iff]
          exact fun element _ => questionsOf_eq_nil sites body _ asks

theorem premisesAtUsing_irrelevant (relEnv : RelationEnv) (language : LanguageDef)
    (recursive other : Pattern → List (Witness × Pattern)) (sites : Pattern) :
    ∀ (premises : List Premise) (bindings : Bindings), (∀ premise ∈ premises, asksStep premise = false) →
      premisesAtUsing relEnv language recursive sites bindings premises =
        premisesAtUsing relEnv language other sites bindings premises
  | [], _, _ => rfl
  | premise :: premises, bindings, quiet => by
      have head : premiseAtUsing relEnv language recursive sites bindings premise =
          premiseAtUsing relEnv language other sites bindings premise :=
        premiseAtUsing_congr relEnv language sites premise bindings (fun question asked => by
          rw [questionsOf_eq_nil sites premise bindings (quiet premise List.mem_cons_self)] at asked
          exact absurd asked List.not_mem_nil)
      simp only [premisesAtUsing]
      rw [head]
      refine List.flatMap_congr fun entry _ => ?_
      rw [premisesAtUsing_irrelevant relEnv language recursive other sites premises entry.2
        (fun premise inside => quiet premise (List.mem_cons_of_mem _ inside))]

/-- Without step premises, one rule layer lists every step. -/
theorem stepsAt_succ_eq_one {relEnv : RelationEnv} {language : LanguageDef} (quiet : NoStepPremises language)
    (k : ℕ) (source : Pattern) : stepsAt relEnv language (k + 1) source = stepsAt relEnv language 1 source := by
  simp only [stepsAt]
  refine List.flatMap_congr fun index _ => ?_
  cases found : language.rewrites[index]? with
  | none => rfl
  | some rule =>
      dsimp only
      congr 1
      funext initial
      rw [premisesAtUsing_irrelevant relEnv language (stepsAt relEnv language k) (fun _ => [])
        (captureSites rule) rule.premises initial (quiet rule (List.mem_of_getElem? found))]

/-- **A language whose premises never ask the step has computable successor lists.** -/
theorem successors_of_noStepPremises (relEnv : RelationEnv) (relations : CodeComputable₂ relEnv.tuples)
    (language : LanguageDef) (quiet : NoStepPremises language) :
    ComputableSuccessors (referenceTheory relEnv language) := by
  refine ⟨fun source => (stepsAt relEnv language 1 source).map Prod.snd,
    (CodeComputable.list_map ((stepsAt_computable relEnv language relations).comp
      (CodeComputable.pair (CodeComputable.const 1) CodeComputable.id)) (CodeComputable.snd.comp CodeComputable.snd)),
    fun (source target : Pattern) => ?_⟩
  refine Iff.trans ?_ (step_iff_exists_mem_stepsAt relEnv language (source := source) (target := target)).symm
  constructor
  · intro listed
    obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp listed
    exact ⟨1, entry.1, inside⟩
  · rintro ⟨fuel, witness, inside⟩
    cases fuel with
    | zero => simp [stepsAt] at inside
    | succ k =>
        rw [stepsAt_succ_eq_one quiet] at inside
        exact List.mem_map.mpr ⟨_, inside, rfl⟩

/-- **A language whose premises never ask the step has decidable steps.** -/
theorem decidable_of_noStepPremises (relEnv : RelationEnv) (relations : CodeComputable₂ relEnv.tuples)
    (language : LanguageDef) (quiet : NoStepPremises language) : DecidableSteps (referenceTheory relEnv language) :=
  (successors_of_noStepPremises relEnv relations language quiet).decidable
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode_injective'

/-! ## Languages with undecidable steps -/

open Nat.Partrec (Code)
open Mettapedia.GSLT.LanguageDef.RewritingUniversality (every_re_relation_steps num_codeComputable)
open Mettapedia.GSLT.LanguageDef.PartialRecursive (num)

/-- **Some language has steps that are not decidable**: one that steps a numeral to the inputs on which
the code it numbers halts. -/
theorem undecidable_steps : ∃ language : LanguageDef, ¬ DecidableSteps (referenceTheory RelationEnv.empty language) := by
  have enumerable : REPred fun p : ℕ × ℕ => ((Denumerable.ofNat Code p.1).eval p.2).Dom :=
    (Code.eval_part.comp ((Computable.ofNat Code).comp Computable.fst) Computable.snd).dom_re
  obtain ⟨language, steps⟩ :=
    every_re_relation_steps (R := fun m n => ((Denumerable.ofNat Code m).eval n).Dom) enumerable
  refine ⟨language, fun decidable => ?_⟩
  obtain ⟨test, computable, agrees⟩ := decidable
  obtain ⟨track, trackComputable, tracks⟩ := num_codeComputable
  apply ComputablePred.halting_problem 0
  refine ComputablePred.computable_iff.mpr ⟨fun c => test (track (Encodable.encode c), track 0),
    computable.comp ((trackComputable.comp Computable.encode).pair (Computable.const _)), ?_⟩
  funext c
  apply propext
  have numbered : ∀ n : ℕ, track n = code (num n) := fun n => tracks n
  beta_reduce
  rw [numbered, numbered]
  refine Iff.trans ?_ (agrees (num (Encodable.encode c)) (num 0)).symm
  show _ ↔ Step RelationEnv.empty language (num (Encodable.encode c)) (num 0)
  rw [steps]
  constructor
  · intro halts
    exact ⟨0, rfl, by simpa using halts⟩
  · rintro ⟨n, same, halts⟩
    rw [Mettapedia.GSLT.LanguageDef.RewritingUniversality.num_injective same]
    simpa using halts

end Mettapedia.GSLT.LanguageClasses

#print axioms Mettapedia.GSLT.LanguageClasses.decidable_of_noStepPremises
#print axioms Mettapedia.GSLT.LanguageClasses.undecidable_steps
#print axioms Mettapedia.GSLT.LanguageClasses.stepFree
#print axioms Mettapedia.GSLT.LanguageClasses.equationFree
