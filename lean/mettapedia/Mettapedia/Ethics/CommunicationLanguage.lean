import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction

/-!
# The communication episode, authored as a language definition

The Formal Ethics communication episode — a message prepared, communicated, and
completed, with the communicator's belief and the message's truth fixed
throughout — authored as a `LanguageDef`.  Its GSLT is the one the OSLF
construction generates from the definition (`communicationTheory`); the
observers, bisimulations and concepts of the communication specimen are stated
over that generated theory.

* `communicationLanguage_validate_eq_nil`: the definition passes the structural
  gate, and it generates no equations.
* `step_iff`: a term steps exactly when it is an episode that is prepared or
  communicating, and it steps to the same episode one phase later with belief
  and truth unchanged.  Belief and truth are whatever terms the episode carries;
  the rules do not inspect them.
* A completed episode does not step (`completed_irreducible`).
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.CommunicationLanguage

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction

def communicationTerms : List GrammarRule := [
    { label := "Prepared", category := "Phase", params := [], syntaxPattern := [] },
    { label := "Communicating", category := "Phase", params := [], syntaxPattern := [] },
    { label := "Completed", category := "Phase", params := [], syntaxPattern := [] },
    { label := "Yes", category := "Truth", params := [], syntaxPattern := [] },
    { label := "No", category := "Truth", params := [], syntaxPattern := [] },
    { label := "Episode", category := "Episode",
      params := [.simple "phase" (.base "Phase"), .simple "belief" (.base "Truth"),
        .simple "truth" (.base "Truth")],
      syntaxPattern := [.nonTerminal "phase", .nonTerminal "belief", .nonTerminal "truth"] }
  ]

def communicationRewrites : List RewriteRule := [
    { name := "Start"
      typeContext := [("belief", .base "Truth"), ("truth", .base "Truth")]
      premises := []
      left := .apply "Episode" [.apply "Prepared" [], .fvar "belief", .fvar "truth"]
      right := .apply "Episode" [.apply "Communicating" [], .fvar "belief", .fvar "truth"] },
    { name := "Finish"
      typeContext := [("belief", .base "Truth"), ("truth", .base "Truth")]
      premises := []
      left := .apply "Episode" [.apply "Communicating" [], .fvar "belief", .fvar "truth"]
      right := .apply "Episode" [.apply "Completed" [], .fvar "belief", .fvar "truth"] }
  ]

/-- The communication episode, authored. -/
def communicationLanguage : LanguageDef :=
  LanguageDef.ofCore "Communication" ["Phase", "Truth", "Episode"] communicationTerms []
    communicationRewrites

theorem communicationLanguage_rewrites :
    communicationLanguage.rewrites = communicationRewrites := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
private theorem communicationRewrites_validate :
    ∀ rule ∈ communicationLanguage.rewrites,
      LanguageDef.validateRewrite communicationLanguage rule = [] := by
  intro rule membership
  simp only [communicationLanguage_rewrites, communicationRewrites, List.mem_cons,
    List.mem_nil_iff, or_false] at membership
  rcases membership with rfl | rfl
  all_goals
    simp +decide [LanguageDef.validateRewrite, communicationLanguage, LanguageDef.ofCore,
      communicationTerms, LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames, LanguageDef.typeNames]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem communicationLanguage_validate_eq_nil : communicationLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  all_goals try decide +kernel
  exact communicationRewrites_validate

theorem communicationLanguage_equationFree : communicationLanguage.isEquationFree = true := by
  decide +kernel

/-- The GSLT the OSLF construction generates from the authored definition. -/
abbrev communicationTheory : Mettapedia.GSLT.GSLT := langGSLT communicationLanguage

/-! ## Terms -/

def prepared : Pattern := .apply "Prepared" []
def communicating : Pattern := .apply "Communicating" []
def completed : Pattern := .apply "Completed" []
def yes : Pattern := .apply "Yes" []
def no : Pattern := .apply "No" []

def episode (phase belief truth : Pattern) : Pattern := .apply "Episode" [phase, belief, truth]

theorem episode_injective {phase belief truth phase' belief' truth' : Pattern}
    (same : episode phase belief truth = episode phase' belief' truth') :
    phase = phase' ∧ belief = belief' ∧ truth = truth' := by
  simpa [episode] using same

/-! ## Reduction -/

abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

theorem communicationLanguage_unconditional :
    isUnconditionalAligned communicationLanguage = true := by
  decide +kernel

theorem engineStep_iff_mem_rootReducts {term target : Pattern} :
    Step base communicationLanguage term target ↔ target ∈ rootReducts communicationLanguage term :=
  step_iff_mem_rootReducts base communicationLanguage communicationLanguage_unconditional term target

theorem theoryStep_iff_engineStep {term target : Pattern} :
    communicationTheory.Step term target ↔ Step base communicationLanguage term target :=
  langSemanticReduces_iff_langReduces_of_equation_free communicationLanguage_equationFree term target

/-- **One step of the generated theory.** -/
theorem step_iff (term target : Pattern) :
    communicationTheory.Step term target ↔
      ∃ belief truth,
        (term = episode prepared belief truth ∧ target = episode communicating belief truth) ∨
          (term = episode communicating belief truth ∧ target = episode completed belief truth) := by
  rw [theoryStep_iff_engineStep, engineStep_iff_mem_rootReducts]
  constructor
  · intro member
    simp only [rootReducts, communicationLanguage_rewrites, communicationRewrites, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_append, List.mem_map] at member
    rcases member with ⟨bindings, matched, rfl⟩ | ⟨bindings, matched, rfl⟩
    · have instance_eq := matchPattern_correct matched (by decide +kernel)
      refine ⟨applyBindings bindings (.fvar "belief"), applyBindings bindings (.fvar "truth"), .inl ⟨?_, ?_⟩⟩
      · rw [← instance_eq]; simp [episode, prepared, applyBindings]
      · simp [episode, communicating, applyBindings]
    · have instance_eq := matchPattern_correct matched (by decide +kernel)
      refine ⟨applyBindings bindings (.fvar "belief"), applyBindings bindings (.fvar "truth"), .inr ⟨?_, ?_⟩⟩
      · rw [← instance_eq]; simp [episode, communicating, applyBindings]
      · simp [episode, completed, applyBindings]
  · rintro ⟨belief, truth, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · simp [rootReducts, communicationLanguage_rewrites, communicationRewrites, episode, prepared, communicating, matchPattern,
        matchArgs, mergeBindings, applyBindings]
    · simp [rootReducts, communicationLanguage_rewrites, communicationRewrites, episode, communicating, completed, matchPattern,
        matchArgs, mergeBindings, applyBindings]

theorem start_step (belief truth : Pattern) :
    communicationTheory.Step (episode prepared belief truth) (episode communicating belief truth) :=
  (step_iff _ _).mpr ⟨belief, truth, .inl ⟨rfl, rfl⟩⟩

theorem finish_step (belief truth : Pattern) :
    communicationTheory.Step (episode communicating belief truth) (episode completed belief truth) :=
  (step_iff _ _).mpr ⟨belief, truth, .inr ⟨rfl, rfl⟩⟩

/-- A completed episode does not step. -/
theorem completed_irreducible (belief truth target : Pattern) :
    ¬ communicationTheory.Step (episode completed belief truth) target := by
  rw [step_iff]
  rintro ⟨belief', truth', (⟨same, -⟩ | ⟨same, -⟩)⟩ <;>
    simp [episode, completed, prepared, communicating] at same

#print axioms communicationLanguage_validate_eq_nil
#print axioms step_iff
#print axioms completed_irreducible

end Mettapedia.Ethics.CommunicationLanguage
