import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.MatchBindingExtension

/-!
# Binding preservation through ordered contextual premises

Premise evaluation may add captures but preserves every existing binding.
Consequently an authored left-hand side still denotes the matched source
after all premises have run. Recursive premises use the actual contextual
step judgment; no replacement evaluator is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ContextualStep

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.MatchBindingExtension

theorem bindingsExtends_refl (bindings : Bindings) : BindingsExtends bindings bindings :=
  fun _ _ found => found

theorem bindingsExtends_trans {first middle final : Bindings}
    (left : BindingsExtends first middle) (right : BindingsExtends middle final) :
    BindingsExtends first final := fun name value found => right name value (left name value found)

theorem bindingsExtends_of_merge {first second result : Bindings}
    (merged : mergeBindings first second = some result) : BindingsExtends first result :=
  fun _ _ found => mergeBindings_subsumed_left merged found

theorem bindingsExtends_of_merge_right {first second result : Bindings}
    (merged : mergeBindings first second = some result) : BindingsExtends second result :=
  fun _ _ found => mergeBindings_subsumed_right merged found

/-- The engine's nonrecursive boundary preserves seed bindings. Its rejected
premise forms have no outputs and cannot grant an extension or an overwrite. -/
theorem engineBasePremises_bindingsExtends
    {env : RelationEnv} {language : LanguageDef} {initial final : Bindings} {premise : Premise}
    (member : final ∈ engineBasePremises env language initial premise) :
    BindingsExtends initial final := by
  cases premise with
  | freshness condition =>
      have unchanged := premiseStepWithEnv_freshness_mem (relEnv := env) (lang := language) member
      subst final
      exact bindingsExtends_refl initial
  | relationQuery relation arguments =>
      obtain ⟨premiseBindings, merged⟩ := premiseStepWithEnv_relationQuery_mem member
      exact bindingsExtends_of_merge merged
  | congruence source target => simp [engineBasePremises] at member
  | scopedStep step => simp [engineBasePremises, premiseStepWithEnv] at member
  | forAll collection parameter body => simp [engineBasePremises, premiseStepWithEnv] at member

theorem PremiseAt.bindingsExtends
    {env : RelationEnv} {language : LanguageDef} {fuel : Nat}
    {initial final : Bindings} {premise : Premise}
    (event : PremiseAt (engineBasePremises env) language fuel initial premise final) :
    BindingsExtends initial final := by
  cases event with
  | freshness member => exact engineBasePremises_bindingsExtends member
  | relationQuery member => exact engineBasePremises_bindingsExtends member
  | forAll member => exact engineBasePremises_bindingsExtends member
  | congruence _ _ merged => exact bindingsExtends_of_merge merged
  | scopedRoot _ _ _ merged => exact bindingsExtends_of_merge merged

theorem PremisesAt.bindingsExtends
    {env : RelationEnv} {language : LanguageDef} {fuel : Nat}
    {initial final : Bindings} {premises : List Premise}
    (events : PremisesAt (engineBasePremises env) language fuel initial premises final) :
    BindingsExtends initial final := by
  induction premises generalizing initial final with
  | nil =>
      cases events
      exact bindingsExtends_refl _
  | cons premise premises ih =>
      cases events with
      | cons first rest => exact bindingsExtends_trans first.bindingsExtends (ih rest)

/-- Matching remains correct after an ordered premise sequence extends its
captures. The syntactic well-formedness requirement is the existing match
contract, rather than an assumption that the desired reconstruction holds. -/
theorem PremisesAt.reconstruct_matched
    {env : RelationEnv} {language : LanguageDef} {fuel : Nat}
    {initial final : Bindings} {premises : List Premise} {schema source : Pattern}
    (events : PremisesAt (engineBasePremises env) language fuel initial premises final)
    (matched : MatchRel schema source initial)
    (correct : Pattern.isMatchCorrect schema = true) :
    applyBindings final schema = source :=
  matchRel_correct_of_extends matched correct events.bindingsExtends

/-- Recover the actual stage at which a retained premise was evaluated. Both
the earlier seed and the resulting captures embed consistently in the run. -/
theorem PremisesAt.premise_member
    {env : RelationEnv} {language : LanguageDef} {fuel : Nat}
    {initial final : Bindings} {premises : List Premise} {selected : Premise}
    (events : PremisesAt (engineBasePremises env) language fuel initial premises final)
    (member : selected ∈ premises) :
    ∃ before after,
      BindingsExtends initial before ∧ BindingsExtends after final ∧
      PremiseAt (engineBasePremises env) language fuel before selected after := by
  induction premises generalizing initial final with
  | nil => cases member
  | cons first rest ih =>
      cases events with
      | cons firstEvent restEvents =>
          rcases List.mem_cons.mp member with same | later
          · subst selected
            exact ⟨_, _, bindingsExtends_refl _, restEvents.bindingsExtends, firstEvent⟩
          · obtain ⟨before, after, seed, tail, event⟩ := ih restEvents later
            exact ⟨before, after, bindingsExtends_trans firstEvent.bindingsExtends seed,
              tail, event⟩

/-- Read a recursive congruence's target in the final capture map. Its source
is read at the original stage; once ground, it can also be read at the final
stage without changing the actual contextual step. -/
theorem PremisesAt.congruence_member
    {env : RelationEnv} {language : LanguageDef} {fuel : Nat}
    {initial final : Bindings} {premises : List Premise} {source target : Pattern}
    (events : PremisesAt (engineBasePremises env) language fuel initial premises final)
    (member : .congruence source target ∈ premises)
    (sourceCorrect : Match.Pattern.isMatchCorrect source = true)
    (targetCorrect : Match.Pattern.isMatchCorrect target = true) :
    ∃ before,
      BindingsExtends initial before ∧ BindingsExtends before final ∧
      StepAt (engineBasePremises env) language fuel
        (applyBindings before source) (applyBindings final target) ∧
      ((applyBindings before source).isGround = true →
        StepAt (engineBasePremises env) language fuel
          (applyBindings final source) (applyBindings final target)) := by
  obtain ⟨before, after, seed, tail, event⟩ := events.premise_member member
  have extension := bindingsExtends_trans event.bindingsExtends tail
  cases event with
  | congruence step matched merged =>
      have result := matchRel_correct_of_extends (matchPattern_sound matched) targetCorrect
        (bindingsExtends_trans (bindingsExtends_of_merge_right merged) tail)
      have actual := result.symm ▸ step
      refine ⟨before, seed, extension, actual, ?_⟩
      intro ground
      have unchanged := applyBindings_eq_of_extends_of_ground sourceCorrect extension ground
      exact unchanged.symm ▸ actual

end Mettapedia.OSLF.MeTTaIL.ContextualStep
