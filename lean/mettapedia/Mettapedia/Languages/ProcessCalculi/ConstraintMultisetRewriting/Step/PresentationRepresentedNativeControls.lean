import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeOriginExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativeOriginControls

/-!
# A represented native publication protocol

The codes name the two fully specified native firings of the existing
conditional-template example, their origin keys and their resulting worlds.
They are not a projection that discards publication recipes. Both results are
represented before permission is considered; the profile permits the intended
publication and refuses its changed recipe and origin alias.

This finite protocol is a nonvacuity control for the general representation
interface, not a bound on native states, programs or candidate families.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.RepresentedNativeControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Interface NativeOrigins NativeOriginControls ContextualConditionalTemplateControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)

inductive Stage where
  | before
  | after (authoredRecipe : Bool)
  deriving DecidableEq

def Choice : Stage → Type
  | .before => Bool × Bool
  | .after _ => Empty

instance (stage : Stage) : DecidableEq (Choice stage) := by
  cases stage <;> dsimp [Choice] <;> infer_instance

def mark (index : Nat) : Configuration Payloads.Term Nat := ⟨[], {index}⟩

def statePattern : Stage → Pattern
  | .before => .apply "StateData" [Payloads.configurationPattern (mark 0)]
  | .after false => .apply "StateData" [Payloads.configurationPattern (mark 1)]
  | .after true => .apply "StateData" [Payloads.configurationPattern (mark 2)]

def readState (pattern : Pattern) : Option Stage :=
  if pattern = statePattern .before then some .before
  else if pattern = statePattern (.after false) then some (.after false)
  else if pattern = statePattern (.after true) then some (.after true)
  else none

def origin (isAlias : Bool) : Nat := if isAlias then 1 else 0

def callPattern (choice : Bool × Bool) : Pattern :=
  .apply "FiringData" [Payloads.configurationPattern (mark 0),
    Payloads.rulePattern ⟨[], [], [], [],
      [.node (.quotedRule (origin choice.1)) .nil, .idx (if choice.2 then 1 else 0)]⟩,
    Payloads.selectionPattern ⟨[], [], []⟩]

def firingPattern : ((stage : Stage) × Choice stage) → Pattern
  | ⟨.before, choice⟩ => callPattern choice
  | ⟨.after _, impossible⟩ => nomatch impossible

def readFiring (pattern : Pattern) : Option ((stage : Stage) × Choice stage) :=
  if pattern = callPattern (false, false) then some ⟨.before, (false, false)⟩
  else if pattern = callPattern (false, true) then some ⟨.before, (false, true)⟩
  else if pattern = callPattern (true, false) then some ⟨.before, (true, false)⟩
  else if pattern = callPattern (true, true) then some ⟨.before, (true, true)⟩
  else none

theorem state_readback (stage : Stage) : readState (statePattern stage) = some stage := by
  cases stage with
  | before => decide +kernel
  | after recipe => cases recipe <;> decide +kernel

theorem firing_readback (candidate : (stage : Stage) × Choice stage) :
    readFiring (firingPattern candidate) = some candidate := by
  rcases candidate with ⟨stage, choice⟩
  cases stage with
  | before => rcases choice with ⟨key, recipe⟩; cases key <;> cases recipe <;> decide +kernel
  | after recipe => nomatch choice

def encoding : Encoding Stage Choice where
  state := ⟨⟨"tcalc.native-publication-world", 1⟩, readState, statePattern, state_readback⟩
  firing := ⟨⟨"tcalc.native-publication-invocation", 1⟩, readFiring, firingPattern, firing_readback⟩

variable (authored raw : NativeFiring originState) (authoredReady : authored.Realized) (rawReady : raw.Realized)

noncomputable abbrev nativeProfile := profile (catalogueAt authored.rule) (permitsExactly authored)

def world : Stage → NativeState base Nat [] ()
  | .before => originState
  | .after false => nativeStep.result raw rawReady
  | .after true => nativeStep.result authored authoredReady

def candidate : {stage : Stage} → Choice stage → Candidate (world authored raw authoredReady rawReady stage)
  | .before, choice => ⟨origin choice.1, if choice.2 then authored else raw⟩
  | .after _, impossible => nomatch impossible

def represented : (nativeProfile authored).effectCore.Representation Stage Choice where
  state := world authored raw authoredReady rawReady
  firing := candidate authored raw authoredReady rawReady
  preparedResult {stage} choice _ := match stage, choice with
    | .before, choice => .after choice.2
    | .after _, impossible => nomatch impossible
  result_eq {stage} choice prepared := by
    cases stage with
    | before => rcases choice with ⟨key, recipe⟩; cases recipe <;> rfl
    | after recipe => nomatch choice

theorem ready (choice : Bool × Bool) :
    (represented authored raw authoredReady rawReady).effect.Prepares (s := .before) choice := by
  rcases choice with ⟨key, recipe⟩
  cases recipe
  · exact nativeStep.prepares rawReady
  · exact nativeStep.prepares authoredReady

theorem allowed_iff (different : authored ≠ raw) (choice : Bool × Bool)
    (prepared : (represented authored raw authoredReady rawReady).effect.Prepares (s := .before) choice) :
    (represented authored raw authoredReady rawReady).admission (nativeProfile authored).eventAdmission
      (s := .before) choice prepared ↔ choice.1 = false ∧ choice.2 = true := by
  rcases choice with ⟨key, recipe⟩
  constructor
  · rintro ⟨_, _, permitted⟩
    have keyFalse : key = false := by
      cases key
      · rfl
      · exact False.elim (Nat.one_ne_zero permitted.1)
    refine ⟨keyFalse, ?_⟩
    cases recipe
    · exact False.elim (different (eq_of_heq permitted.2).symm)
    · rfl
  · rintro ⟨rfl, rfl⟩
    exact ⟨authoredReady, lookup_alias authored.rule 0 (by decide), rfl, HEq.rfl⟩

noncomputable def decisions := Decisions.ofClassical
  (represented authored raw authoredReady rawReady).effect
  ((represented authored raw authoredReady rawReady).admission (nativeProfile authored).eventAdmission)

noncomputable def queries := effectQueries
  (represented authored raw authoredReady rawReady).effect
  ((represented authored raw authoredReady rawReady).admission (nativeProfile authored).eventAdmission)
  encoding (decisions authored raw authoredReady rawReady)

def requestCode (choice : Bool × Bool) : Pattern := request (statePattern .before) (callPattern choice)

theorem authored_publication_executes (different : authored ≠ raw) :
    atState (statePattern (.after true)) ∈ rewriteStepWithPremisesUsing
      (queries authored raw authoredReady rawReady).relations authoredLanguage (requestCode (false, true)) := by
  apply (authored_execution_iff_represented _ _ (represented authored raw authoredReady rawReady)
    encoding (decisions authored raw authoredReady rawReady)
    (source := .before) (target := .after true) (false, true)).mpr
  have prepared := ready authored raw authoredReady rawReady (false, true)
  exact ⟨⟨(false, true), prepared,
    (allowed_iff authored raw authoredReady rawReady different _ prepared).mpr ⟨rfl, rfl⟩, rfl⟩, rfl⟩

include rawReady in
theorem authored_publication_has_native_event (different : authored ≠ raw) :
    ∃ event : SourceEvent (catalogueAt authored.rule) (permitsExactly authored) originState
        (nativeStep.result authored authoredReady), event.event.firing = ⟨0, authored⟩ := by
  exact authored_execution_preserves _ _ (represented authored raw authoredReady rawReady)
    encoding (decisions authored raw authoredReady rawReady)
    (source := .before) (target := .after true) (false, true)
    (authored_publication_executes authored raw authoredReady rawReady different)

theorem refused_preparation_retained (different : authored ≠ raw) (choice : Bool × Bool)
    (refused : ¬ (choice.1 = false ∧ choice.2 = true)) :
    (queries authored raw authoredReady rawReady).prepare (statePattern .before) (callPattern choice) =
        some (statePattern (.after choice.2)) ∧
      ∀ target, atState (statePattern target) ∉ rewriteStepWithPremisesUsing
        (queries authored raw authoredReady rawReady).relations authoredLanguage (requestCode choice) := by
  constructor
  · change (effectQueries (represented authored raw authoredReady rawReady).effect
      ((represented authored raw authoredReady rawReady).admission (nativeProfile authored).eventAdmission)
      encoding (decisions authored raw authoredReady rawReady)).prepare
      (encoding.state.view (sort := ()) .before)
      (encoding.firing.view (sort := ()) ⟨.before, choice⟩) = _
    rw [preparation_encoded]
    split
    · rfl
    · rename_i impossible
      exact False.elim (impossible (ready authored raw authoredReady rawReady choice))
  · intro target executed
    obtain ⟨event, same⟩ := (authored_execution_iff_represented _ _
      (represented authored raw authoredReady rawReady) encoding
      (decisions authored raw authoredReady rawReady) (source := .before) (target := target) choice).mp executed
    apply refused
    simpa only [same] using
      (allowed_iff authored raw authoredReady rawReady different event.firing event.prepared).mp event.permitted

/-- A real conditional-template execution instantiates the represented
publication protocol; its two terminal interpretations are different. -/
theorem actual_native_presentation (fuel : Nat) :
    ∃ (authored raw : NativeFiring originState) (authoredReady : authored.Realized) (rawReady : raw.Realized),
      authored.rule = raw.rule ∧
      world authored raw authoredReady rawReady (.after true) ≠
        world authored raw authoredReady rawReady (.after false) ∧
      atState (statePattern (.after true)) ∈ rewriteStepWithPremisesUsing
        (queries authored raw authoredReady rawReady).relations authoredLanguage (requestCode (false, true)) ∧
      (queries authored raw authoredReady rawReady).prepare (statePattern .before) (callPattern (false, false)) =
        some (statePattern (.after false)) ∧
      ∀ target, atState (statePattern target) ∉ rewriteStepWithPremisesUsing
        (queries authored raw authoredReady rawReady).relations authoredLanguage (requestCode (false, false)) := by
  obtain ⟨authored, raw, authoredReady, rawReady, sameRule, _, _, _, _, _, different⟩ :=
    PublicationControls.native_result_depends_on_recipes fuel
  have distinct : authored ≠ raw := by
    intro same
    subst raw
    exact different rfl
  have refusal := refused_preparation_retained authored raw authoredReady rawReady distinct
    (false, false) (by simp)
  exact ⟨authored, raw, authoredReady, rawReady, sameRule, different,
    authored_publication_executes authored raw authoredReady rawReady distinct, refusal⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.RepresentedNativeControls
