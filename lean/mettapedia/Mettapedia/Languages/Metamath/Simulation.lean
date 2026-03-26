import Mettapedia.Languages.Metamath.GroundedSemantics
import Mettapedia.Languages.Metamath.LanguageDefDSL

/-!
# Metamath Simulation Scaffold

First bridge lemmas connecting language-labeled transitions to
`StateCorresponds`.
-/

namespace Mettapedia.Languages.Metamath.Simulation

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.LanguageDefDSL

/-- Label lookup over the authored Metamath rewrite table. -/
def hasRewriteByName (label : String) : Bool :=
  metamathCore.rewrites.any (fun rw => rw.name == label)

/-- A language transition is a runtime step whose label is present in the
    authored Metamath rewrite set. -/
def LanguageTransition (rt rt' : RuntimeState) (label : String) : Prop :=
  hasRewriteByName label = true ∧ RuntimeState.step? rt label = some rt'

/-- `stepSpec?` is exactly runtime stepping followed by bridge projection. -/
theorem stepSpec?_iff
    (rt : RuntimeState) (label : String) (sp' : SpecState) :
    RuntimeState.stepSpec? rt label = some sp' ↔
      ∃ rt', RuntimeState.step? rt label = some rt' ∧
        RuntimeState.toSpecState? rt' = some sp' := by
  unfold RuntimeState.stepSpec?
  constructor
  · intro h
    cases hstep : RuntimeState.step? rt label with
    | none =>
        simp [hstep] at h
    | some rt' =>
        refine ⟨rt', ?_, ?_⟩
        · simp
        simp [hstep] at h
        exact h
  · intro h
    rcases h with ⟨rt', hstep, hspec⟩
    simp [hstep, hspec]

theorem stepSpec?_sound
    (rt : RuntimeState) (label : String) (sp' : SpecState)
    (h : RuntimeState.stepSpec? rt label = some sp') :
    ∃ rt', RuntimeState.step? rt label = some rt' ∧ StateCorresponds rt' sp' := by
  rcases (stepSpec?_iff rt label sp').1 h with ⟨rt', hrt, hspec⟩
  exact ⟨rt', hrt, RuntimeState.toSpecState?_sound rt' sp' hspec⟩

/-- Completeness direction: if a runtime step exists and the stepped state
    corresponds to `sp'`, then `stepSpec?` returns `sp'`. -/
theorem stepSpec?_complete
    (rt : RuntimeState) (label : String) (rt' : RuntimeState) (sp' : SpecState)
    (hStep : RuntimeState.step? rt label = some rt')
    (hCorr : StateCorresponds rt' sp') :
    RuntimeState.stepSpec? rt label = some sp' := by
  apply (stepSpec?_iff rt label sp').2
  refine ⟨rt', hStep, ?_⟩
  exact RuntimeState.toSpecState?_complete rt' sp' hCorr

theorem languageTransition_stepSpec?_sound
    (rt : RuntimeState) (label : String) (sp' : SpecState)
    (hRule : hasRewriteByName label = true)
    (hStep : RuntimeState.stepSpec? rt label = some sp') :
    ∃ rt', LanguageTransition rt rt' label ∧ StateCorresponds rt' sp' := by
  rcases stepSpec?_sound rt label sp' hStep with ⟨rt', hrt, hcorr⟩
  exact ⟨rt', ⟨hRule, hrt⟩, hcorr⟩

theorem languageTransition_stepSpec?_complete
    (rt rt' : RuntimeState) (label : String) (sp' : SpecState)
    (hTrans : LanguageTransition rt rt' label)
    (hCorr : StateCorresponds rt' sp') :
    RuntimeState.stepSpec? rt label = some sp' := by
  exact stepSpec?_complete rt label rt' sp' hTrans.2 hCorr

/-- Under a known authored rewrite label, runtime/spec correspondence is
equivalent to obtaining a `stepSpec?` image. -/
theorem languageTransition_stepSpec?_iff
    (rt : RuntimeState) (label : String) (sp' : SpecState)
    (hRule : hasRewriteByName label = true) :
    RuntimeState.stepSpec? rt label = some sp' ↔
      ∃ rt', LanguageTransition rt rt' label ∧ StateCorresponds rt' sp' := by
  constructor
  · intro hStep
    exact languageTransition_stepSpec?_sound rt label sp' hRule hStep
  · intro h
    rcases h with ⟨rt', hTrans, hCorr⟩
    exact languageTransition_stepSpec?_complete rt rt' label sp' hTrans hCorr

example : hasRewriteByName "BeginLower" = true := by native_decide
example : hasRewriteByName "CompileLinearizeDone" = true := by native_decide
example : hasRewriteByName "DefinitelyMissingRule" = false := by native_decide

end Mettapedia.Languages.Metamath.Simulation
