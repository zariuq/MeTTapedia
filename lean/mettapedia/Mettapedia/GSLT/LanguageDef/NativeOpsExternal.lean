import Mettapedia.GSLT.LanguageDef.NativeOpsRuntimeState

/-!
# Concrete external call boundaries

An external call returns a raw typed value and its exact post-state. Its own
reader or execution state can change while the operational context remains
clear. The emitted context check follows the call. These contracts describe
only calls, values and storage effects; they grant no logical theorem authority.
The source and target call relations are supplied independently.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

structure SourceExternalSemantics (World : Type) where
  call : String → List SourceValue → SourceState World → SourceValue → SourceState World → Prop

structure TargetExternalSemantics (World : Type) where
  call : String → List TargetValue → TargetState World → TargetValue → TargetState World → Prop

structure ExternalCorrespondence {SourceWorld TargetWorld : Type}
    (source : SourceExternalSemantics SourceWorld)
    (target : TargetExternalSemantics TargetWorld)
    (worldRelated : SourceWorld → TargetWorld → Prop) : Prop where
  forward : ∀ name arguments sourcePre targetPre sourceRaw sourcePost,
    StateRelated worldRelated sourcePre targetPre →
    source.call name arguments sourcePre sourceRaw sourcePost →
    ∃ targetPost,
      target.call name (encodeValues arguments) targetPre (encodeValue sourceRaw) targetPost ∧
      StateRelated worldRelated sourcePost targetPost
  backward : ∀ name arguments sourcePre targetPre targetRaw targetPost,
    StateRelated worldRelated sourcePre targetPre →
    target.call name (encodeValues arguments) targetPre targetRaw targetPost →
    ∃ sourceRaw sourcePost,
      source.call name arguments sourcePre sourceRaw sourcePost ∧
      targetRaw = encodeValue sourceRaw ∧ StateRelated worldRelated sourcePost targetPost

theorem external_call_observation_forward {SourceWorld TargetWorld : Type}
    {source : SourceExternalSemantics SourceWorld}
    {target : TargetExternalSemantics TargetWorld}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (contract : ExternalCorrespondence source target worldRelated)
    (name : String) (arguments : List SourceValue)
    {sourcePre : SourceState SourceWorld} {targetPre : TargetState TargetWorld}
    {sourceRaw : SourceValue} {sourcePost : SourceState SourceWorld}
    (related : StateRelated worldRelated sourcePre targetPre)
    (called : source.call name arguments sourcePre sourceRaw sourcePost) :
    ∃ targetPost,
      target.call name (encodeValues arguments) targetPre (encodeValue sourceRaw) targetPost ∧
      OutcomeRelated worldRelated (sourceObserve sourcePost sourceRaw)
        (targetObserve targetPost (encodeValue sourceRaw)) := by
  obtain ⟨targetPost, executed, postRelated⟩ :=
    contract.forward name arguments sourcePre targetPre sourceRaw sourcePost related called
  exact ⟨targetPost, executed, observation_correspondence postRelated sourceRaw⟩

theorem external_call_observation_backward {SourceWorld TargetWorld : Type}
    {source : SourceExternalSemantics SourceWorld}
    {target : TargetExternalSemantics TargetWorld}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (contract : ExternalCorrespondence source target worldRelated)
    (name : String) (arguments : List SourceValue)
    {sourcePre : SourceState SourceWorld} {targetPre : TargetState TargetWorld}
    {targetRaw : TargetValue} {targetPost : TargetState TargetWorld}
    (related : StateRelated worldRelated sourcePre targetPre)
    (called : target.call name (encodeValues arguments) targetPre targetRaw targetPost) :
    ∃ sourceRaw sourcePost,
      source.call name arguments sourcePre sourceRaw sourcePost ∧
      OutcomeRelated worldRelated (sourceObserve sourcePost sourceRaw)
        (targetObserve targetPost targetRaw) := by
  obtain ⟨sourceRaw, sourcePost, executed, rawRelated, postRelated⟩ :=
    contract.backward name arguments sourcePre targetPre targetRaw targetPost related called
  subst targetRaw
  exact ⟨sourceRaw, sourcePost, executed, observation_correspondence postRelated sourceRaw⟩

theorem external_raw_value_no_extra_results {SourceWorld TargetWorld : Type}
    {source : SourceExternalSemantics SourceWorld}
    {target : TargetExternalSemantics TargetWorld}
    {worldRelated : SourceWorld → TargetWorld → Prop}
    (contract : ExternalCorrespondence source target worldRelated)
    (name : String) (arguments : List SourceValue)
    {sourcePre : SourceState SourceWorld} {targetPre : TargetState TargetWorld}
    (related : StateRelated worldRelated sourcePre targetPre) (raw : SourceValue) :
    (∃ targetPost, target.call name (encodeValues arguments) targetPre
        (encodeValue raw) targetPost) ↔
      ∃ sourcePost, source.call name arguments sourcePre raw sourcePost := by
  constructor
  · rintro ⟨targetPost, called⟩
    obtain ⟨sourceRaw, sourcePost, sourceCalled, equal, _⟩ :=
      contract.backward name arguments sourcePre targetPre (encodeValue raw) targetPost
        related called
    have same : raw = sourceRaw := encodeValue_injective equal
    exact ⟨sourcePost, same.symm ▸ sourceCalled⟩
  · rintro ⟨sourcePost, called⟩
    obtain ⟨targetPost, targetCalled, _⟩ :=
      contract.forward name arguments sourcePre targetPre raw sourcePost related called
    exact ⟨targetPost, targetCalled⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
