import Mettapedia.GSLT.Core.SemanticTransport
import Mettapedia.GSLT.Core.NonFactorization
import Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

/-!
# Observer-relative form of semantic transport

`SemanticInvariant` and `DenotationSquare` state semantic conservation at the
operational GSLT layer.  `ObserverPreservingMap` states the corresponding law
for a selected downstream view.  This module proves that the latter is exactly
the observer-facing boundary of a denotation square; it does not introduce a
second semantics interface.

The operational realization remains proof-relevant and path-valued.  Passing
to an observer-preserving map deliberately exposes only its term map and the
declared view.  No injectivity, reflection, or preservation of a finer observer
is inferred.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObserverSemanticTransport

open Mettapedia.Cybernetics
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Dynamics.ObserverRelativeTransformationCrown

universe uSource uTarget uSourceMeaning uTargetMeaning

/-- The selected denotation of a GSLT, exposed as an observer on its terms. -/
def invariantObserver
    {system : GSLT.{uSource}} {Meaning : Type uSourceMeaning}
    (invariant : SemanticInvariant system Meaning) :
    Observer system.Term Meaning where
  observe := invariant.denote

@[simp] theorem invariantObserver_observe
    {system : GSLT.{uSource}} {Meaning : Type uSourceMeaning}
    (invariant : SemanticInvariant system Meaning) (term : system.Term) :
    (invariantObserver invariant).observe term = invariant.denote term :=
  rfl

/-- A denotation square exposes an observer-preserving representation map.
The source observer is first translated into the target meaning language. -/
def observerMapOfDenotationSquare
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {SourceMeaning : Type uSourceMeaning}
    {TargetMeaning : Type uTargetMeaning}
    {realization : OperationalRealization source target}
    {sourceDenotation : SemanticInvariant source SourceMeaning}
    {targetDenotation : SemanticInvariant target TargetMeaning}
    {mapMeaning : SourceMeaning → TargetMeaning}
    (square : DenotationSquare realization sourceDenotation
      targetDenotation mapMeaning) :
    ObserverPreservingMap source.Term target.Term TargetMeaning
      (invariantObserver (sourceDenotation.map mapMeaning))
      (invariantObserver targetDenotation) where
  transform := realization.mapTerm
  preserves := square.commutes

@[simp] theorem observerMapOfDenotationSquare_transform
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {SourceMeaning : Type uSourceMeaning}
    {TargetMeaning : Type uTargetMeaning}
    {realization : OperationalRealization source target}
    {sourceDenotation : SemanticInvariant source SourceMeaning}
    {targetDenotation : SemanticInvariant target TargetMeaning}
    {mapMeaning : SourceMeaning → TargetMeaning}
    (square : DenotationSquare realization sourceDenotation
      targetDenotation mapMeaning) :
    (observerMapOfDenotationSquare square).transform = realization.mapTerm :=
  rfl

/-- Exact observer-facing characterization of a semantic square.  The
existential map carries no extra operational authority: its transformation is
required to be the already selected realization map. -/
theorem denotationSquare_iff_observerPreservingMap
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {SourceMeaning : Type uSourceMeaning}
    {TargetMeaning : Type uTargetMeaning}
    (realization : OperationalRealization source target)
    (sourceDenotation : SemanticInvariant source SourceMeaning)
    (targetDenotation : SemanticInvariant target TargetMeaning)
    (mapMeaning : SourceMeaning → TargetMeaning) :
    DenotationSquare realization sourceDenotation targetDenotation mapMeaning
      ↔
    ∃ representation :
        ObserverPreservingMap source.Term target.Term TargetMeaning
          (invariantObserver (sourceDenotation.map mapMeaning))
          (invariantObserver targetDenotation),
      representation.transform = realization.mapTerm := by
  constructor
  · intro square
    exact ⟨observerMapOfDenotationSquare square, rfl⟩
  · rintro ⟨representation, equal⟩
    constructor
    intro term
    have preserved := representation.preserves term
    change targetDenotation.denote (representation.transform term) =
      mapMeaning (sourceDenotation.denote term) at preserved
    simpa [equal] using preserved

/-! ## Exact observer descent through a realization -/

/-- A selected source observer descends through an operational realization
when its view can be recovered from the realized target term.  This property
mentions only the selected observation: it does not claim injectivity or
reflection for the operational realization. -/
def ObserverDescends
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {View : Type uTargetMeaning}
    (realization : OperationalRealization source target)
    (sourceObserver : Observer source.Term View) : Prop :=
  Factors realization.mapTerm sourceObserver.observe

/-- Observer descent is exactly the existence of a target observer and a
commuting representation map whose transformation is the already selected
operational realization.  No second operational map is introduced. -/
theorem observerDescends_iff_preservingMap
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {View : Type uTargetMeaning}
    (realization : OperationalRealization source target)
    (sourceObserver : Observer source.Term View) :
    ObserverDescends realization sourceObserver ↔
      ∃ targetObserver : Observer target.Term View,
        ∃ representation : ObserverPreservingMap source.Term target.Term View
            sourceObserver targetObserver,
          representation.transform = realization.mapTerm := by
  constructor
  · rintro ⟨recover, recovers⟩
    let targetObserver : Observer target.Term View := ⟨recover⟩
    refine ⟨targetObserver,
      { transform := realization.mapTerm
        preserves := fun term => recovers term }, rfl⟩
  · rintro ⟨targetObserver, representation, equal⟩
    refine ⟨targetObserver.observe, fun term => ?_⟩
    have preserved := representation.preserves term
    simpa [equal] using preserved

/-- For a realization reaching every target term, an observer descends
exactly when it is constant on the fibres of the realization map. -/
theorem observerDescends_iff_constantOnFibers
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {View : Type uTargetMeaning}
    (realization : OperationalRealization source target)
    (surjective : Function.Surjective realization.mapTerm)
    (sourceObserver : Observer source.Term View) :
    ObserverDescends realization sourceObserver ↔
      ConstantOnFibers realization.mapTerm sourceObserver.observe :=
  factors_iff_constantOnFibers surjective sourceObserver.observe

/-! ## Positive and negative controls -/

namespace Canary

open DenotationSquareCanary

/-- Boolean negation preserves the view when the meaning map is also
negation. -/
def flipObserverMap :
    ObserverPreservingMap Bool Bool Bool
      (invariantObserver (booleanDenotation.map Bool.not))
      (invariantObserver booleanDenotation) :=
  observerMapOfDenotationSquare flipNegationSquare

/-- The same operational transformation cannot preserve the identity Boolean
view.  Operational validity does not imply observer validity. -/
theorem noFlipIdentityObserverMap :
    ¬ ∃ representation :
        ObserverPreservingMap Bool Bool Bool
          (invariantObserver (booleanDenotation.map _root_.id))
          (invariantObserver booleanDenotation),
      representation.transform = flip.mapTerm := by
  intro representation
  exact noFlipIdentitySquare
    ((denotationSquare_iff_observerPreservingMap flip booleanDenotation
      booleanDenotation _root_.id).2 representation)

/-! A transition-erasing fusion is the non-vacuous lossy control. -/

/-- Forgetting a Boolean state preserves the constant unit observation. -/
def fusedConstantObserverMap :
    ObserverPreservingMap Bool Unit Unit
      ⟨fun _ => ()⟩ ⟨fun _ => ()⟩ where
  transform := OperationalRealization.FusionCanary.fused.mapTerm
  preserves := fun _ => rfl

/-- The constant observation descends through the lossy fusion. -/
theorem fusedConstantObserverDescends :
    ObserverDescends OperationalRealization.FusionCanary.fused
      ⟨fun _ => ()⟩ := by
  exact (observerDescends_iff_preservingMap
    OperationalRealization.FusionCanary.fused ⟨fun _ => ()⟩).2
      ⟨⟨fun _ => ()⟩, fusedConstantObserverMap, rfl⟩

/-- Full Boolean identity observation distinguishes the two source states
identified by the fusion, so it cannot descend to the unit target. -/
theorem fusedIdentityObserverDoesNotDescend :
    ¬ ObserverDescends OperationalRealization.FusionCanary.fused
      (Observer.identity Bool) := by
  intro descends
  have constant := descends.constantOnFibers
  have impossible := constant false true rfl
  change false = true at impossible
  exact Bool.noConfusion impossible

end Canary

#print axioms invariantObserver
#print axioms observerMapOfDenotationSquare
#print axioms denotationSquare_iff_observerPreservingMap
#print axioms ObserverDescends
#print axioms observerDescends_iff_preservingMap
#print axioms observerDescends_iff_constantOnFibers
#print axioms Canary.flipObserverMap
#print axioms Canary.noFlipIdentityObserverMap
#print axioms Canary.fusedConstantObserverDescends
#print axioms Canary.fusedIdentityObserverDoesNotDescend

end Mettapedia.GSLT.Dynamics.ObserverSemanticTransport
