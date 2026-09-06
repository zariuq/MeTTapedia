import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Logic.HennessyMilnerTransport

/-!
# Equation-class covers and operational implementations

A semantic compiler or runtime boundary connects GSLTs, even when its
implementation uses a convenient host-language state type.  Literal equality
of target representatives is too strong for an equation-aware GSLT: exactness
means that every target step from an encoded state lifts to a source step whose
encoded target lies in the same target equation class.

`SemanticCoveredTranslation` is that quotient-correct morphism.  The strict
`CoveredTranslation` embeds into it, semantic covers compose, and every such
cover induces the existing Hennessy--Milner `SystemCover`.

`OperationalImplementation` then packages a host state machine as a GSLT and
requires a faithful state encoding plus preservation and equation-class
reflection of steps.  Thus a parser table, chart, or VM record may implement a
pipeline stage, but it is never itself an additional semantic intermediate
language: the public endpoints remain GSLTs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Ultrainfinite

universe uSource uMiddle uTarget uAtom uAtom'

/-! ## Covers at the equation-class boundary -/

/-- A forward operational translation that reflects every target step at an
image state to a source step, up to the target GSLT's equations. -/
structure SemanticCoveredTranslation
    (source : GSLT.{uSource}) (target : GSLT.{uTarget})
    extends OperationalTranslation source target where
  liftStep : forall {sourceTerm : source.Term} {targetTerm : target.Term},
    target.Step (mapTerm sourceTerm) targetTerm ->
      exists sourceTarget : source.Term,
        source.Step sourceTerm sourceTarget /\
          target.Equiv (mapTerm sourceTarget) targetTerm

namespace SemanticCoveredTranslation

@[ext]
theorem ext {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {first second : SemanticCoveredTranslation source target}
    (mapTerm : first.mapTerm = second.mapTerm) : first = second := by
  cases first with
  | mk firstOperational firstLift =>
      cases second with
      | mk secondOperational secondLift =>
          cases firstOperational with
          | mk firstMap firstEquiv firstStep =>
              cases secondOperational with
              | mk secondMap secondEquiv secondStep =>
                  dsimp only at mapTerm
                  subst secondMap
                  congr

/-- Identity is semantically covered. -/
def id (theory : GSLT.{uSource}) : SemanticCoveredTranslation theory theory where
  mapTerm := _root_.id
  mapEquiv := fun equivalent => equivalent
  mapStep := fun step => step
  liftStep := fun step =>
    ⟨_, step, theory.equations.iseqv.refl _⟩

/-- Equation-class covers compose in execution order. -/
def comp {source : GSLT.{uSource}} {middle : GSLT.{uMiddle}}
    {target : GSLT.{uTarget}}
    (earlier : SemanticCoveredTranslation source middle)
    (later : SemanticCoveredTranslation middle target) :
    SemanticCoveredTranslation source target where
  mapTerm := later.mapTerm ∘ earlier.mapTerm
  mapEquiv := fun equivalent => later.mapEquiv (earlier.mapEquiv equivalent)
  mapStep := fun step => later.mapStep (earlier.mapStep step)
  liftStep := by
    intro sourceTerm targetTerm targetStep
    obtain ⟨middleTarget, middleStep, targetEquivalent⟩ :=
      later.liftStep targetStep
    obtain ⟨sourceTarget, sourceStep, middleEquivalent⟩ :=
      earlier.liftStep middleStep
    exact ⟨sourceTarget, sourceStep,
      target.equations.iseqv.trans
        (later.mapEquiv middleEquivalent) targetEquivalent⟩

@[simp]
theorem comp_mapTerm {source : GSLT.{uSource}} {middle : GSLT.{uMiddle}}
    {target : GSLT.{uTarget}}
    (earlier : SemanticCoveredTranslation source middle)
    (later : SemanticCoveredTranslation middle target) :
    (earlier.comp later).mapTerm = later.mapTerm ∘ earlier.mapTerm :=
  rfl

/-- Forgetting local reflection retains an operational translation. -/
def toOperational {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    (translation : SemanticCoveredTranslation source target) :
    OperationalTranslation source target :=
  translation.toOperationalTranslation

/-- Quotienting both endpoints turns coverage up to target equations into
literal coverage.  This is the precise bridge from semantic covers to the
existing covered-diagram machinery: representatives may differ before the
quotient, while their equation classes are definitionally the same target
state afterwards. -/
def onSemanticTheories {source target : GSLT.{uSource}}
    (translation : SemanticCoveredTranslation source target) :
    CoveredTranslation (semanticTheory source) (semanticTheory target) where
  mapTerm := translation.toOperational.mapSemantic
  mapEquiv := fun equal => congrArg translation.toOperational.mapSemantic equal
  cover := {
    mapStep := translation.toOperational.onSemanticTheories.mapStep
    liftStep := by
      intro sourceClass targetClass targetStep
      induction sourceClass using Quotient.inductionOn with
      | _ sourceRepresentative =>
          induction targetClass using Quotient.inductionOn with
          | _ targetRepresentative =>
              have representativeStep :
                  target.Step (translation.mapTerm sourceRepresentative)
                    targetRepresentative :=
                (semanticStep_mk_iff_step target _ _).mp targetStep
              obtain ⟨sourceTarget, sourceStep, targetEquivalent⟩ :=
                translation.liftStep representativeStep
              exact ⟨Quotient.mk source.equations sourceTarget,
                semanticStep_mk sourceStep, Quotient.sound targetEquivalent⟩ }

@[simp]
theorem onSemanticTheories_mapTerm {source target : GSLT.{uSource}}
    (translation : SemanticCoveredTranslation source target) :
    translation.onSemanticTheories.mapTerm =
      translation.toOperational.mapSemantic :=
  rfl

/-- A literal representative-level cover is, in particular, a semantic
equation-class cover. -/
def ofCoveredTranslation {source target : GSLT.{uSource}}
    (translation : CoveredTranslation source target) :
    SemanticCoveredTranslation source target where
  mapTerm := translation.mapTerm
  mapEquiv := translation.mapEquiv
  mapStep := translation.cover.mapStep
  liftStep := by
    intro sourceTerm targetTerm step
    obtain ⟨sourceTarget, sourceStep, equal⟩ := translation.cover.liftStep step
    subst equal
    exact ⟨sourceTarget, sourceStep, target.equations.iseqv.refl _⟩

/-- A semantic cover whose observations are carried exactly induces a cover
of the associated one-label Hennessy--Milner systems. -/
def systemCover {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    (translation : SemanticCoveredTranslation source target)
    (sourceObserved : ObservedGSLT.{uAtom} source)
    (targetObserved : ObservedGSLT.{uAtom'} target)
    (sourceResp : forall (atom : sourceObserved.Atom) {left right : source.Term},
      source.Equiv left right ->
        (sourceObserved.observes atom left <-> sourceObserved.observes atom right))
    (targetResp : forall (atom : targetObserved.Atom) {left right : target.Term},
      target.Equiv left right ->
        (targetObserved.observes atom left <-> targetObserved.observes atom right))
    (mapAtom : sourceObserved.Atom -> targetObserved.Atom)
    (observes_iff : forall atom term,
      sourceObserved.observes atom term <->
        targetObserved.observes (mapAtom atom) (translation.mapTerm term)) :
    SystemCover (System.ofObserved sourceObserved sourceResp)
      (System.ofObserved targetObserved targetResp) where
  mapTerm := translation.mapTerm
  mapAtom := mapAtom
  mapLabel := _root_.id
  mapEquiv := translation.mapEquiv
  observes_iff := observes_iff
  mapAct := fun step => translation.mapStep step
  liftAct := fun step => translation.liftStep step

/-- Semantic covers preserve ordinary strong bisimilarity.  The image
relation is closed under target equations, which is essential when a lifted
step returns a different representative of the same semantic state. -/
theorem preservesBisimilar
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    (translation : SemanticCoveredTranslation source target)
    {left right : source.Term} (bisimilar : source.Bisimilar left right) :
    target.Bisimilar (translation.mapTerm left) (translation.mapTerm right) := by
  obtain ⟨relation, ⟨forward, backward⟩, related⟩ := bisimilar
  let imageRelation : target.Term -> target.Term -> Prop :=
    fun first second => exists sourceFirst sourceSecond,
      target.Equiv (translation.mapTerm sourceFirst) first /\
        target.Equiv (translation.mapTerm sourceSecond) second /\
          relation sourceFirst sourceSecond
  refine ⟨imageRelation, ⟨?_, ?_⟩, ?_⟩
  · rintro first second
      ⟨sourceFirst, sourceSecond, firstEquivalent, secondEquivalent, sourceRelated⟩
      firstTarget firstStep
    obtain ⟨firstTarget', imageStep, targetEquivalent⟩ :=
      target.rewrites_resp_left
        (target.equations.iseqv.symm firstEquivalent) firstStep
    obtain ⟨liftedFirst, liftedStep, liftedEquivalent⟩ :=
      translation.liftStep imageStep
    obtain ⟨liftedSecond, sourceSecondStep, targetsRelated⟩ :=
      forward sourceRelated liftedStep
    obtain ⟨secondTarget, secondStep, secondTargetEquivalent⟩ :=
      target.rewrites_resp_left secondEquivalent
        (translation.mapStep sourceSecondStep)
    refine ⟨secondTarget, secondStep, liftedFirst, liftedSecond, ?_,
      secondTargetEquivalent, targetsRelated⟩
    exact target.equations.iseqv.trans liftedEquivalent
      (target.equations.iseqv.symm targetEquivalent)
  · rintro first second
      ⟨sourceFirst, sourceSecond, firstEquivalent, secondEquivalent, sourceRelated⟩
      secondTarget secondStep
    obtain ⟨secondTarget', imageStep, targetEquivalent⟩ :=
      target.rewrites_resp_left
        (target.equations.iseqv.symm secondEquivalent) secondStep
    obtain ⟨liftedSecond, liftedStep, liftedEquivalent⟩ :=
      translation.liftStep imageStep
    obtain ⟨liftedFirst, sourceFirstStep, targetsRelated⟩ :=
      backward sourceRelated liftedStep
    obtain ⟨firstTarget, firstStep, firstTargetEquivalent⟩ :=
      target.rewrites_resp_left firstEquivalent
        (translation.mapStep sourceFirstStep)
    refine ⟨firstTarget, firstStep, liftedFirst, liftedSecond,
      firstTargetEquivalent, ?_, targetsRelated⟩
    exact target.equations.iseqv.trans liftedEquivalent
      (target.equations.iseqv.symm targetEquivalent)
  · exact ⟨left, right, target.equations.iseqv.refl _,
      target.equations.iseqv.refl _, related⟩

end SemanticCoveredTranslation

/-! ## The category of equation-class-covered GSLTs -/

/-- An object of the semantic covered category. -/
structure SemanticCoveredTheory where
  theory : GSLT.{uSource}

instance : CategoryTheory.Category SemanticCoveredTheory where
  Hom source target := SemanticCoveredTranslation source.theory target.theory
  id source := SemanticCoveredTranslation.id source.theory
  comp earlier later := earlier.comp later
  id_comp morphism := by
    apply SemanticCoveredTranslation.ext
    rfl
  comp_id morphism := by
    apply SemanticCoveredTranslation.ext
    rfl
  assoc first second third := by
    apply SemanticCoveredTranslation.ext
    rfl

/-- Quotient completion sends a semantic cover to a literal cover.  Hence a
pipeline indexed in `SemanticCoveredTheory` becomes an ordinary
`CoveredDiagram` only after equation classes, not by silently identifying
distinct representatives. -/
def quotientCoverage :
    CategoryTheory.Functor SemanticCoveredTheory.{uSource}
      CoveredTheory.{uSource} where
  obj object := ⟨semanticTheory object.theory⟩
  map translation := translation.onSemanticTheories
  map_id object := by
    apply CoveredTranslation.ext
    funext term
    exact OperationalTranslation.mapSemantic_id object.theory term
  map_comp earlier later := by
    apply CoveredTranslation.ext
    funext term
    exact OperationalTranslation.mapSemantic_comp
      earlier.toOperational later.toOperational term

/-! ## A nontrivial quotient-completion canary -/

namespace SemanticCoveredTranslation.QuotientCanary

/-- A two-state source machine. -/
def source : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun first second => first = false /\ second = true
  rewrites_resp_left := by
    intro first first' second equal step
    subst equal
    exact ⟨second, step, rfl⟩
  rewrites_resp_right := by
    intro first second second' step equal
    subst equal
    exact step

/-- The target identifies `none` with `some true`, but not with
`some false`. -/
def targetKey : Option Bool -> Bool
  | none => true
  | some value => value

/-- A target machine whose successful result has two distinct but equivalent
representatives. -/
def target : GSLT where
  Term := Option Bool
  equations := {
    r := fun left right => targetKey left = targetKey right
    iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩ }
  rewrites := fun first second =>
    targetKey first = false /\ targetKey second = true
  rewrites_resp_left := by
    intro first first' second firstEquivalent step
    exact ⟨second,
      ⟨firstEquivalent.symm.trans step.1, step.2⟩, rfl⟩
  rewrites_resp_right := by
    intro first second second' step secondEquivalent
    exact ⟨step.1, secondEquivalent.symm.trans step.2⟩

/-- Coverage is valid modulo target equations. -/
def semantic : SemanticCoveredTranslation source target where
  mapTerm := some
  mapEquiv := by
    intro left right equal
    subst equal
    rfl
  mapStep := by
    rintro first second ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  liftStep := by
    intro first targetTerm step
    refine ⟨true, ⟨step.1, rfl⟩, ?_⟩
    change true = targetKey targetTerm
    exact step.2.symm

/-- Literal representative coverage is impossible: the target may choose
`none`, whereas the source encoding always produces `some _`. -/
theorem no_literal_cover_with_some_map :
    Not (exists translation : CoveredTranslation source target,
      translation.mapTerm = some) := by
  rintro ⟨translation, mapTerm⟩
  have step : target.Step (translation.mapTerm false) none := by
    rw [mapTerm]
    exact ⟨rfl, rfl⟩
  obtain ⟨sourceTarget, _, targetEqual⟩ :=
    translation.cover.liftStep step
  rw [mapTerm] at targetEqual
  cases targetEqual

/-- After quotient completion, the same non-literal semantic cover is an
ordinary covered translation. -/
def quotientCompleted :
    CoveredTranslation (semanticTheory source) (semanticTheory target) :=
  semantic.onSemanticTheories

end SemanticCoveredTranslation.QuotientCanary

/-! ## A quotient-level obstruction -/

/-- A target step escapes the source image even after target equations are
taken into account. -/
structure EquationClassEscapingStep
    (source : GSLT.{uSource}) (target : GSLT.{uTarget})
    (mapTerm : source.Term -> target.Term) where
  sourceTerm : source.Term
  targetTerm : target.Term
  step : target.Step (mapTerm sourceTerm) targetTerm
  target_not_in_image : forall sourceTarget,
    Not (target.Equiv (mapTerm sourceTarget) targetTerm)

namespace EquationClassEscapingStep

/-- An equation-class-escaping transition rules out a semantic cover. -/
theorem not_semanticCoveredTranslation
    {source : GSLT.{uSource}} {target : GSLT.{uTarget}}
    {mapTerm : source.Term -> target.Term}
    (escaping : EquationClassEscapingStep source target mapTerm) :
    Not (exists translation : SemanticCoveredTranslation source target,
      translation.mapTerm = mapTerm) := by
  rintro ⟨translation, equal⟩
  have step : target.Step (translation.mapTerm escaping.sourceTerm)
      escaping.targetTerm := by
    rw [equal]
    exact escaping.step
  obtain ⟨sourceTarget, _, equivalent⟩ := translation.liftStep step
  exact escaping.target_not_in_image sourceTarget (equal ▸ equivalent)

end EquationClassEscapingStep

/-! ## Host machines as GSLT implementations -/

/-- A faithful host implementation of a semantic GSLT.  Its state relation is
made into a GSLT, and `complete` forbids target behavior that the host machine
cannot realize, modulo the target's equations. -/
structure OperationalImplementation (theory : GSLT.{uTarget}) where
  State : Type uSource
  encode : State -> theory.Term
  encode_injective : Function.Injective encode
  step : State -> State -> Prop
  sound : forall {source target}, step source target ->
    theory.Step (encode source) (encode target)
  complete : forall {source target}, theory.Step (encode source) target ->
    exists next, step source next /\ theory.Equiv (encode next) target

namespace OperationalImplementation

variable {theory : GSLT.{uTarget}}

/-- The implementation state machine is itself a GSLT; equality is the only
structural equation internal to the host representation. -/
def asGSLT (implementation : OperationalImplementation.{uSource, uTarget} theory) : GSLT where
  Term := implementation.State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := implementation.step
  rewrites_resp_left := by
    intro source source' target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst equal
    exact step

/-- The required soundness and completeness laws expose the implementation
as a semantic cover between two GSLTs. -/
def semanticCover
    (implementation : OperationalImplementation.{uSource, uTarget} theory) :
    SemanticCoveredTranslation implementation.asGSLT theory where
  mapTerm := implementation.encode
  mapEquiv := by
    intro left right equal
    subst equal
    exact theory.equations.iseqv.refl _
  mapStep := implementation.sound
  liftStep := implementation.complete

@[simp]
theorem semanticCover_mapTerm
    (implementation : OperationalImplementation.{uSource, uTarget} theory) :
    implementation.semanticCover.mapTerm = implementation.encode :=
  rfl

/-- At every encoded state, semantic stepping is exactly implementation
stepping followed by a choice of target representative. -/
theorem semanticStep_iff_exists_implementationStep
    (implementation : OperationalImplementation.{uSource, uTarget} theory)
    (source : implementation.State) (target : theory.Term) :
    theory.Step (implementation.encode source) target <->
      exists next : implementation.State,
        implementation.step source next /\
          theory.Equiv (implementation.encode next) target := by
  constructor
  · exact implementation.complete
  · rintro ⟨next, step, equivalent⟩
    exact theory.rewrites_resp_right (implementation.sound step) equivalent

/-! ## Positive and negative controls -/

namespace Canary

/-- A small semantic machine with one transition. -/
def target : GSLT where
  Term := Option Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source result => source = some false /\ result = some true
  rewrites_resp_left := by
    intro source source' result equal step
    subst equal
    exact ⟨result, step, rfl⟩
  rewrites_resp_right := by
    intro source result result' step equal
    subst equal
    exact step

/-- The host carrier differs from the semantic carrier, so this is not an
identity construction disguised as a compiler theorem. -/
def implementation : OperationalImplementation target where
  State := Bool
  encode := some
  encode_injective := fun _ _ equal => Option.some.inj equal
  step := fun source result => source = false /\ result = true
  sound := by
    intro source result step
    exact ⟨congrArg some step.1, congrArg some step.2⟩
  complete := by
    intro source result step
    refine ⟨true, ⟨Option.some.inj step.1, rfl⟩, ?_⟩
    change some true = result
    exact step.2.symm

theorem positive_step : implementation.asGSLT.Step false true :=
  ⟨rfl, rfl⟩

theorem positive_step_maps : target.Step
    (implementation.semanticCover.mapTerm false)
    (implementation.semanticCover.mapTerm true) :=
  implementation.semanticCover.mapStep positive_step

/-- A target with an extra transition to `none`, outside the encoding image. -/
def escapingTarget : GSLT where
  Term := Option Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source result =>
    source = some false /\ (result = some true \/ result = none)
  rewrites_resp_left := by
    intro source source' result equal step
    subst equal
    exact ⟨result, step, rfl⟩
  rewrites_resp_right := by
    intro source result result' step equal
    subst equal
    exact step

theorem escaping_step : escapingTarget.Step (some false) none :=
  ⟨rfl, Or.inr rfl⟩

/-- Forward preservation alone cannot certify an implementation: the extra
target transition has no source lift, even up to target equations. -/
theorem no_semantic_cover_with_some_encoding :
    Not (exists translation :
      SemanticCoveredTranslation implementation.asGSLT escapingTarget,
      translation.mapTerm = some) := by
  rintro ⟨translation, mapTerm⟩
  have step : escapingTarget.Step (translation.mapTerm false) none := by
    rw [mapTerm]
    exact escaping_step
  obtain ⟨next, _, equivalent⟩ := translation.liftStep step
  rw [mapTerm] at equivalent
  change some next = none at equivalent
  cases equivalent

end Canary

end OperationalImplementation

/-! ## Axiom audit -/

#print axioms SemanticCoveredTranslation.comp
#print axioms SemanticCoveredTranslation.onSemanticTheories
#print axioms SemanticCoveredTranslation.systemCover
#print axioms SemanticCoveredTranslation.preservesBisimilar
#print axioms quotientCoverage
#print axioms SemanticCoveredTranslation.QuotientCanary.no_literal_cover_with_some_map
#print axioms SemanticCoveredTranslation.QuotientCanary.quotientCompleted
#print axioms EquationClassEscapingStep.not_semanticCoveredTranslation
#print axioms OperationalImplementation.semanticCover
#print axioms OperationalImplementation.semanticStep_iff_exists_implementationStep
#print axioms OperationalImplementation.Canary.positive_step_maps
#print axioms OperationalImplementation.Canary.no_semantic_cover_with_some_encoding

end Mettapedia.GSLT.IndexedOperational
