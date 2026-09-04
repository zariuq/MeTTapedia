import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularNormalization
import Mettapedia.TypeTheory.ConversionDecisionComparison

/-!
# Exact conversion for a regular two-sort dependent calculus

This module places the existing normalization theorem for the sealed two-sort
dependent calculus into the general comparison between proof-relevant
conversion, canonical invariants, and Boolean decisions.

The calculus has dependent products, dependent sums, intensional identity
types, one distinguished ground type, and one untyped formation marker.  It is
a concrete normalization experiment, not a universe design or a selected
language foundation.

The main construction uses only terms in the proved accessibility domain.
One-step reduction lifts to a proof-relevant free conversion path, while the
computed normal form is a complete invariant.  Thus four independently useful
faces agree on endpoints:

* explicit reduction paths;
* fragment-internal declarative conversion;
* equality of computed normal forms; and
* the executable Boolean decision.

A genuinely dependent beta canary uses the codomain `Id U0 x x`; its result
type changes when the binder is instantiated.  A negative canary separates
the ground type from the formation marker, and the usual untyped looping term
remains outside the normalization domain.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RegularDependentConversionDecision

open Mettapedia.TypeTheory.FreeConversion
open Mettapedia.TypeTheory.JudgmentalEquality
open Mettapedia.TypeTheory.ConversionDecisionComparison
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

/-! ## The normalization domain as an indexed conversion system -/

/-- Terms equipped with erased evidence that the accessibility normalizer is
defined on them.  The index is the de Bruijn context length. -/
abbrev State (contextLength : Nat) :=
  accessibleNormalizationSpecification.Term contextLength

/-- A primitive conversion generator is one actual reduction between two
terms which both remain in the normalization domain. -/
structure ReductionGenerator {contextLength : Nat}
    (source target : State contextLength) : Type where
  reduction : Red source.1 target.1

/-- Accessibility and declaration-freedom descend along one reduction. -/
def domainAfterReduction {contextLength : Nat}
    {source target : PureTm contextLength}
    (covered : accessibleNormalizationSpecification.Domain source)
    (step : Red source target) :
    accessibleNormalizationSpecification.Domain target :=
  ⟨covered.1.inv step, covered.2.red step⟩

/-- Accessibility and declaration-freedom descend along a finite forward
reduction path. -/
def domainAfterRedStar {contextLength : Nat}
    (source : State contextLength) {target : PureTm contextLength} :
    RedStar source.1 target →
      accessibleNormalizationSpecification.Domain target := by
  intro steps
  induction steps with
  | refl => exact source.2
  | tail pathPrefix step ih =>
      exact domainAfterReduction ih step

/-- The endpoint of a lifted finite reduction path, retaining its derived
normalization-domain evidence. -/
def stateAfterRedStar {contextLength : Nat}
    (source : State contextLength) {target : PureTm contextLength}
    (steps : RedStar source.1 target) : State contextLength :=
  ⟨target, domainAfterRedStar source steps⟩

/-- Every finite forward reduction entails the existence of a proof-relevant
conversion path whose intermediate states all remain in the normalization
domain.  The result is proposition-valued: a propositional reduction closure
does not manufacture a distinguished proof history. -/
theorem nonemptyPathOfRedStar {contextLength : Nat}
    (source : State contextLength) {target : PureTm contextLength}
    (steps : RedStar source.1 target) :
    Nonempty
      (Path State (fun {index} => @ReductionGenerator index)
        source (stateAfterRedStar source steps)) := by
  induction steps with
  | refl =>
      exact ⟨ConversionEvidence.refl
        (computation := computation State
          (fun {index} => @ReductionGenerator index)) source⟩
  | tail pathPrefix step ih =>
      rcases ih with ⟨path⟩
      exact ⟨.trans path (.step ⟨step⟩)⟩

/-- The computed normal form, itself retained inside the accessibility
domain. -/
def normalState {contextLength : Nat}
    (source : State contextLength) : State contextLength :=
  stateAfterRedStar source
    (accessibleNormalizationSpecification.reduces source.1 source.2)

/-- Normalization proves that some proof-relevant path reaches the canonical
state; it does not select a canonical history. -/
theorem nonemptyPathToNormal {contextLength : Nat}
    (source : State contextLength) :
    Nonempty
      (Path State (fun {index} => @ReductionGenerator index)
        source (normalState source)) :=
  nonemptyPathOfRedStar source
    (accessibleNormalizationSpecification.reduces source.1 source.2)

/-- Computed normal form is a complete invariant for proof-relevant
conversion on the accessibility domain. -/
def normalizationInvariant :
    CompleteInvariant State (fun {index} => @ReductionGenerator index)
      (fun contextLength => PureTm contextLength) where
  classify := fun _ source =>
    accessibleNormalizationSpecification.normalize source.1 source.2
  generatorInvariant := by
    intro contextLength source target step
    exact
      accessibleNormalizationSpecification.normalize_eq_of_converts
        (.rel ⟨step.reduction, source.2.2, target.2.2⟩)
  complete := by
    intro contextLength source target equalNormalForms
    have normalStatesEqual : normalState source = normalState target := by
      apply Subtype.ext
      exact equalNormalForms
    have returnFromRight :
        Nonempty
          (Path State (fun {index} => @ReductionGenerator index)
            (normalState source) target) := by
      rw [normalStatesEqual]
      rcases nonemptyPathToNormal target with ⟨rightPath⟩
      exact ⟨.symm rightPath⟩
    rcases nonemptyPathToNormal source with ⟨leftPath⟩
    rcases returnFromRight with ⟨rightPath⟩
    exact ⟨.trans leftPath rightPath⟩

/-- Proof-relevant path existence is exactly the existing
fragment-internal declarative conversion relation. -/
theorem nonemptyPath_iff_fragmentConversion
    {contextLength : Nat} (source target : State contextLength) :
    Nonempty
        (Path State (fun {index} => @ReductionGenerator index)
          source target) ↔
      ConstantFreeConv source.1 target.1 := by
  exact
    normalizationInvariant.nonemptyPath_iff_classify_eq.trans
      (accessibleNormalizationSpecification.normalize_eq_iff_converts
        source target)

/-- The generic Boolean classifier decides exactly fragment-internal
conversion. -/
theorem decideConversion_eq_true_iff_fragmentConversion
    {contextLength : Nat} (source target : State contextLength) :
    normalizationInvariant.decideConversion contextLength source target =
        true ↔
      ConstantFreeConv source.1 target.1 := by
  rw [normalizationInvariant.decideConversion_eq_true_iff]
  exact nonemptyPath_iff_fragmentConversion source target

/-- The generic complete-invariant decision and the existing exact regular
normalization decision are the same computation. -/
theorem genericDecision_eq_regularDecision
    {contextLength : Nat} (source target : State contextLength) :
    normalizationInvariant.decideConversion contextLength source target =
      (regularDecidedConversion contextLength).decide source target :=
  rfl

/-! ## Exact transport at the typing boundary -/

/-- The inferred type of a regular judgment is covered by normalization. -/
def inferredTypeState {contextLength : Nat} {context : Ctx contextLength}
    {term sourceType : PureTm contextLength}
    (typing : RegularJudgment context term sourceType) : State contextLength :=
  ⟨sourceType, regularNormalizationSpecification.covers_type typing⟩

/-- A formed ordinary target type is covered as a typed subject. -/
def formedTypeState {contextLength : Nat} {context : Ctx contextLength}
    {targetType : PureTm contextLength}
    (formation : RegularJudgment context targetType .u1) :
    State contextLength :=
  ⟨targetType,
    regularNormalizationSpecification.covers_subject formation⟩

/-- Transport a regular typing judgment to a formed convertible target type.
The decision is computed by exact normalization; target formation remains a
separate premise and therefore cannot be manufactured by conversion. -/
structure TypingTransportEvidence {contextLength : Nat}
    (context : Ctx contextLength) (term targetType : PureTm contextLength) :
    Type where
  judgment : RegularJudgment context term targetType

def transportTyping? {contextLength : Nat} {context : Ctx contextLength}
    {term sourceType targetType : PureTm contextLength}
    (typing : RegularJudgment context term sourceType)
    (targetFormation : RegularJudgment context targetType .u1) :
    Option (TypingTransportEvidence context term targetType) :=
  if accepted :
      normalizationInvariant.decideConversion contextLength
          (inferredTypeState typing) (formedTypeState targetFormation) = true
  then
    some ⟨⟨typing.context,
      .conv_type typing.typing targetFormation.typing
        ((decideConversion_eq_true_iff_fragmentConversion _ _).1
          accepted)⟩⟩
  else
    none

/-- Exact normalization accepts a typing transport exactly when the source
and target types are fragment-internally convertible. -/
theorem transportTyping?_isSome_iff
    {contextLength : Nat} {context : Ctx contextLength}
    {term sourceType targetType : PureTm contextLength}
    (typing : RegularJudgment context term sourceType)
    (targetFormation : RegularJudgment context targetType .u1) :
    (transportTyping? typing targetFormation).isSome = true ↔
      ConstantFreeConv sourceType targetType := by
  unfold transportTyping?
  split
  · rename_i accepted
    have conversion : ConstantFreeConv sourceType targetType :=
      (decideConversion_eq_true_iff_fragmentConversion
          (inferredTypeState typing) (formedTypeState targetFormation)).1
        accepted
    simp only [Option.isSome_some, true_iff]
    exact conversion
  · rename_i rejected
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro conversion
    exact rejected
      ((decideConversion_eq_true_iff_fragmentConversion
        (inferredTypeState typing) (formedTypeState targetFormation)).2
        conversion)

/-! ## A genuinely dependent beta canary -/

namespace DependentBetaCanary

/-- One ordinary value variable `a : U0`. -/
def context : Ctx 1 := .snoc .nil .u0

theorem context_regular : RegularCtx context := by
  exact .snoc .nil (.u0_type .nil)

/-- Under a new binder `x : U0`, the result type is `Id U0 x x`. -/
def codomain : PureTm 2 :=
  .id .u0 (.var 0) (.var 0)

/-- The dependent body proves its binder equal to itself. -/
def body : PureTm 2 := .refl (.var 0)

def argument : PureTm 1 := .var 0

def source : PureTm 1 := .app (.lam body) argument

def target : PureTm 1 := .refl argument

def resultType : PureTm 1 := .id .u0 argument argument

theorem argument_typed : RegularHasType context argument .u0 := by
  simpa [context, argument, lookup, rename] using
    (RegularHasType.var (Γ := context) (i := (0 : Fin 1)))

theorem codomain_formed :
    RegularHasType (.snoc context .u0) codomain .u1 := by
  apply RegularHasType.id_form (.u0_type _)
  · simpa [codomain, lookup, rename] using
      (RegularHasType.var
        (Γ := .snoc context (.u0 : PureTm 1)) (i := (0 : Fin 2)))
  · simpa [codomain, lookup, rename] using
      (RegularHasType.var
        (Γ := .snoc context (.u0 : PureTm 1)) (i := (0 : Fin 2)))

theorem body_typed :
    RegularHasType (.snoc context .u0) body codomain := by
  apply RegularHasType.refl_intro (.u0_type _)
  simpa [body, codomain, lookup, rename] using
    (RegularHasType.var
      (Γ := .snoc context (.u0 : PureTm 1)) (i := (0 : Fin 2)))

theorem function_typed :
    RegularHasType context (.lam body) (.pi .u0 codomain) :=
  .lam_intro (.u0_type _) codomain_formed body_typed

theorem source_typed : RegularHasType context source resultType := by
  simpa [source, resultType, argument, codomain, inst0, subst, subst0] using
    (RegularHasType.app_elim (.u0_type context) function_typed
      argument_typed codomain_formed)

theorem target_typed : RegularHasType context target resultType := by
  exact .refl_intro (.u0_type _) argument_typed

theorem resultType_formed : RegularHasType context resultType .u1 :=
  .id_form (.u0_type _) argument_typed argument_typed

def sourceJudgment : RegularJudgment context source resultType :=
  ⟨context_regular, source_typed⟩

def targetJudgment : RegularJudgment context target resultType :=
  ⟨context_regular, target_typed⟩

def sourceState : State 1 :=
  ⟨source, regularNormalizationSpecification.covers_subject sourceJudgment⟩

def targetState : State 1 :=
  ⟨target, regularNormalizationSpecification.covers_subject targetJudgment⟩

theorem source_reduces_target : Red source target := by
  simpa [source, target, body, argument, inst0, subst, subst0] using
    (Red.betaPi body argument)

/-- The dependent beta contraction is retained as an explicit primitive
conversion path. -/
def betaPath :
    Path State (fun {index} => @ReductionGenerator index)
      sourceState targetState :=
  .step ⟨source_reduces_target⟩

/-- The normal-form decision accepts the same dependent beta event. -/
theorem decision_accepts_dependent_beta :
    normalizationInvariant.decideConversion 1 sourceState targetState =
      true :=
  normalizationInvariant.decideConversion_eq_true_iff.mpr ⟨betaPath⟩

/-- The existing regular decision agrees on the same event. -/
theorem regularDecision_accepts_dependent_beta :
    (regularDecidedConversion 1).decide sourceState targetState = true := by
  rw [← genericDecision_eq_regularDecision]
  exact decision_accepts_dependent_beta

/-! ### Conversion of an actually dependent type -/

/-- A value-level identity redex which may occur inside a dependent type. -/
def endpointRedex : PureTm 1 :=
  .app (.lam (.var 0)) argument

/-- The expected type before beta contraction. -/
def expandedType : PureTm 1 :=
  .id .u0 endpointRedex argument

theorem identityFunction_typed :
    RegularHasType context (.lam (.var 0)) (.pi .u0 .u0) := by
  apply RegularHasType.lam_intro (.u0_type _) (.u0_type _)
  simpa [lookup, rename] using
    (RegularHasType.var
      (Γ := .snoc context (.u0 : PureTm 1)) (i := (0 : Fin 2)))

theorem endpointRedex_typed :
    RegularHasType context endpointRedex .u0 := by
  simpa [endpointRedex, argument, inst0, subst, subst0] using
    (RegularHasType.app_elim (.u0_type context) identityFunction_typed
      argument_typed (.u0_type _))

theorem expandedType_formed :
    RegularHasType context expandedType .u1 :=
  .id_form (.u0_type _) endpointRedex_typed argument_typed

theorem expandedType_reduces_resultType : Red expandedType resultType := by
  exact .congIdLeft (by
    simpa [endpointRedex, target, argument, inst0, subst, subst0] using
      (Red.betaPi (.var 0 : PureTm 2) argument))

def resultTypingJudgment : RegularJudgment context target resultType :=
  ⟨context_regular, target_typed⟩

def expandedTypeFormation : RegularJudgment context expandedType .u1 :=
  ⟨context_regular, expandedType_formed⟩

/-- Exact normalization transports an ordinary typing derivation across a
nontrivial beta step inside its dependent result type. -/
theorem transport_accepts_dependent_type_conversion :
    (transportTyping? resultTypingJudgment expandedTypeFormation).isSome =
      true := by
  rw [transportTyping?_isSome_iff]
  exact .symm (.rel
    ⟨expandedType_reduces_resultType,
      expandedType_formed.constantFree_both
        context_regular.constantFreeCtx |>.1,
      resultType_formed.constantFree_both
        context_regular.constantFreeCtx |>.1⟩)

theorem target_has_expandedType :
    RegularHasType context target expandedType := by
  cases generated : transportTyping? resultTypingJudgment expandedTypeFormation with
  | none =>
      have accepted := transport_accepts_dependent_type_conversion
      rw [generated] at accepted
      contradiction
  | some judgment =>
      exact judgment.judgment.typing

/-- Instantiating the codomain computes the expected identity family. -/
theorem instantiate_codomain (value : PureTm 1) :
    inst0 value codomain = .id .u0 value value := by
  simp [codomain, inst0, subst, subst0]

/-- The family is genuinely dependent: two distinct variables select
syntactically distinct fibres. -/
theorem codomain_distinguishes_arguments :
    inst0 (.var 0 : PureTm 2)
        (.id .u0 (.var 0) (.var 0) : PureTm 3) ≠
      inst0 (.var 1 : PureTm 2)
        (.id .u0 (.var 0) (.var 0) : PureTm 3) := by
  decide

/-- Endpoint conversion forgets which proof tree was supplied. -/
def paddedBetaPath :
    Path State (fun {index} => @ReductionGenerator index)
      sourceState targetState :=
  .trans
    (ConversionEvidence.refl
      (computation := computation State
        (fun {index} => @ReductionGenerator index)) sourceState)
    betaPath

theorem betaPath_ne_paddedBetaPath : betaPath ≠ paddedBetaPath := by
  intro equality
  cases equality

theorem dependent_beta_history_not_recoverable :
    ¬ ∃ recover :
        Nonempty
            (Path State (fun {index} => @ReductionGenerator index)
              sourceState targetState) →
          Path State (fun {index} => @ReductionGenerator index)
            sourceState targetState,
        ∀ path, recover ⟨path⟩ = path :=
  no_path_history_retraction betaPath paddedBetaPath
    betaPath_ne_paddedBetaPath

end DependentBetaCanary

/-! ## The one-base simple fragment -/

namespace SimpleFragment

/-- The ordinary one-base simple types.  This is only the constant-codomain
fragment used to compare conversion behavior; it is not a full HOL signature. -/
inductive SimpleType where
  | base
  | arrow : SimpleType → SimpleType → SimpleType
  deriving DecidableEq, Repr

/-- Embed a simple type as a dependent type whose codomain does not mention
its newly bound variable. -/
def embed (contextLength : Nat) : SimpleType → PureTm contextLength
  | .base => .u0
  | .arrow domain codomain =>
      .pi (embed contextLength domain) (embed (contextLength + 1) codomain)

/-- The simple embedding is faithful. -/
theorem embed_injective (contextLength : Nat) :
    Function.Injective (embed contextLength) := by
  intro source
  induction source generalizing contextLength with
  | base =>
      intro target equality
      cases target with
      | base => rfl
      | arrow domain codomain => cases equality
  | arrow sourceDomain sourceCodomain domainIH codomainIH =>
      intro target equality
      cases target with
      | base => cases equality
      | arrow targetDomain targetCodomain =>
          injection equality with contextEquality domainEquality codomainEquality
          cases contextEquality
          exact congrArg₂ SimpleType.arrow
            (domainIH contextLength domainEquality)
            (codomainIH (contextLength + 1) codomainEquality)

/-- Embedded simple types stay in the declaration-free fragment. -/
theorem embed_constantFree (contextLength : Nat) (type : SimpleType) :
    ConstantFree (embed contextLength type) := by
  induction type generalizing contextLength with
  | base => exact .u0
  | arrow domain codomain domainIH codomainIH =>
      exact .pi (domainIH contextLength) (codomainIH (contextLength + 1))

/-- Embedded simple types contain no computational redex. -/
theorem embed_redNormal (contextLength : Nat) (type : SimpleType) :
    RedNormal (embed contextLength type) := by
  induction type generalizing contextLength with
  | base =>
      intro target step
      cases step
  | arrow domain codomain domainIH codomainIH =>
      intro target step
      cases step with
      | congPiDom domainStep =>
          exact domainIH contextLength _ domainStep
      | congPiCod codomainStep =>
          exact codomainIH (contextLength + 1) _ codomainStep

/-- Every embedded simple type is formed in every regular context. -/
theorem embed_formed {contextLength : Nat} {context : Ctx contextLength}
    (contextRegular : RegularCtx context) (type : SimpleType) :
    RegularHasType context (embed contextLength type) .u1 := by
  induction type generalizing contextLength with
  | base => exact .u0_type context
  | arrow domain codomain domainIH codomainIH =>
      have domainFormed := domainIH contextRegular
      exact .pi_form domainFormed
        (codomainIH (.snoc contextRegular domainFormed))

/-- In the one-base simple image, dependent conversion is exactly literal
simple-type equality. -/
theorem fragmentConversion_iff_eq
    (contextLength : Nat) (source target : SimpleType) :
    ConstantFreeConv (embed contextLength source)
        (embed contextLength target) ↔
      source = target := by
  constructor
  · intro conversion
    apply embed_injective contextLength
    exact normalForms_eq_of_conv
      Relation.ReflTransGen.refl Relation.ReflTransGen.refl
      (embed_redNormal contextLength source)
      (embed_redNormal contextLength target) conversion.toConv
  · intro equality
    subst target
    exact .refl _ (embed_constantFree contextLength source)

/-- A regular context turns every embedded simple type into a state of the
exact normalizer. -/
def state {contextLength : Nat} {context : Ctx contextLength}
    (contextRegular : RegularCtx context) (type : SimpleType) :
    State contextLength :=
  ⟨embed contextLength type,
    regularNormalizationSpecification.covers_subject
      (⟨contextRegular, embed_formed contextRegular type⟩ :
        RegularJudgment context (embed contextLength type) .u1)⟩

/-- The generic normalization decision restricts to decidable equality on
the simple image. -/
theorem decision_eq_true_iff_type_eq
    {contextLength : Nat} {context : Ctx contextLength}
    (contextRegular : RegularCtx context) (source target : SimpleType) :
    normalizationInvariant.decideConversion contextLength
        (state contextRegular source) (state contextRegular target) = true ↔
      source = target := by
  rw [decideConversion_eq_true_iff_fragmentConversion]
  exact fragmentConversion_iff_eq contextLength source target

/-- Positive control: an arrow type converts to itself. -/
theorem arrow_self_accepted :
    normalizationInvariant.decideConversion 0
        (state RegularCtx.nil (.arrow .base .base))
        (state RegularCtx.nil (.arrow .base .base)) = true := by
  exact (decision_eq_true_iff_type_eq .nil _ _).2 rfl

/-- Negative control: the base type is not confused with an arrow. -/
theorem base_arrow_rejected :
    normalizationInvariant.decideConversion 0
        (state RegularCtx.nil .base)
        (state RegularCtx.nil (.arrow .base .base)) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro accepted
  have equality :=
    (decision_eq_true_iff_type_eq .nil .base (.arrow .base .base)).1
      accepted
  cases equality

end SimpleFragment

/-! ## Negative boundaries of the concrete calculus -/

/-- The distinguished ground type and the untyped formation marker are not
convertible. -/
theorem ground_not_convertible_to_formationMarker :
    ¬ Nonempty
      (Path State (fun {index} => @ReductionGenerator index)
        coveredRegularU0 coveredRegularU1) := by
  intro path
  have accepted :=
    normalizationInvariant.decideConversion_eq_true_iff.mpr path
  rw [genericDecision_eq_regularDecision] at accepted
  rw [regular_rejects_u0_u1] at accepted
  contradiction

/-- The sealed fragment cannot quantify over its untyped formation marker. -/
theorem formationMarker_domain_is_rejected {contextLength : Nat}
    {context : Ctx contextLength} {type : PureTm contextLength} :
    ¬ RegularHasType context (.pi .u1 .u1) type :=
  no_regular_pi_u1_domain

/-- The untyped self-reducing term is not silently admitted to the exact
normalization domain. -/
theorem loopingTerm_outside_domain :
    ¬ accessibleNormalizationSpecification.Domain regularOmega :=
  accessibleNormalizationSpecification.omega_not_in_domain

/-! ## Axiom audit -/

#print axioms domainAfterRedStar
#print axioms nonemptyPathOfRedStar
#print axioms normalizationInvariant
#print axioms nonemptyPath_iff_fragmentConversion
#print axioms decideConversion_eq_true_iff_fragmentConversion
#print axioms genericDecision_eq_regularDecision
#print axioms transportTyping?_isSome_iff
#print axioms DependentBetaCanary.source_typed
#print axioms DependentBetaCanary.target_typed
#print axioms DependentBetaCanary.decision_accepts_dependent_beta
#print axioms DependentBetaCanary.transport_accepts_dependent_type_conversion
#print axioms DependentBetaCanary.target_has_expandedType
#print axioms DependentBetaCanary.codomain_distinguishes_arguments
#print axioms DependentBetaCanary.dependent_beta_history_not_recoverable
#print axioms SimpleFragment.embed_injective
#print axioms SimpleFragment.embed_redNormal
#print axioms SimpleFragment.embed_formed
#print axioms SimpleFragment.fragmentConversion_iff_eq
#print axioms SimpleFragment.decision_eq_true_iff_type_eq
#print axioms SimpleFragment.arrow_self_accepted
#print axioms SimpleFragment.base_arrow_rejected
#print axioms ground_not_convertible_to_formationMarker
#print axioms formationMarker_domain_is_rejected
#print axioms loopingTerm_outside_domain

end Mettapedia.TypeTheory.RegularDependentConversionDecision
