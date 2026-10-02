import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizNativeQualifiedHOTGIntegration
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMapComputation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLTraceDisplayedTerms

/-!
# A recursively compiled HOL proof observed through native execution

The recursive HOL compiler and the native list evaluator meet here on the
same trace-coded set model.  The compiler's retained map-fusion proof yields
an identity witness between the two semantic endpoints.  That witness
transports an arbitrary property, and the independently defined native
beta/iota reduction makes the transported property observable after either
program.

The bridge is intentionally observation-indexed.  It establishes finite
reachability of the same pure constructor result; it does not identify
execution traces or license the theorem for effects, ordering, or mutation.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace NativeHOLRecursiveProofOperationalObservation

open Presentation NativeIndexedFamilies IntrinsicNativeListMapComputation
open FormationSensitiveHOLInterface FormationSensitiveHOLUniformList
open Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniformListTraceTermInterpretation
open HOLLeibnizNativeQualifiedHOTGIntegration
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe u

abbrev ElementMeaning {n : Nat} (a : ZFSet.{u})
    (context : NativeTraceLambdaSemantics.Context.{u} n) :=
  context.Environment -> Value a element

abbrev FunctionMeaning {n : Nat} (a : ZFSet.{u})
    (context : NativeTraceLambdaSemantics.Context.{u} n) :=
  context.Environment -> Value a mapping

abbrev Heads {n : Nat} (a : ZFSet.{u})
    (context : NativeTraceLambdaSemantics.Context.{u} n) :=
  List (Tower.Tm n × ElementMeaning a context)

def elementCode (n : Nat) : Tower.Tm n :=
  typeAt types n element

def headValues {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (heads : Heads a context) (environment : context.Environment) :
    List (Value a element) :=
  heads.map (fun head => head.2 environment)

/-- A native List constructor spine denotes an actual list in the same
trace-coded set model used by the recursively compiled proof. -/
inductive SpineDenotes (a : ZFSet.{u}) {n : Nat}
    (context : NativeTraceLambdaSemantics.Context.{u} n) :
    Tower.Tm n -> (context.Environment -> Value a sequence) -> Prop where
  | nil : SpineDenotes a context
      (Intrinsic.nilApp (elementCode n))
      (fun _ => ZFSetList.nil a)
  | cons {head tail : Tower.Tm n}
      {headValue : ElementMeaning a context}
      {tailValue : context.Environment -> Value a sequence} :
      NativeHOLTraceDisplayedTerms.Denotes a context head headValue ->
      SpineDenotes a context tail tailValue ->
      SpineDenotes a context
        (Intrinsic.consApp (elementCode n) head tail)
        (fun environment => ZFSetList.cons
          (headValue environment) (tailValue environment))

theorem encode_denotes {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (heads : Heads a context)
    (interpreted : ∀ head ∈ heads,
      NativeHOLTraceDisplayedTerms.Denotes a context head.1 head.2) :
    SpineDenotes a context
      (encode (elementCode n) (heads.map Prod.fst))
      (fun environment => ZFSetList.encodeValue (headValues heads environment)) := by
  induction heads with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons (interpreted head List.mem_cons_self)
        (inductionHypothesis
          (fun current member => interpreted current
            (List.mem_cons_of_mem head member)))

/-- The common constructor result of the two native map programs has the
pointwise Aczel-trace meaning of their submitted functions. -/
theorem fusion_output_denotes {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (f g : Tower.Tm n) (fMeaning gMeaning : FunctionMeaning a context)
    (fDenotes : NativeHOLTraceDisplayedTerms.Denotes a context f fMeaning)
    (gDenotes : NativeHOLTraceDisplayedTerms.Denotes a context g gMeaning)
    (heads : Heads a context)
    (interpreted : ∀ head ∈ heads,
      NativeHOLTraceDisplayedTerms.Denotes a context head.1 head.2) :
    SpineDenotes a context
      (encode (elementCode n)
        ((heads.map Prod.fst).map (fun x => .app f (.app g x))))
      (fun environment => ZFSetList.encodeValue
        ((headValues heads environment).map
          (fun x => app (fMeaning environment) (app (gMeaning environment) x)))) := by
  induction heads with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      have headMeaning := NativeHOLTraceDisplayedTerms.Denotes.application
        fDenotes
        (NativeHOLTraceDisplayedTerms.Denotes.application gDenotes
          (interpreted head List.mem_cons_self))
      have tailMeaning := inductionHypothesis
        (fun current member => interpreted current
          (List.mem_cons_of_mem head member))
      simpa only [List.map_cons, encode, headValues,
        ZFSetList.encodeValue_cons] using
          (SpineDenotes.cons headMeaning tailMeaning)

theorem decoded_double_application {a : ZFSet.{u}}
    (f g : Value a mapping) (x : Value a element) :
    (decode a mapping f) ((decode a mapping g) x) =
      app f (app g x) := by
  exact
    (congrArg (decode a mapping f) (decode_app g x).symm).trans
      (decode_app f (app g x)).symm

theorem beforeSection_encodeValue {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : List (Value a element)) :
    ZFSetUniformListTraceProofBridge.beforeSection f g
        (ZFSetList.encodeValue xs) PUnit.unit =
      ZFSetList.encodeValue
        ((xs.map (fun x => app g x)).map (fun x => app f x)) := by
  unfold ZFSetUniformListTraceProofBridge.beforeSection
  apply (decode a sequence).injective
  rw [ZFSetUniformListTraceTermInterpretation.term_agreement]
  change ZFSetUniformListModel.mapValue (decode a mapping f)
      (ZFSetUniformListModel.mapValue (decode a mapping g)
        (ZFSetList.encodeValue xs)) =
    ZFSetList.encodeValue
      ((xs.map (fun x => app g x)).map (fun x => app f x))
  calc
    _ = ZFSetList.map (decode a mapping f)
        (ZFSetUniformListModel.mapValue (decode a mapping g)
          (ZFSetList.encodeValue xs)) :=
      ZFSetUniformListModel.mapValue_eq _ _
    _ = ZFSetList.map (decode a mapping f)
        (ZFSetList.map (decode a mapping g) (ZFSetList.encodeValue xs)) :=
      congrArg (ZFSetList.map (decode a mapping f))
        (ZFSetUniformListModel.mapValue_eq _ _)
    _ = _ := by
      simp only [ZFSetList.map, ZFSetList.decode_encode]
      apply congrArg ZFSetList.encodeValue
      induction xs with
      | nil => rfl
      | cons x rest inductionHypothesis =>
          simp only [List.map_cons]
          exact congrArg₂ List.cons
            (decoded_double_application f g x) inductionHypothesis

theorem afterSection_encodeValue {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : List (Value a element)) :
    ZFSetUniformListTraceProofBridge.afterSection f g
        (ZFSetList.encodeValue xs) PUnit.unit =
      ZFSetList.encodeValue
        (xs.map (fun x => app f (app g x))) := by
  unfold ZFSetUniformListTraceProofBridge.afterSection
  apply (decode a sequence).injective
  rw [ZFSetUniformListTraceTermInterpretation.term_agreement]
  change ZFSetUniformListModel.mapValue
      (fun x => (decode a mapping f) ((decode a mapping g) x))
      (ZFSetList.encodeValue xs) =
    ZFSetList.encodeValue (xs.map (fun x => app f (app g x)))
  calc
    _ = ZFSetList.map
        (fun x => (decode a mapping f) ((decode a mapping g) x))
        (ZFSetList.encodeValue xs) :=
      ZFSetUniformListModel.mapValue_eq _ _
    _ = _ := by
      simp only [ZFSetList.map, ZFSetList.decode_encode]
      apply congrArg ZFSetList.encodeValue
      apply List.map_congr_left
      intro x _
      exact decoded_double_application f g x

/-- Membership of the recursive compiler's identity witness reflects the
literal equality of its two trace-coded sequence endpoints. -/
theorem recursive_fusion_endpoints_equal {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence) :
    ZFSetUniformListTraceProofBridge.beforeSection f g xs PUnit.unit =
      ZFSetUniformListTraceProofBridge.afterSection f g xs PUnit.unit := by
  have member :=
    (DependentConsumption.recursiveFusionIdentityWitness f g xs).2
  change
    (DependentConsumption.recursiveFusionIdentityWitness f g xs).1 ∈
      ZFSetTraceProofDecoding.truthCode
        (ZFSetUniformListTraceProofBridge.beforeSection f g xs PUnit.unit =
          ZFSetUniformListTraceProofBridge.afterSection f g xs PUnit.unit) at member
  exact (ZFSetTraceProofDecoding.mem_truthCode _ _).mp member |>.2

/-- An arbitrary semantic property is transported by the witness extracted
from the actual recursively compiled proof. -/
theorem recursive_fusion_transports_property {a : ZFSet.{u}}
    (f g : Value a mapping) (xs : Value a sequence)
    (property : Value a sequence -> Prop)
    (accepted : property
      (ZFSetUniformListTraceProofBridge.beforeSection f g xs PUnit.unit)) :
    property (ZFSetUniformListTraceProofBridge.afterSection f g xs PUnit.unit) := by
  rw [recursive_fusion_endpoints_equal f g xs] at accepted
  exact accepted

/-- An OSLF observation of a native constructor result through its meaning in
the common trace-coded set model. -/
def observes {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (environment : context.Environment)
    (property : Value a sequence -> Prop) (output : Tower.Tm n) : Prop :=
  ∃ values, SpineDenotes a context output values ∧ property (values environment)

/-- The same observation as an OSLF semantic predicate.  The native reduction
uses syntactic equality as its equation theory, so the invariance proof is
literal here; presentations with nontrivial equations use the same interface
with a substantive invariance proof. -/
def semanticObservation {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (environment : context.Environment)
    (property : Value a sequence -> Prop) :
    EquationPredicate (reduction level n).closure :=
  invariantPredicate (reduction level n).closure
    (observes environment property) (by
      intro left right equivalent
      change left = right at equivalent
      subst right
      exact Iff.rfl)

/-- The quotient-level reading of the same observation.  This is the natural
interface when authored equations are nontrivial. -/
def quotientObservation {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (environment : context.Environment)
    (property : Value a sequence -> Prop) :
    Quotient (reduction level n).closure.equations -> Prop :=
  descendPredicate (reduction level n).closure
    (semanticObservation level environment property)

@[simp] theorem quotientObservation_mk {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (environment : context.Environment)
    (property : Value a sequence -> Prop) (term : Tower.Tm n) :
    quotientObservation level environment property
        (Quotient.mk (reduction level n).closure.equations term) =
      observes environment property term :=
  rfl

theorem semanticObservation_mono {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (environment : context.Environment)
    {first second : Value a sequence -> Prop}
    (implication : ∀ value, first value -> second value) :
    semanticObservation level environment first ≤
      semanticObservation level environment second := by
  rintro term ⟨values, meaning, accepted⟩
  exact ⟨values, meaning, implication _ accepted⟩

/-- The central commuting square.  The property premise is attached to the
unfused semantic endpoint.  The retained recursive compiler witness transports
it to the fused endpoint; native beta/iota execution then exposes that same
endpoint after both programs as a GSLT diamond observation. -/
theorem recursive_proof_fusion_observed {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (f g : Tower.Tm n)
    (fMeaning gMeaning : FunctionMeaning a context)
    (fDenotes : NativeHOLTraceDisplayedTerms.Denotes a context f fMeaning)
    (gDenotes : NativeHOLTraceDisplayedTerms.Denotes a context g gMeaning)
    (heads : Heads a context)
    (interpreted : ∀ head ∈ heads,
      NativeHOLTraceDisplayedTerms.Denotes a context head.1 head.2)
    (environment : context.Environment) (property : Value a sequence -> Prop)
    (accepted : property
      (ZFSetUniformListTraceProofBridge.beforeSection
        (fMeaning environment) (gMeaning environment)
        (ZFSetList.encodeValue (headValues heads environment)) PUnit.unit)) :
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
        (reduction level n).closure (observes environment property)
        (applyMap (elementCode n) (elementCode n) f
          (applyMap (elementCode n) (elementCode n) g
            (encode (elementCode n) (heads.map Prod.fst)))) ∧
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
        (reduction level n).closure (observes environment property)
        (applyMap (elementCode n) (elementCode n) (compose f g)
          (encode (elementCode n) (heads.map Prod.fst))) := by
  apply fusion_observed level (elementCode n) (elementCode n) (elementCode n)
    f g (heads.map Prod.fst) (observes environment property)
  refine ⟨_, fusion_output_denotes f g fMeaning gMeaning
    fDenotes gDenotes heads interpreted, ?_⟩
  have transported := recursive_fusion_transports_property
    (fMeaning environment) (gMeaning environment)
      (ZFSetList.encodeValue (headValues heads environment)) property accepted
  rw [afterSection_encodeValue] at transported
  exact transported

/-- The commuting square stated inside the equation-respecting OSLF
predicate frame, rather than over a raw predicate on syntax. -/
theorem recursive_proof_fusion_semantic_observed {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (f g : Tower.Tm n)
    (fMeaning gMeaning : FunctionMeaning a context)
    (fDenotes : NativeHOLTraceDisplayedTerms.Denotes a context f fMeaning)
    (gDenotes : NativeHOLTraceDisplayedTerms.Denotes a context g gMeaning)
    (heads : Heads a context)
    (interpreted : ∀ head ∈ heads,
      NativeHOLTraceDisplayedTerms.Denotes a context head.1 head.2)
    (environment : context.Environment) (property : Value a sequence -> Prop)
    (accepted : property
      (ZFSetUniformListTraceProofBridge.beforeSection
        (fMeaning environment) (gMeaning environment)
        (ZFSetList.encodeValue (headValues heads environment)) PUnit.unit)) :
    semanticDiamond (reduction level n).closure
        (semanticObservation level environment property)
        (applyMap (elementCode n) (elementCode n) f
          (applyMap (elementCode n) (elementCode n) g
            (encode (elementCode n) (heads.map Prod.fst)))) ∧
      semanticDiamond (reduction level n).closure
        (semanticObservation level environment property)
        (applyMap (elementCode n) (elementCode n) (compose f g)
          (encode (elementCode n) (heads.map Prod.fst))) := by
  exact recursive_proof_fusion_observed level f g fMeaning gMeaning
    fDenotes gDenotes heads interpreted environment property accepted

/-- Negative modal control: neither raw nor quotient-aware OSLF synthesis can
manufacture an observation whose semantic property is false. -/
theorem false_semantic_observation_unreachable {n : Nat} {a : ZFSet.{u}}
    {context : NativeTraceLambdaSemantics.Context.{u} n}
    (level : LevelExpr Nat) (environment : context.Environment)
    (source : Tower.Tm n) :
    ¬ semanticDiamond (reduction level n).closure
        (semanticObservation level environment
          (fun _ : Value a sequence => False)) source := by
  intro reached
  obtain ⟨target, _step, values, _meaning, impossible⟩ :=
    (gsltDiamond_spec (reduction level n).closure
      (semanticObservation level environment
        (fun _ : Value a sequence => False)) source).mp reached
  exact impossible

namespace Controls

/-- One genuinely open element variable supplies a nonempty native list. -/
noncomputable def elementContext (a : ZFSet.{u}) :
    NativeTraceLambdaSemantics.Context.{u} 1 :=
  NativeTraceLambdaSemantics.Context.nil.snoc
    (NativeHOLTraceDisplayedTerms.typeFamily a
      NativeTraceLambdaSemantics.Context.nil element)

noncomputable def elementEnvironment {a : ZFSet.{u}} (x : Value a element) :
    (elementContext a).Environment :=
  ⟨PUnit.unit, x⟩

def nativeIdentity : Tower.Tm 1 :=
  .lam (.var 0)

noncomputable def identityMeaning {a : ZFSet.{u}} :
    FunctionMeaning a (elementContext a) :=
  fun _ => lam (fun x => x)

def nativeHead : Tower.Tm 1 :=
  .var 0

noncomputable def headMeaning {a : ZFSet.{u}} :
    ElementMeaning a (elementContext a) :=
  (elementContext a).projection 0

noncomputable def singletonHeads {a : ZFSet.{u}} :
    Heads a (elementContext a) :=
  [(nativeHead, headMeaning)]

theorem identity_denotes (a : ZFSet.{u}) :
    NativeHOLTraceDisplayedTerms.Denotes a (elementContext a)
      nativeIdentity identityMeaning := by
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value
    (NativeHOLTraceDisplayedTerms.Denotes.abstraction
      (NativeHOLTraceDisplayedTerms.Controls.newest_object_variable_denotes
        a (elementContext a) element))
  rfl

theorem head_denotes (a : ZFSet.{u}) :
    NativeHOLTraceDisplayedTerms.Denotes a (elementContext a)
      nativeHead headMeaning := by
  exact NativeHOLTraceDisplayedTerms.Controls.newest_object_variable_denotes
    a NativeTraceLambdaSemantics.Context.nil element

/-- In this displayed one-variable context the raw head has exactly the
context projection as its meaning. -/
theorem head_denotation_unique {a : ZFSet.{u}}
    {meaning : ElementMeaning a (elementContext a)}
    (denotes : NativeHOLTraceDisplayedTerms.Denotes a (elementContext a)
      nativeHead meaning) :
    meaning = headMeaning := by
  cases denotes with
  | «variable» index variableMeaning =>
      cases variableMeaning
      rfl

/-- Exact semantic reading of the one-element constructor output. -/
theorem observes_singleton_iff {a : ZFSet.{u}} (x : Value a element)
    (property : Value a sequence -> Prop) :
    observes (elementEnvironment x) property
        (encode (elementCode 1) [nativeHead]) ↔
      property (ZFSetList.encodeValue [x]) := by
  constructor
  · rintro ⟨values, meaning, accepted⟩
    cases meaning with
    | cons head tail =>
        cases tail with
        | nil =>
            rw [head_denotation_unique head] at accepted
            simpa [headMeaning, elementEnvironment, elementContext,
              ZFSetList.nil] using accepted
  · intro accepted
    refine ⟨fun environment =>
        ZFSetList.encodeValue (headValues singletonHeads environment),
      encode_denotes singletonHeads ?_, ?_⟩
    · intro head member
      simp only [singletonHeads, List.mem_singleton] at member
      subst head
      exact head_denotes a
    · simpa [headValues, singletonHeads, headMeaning, elementEnvironment,
        elementContext] using accepted

/-- A nonempty end-to-end control: the actual recursively compiled HOL proof
transports singleton identity-map fusion, and native beta/iota execution makes
the same Aczel list value visible through both GSLT diamonds. -/
theorem singleton_identity_fusion_observed (level : LevelExpr Nat)
    {a : ZFSet.{u}} (x : Value a element) :
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
        (reduction level 1).closure
        (observes (elementEnvironment x)
          (fun output => output = ZFSetList.encodeValue [x]))
        (applyMap (elementCode 1) (elementCode 1) nativeIdentity
          (applyMap (elementCode 1) (elementCode 1) nativeIdentity
            (encode (elementCode 1) [nativeHead]))) ∧
      Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
        (reduction level 1).closure
        (observes (elementEnvironment x)
          (fun output => output = ZFSetList.encodeValue [x]))
        (applyMap (elementCode 1) (elementCode 1)
          (compose nativeIdentity nativeIdentity)
          (encode (elementCode 1) [nativeHead])) := by
  apply recursive_proof_fusion_observed level nativeIdentity nativeIdentity
    identityMeaning identityMeaning (identity_denotes a) (identity_denotes a)
    singletonHeads
  · intro head member
    simp only [singletonHeads, List.mem_singleton] at member
    subst head
    exact head_denotes a
  · rw [beforeSection_encodeValue]
    simp [identityMeaning, elementEnvironment, headValues, singletonHeads,
      headMeaning, elementContext]

/-- The nonempty control through the generated OSLF semantic frame. -/
theorem singleton_identity_fusion_semantic_observed (level : LevelExpr Nat)
    {a : ZFSet.{u}} (x : Value a element) :
    semanticDiamond (reduction level 1).closure
        (semanticObservation level (elementEnvironment x)
          (fun output => output = ZFSetList.encodeValue [x]))
        (applyMap (elementCode 1) (elementCode 1) nativeIdentity
          (applyMap (elementCode 1) (elementCode 1) nativeIdentity
            (encode (elementCode 1) [nativeHead]))) ∧
      semanticDiamond (reduction level 1).closure
        (semanticObservation level (elementEnvironment x)
          (fun output => output = ZFSetList.encodeValue [x]))
        (applyMap (elementCode 1) (elementCode 1)
          (compose nativeIdentity nativeIdentity)
          (encode (elementCode 1) [nativeHead])) := by
  exact singleton_identity_fusion_observed level x

/-- Changed-property control over the same concrete representation: the
singleton containing `zero` is not observed as the singleton containing
`one`. -/
theorem changed_singleton_observation_rejected :
    ¬ observes
      (elementEnvironment
        ZFSetUniformListProofConsumption.Controls.zero)
      (fun output => output = ZFSetList.encodeValue
        [ZFSetUniformListProofConsumption.Controls.one])
      (encode (elementCode 1) [nativeHead]) := by
  rw [observes_singleton_iff]
  intro equal
  have consEqual :
      ZFSetList.cons ZFSetUniformListProofConsumption.Controls.zero
          (ZFSetList.encodeValue []) =
        ZFSetList.cons ZFSetUniformListProofConsumption.Controls.one
          (ZFSetList.encodeValue []) := by
    simpa only [ZFSetList.encodeValue_cons] using equal
  exact ZFSetUniformListProofConsumption.Controls.zero_ne_one
    (ZFSetList.cons_injective consEqual).1

/-! ### A noncommuting orientation control -/

noncomputable def twoElementContext (a : ZFSet.{u}) :
    NativeTraceLambdaSemantics.Context.{u} 2 :=
  let first := NativeTraceLambdaSemantics.Context.nil.snoc
    (NativeHOLTraceDisplayedTerms.typeFamily a
      NativeTraceLambdaSemantics.Context.nil element)
  first.snoc (NativeHOLTraceDisplayedTerms.typeFamily a first element)

noncomputable def twoElementEnvironment {a : ZFSet.{u}}
    (older newer : Value a element) : (twoElementContext a).Environment :=
  ⟨⟨PUnit.unit, older⟩, newer⟩

/-- Under the lambda binder, index two is the older external element. -/
def constantOlder : Tower.Tm 2 :=
  .lam (.var 2)

/-- Under the lambda binder, index one is the newer external element. -/
def constantNewer : Tower.Tm 2 :=
  .lam (.var 1)

def olderHead : Tower.Tm 2 :=
  .var 1

noncomputable def constantOlderMeaning {a : ZFSet.{u}} :
    FunctionMeaning a (twoElementContext a) :=
  fun environment => lam (fun _ => (twoElementContext a).projection 1 environment)

noncomputable def constantNewerMeaning {a : ZFSet.{u}} :
    FunctionMeaning a (twoElementContext a) :=
  fun environment => lam (fun _ => (twoElementContext a).projection 0 environment)

noncomputable def olderHeadMeaning {a : ZFSet.{u}} :
    ElementMeaning a (twoElementContext a) :=
  (twoElementContext a).projection 1

noncomputable def olderSingletonHeads {a : ZFSet.{u}} :
    Heads a (twoElementContext a) :=
  [(olderHead, olderHeadMeaning)]

@[simp] theorem twoElement_projection_zero {a : ZFSet.{u}}
    (older newer : Value a element) :
    (twoElementContext a).projection 0
        (twoElementEnvironment older newer) = newer :=
  rfl

@[simp] theorem twoElement_projection_one {a : ZFSet.{u}}
    (older newer : Value a element) :
    (twoElementContext a).projection 1
        (twoElementEnvironment older newer) = older :=
  rfl

@[simp] theorem olderSingleton_headValues {a : ZFSet.{u}}
    (older newer : Value a element) :
    headValues olderSingletonHeads (twoElementEnvironment older newer) =
      [older] :=
  rfl

theorem constantOlder_denotes (a : ZFSet.{u}) :
    NativeHOLTraceDisplayedTerms.Denotes a (twoElementContext a)
      constantOlder constantOlderMeaning := by
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value
    (NativeHOLTraceDisplayedTerms.Denotes.abstraction
      (NativeHOLTraceDisplayedTerms.Denotes.variable 2
        (NativeTraceLambdaSemantics.Denotes.var _ 2)))
  rfl

theorem constantNewer_denotes (a : ZFSet.{u}) :
    NativeHOLTraceDisplayedTerms.Denotes a (twoElementContext a)
      constantNewer constantNewerMeaning := by
  apply NativeHOLTraceDisplayedTerms.Denotes.change_value
    (NativeHOLTraceDisplayedTerms.Denotes.abstraction
      (NativeHOLTraceDisplayedTerms.Denotes.variable 1
        (NativeTraceLambdaSemantics.Denotes.var _ 1)))
  rfl

theorem olderHead_denotes (a : ZFSet.{u}) :
    NativeHOLTraceDisplayedTerms.Denotes a (twoElementContext a)
      olderHead olderHeadMeaning := by
  exact NativeHOLTraceDisplayedTerms.Denotes.variable 1
    (NativeTraceLambdaSemantics.Denotes.var _ 1)

/-- These two native functions really do not commute when their captured
external elements differ. -/
theorem captured_constants_do_not_commute {a : ZFSet.{u}}
    (older newer : Value a element) (different : older ≠ newer) :
    app (constantOlderMeaning (twoElementEnvironment older newer))
        (app (constantNewerMeaning (twoElementEnvironment older newer)) older) ≠
      app (constantNewerMeaning (twoElementEnvironment older newer))
        (app (constantOlderMeaning (twoElementEnvironment older newer)) older) := by
  simpa only [constantOlderMeaning, constantNewerMeaning,
    ZFSetUniformListTraceTypeInterpretation.app_lam,
    twoElement_projection_zero, twoElement_projection_one] using different

/-- The strongest positive control in this module: the two functions do not
commute, so observing the older singleton confirms that both the compiled HOL
statement and the native `compose` program use `f (g x)`, not `g (f x)`. -/
theorem noncommuting_fusion_semantic_observed (level : LevelExpr Nat)
    {a : ZFSet.{u}} (older newer : Value a element) :
    semanticDiamond (reduction level 2).closure
        (semanticObservation level (twoElementEnvironment older newer)
          (fun output => output = ZFSetList.encodeValue [older]))
        (applyMap (elementCode 2) (elementCode 2) constantOlder
          (applyMap (elementCode 2) (elementCode 2) constantNewer
            (encode (elementCode 2) [olderHead]))) ∧
      semanticDiamond (reduction level 2).closure
        (semanticObservation level (twoElementEnvironment older newer)
          (fun output => output = ZFSetList.encodeValue [older]))
        (applyMap (elementCode 2) (elementCode 2)
          (compose constantOlder constantNewer)
          (encode (elementCode 2) [olderHead])) := by
  apply recursive_proof_fusion_semantic_observed level
    constantOlder constantNewer constantOlderMeaning constantNewerMeaning
    (constantOlder_denotes a) (constantNewer_denotes a) olderSingletonHeads
  · intro head member
    simp only [olderSingletonHeads, List.mem_singleton] at member
    subst head
    exact olderHead_denotes a
  · rw [beforeSection_encodeValue]
    simp only [olderSingleton_headValues, List.map_cons, List.map_nil,
      constantOlderMeaning, constantNewerMeaning,
      ZFSetUniformListTraceTypeInterpretation.app_lam,
      twoElement_projection_zero, twoElement_projection_one]

/-- Concrete two-point witness that the orientation control is non-vacuous. -/
theorem concrete_captured_constants_do_not_commute :
    app
        (constantOlderMeaning
          (twoElementEnvironment
            ZFSetUniformListProofConsumption.Controls.one
            ZFSetUniformListProofConsumption.Controls.zero))
        (app
          (constantNewerMeaning
            (twoElementEnvironment
              ZFSetUniformListProofConsumption.Controls.one
              ZFSetUniformListProofConsumption.Controls.zero))
          ZFSetUniformListProofConsumption.Controls.one) ≠
      app
        (constantNewerMeaning
          (twoElementEnvironment
            ZFSetUniformListProofConsumption.Controls.one
            ZFSetUniformListProofConsumption.Controls.zero))
        (app
          (constantOlderMeaning
            (twoElementEnvironment
              ZFSetUniformListProofConsumption.Controls.one
              ZFSetUniformListProofConsumption.Controls.zero))
          ZFSetUniformListProofConsumption.Controls.one) :=
  captured_constants_do_not_commute _ _
    ZFSetUniformListProofConsumption.Controls.zero_ne_one.symm

end Controls

#print axioms recursive_fusion_endpoints_equal
#print axioms recursive_fusion_transports_property
#print axioms recursive_proof_fusion_observed
#print axioms recursive_proof_fusion_semantic_observed
#print axioms quotientObservation_mk
#print axioms false_semantic_observation_unreachable
#print axioms Controls.singleton_identity_fusion_observed
#print axioms Controls.singleton_identity_fusion_semantic_observed
#print axioms Controls.observes_singleton_iff
#print axioms Controls.changed_singleton_observation_rejected
#print axioms Controls.noncommuting_fusion_semantic_observed
#print axioms Controls.concrete_captured_constants_do_not_commute

end NativeHOLRecursiveProofOperationalObservation
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
