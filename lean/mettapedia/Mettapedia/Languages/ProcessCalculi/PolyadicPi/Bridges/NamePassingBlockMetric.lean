import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalCorrespondence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingValueNative
import Mettapedia.GSLT.Distinction.BlockTransport

/-!
# One source event is one authored polyadic communication block

The existing compiler and independent image inversion instantiate the shared
CompiledBlocks interface. Static scope administration is already in the
equations and contributes no primitive steps. Logical distance transports
exactly for the public returned-function reading; behavioral distance uses the
existing source finite-branching hypothesis. This is the polyadic stage, not
an instruction-count metric on the later unary or rho implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBlockMetric

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Distinction Mettapedia.GSLT.HennessyMilner
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open NamePassingLambda NamePassingEnvironmentEquationsNative

def blocks (Δ : Ctx sig) : BlockReading (NativeTypes.operationalTheory Δ) Unit where
  silent _ _ := False
  complete _ := StepModulo
  external _ _ := False
  silent_step h := h.elim
  complete_step h := h
  external_step h := h.elim
  classify step := .inr (.inl ⟨(), step⟩)
  silent_resp_left _ h := h.elim
  complete_resp_left equal step := (NativeTypes.operationalTheory Δ).rewrites_resp_left equal step
  complete_resp_right step equal := (NativeTypes.operationalTheory Δ).rewrites_resp_right step equal

private theorem silent_eq {Δ : Ctx sig} {first last : Proc Δ}
    (path : Relation.ReflTransGen (blocks Δ).silent first last) : first = last := by
  induction path with
  | refl => rfl
  | tail _ step _ => exact step.elim

private theorem protocol_path {Δ : Ctx sig} {first last : Proc Δ}
    (path : Relation.ReflTransGen (blocks Δ).ProtocolStep first last) :
    (NativeTypes.operationalTheory Δ).MultiStep first last := by
  induction path with
  | refl => exact .refl _
  | tail _ step ih =>
      rcases step with impossible | ⟨label, actual⟩
      · exact impossible.elim
      · exact multiStepAppend ih (.step actual (.refl _))

private theorem multiStep_rtc {S : GSLT} {first last : S.Term}
    (path : S.MultiStep first last) : Relation.ReflTransGen S.Step first last := by
  induction path with
  | refl => exact .refl
  | step first _ ih => exact .head first ih

def compiled {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (faithful : Function.Injective (environment .nm)) (result : Var Δ .nm) :
    CompiledBlocks (sourceTheory Γ) (NativeTypes.operationalTheory Δ) (blocks Δ) where
  realization := realization environment result
  realizedBlocks step := .complete _ ((compiler environment result).mapStep step)
  reflectBlock := by
    rintro source final ⟨middle, administration, actual⟩
    have same := silent_eq administration
    subst middle
    obtain ⟨action, after, step, equal⟩ :=
      NamePassingCompilerReadback.modulo_step_readback source environment faithful result actual
    exact ⟨after, ⟨action, step⟩, equal.symm⟩
  prefixReflection := by
    intro source final actual
    obtain ⟨after, sourcePath, equal⟩ :=
      (NamePassingOperationalCorrespondence.readback environment faithful result).reflectMultiStep
        (.refl _) (protocol_path actual)
    exact ⟨after, multiStep_rtc sourcePath, final, equal.symm, .refl⟩

def sourceObserver (Γ : Ctx sig) : System (sourceTheory Γ) :=
  .ofObserved ⟨Unit, fun _ source => (NamePassingValueNative.sourcePredicate Γ).1 source⟩
    (fun _ _ _ equal => (NamePassingValueNative.sourcePredicate Γ).2 equal)

def targetObserver {Δ : Ctx sig} (result : Var Δ .nm) : System (NativeTypes.operationalTheory Δ) :=
  .ofObserved ⟨Unit, fun _ target => (NamePassingValueNative.targetPredicate result).1 target⟩
    (fun _ _ _ equal => (NamePassingValueNative.targetPredicate result).2 equal)

noncomputable def sourceReadings (Γ : Ctx sig) := GradedObservations.ofSystem (sourceObserver Γ)
noncomputable def targetReadings {Δ : Ctx sig} (result : Var Δ .nm) :=
  GradedObservations.ofSystem (targetObserver result)

private theorem values_agree {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (observation : Unit) (source : Expr Γ) :
    (targetReadings result).value observation (compile source environment result) =
      (sourceReadings Γ).value observation source := by
  classical
  simp only [targetReadings, sourceReadings, GradedObservations.ofSystem, targetObserver,
    sourceObserver, System.ofObserved]
  have observed := NamePassingValueNative.compiled_value_iff source environment result
  by_cases returned : (NamePassingValueNative.sourcePredicate Γ).1 source
  · simp only [returned, observed.mp returned, if_true]
  · simp only [returned, mt observed.mpr returned, if_false]

theorem logicalDistance_eq {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (faithful : Function.Injective (environment .nm)) (result : Var Δ .nm)
    (discount : ℝ) (nonneg : 0 ≤ discount) (bounded : discount ≤ 1) (left right : Expr Γ) :
    ((blocks Δ).graded (targetReadings result) discount nonneg bounded).logicalDistance
        (compile left environment result) (compile right environment result) =
      (GradedSystem.stepping (sourceTheory Γ) (sourceReadings Γ) discount nonneg bounded).logicalDistance
        left right :=
  (compiled environment faithful result).logicalDistance_eq (sourceReadings Γ) (targetReadings result)
    nonneg bounded id (values_agree environment result) Function.surjective_id left right

theorem behaviouralDistance_eq {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (faithful : Function.Injective (environment .nm)) (result : Var Δ .nm)
    (discount : ℝ) (nonneg : 0 ≤ discount) (bounded : discount ≤ 1)
    (finite : (GradedSystem.stepping (sourceTheory Γ) (sourceReadings Γ)
      discount nonneg bounded).dynamics.ImageFiniteModulo) (left right : Expr Γ) :
    ((blocks Δ).graded (targetReadings result) discount nonneg bounded).behaviouralDistance
        (compile left environment result) (compile right environment result) =
      (GradedSystem.stepping (sourceTheory Γ) (sourceReadings Γ) discount nonneg bounded).behaviouralDistance
        left right :=
  (compiled environment faithful result).behaviouralDistance_eq (sourceReadings Γ) (targetReadings result)
    nonneg bounded id (values_agree environment result) Function.surjective_id finite left right

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBlockMetric
