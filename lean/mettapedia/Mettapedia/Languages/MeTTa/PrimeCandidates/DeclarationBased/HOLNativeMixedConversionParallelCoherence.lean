import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ParallelConversionViews
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeMixedConversionParallelSubstitution

/-!
# Authored conversion qualification from completed parallel coherence

Every authored contextual step is a completed parallel step, and every finite
completed parallel path is authored conversion evidence. A diamond proof for
the auxiliary relation therefore joins authored conversions and yields Pi and
Sigma component injectivity and head separation for the actual joint rules.

The diamond is an explicit hypothesis here, to be discharged by a separate
development theorem. No Church--Rosser property of raw authored execution is
assumed or concluded.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeMixedConversionParallel

open Presentation NativeIndexedFamilies HOLNativeMixedConversionCompletion
open FormationSensitiveHOLProofFamily FormationSensitiveHOLUniformList

variable {n : Nat}

/-- Finite paths in the auxiliary parallel relation. -/
abbrev ParStar (left right : Tower.Tm n) : Prop :=
  Relation.ReflTransGen Par left right

/-- The one-step parallel diamond required by the qualification theorem. -/
abbrev Diamond : Prop :=
  ∀ {n : Nat} {source left right : Tower.Tm n},
    Par source left → Par source right → ∃ common, Par left common ∧ Par right common

theorem root_to_par {left right : Tower.Tm n} (root : Root left right) : Par left right := by
  cases root with
  | listNil ca =>
      exact .listNil ca (par_refl _) (par_refl _) (par_refl _) (par_refl _)
  | listCons ca =>
      exact .listCons ca (par_refl _) (par_refl _) (par_refl _) (par_refl _)
        (par_refl _) (par_refl _)
  | identity cy cw =>
      exact .identity cy cw (par_refl _) (par_refl _) (par_refl _) (par_refl _)
        (par_refl _) (par_refl _)
  | relNil ca cb cr cx cy =>
      exact .relNil ca cb cr cx cy
        (par_refl _) (par_refl _) (par_refl _) (par_refl _)
        (par_refl _) (par_refl _) (par_refl _) (par_refl _)
  | relCons ca cb cr cx cy =>
      exact .relCons ca cb cr cx cy
        (par_refl _) (par_refl _) (par_refl _) (par_refl _)
        (par_refl _) (par_refl _) (par_refl _) (par_refl _)
        (par_refl _) (par_refl _) (par_refl _) (par_refl _) (par_refl _) (par_refl _)

  | implication p q => exact .implication (par_refl p) (par_refl q)
  | universal a f => exact .universal (par_refl a) (par_refl f)

/-- Every contextual step of the completed presentation is covered by the
parallel relation, including its actual coherence guards. -/
theorem completed_step_to_par {left right : Tower.Tm n}
    (step : Step HOLNativeMixedConversionCompletion.rules.headEq left right
      HOLNativeMixedConversionCompletion.rules.computation) : Par left right := by
  induction step with
  | betaPi body argument => exact .betaPi (par_refl body) (par_refl argument)
  | betaSigmaFst first second => exact .betaSigmaFst (par_refl first) (par_refl second)
  | betaSigmaSnd first second => exact .betaSigmaSnd (par_refl first) (par_refl second)
  | head equality => exact .headRel equality
  | root rootStep => exact root_to_par rootStep
  | congPiDom _ ih => exact .pi ih (par_refl _)
  | congPiCod _ ih => exact .pi (par_refl _) ih
  | congSigmaDom _ ih => exact .sigma ih (par_refl _)
  | congSigmaCod _ ih => exact .sigma (par_refl _) ih
  | congIdTy _ ih => exact .id ih (par_refl _) (par_refl _)
  | congIdLeft _ ih => exact .id (par_refl _) ih (par_refl _)
  | congIdRight _ ih => exact .id (par_refl _) (par_refl _) ih
  | congLam _ ih => exact .lam ih
  | congAppFun _ ih => exact .app ih (par_refl _)
  | congAppArg _ ih => exact .app (par_refl _) ih
  | congPairFst _ ih => exact .pair ih (par_refl _)
  | congPairSnd _ ih => exact .pair (par_refl _) ih
  | congFst _ ih => exact .fst ih
  | congSnd _ ih => exact .snd ih
  | congRefl _ ih => exact .refl ih

/-- Actual authored execution is included, without reversing or completing
any authored runtime step. -/
theorem authored_step_to_par {left right : Tower.Tm n}
    (step : Step FormationSensitiveHOLProofListIntegration.rules.headEq left right
      FormationSensitiveHOLProofListIntegration.rules.computation) : Par left right :=
  completed_step_to_par (conservative.step_inclusion step)

/-- Auxiliary paths retain their meaning in the original conversion theory. -/
theorem ParStar.sound {left right : Tower.Tm n} (steps : ParStar left right) :
    AuthoredConv left right :=
  ParallelConversionViews.path_sound (R := FormationSensitiveHOLProofListIntegration.rules) Par.sound steps

private theorem par_pi_decomp : ParallelConversionViews.BinaryViews Par Tm.pi := by
  intro n first second target parallel
  cases parallel with
  | pi firstStep secondStep => exact ⟨_, _, rfl, firstStep, secondStep⟩

/-- Pi is structurally preserved along arbitrary finite completed paths;
both component paths are retained. -/
theorem parStar_pi_decomp {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    {target : Tower.Tm n} (steps : ParStar (.pi A B) target) :
    ∃ A' B', target = .pi A' B' ∧ ParStar A A' ∧ ParStar B B' :=
  Mettapedia.Logic.Relation.BinaryDecomposition.path (par_pi_decomp (n := n)) steps

private theorem par_sigma_decomp : ParallelConversionViews.BinaryViews Par Tm.sigma := by
  intro n first second target parallel
  cases parallel with
  | sigma firstStep secondStep => exact ⟨_, _, rfl, firstStep, secondStep⟩

/-- Sigma paths expose their exact component developments as well. -/
theorem parStar_sigma_decomp {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    {target : Tower.Tm n} (steps : ParStar (.sigma A B) target) :
    ∃ A' B', target = .sigma A' B' ∧ ParStar A A' ∧ ParStar B B' :=
  Mettapedia.Logic.Relation.BinaryDecomposition.path (par_sigma_decomp (n := n)) steps

private theorem par_head_shape : ParallelConversionViews.HeadViews Par := by
  intro n value target parallel
  cases parallel with
  | head _ => exact ⟨_, rfl⟩
  | headRel _ => exact ⟨_, rfl⟩

/-- Head equality may change the head value but never its outer constructor. -/
theorem parStar_head_shape {head : Tower.Head} {target : Tower.Tm n}
    (steps : ParStar (.head head) target) : ∃ head', target = .head head' :=
  ParallelConversionViews.head_path par_head_shape steps

/-- A proved diamond lifts to confluence of finite auxiliary paths. -/
theorem parStar_confluence (diamond : Diamond) {source left right : Tower.Tm n}
    (first : ParStar source left) (second : ParStar source right) :
    ∃ common, ParStar left common ∧ ParStar right common :=
  Mettapedia.Logic.Relation.confluent_of_diamond (fun a b => diamond a b) _ _ _ first second

/-- Every authored conversion has a common completed reduct once the actual
parallel diamond has been established. This is not an authored-run theorem. -/
theorem authored_conv_join (diamond : Diamond) {left right : Tower.Tm n}
    (conversion : AuthoredConv left right) :
    ∃ common, ParStar left common ∧ ParStar right common :=
  ParallelConversionViews.joins_of_diamond (R := FormationSensitiveHOLProofListIntegration.rules) (parallel := Par)
    authored_step_to_par diamond conversion

/-- Qualification of actual native Pi conversion from the independently
proved diamond of its conservative completed parallel presentation. -/
theorem piConversionBoundaryOfDiamond (diamond : Diamond) :
    PiConversionBoundary FormationSensitiveHOLProofListIntegration.rules :=
  ParallelConversionViews.pi_boundary par_pi_decomp par_head_shape Par.sound
    (fun conversion => authored_conv_join diamond conversion)

/-- The same checked argument qualifies native Sigma conversion. -/
theorem sigmaConversionBoundaryOfDiamond (diamond : Diamond) :
    SigmaConversionBoundary FormationSensitiveHOLProofListIntegration.rules :=
  ParallelConversionViews.sigma_boundary par_sigma_decomp par_head_shape Par.sound
    (fun conversion => authored_conv_join diamond conversion)

namespace CoherenceExamples

/-- Every one of the five actual root families remains available inside
both components of a dependent function constructor. This is a raw path law,
not formation of that constructor or typing preservation of its arguments. -/
theorem native_step_under_pi {left right : Tower.Tm n}
    (evidence : IntrinsicRelator.CombinedIotaEvidence n left right) :
    ParStar (.pi left (rename wk left)) (.pi right (rename wk right)) ∧
      AuthoredConv left right := by
  have native : Par left right := root_to_par (Root.of_iota evidence)
  exact ⟨.tail .refl (.pi native (par_rename wk native)), native.sound⟩

theorem native_step_under_sigma {left right : Tower.Tm n}
    (evidence : IntrinsicRelator.CombinedIotaEvidence n left right) :
    ParStar (.sigma left (rename wk left)) (.sigma right (rename wk right)) := by
  have native : Par left right := root_to_par (Root.of_iota evidence)
  exact .tail .refl (.sigma native (par_rename wk native))

/-- Even without assuming the diamond, a Pi and a head have no common
completed reduct. The diamond connects this obstruction to authored Conv. -/
theorem pi_head_no_common {A : Tower.Tm n} {B : Tower.Tm (n + 1)} {head : Tower.Head} :
    ¬ ∃ common, ParStar (.pi A B) common ∧ ParStar (.head head) common :=
  ParallelConversionViews.no_common_head (assemble := Tm.pi)
    (fun _ _ _ same => by cases same) par_pi_decomp par_head_shape

theorem sigma_head_no_common {A : Tower.Tm n} {B : Tower.Tm (n + 1)} {head : Tower.Head} :
    ¬ ∃ common, ParStar (.sigma A B) common ∧ ParStar (.head head) common :=
  ParallelConversionViews.no_common_head (assemble := Tm.sigma)
    (fun _ _ _ same => by cases same) par_sigma_decomp par_head_shape

end CoherenceExamples

#print axioms root_to_par
#print axioms completed_step_to_par
#print axioms authored_step_to_par
#print axioms ParStar.sound
#print axioms parStar_pi_decomp
#print axioms parStar_sigma_decomp
#print axioms parStar_head_shape
#print axioms parStar_confluence
#print axioms authored_conv_join
#print axioms piConversionBoundaryOfDiamond
#print axioms sigmaConversionBoundaryOfDiamond
#print axioms CoherenceExamples.native_step_under_pi
#print axioms CoherenceExamples.native_step_under_sigma
#print axioms CoherenceExamples.pi_head_no_common
#print axioms CoherenceExamples.sigma_head_no_common

end HOLNativeMixedConversionParallel
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
