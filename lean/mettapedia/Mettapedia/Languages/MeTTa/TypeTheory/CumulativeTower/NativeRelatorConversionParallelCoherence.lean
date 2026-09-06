import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeRelatorConversionParallelSubstitution

/-!
# Authored conversion qualification from completed parallel coherence

Every authored contextual step is a completed parallel step, and every finite
completed parallel path is authored conversion evidence. A diamond proof for
the auxiliary relation therefore joins authored conversions and yields Pi and
Sigma component injectivity and head separation for the actual native rules.

The diamond is an explicit hypothesis here, to be discharged by a separate
development theorem. No Church--Rosser property of raw authored execution is
assumed or concluded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeRelatorConversionParallel

open Presentation NativeIndexedFamilies NativeRelatorConversionCompletion

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

/-- Every contextual step of the completed presentation is covered by the
parallel relation, including its actual coherence guards. -/
theorem completed_step_to_par {left right : Tower.Tm n}
    (step : Step NativeRelatorConversionCompletion.rules.headEq left right
      NativeRelatorConversionCompletion.rules.computation) : Par left right := by
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
    (step : Step IntrinsicRelator.rules.headEq left right
      IntrinsicRelator.rules.computation) : Par left right :=
  completed_step_to_par (conservative.step_inclusion step)

/-- Auxiliary paths retain their meaning in the original conversion theory. -/
theorem ParStar.sound {left right : Tower.Tm n} (steps : ParStar left right) :
    AuthoredConv left right := by
  induction steps with
  | refl => exact .refl _
  | tail previous finalStep ih => exact .trans _ _ _ ih finalStep.sound

private theorem par_pi_decomp {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    {target : Tower.Tm n} (parallel : Par (.pi A B) target) :
    ∃ A' B', target = .pi A' B' ∧ Par A A' ∧ Par B B' := by
  cases parallel with
  | pi first second => exact ⟨_, _, rfl, first, second⟩

/-- Pi is structurally preserved along arbitrary finite completed paths;
both component paths are retained. -/
theorem parStar_pi_decomp {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    {target : Tower.Tm n} (steps : ParStar (.pi A B) target) :
    ∃ A' B', target = .pi A' B' ∧ ParStar A A' ∧ ParStar B B' := by
  induction steps with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail previous finalStep ih =>
      obtain ⟨A', B', rfl, first, second⟩ := ih
      obtain ⟨A'', B'', rfl, lastFirst, lastSecond⟩ := par_pi_decomp finalStep
      exact ⟨_, _, rfl, first.tail lastFirst, second.tail lastSecond⟩

private theorem par_sigma_decomp {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    {target : Tower.Tm n} (parallel : Par (.sigma A B) target) :
    ∃ A' B', target = .sigma A' B' ∧ Par A A' ∧ Par B B' := by
  cases parallel with
  | sigma first second => exact ⟨_, _, rfl, first, second⟩

/-- Sigma paths expose their exact component developments as well. -/
theorem parStar_sigma_decomp {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    {target : Tower.Tm n} (steps : ParStar (.sigma A B) target) :
    ∃ A' B', target = .sigma A' B' ∧ ParStar A A' ∧ ParStar B B' := by
  induction steps with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail previous finalStep ih =>
      obtain ⟨A', B', rfl, first, second⟩ := ih
      obtain ⟨A'', B'', rfl, lastFirst, lastSecond⟩ := par_sigma_decomp finalStep
      exact ⟨_, _, rfl, first.tail lastFirst, second.tail lastSecond⟩

private theorem par_head_shape {head : Tower.Head} {target : Tower.Tm n}
    (parallel : Par (.head head) target) : ∃ head', target = .head head' := by
  cases parallel with
  | head _ => exact ⟨_, rfl⟩
  | headRel _ => exact ⟨_, rfl⟩

/-- Head equality may change the head value but never its outer constructor. -/
theorem parStar_head_shape {head : Tower.Head} {target : Tower.Tm n}
    (steps : ParStar (.head head) target) : ∃ head', target = .head head' := by
  induction steps with
  | refl => exact ⟨_, rfl⟩
  | tail previous finalStep ih =>
      obtain ⟨head', rfl⟩ := ih
      exact par_head_shape finalStep

/-- A proved diamond lifts to confluence of finite auxiliary paths. -/
theorem parStar_confluence (diamond : Diamond) {source left right : Tower.Tm n}
    (first : ParStar source left) (second : ParStar source right) :
    ∃ common, ParStar left common ∧ ParStar right common := by
  have localJoin : ∀ a b c : Tower.Tm n,
      Par a b → Par a c → ∃ d, Relation.ReflGen Par b d ∧ ParStar c d := by
    intro a b c leftStep rightStep
    obtain ⟨common, firstJoin, secondJoin⟩ := diamond leftStep rightStep
    exact ⟨common, .single firstJoin, .tail .refl secondJoin⟩
  exact Relation.church_rosser localJoin first second

/-- Every authored conversion has a common completed reduct once the actual
parallel diamond has been established. This is not an authored-run theorem. -/
theorem authored_conv_join (diamond : Diamond) {left right : Tower.Tm n}
    (conversion : AuthoredConv left right) :
    ∃ common, ParStar left common ∧ ParStar right common := by
  induction conversion with
  | rel _ _ step => exact ⟨_, .tail .refl (authored_step_to_par step), .refl⟩
  | refl _ => exact ⟨_, .refl, .refl⟩
  | symm _ _ _ ih =>
      obtain ⟨common, first, second⟩ := ih
      exact ⟨common, second, first⟩
  | trans _ _ _ _ _ firstHypothesis secondHypothesis =>
      obtain ⟨firstCommon, leftSteps, middleFirstSteps⟩ := firstHypothesis
      obtain ⟨secondCommon, middleSecondSteps, rightSteps⟩ := secondHypothesis
      obtain ⟨common, firstJoin, secondJoin⟩ :=
        parStar_confluence diamond middleFirstSteps middleSecondSteps
      exact ⟨common, leftSteps.trans firstJoin, rightSteps.trans secondJoin⟩

/-- Qualification of actual native Pi conversion from the independently
proved diamond of its conservative completed parallel presentation. -/
def piConversionBoundaryOfDiamond (diamond : Diamond) :
    PiConversionBoundary IntrinsicRelator.rules where
  components := by
    intro n A A' B B' conversion
    obtain ⟨common, firstSteps, secondSteps⟩ := authored_conv_join diamond conversion
    obtain ⟨firstA, firstB, firstShape, firstAPath, firstBPath⟩ := parStar_pi_decomp firstSteps
    obtain ⟨secondA, secondB, secondShape, secondAPath, secondBPath⟩ := parStar_pi_decomp secondSteps
    have equality := firstShape.symm.trans secondShape
    injection equality with domains codomains
    subst secondA
    subst secondB
    exact ⟨.trans _ _ _ firstAPath.sound (.symm _ _ secondAPath.sound),
      .trans _ _ _ firstBPath.sound (.symm _ _ secondBPath.sound)⟩
  headDisjoint := by
    intro n A B head conversion
    obtain ⟨common, piSteps, headSteps⟩ := authored_conv_join diamond conversion
    obtain ⟨A', B', piShape, _, _⟩ := parStar_pi_decomp piSteps
    obtain ⟨head', headShape⟩ := parStar_head_shape headSteps
    rw [piShape] at headShape
    cases headShape

/-- The same checked argument qualifies native Sigma conversion. -/
def sigmaConversionBoundaryOfDiamond (diamond : Diamond) :
    SigmaConversionBoundary IntrinsicRelator.rules where
  components := by
    intro n A A' B B' conversion
    obtain ⟨common, firstSteps, secondSteps⟩ := authored_conv_join diamond conversion
    obtain ⟨firstA, firstB, firstShape, firstAPath, firstBPath⟩ := parStar_sigma_decomp firstSteps
    obtain ⟨secondA, secondB, secondShape, secondAPath, secondBPath⟩ := parStar_sigma_decomp secondSteps
    have equality := firstShape.symm.trans secondShape
    injection equality with domains codomains
    subst secondA
    subst secondB
    exact ⟨.trans _ _ _ firstAPath.sound (.symm _ _ secondAPath.sound),
      .trans _ _ _ firstBPath.sound (.symm _ _ secondBPath.sound)⟩
  headDisjoint := by
    intro n A B head conversion
    obtain ⟨common, sigmaSteps, headSteps⟩ := authored_conv_join diamond conversion
    obtain ⟨A', B', sigmaShape, _, _⟩ := parStar_sigma_decomp sigmaSteps
    obtain ⟨head', headShape⟩ := parStar_head_shape headSteps
    rw [sigmaShape] at headShape
    cases headShape

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
    ¬ ∃ common, ParStar (.pi A B) common ∧ ParStar (.head head) common := by
  rintro ⟨common, piSteps, headSteps⟩
  obtain ⟨A', B', piShape, _, _⟩ := parStar_pi_decomp piSteps
  obtain ⟨head', headShape⟩ := parStar_head_shape headSteps
  rw [piShape] at headShape
  cases headShape

theorem sigma_head_no_common {A : Tower.Tm n} {B : Tower.Tm (n + 1)} {head : Tower.Head} :
    ¬ ∃ common, ParStar (.sigma A B) common ∧ ParStar (.head head) common := by
  rintro ⟨common, sigmaSteps, headSteps⟩
  obtain ⟨A', B', sigmaShape, _, _⟩ := parStar_sigma_decomp sigmaSteps
  obtain ⟨head', headShape⟩ := parStar_head_shape headSteps
  rw [sigmaShape] at headShape
  cases headShape

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

end NativeRelatorConversionParallel
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
