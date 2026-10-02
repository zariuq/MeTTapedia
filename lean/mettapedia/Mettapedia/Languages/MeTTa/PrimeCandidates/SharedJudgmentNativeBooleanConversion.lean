import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanDevelopmentRelator
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanParallelCoherence

/-!
# Complete development for the Boolean-extended native presentation

Cofinal developments are constructed from developments of the immediate
subterms. A root classification separates beta and all seven native redexes
from structural applications without asserting that the classification is a
conversion decision procedure. The inherited List, identity, and relator
computation rules are retained alongside both Boolean computation rules.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace SharedJudgmentNativeBooleanParallel

open Presentation NativeIndexedFamilies SharedJudgmentNativeBooleanCompletion

variable {n : Nat}

private theorem lam_to_fixed {body body' : Tower.Tm (n + 1)}
    (parallel : Par (.lam body) (.lam body')) : Par body body' := by
  cases parallel with | lam inner => exact inner

private theorem pair_to_fixed {first second first' second' : Tower.Tm n}
    (parallel : Par (.pair first second) (.pair first' second')) :
    Par first first' ∧ Par second second' := by
  cases parallel with | pair left right => exact ⟨left, right⟩

theorem cofinal_beta {body : Tower.Tm (n + 1)} {argument : Tower.Tm n}
    (function : Cofinal (.lam body)) (argumentDevelop : Cofinal argument) :
    Cofinal (.app (.lam body) argument) := by
  obtain ⟨df, function⟩ := function
  obtain ⟨da, argumentDevelop⟩ := argumentDevelop
  obtain ⟨db, rfl, _⟩ := lam_inversion (function _ (par_refl _))
  refine ⟨inst0 da db, ?_⟩
  intro target parallel
  cases parallel with
  | app functionStep argumentStep =>
      obtain ⟨body', rfl, _⟩ := lam_inversion functionStep
      exact .betaPi (lam_to_fixed (function _ functionStep)) (argumentDevelop _ argumentStep)
  | betaPi bodyStep argumentStep =>
      exact par_inst0 (argumentDevelop _ argumentStep) (lam_to_fixed (function _ (.lam bodyStep)))

theorem cofinal_pair_fst {first second : Tower.Tm n}
    (pairDevelop : Cofinal (.pair first second)) : Cofinal (.fst (.pair first second)) := by
  obtain ⟨common, pairDevelop⟩ := pairDevelop
  obtain ⟨df, ds, rfl, _, _⟩ := pair_inversion (pairDevelop _ (par_refl _))
  refine ⟨df, ?_⟩
  intro target parallel
  cases parallel with
  | fst pairStep =>
      obtain ⟨first', second', rfl, _, _⟩ := pair_inversion pairStep
      obtain ⟨left, right⟩ := pair_to_fixed (pairDevelop _ pairStep)
      exact .betaSigmaFst left right
  | betaSigmaFst left right =>
      exact (pair_to_fixed (pairDevelop _ (.pair left right))).1

theorem cofinal_pair_snd {first second : Tower.Tm n}
    (pairDevelop : Cofinal (.pair first second)) : Cofinal (.snd (.pair first second)) := by
  obtain ⟨common, pairDevelop⟩ := pairDevelop
  obtain ⟨df, ds, rfl, _, _⟩ := pair_inversion (pairDevelop _ (par_refl _))
  refine ⟨ds, ?_⟩
  intro target parallel
  cases parallel with
  | snd pairStep =>
      obtain ⟨first', second', rfl, _, _⟩ := pair_inversion pairStep
      obtain ⟨left, right⟩ := pair_to_fixed (pairDevelop _ pairStep)
      exact .betaSigmaSnd left right
  | betaSigmaSnd left right =>
      exact (pair_to_fixed (pairDevelop _ (.pair left right))).2

theorem cofinal_boolFalse {motive onFalse onTrue : Tower.Tm n}
    (function : Cofinal (boolPrefix motive onFalse onTrue)) :
    Cofinal (SharedJudgmentNativeBooleanRegion.eliminate motive onFalse onTrue
      SharedJudgmentNativeBooleanRegion.falseTm) := by
  obtain ⟨df, function⟩ := function
  obtain ⟨dm, df, dt, rfl, _, _, _⟩ := boolPrefix_inversion (function _ (par_refl _))
  refine ⟨df, ?_⟩
  intro target parallel
  generalize sourceEq : SharedJudgmentNativeBooleanRegion.eliminate motive onFalse onTrue
    SharedJudgmentNativeBooleanRegion.falseTm = source at parallel
  cases parallel with
  | app functionStep argumentStep =>
      have fields := Tm.app.inj sourceEq
      have fixedFunction := fields.1 ▸ functionStep
      have fixedArgument := fields.2 ▸ argumentStep
      obtain ⟨motive', onFalse', onTrue', rfl, _, _, _⟩ := boolPrefix_inversion fixedFunction
      have argumentShape := const_inversion fixedArgument
      subst argumentShape
      obtain ⟨hm, hf, ht⟩ := boolPrefix_to_fixed (function _ fixedFunction)
      exact .boolFalse hm hf ht
  | boolFalse hm hf ht =>
      simp only [SharedJudgmentNativeBooleanRegion.eliminate, Tm.app.injEq,
        and_true, true_and] at sourceEq
      rcases sourceEq with ⟨⟨rfl, rfl⟩, rfl⟩
      exact (boolPrefix_to_fixed (function _ (par_boolPrefix hm hf ht))).2.1
  | boolTrue _ _ _ =>
      exact False.elim (SharedJudgmentNativeBooleanRegion.false_true_distinct (Tm.app.inj sourceEq).2)
  | const _ => cases sourceEq
  | _ =>
      have names := congrArg spineHead sourceEq
      simp [SharedJudgmentNativeBooleanRegion.eliminate, SharedJudgmentNativeBooleanRegion.eliminateName,
        Intrinsic.eliminateApp, Intrinsic.identityEliminateApp, IntrinsicRelator.eliminateApp,
        Intrinsic.eliminateName, Intrinsic.identityEliminateName, IntrinsicRelator.eliminateName,
        spineHead] at names

theorem cofinal_boolTrue {motive onFalse onTrue : Tower.Tm n}
    (function : Cofinal (boolPrefix motive onFalse onTrue)) :
    Cofinal (SharedJudgmentNativeBooleanRegion.eliminate motive onFalse onTrue
      SharedJudgmentNativeBooleanRegion.trueTm) := by
  obtain ⟨df, function⟩ := function
  obtain ⟨dm, df, dt, rfl, _, _, _⟩ := boolPrefix_inversion (function _ (par_refl _))
  refine ⟨dt, ?_⟩
  intro target parallel
  generalize sourceEq : SharedJudgmentNativeBooleanRegion.eliminate motive onFalse onTrue
    SharedJudgmentNativeBooleanRegion.trueTm = source at parallel
  cases parallel with
  | app functionStep argumentStep =>
      have fields := Tm.app.inj sourceEq
      have fixedFunction := fields.1 ▸ functionStep
      have fixedArgument := fields.2 ▸ argumentStep
      obtain ⟨motive', onFalse', onTrue', rfl, _, _, _⟩ := boolPrefix_inversion fixedFunction
      have argumentShape := const_inversion fixedArgument
      subst argumentShape
      obtain ⟨hm, hf, ht⟩ := boolPrefix_to_fixed (function _ fixedFunction)
      exact .boolTrue hm hf ht
  | boolFalse _ _ _ =>
      exact False.elim (SharedJudgmentNativeBooleanRegion.false_true_distinct (Tm.app.inj sourceEq).2.symm)
  | boolTrue hm hf ht =>
      simp only [SharedJudgmentNativeBooleanRegion.eliminate, Tm.app.injEq,
        and_true, true_and] at sourceEq
      rcases sourceEq with ⟨⟨rfl, rfl⟩, rfl⟩
      exact (boolPrefix_to_fixed (function _ (par_boolPrefix hm hf ht))).2.2
  | const _ => cases sourceEq
  | _ =>
      have names := congrArg spineHead sourceEq
      simp [SharedJudgmentNativeBooleanRegion.eliminate, SharedJudgmentNativeBooleanRegion.eliminateName,
        Intrinsic.eliminateApp, Intrinsic.identityEliminateApp, IntrinsicRelator.eliminateApp,
        Intrinsic.eliminateName, Intrinsic.identityEliminateName, IntrinsicRelator.eliminateName,
        spineHead] at names

inductive AppRoot : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop where
  | beta {n : Nat} (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
      AppRoot (.lam body) argument
  | listNil {n : Nat} {a p z s innerA : Tower.Tm n} :
      AuthoredConv innerA a →
      AppRoot (listPrefix a p z s) (Intrinsic.nilApp innerA)
  | listCons {n : Nat} {a p z s innerA h t : Tower.Tm n} :
      AuthoredConv innerA a →
      AppRoot (listPrefix a p z s) (Intrinsic.consApp innerA h t)
  | identity {n : Nat} {a x p d y witness : Tower.Tm n} :
      AuthoredConv y x → AuthoredConv witness x →
      AppRoot (identityPrefix a x p d y) (.refl witness)
  | relNil {n : Nat} {a b r p z s xs ys innerA innerB innerR : Tower.Tm n} :
      AuthoredConv innerA a → AuthoredConv innerB b → AuthoredConv innerR r → AuthoredConv xs (Intrinsic.nilApp a) → AuthoredConv ys (Intrinsic.nilApp b) →
      AppRoot (relPrefix a b r p z s xs ys) (IntrinsicRelator.nilRelApp innerA innerB innerR)
  | relCons {n : Nat} {a b r p z s xs ys innerA innerB innerR h k t u he te : Tower.Tm n} :
      AuthoredConv innerA a → AuthoredConv innerB b → AuthoredConv innerR r → AuthoredConv xs (Intrinsic.consApp a h t) → AuthoredConv ys (Intrinsic.consApp b k u) →
      AppRoot (relPrefix a b r p z s xs ys) (IntrinsicRelator.consRelApp innerA innerB innerR h k t u he te)
  | boolFalse {n : Nat} (motive onFalse onTrue : Tower.Tm n) :
      AppRoot (boolPrefix motive onFalse onTrue) SharedJudgmentNativeBooleanRegion.falseTm
  | boolTrue {n : Nat} (motive onFalse onTrue : Tower.Tm n) :
      AppRoot (boolPrefix motive onFalse onTrue) SharedJudgmentNativeBooleanRegion.trueTm

theorem cofinal_structural_app {function argument : Tower.Tm n}
    (noRoot : ¬ AppRoot function argument)
    (functionDevelop : Cofinal function) (argumentDevelop : Cofinal argument) :
    Cofinal (.app function argument) := by
  obtain ⟨df, functionDevelop⟩ := functionDevelop
  obtain ⟨da, argumentDevelop⟩ := argumentDevelop
  refine ⟨.app df da, ?_⟩
  intro target parallel
  cases parallel with
  | app functionStep argumentStep => exact .app (functionDevelop _ functionStep) (argumentDevelop _ argumentStep)
  | betaPi _ _ => exact False.elim (noRoot (.beta _ _))
  | listNil ca _ _ _ _ =>
      exact False.elim (noRoot (.listNil ca))
  | listCons ca _ _ _ _ _ _ =>
      exact False.elim (noRoot (.listCons ca))
  | identity cy cw _ _ _ _ _ _ =>
      exact False.elim (noRoot (.identity cy cw))
  | relNil ca cb cr cx cy _ _ _ _ _ _ _ _ =>
      exact False.elim (noRoot (.relNil ca cb cr cx cy))
  | relCons ca cb cr cx cy _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact False.elim (noRoot (.relCons ca cb cr cx cy))
  | boolFalse _ _ _ => exact False.elim (noRoot (.boolFalse _ _ _))
  | boolTrue _ _ _ => exact False.elim (noRoot (.boolTrue _ _ _))

theorem cofinal_app {function argument : Tower.Tm n}
    (functionDevelop : Cofinal function) (argumentDevelop : Cofinal argument) :
    Cofinal (.app function argument) := by
  classical
  by_cases root : AppRoot function argument
  · cases root with
    | beta => exact cofinal_beta functionDevelop argumentDevelop
    | listNil ca =>
        exact cofinal_listNil ca functionDevelop argumentDevelop
    | listCons ca =>
        exact cofinal_listCons ca functionDevelop argumentDevelop
    | identity cy cw =>
        exact cofinal_identity cy cw functionDevelop argumentDevelop
    | relNil ca cb cr cx cy =>
        exact cofinal_relNil ca cb cr cx cy functionDevelop argumentDevelop
    | relCons ca cb cr cx cy =>
        exact cofinal_relCons ca cb cr cx cy functionDevelop argumentDevelop
    | boolFalse _ _ _ => exact cofinal_boolFalse functionDevelop
    | boolTrue _ _ _ => exact cofinal_boolTrue functionDevelop
  · exact cofinal_structural_app root functionDevelop argumentDevelop

/-- Complete development for every open raw term of the actual native
syntax. The proof preserves the original metadata-conversion guards. -/
theorem cofinal (source : Tower.Tm n) : Cofinal source := by
  induction source with
  | var index =>
      refine ⟨.var index, ?_⟩
      intro target parallel
      cases parallel
      exact .var index
  | const name =>
      refine ⟨.const name, ?_⟩
      intro target parallel
      cases parallel
      exact .const name
  | head value =>
      refine ⟨.head value, ?_⟩
      intro target parallel
      cases parallel with
      | head _ => exact .head value
      | headRel equality => exact .headRel (LevelTower.headEq_symmetric.symm _ _ equality)
  | pi domain codomain first second =>
      obtain ⟨dd, first⟩ := first
      obtain ⟨dc, second⟩ := second
      refine ⟨.pi dd dc, ?_⟩
      intro target parallel
      cases parallel with
      | pi domainStep codomainStep => exact .pi (first _ domainStep) (second _ codomainStep)
  | sigma domain codomain first second =>
      obtain ⟨dd, first⟩ := first
      obtain ⟨dc, second⟩ := second
      refine ⟨.sigma dd dc, ?_⟩
      intro target parallel
      cases parallel with
      | sigma domainStep codomainStep => exact .sigma (first _ domainStep) (second _ codomainStep)
  | id type left right first second third =>
      obtain ⟨dt, first⟩ := first
      obtain ⟨dl, second⟩ := second
      obtain ⟨dr, third⟩ := third
      refine ⟨.id dt dl dr, ?_⟩
      intro target parallel
      cases parallel with
      | id typeStep leftStep rightStep => exact .id (first _ typeStep) (second _ leftStep) (third _ rightStep)
  | lam body inner =>
      obtain ⟨db, inner⟩ := inner
      refine ⟨.lam db, ?_⟩
      intro target parallel
      cases parallel with
      | lam bodyStep => exact .lam (inner _ bodyStep)
  | app function argument first second => exact cofinal_app first second
  | pair first second firstDevelop secondDevelop =>
      obtain ⟨df, firstDevelop⟩ := firstDevelop
      obtain ⟨ds, secondDevelop⟩ := secondDevelop
      refine ⟨.pair df ds, ?_⟩
      intro target parallel
      cases parallel with
      | pair firstStep secondStep => exact .pair (firstDevelop _ firstStep) (secondDevelop _ secondStep)
  | fst pair inner =>
      cases pair with
      | pair first second => exact cofinal_pair_fst inner
      | _ =>
          obtain ⟨dp, inner⟩ := inner
          refine ⟨.fst dp, ?_⟩
          intro target parallel
          cases parallel with
          | fst pairStep => exact .fst (inner _ pairStep)
  | snd pair inner =>
      cases pair with
      | pair first second => exact cofinal_pair_snd inner
      | _ =>
          obtain ⟨dp, inner⟩ := inner
          refine ⟨.snd dp, ?_⟩
          intro target parallel
          cases parallel with
          | snd pairStep => exact .snd (inner _ pairStep)
  | refl term inner =>
      obtain ⟨dt, inner⟩ := inner
      refine ⟨.refl dt, ?_⟩
      intro target parallel
      cases parallel with
      | refl termStep => exact .refl (inner _ termStep)

/-- The diamond is a theorem of the specific completed native relation,
not an assumption about arbitrary nonlinear algebraic rules. -/
theorem diamond : Diamond := by
  intro n source left right first second
  obtain ⟨common, reaches⟩ := cofinal source
  exact ⟨common, reaches _ first, reaches _ second⟩

theorem conversion_join {left right : Tower.Tm n} (conversion : AuthoredConv left right) :
    ∃ common, ParStar left common ∧ ParStar right common :=
  authored_conv_join diamond conversion

theorem nativePiConversionBoundary : PiConversionBoundary SharedJudgmentNativeBooleanRegion.rules :=
  piConversionBoundaryOfDiamond diamond

theorem nativeSigmaConversionBoundary : SigmaConversionBoundary SharedJudgmentNativeBooleanRegion.rules :=
  sigmaConversionBoundaryOfDiamond diamond

/-- Constants cannot acquire a reduct through a completed parallel path.
The actual signature has no defining bodies; its computation rules apply
only to fully applied eliminators. -/
theorem parStar_const_fixed {name : DeclName} {target : Tower.Tm n}
    (steps : ParStar (.const name) target) : target = .const name := by
  induction steps with
  | refl => rfl
  | tail previous finalStep ih =>
      rw [ih] at finalStep
      exact const_inversion finalStep

/-- Distinct constant names remain distinct under full authored conversion,
including conversion paths through arbitrary intermediate terms. -/
theorem constants_conversion_iff {left right : DeclName} :
    AuthoredConv (.const left : Tower.Tm n) (.const right) ↔ left = right := by
  constructor
  · intro conversion
    obtain ⟨common, leftSteps, rightSteps⟩ := conversion_join conversion
    exact Tm.const.inj ((parStar_const_fixed leftSteps).symm.trans
      (parStar_const_fixed rightSteps))
  · rintro rfl
    exact .refl _

/-- Boolean constructor separation is an unbounded conversion theorem for
the actual combined rules, not a bounded normalization experiment. -/
theorem false_not_convertible_true :
    ¬ AuthoredConv (SharedJudgmentNativeBooleanRegion.falseTm : Tower.Tm n)
      SharedJudgmentNativeBooleanRegion.trueTm := by
  intro conversion
  have names := constants_conversion_iff.mp conversion
  exact (by decide : SharedJudgmentNativeBooleanRegion.falseName ≠
    SharedJudgmentNativeBooleanRegion.trueName) names

/-- Dependent functions and dependent pairs remain different constructors
under conversion even though their components may compute. -/
theorem pi_not_convertible_sigma {A C : Tower.Tm n} {B D : Tower.Tm (n + 1)} :
    ¬ AuthoredConv (.pi A B) (.sigma C D) := by
  intro conversion
  obtain ⟨common, firstSteps, secondSteps⟩ := conversion_join conversion
  obtain ⟨A', B', firstShape, _, _⟩ := parStar_pi_decomp firstSteps
  obtain ⟨C', D', secondShape, _, _⟩ := parStar_sigma_decomp secondSteps
  rw [firstShape] at secondShape
  cases secondShape

/-- J on an open path variable cannot use the reflexivity computation rule.
Its other arguments may develop freely without losing that neutral path. -/
theorem par_neutral_identity_shape {A x motive method y target : Tower.Tm n}
    {path : Fin n}
    (parallel : Par (Intrinsic.identityEliminateApp A x motive method y (.var path)) target) :
    ∃ A' x' motive' method' y',
      target = Intrinsic.identityEliminateApp A' x' motive' method' y' (.var path) := by
  cases parallel with
  | app functionStep argumentStep =>
      cases argumentStep
      obtain ⟨A', x', motive', method', y', shape, _, _, _, _, _⟩ :=
        identityPrefix_inversion functionStep
      exact ⟨A', x', motive', method', y',
        congrArg (fun f : Tower.Tm n => Tm.app f (.var path)) shape⟩

theorem parStar_neutral_identity_shape {A x motive method y target : Tower.Tm n}
    {path : Fin n}
    (steps : ParStar (Intrinsic.identityEliminateApp A x motive method y (.var path)) target) :
    ∃ A' x' motive' method' y',
      target = Intrinsic.identityEliminateApp A' x' motive' method' y' (.var path) := by
  induction steps with
  | refl => exact ⟨_, _, _, _, _, rfl⟩
  | tail previous finalStep ih =>
      obtain ⟨A', x', motive', method', y', rfl⟩ := ih
      exact par_neutral_identity_shape finalStep

/-- In particular, J on a neutral path does not become its constant method
by an arbitrary conversion detour. This distinguishes propositional path
uniqueness from adding a definitional computation rule for neutral paths. -/
theorem neutral_identity_not_convertible_constant {A x motive method y : Tower.Tm n}
    {path : Fin n} {name : DeclName} :
    ¬ AuthoredConv (Intrinsic.identityEliminateApp A x motive method y (.var path))
      (.const name) := by
  intro conversion
  obtain ⟨common, identitySteps, constantSteps⟩ := conversion_join conversion
  obtain ⟨A', x', motive', method', y', identityShape⟩ :=
    parStar_neutral_identity_shape identitySteps
  have constantShape := parStar_const_fixed constantSteps
  rw [identityShape] at constantShape
  cases constantShape

/-- Positive control: Boolean computation is retained in both components
of a Pi constructor by the very relation used in the boundary proof. -/
theorem boolean_step_under_pi (motive onFalse onTrue : Tower.Tm n) :
    AuthoredConv
      (.pi (SharedJudgmentNativeBooleanRegion.eliminate motive onFalse onTrue
          SharedJudgmentNativeBooleanRegion.falseTm)
        (rename wk (SharedJudgmentNativeBooleanRegion.eliminate motive onFalse onTrue
          SharedJudgmentNativeBooleanRegion.falseTm)))
      (.pi onFalse (rename wk onFalse)) := by
  have step : Par (SharedJudgmentNativeBooleanRegion.eliminate motive onFalse onTrue
      SharedJudgmentNativeBooleanRegion.falseTm) onFalse :=
    root_to_par (.boolFalse _ _ _)
  exact (Par.pi step (par_rename wk step)).sound

theorem boolean_step_under_sigma (motive onFalse onTrue : Tower.Tm n) :
    AuthoredConv
      (.sigma (SharedJudgmentNativeBooleanRegion.eliminate motive onFalse onTrue
          SharedJudgmentNativeBooleanRegion.trueTm)
        (rename wk (SharedJudgmentNativeBooleanRegion.eliminate motive onFalse onTrue
          SharedJudgmentNativeBooleanRegion.trueTm)))
      (.sigma onTrue (rename wk onTrue)) := by
  have step : Par (SharedJudgmentNativeBooleanRegion.eliminate motive onFalse onTrue
      SharedJudgmentNativeBooleanRegion.trueTm) onTrue :=
    root_to_par (.boolTrue _ _ _)
  exact (Par.sigma step (par_rename wk step)).sound

#print axioms cofinal_beta
#print axioms cofinal_pair_fst
#print axioms cofinal_pair_snd
#print axioms cofinal_boolFalse
#print axioms cofinal_boolTrue
#print axioms cofinal_structural_app
#print axioms cofinal_app
#print axioms cofinal
#print axioms diamond
#print axioms conversion_join
#print axioms nativePiConversionBoundary
#print axioms nativeSigmaConversionBoundary
#print axioms constants_conversion_iff
#print axioms false_not_convertible_true
#print axioms pi_not_convertible_sigma
#print axioms neutral_identity_not_convertible_constant
#print axioms boolean_step_under_pi
#print axioms boolean_step_under_sigma

end SharedJudgmentNativeBooleanParallel
end Mettapedia.Languages.MeTTa.PrimeCandidates
