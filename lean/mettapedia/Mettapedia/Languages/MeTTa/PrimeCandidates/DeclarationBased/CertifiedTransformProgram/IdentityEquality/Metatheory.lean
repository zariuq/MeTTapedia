import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Basic
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.DraftComparison

/-!
# Confluence and preservation for the identity profile

The linearized program with the equation decoder is again a definition by
constructor patterns: the decoder's left side `Holds (eq@T x y)` is linear,
headed by the proof family at arity one, and meets no other equation.  So the
profile is Church–Rosser and separates dependent functions, pairs and identity
types.

The profile is a host of the linearized program.  Every inherited equation
preserves typing by the host laws, and the decoder preserves typing by the
generic identity interpretation.  Every run of the profile over the draft's
program is a run of the linearized profile.

The profile over the draft's program differs from the linearized profile only
in identity elimination, so on typed terms their runs that stop agree, and
between such terms their conversions agree.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Metatheory

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.AlgebraicSchema (SchemaFamily LeftLinearFamily variableMultiplicity)
open Presentation.AlgebraicParallel Presentation.ConversionCoherence
open Presentation.ConstructorSystem (LeftSide System unifiable)
open SetProfile (numTy holdsName)
open CertifiedTransformProgram.Package CertifiedTransformProgram.Confluence
open CertifiedTransformProgram.Preservation CertifiedTransformProgram.IdentityEquality
open FormationSensitiveHOLIdentityEquality (IdentityStep interpret interpretMorphism
  interpret_map identityStep_preserves declarations)
open Mettapedia.Logic

/-- The linearized program with represented equations read as identity types. -/
noncomputable abbrev identityLinearRules : Rules Tower.Head :=
  interpret linearRules SetProfile.signature holdsName

theorem linearToIdentity : linearRules.Morphism identityLinearRules (fun head => head) :=
  interpretMorphism linearRules SetProfile.signature holdsName

/-- The profile over the draft's program embeds in the linearized profile. -/
theorem identityToLinear : identityRules.Morphism identityLinearRules (fun head => head) :=
  interpret_map SetProfile.signature holdsName packageToLinear

/-! ## The rewrite system -/

/-- `Holds (eq@T x y)`, over the telescope `x, y`. -/
abbrev equationLeft (type : HOL.Ty SetProfile.SetBase) : Tower.Tm 2 :=
  .app (.const holdsName) (.app (.app (.const (SetProfile.eqName type)) (.var 1)) (.var 0))

/-- `Id T x y`. -/
noncomputable abbrev equationRight (type : HOL.Ty SetProfile.SetBase) : Tower.Tm 2 :=
  .id (FormationSensitiveHOLInterface.typeAt SetProfile.signature.types 2 type) (.var 1) (.var 0)

/-- The equations of the profile: those of the linearized program and the
equation decoder. -/
inductive IdentitySchema : SchemaFamily Tower.Head
  | linear {arity : Nat} {left right : Tower.Tm arity} :
      LinearSchema left right → IdentitySchema left right
  | equation (type : HOL.Ty SetProfile.SetBase) :
      IdentitySchema (equationLeft type) (equationRight type)

theorem equation_instance (type : HOL.Ty SetProfile.SetBase) {n : Nat}
    (σ : Sub Tower.Head 2 n) :
    subst σ (equationRight type) =
      .id (FormationSensitiveHOLInterface.typeAt SetProfile.signature.types n type) (σ 1) (σ 0) := by
  simp only [Presentation.subst, FormationSensitiveHOLInterface.typeAt_subst]

theorem identitySchema_sound {arity n : Nat} {left right : Tower.Tm arity}
    (rule : IdentitySchema left right) (σ : Sub Tower.Head arity n) :
    identityLinearRules.computation.step (subst σ left) (subst σ right) := by
  cases rule with
  | linear rule => exact RootStep.inherited (linearSchema_sound rule σ)
  | equation type =>
      rw [equation_instance]
      exact RootStep.declared (IdentityStep.equation type (σ 1) (σ 0))

theorem identitySchema_cover {n : Nat} {source target : Tower.Tm n}
    (step : identityLinearRules.computation.step source target) :
    ∃ (arity : Nat) (left right : Tower.Tm arity) (σ : Sub Tower.Head arity n),
      IdentitySchema left right ∧ subst σ left = source ∧ subst σ right = target := by
  cases step with
  | inherited linearStep =>
      obtain ⟨arity, left, right, σ, rule, leftShape, rightShape⟩ := linearSchema_cover linearStep
      exact ⟨arity, left, right, σ, .linear rule, leftShape, rightShape⟩
  | delta lookup => simp [Signature.valueOf?, declarations, Signature.empty] at lookup
  | declared decoded =>
      cases decoded with
      | equation type l r =>
          exact ⟨2, equationLeft type, equationRight type, Fin.cons r (Fin.cons l Fin.elim0),
            .equation type, rfl, by rw [equation_instance]; rfl⟩

def identityPresentation : SchemaPresentation identityLinearRules where
  schema := IdentitySchema
  sound := identitySchema_sound
  cover := by
    intro n source target step
    obtain ⟨arity, left, right, σ, rule, leftShape, rightShape⟩ := identitySchema_cover step
    exact ⟨arity, left, right, σ, rule, leftShape, rightShape⟩

/-! ## A constructor system -/

/-- No equality instance is a defined constant. -/
theorem eqName_not_defined (type : HOL.Ty SetProfile.SetBase) :
    ¬ Defined (SetProfile.eqName type) := by
  intro listed
  simp only [Defined, definedHeads, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with same | same | same | same | same | same | same | same | same | same |
    same | same | same | same | same | same <;>
    exact SetProfile.eqName_ne_of_eqInstance? (by decide) type same

theorem identitySchema_left {m : Nat} {left right : Tower.Tm m} (rule : IdentitySchema left right) :
    ∃ name, Defined name ∧ 0 < arityOf name ∧ LeftSide Defined left name (arityOf name) := by
  cases rule with
  | linear rule => exact linearSchema_left rule
  | equation type =>
      refine ⟨holdsName, by decide, by decide, ?_⟩
      show LeftSide Defined (equationLeft type) holdsName 1
      exact .app (.const _) (.app (.app (.const (eqName_not_defined type)) (.var 1)) (.var 0))

theorem identitySchema_linear : LeftLinearFamily IdentitySchema := by
  intro m left right rule
  cases rule with
  | linear rule => exact linearSchema_linear rule
  | equation type =>
      exact Fin.forall_fin_two.mpr ⟨by simp [variableMultiplicity], by simp [variableMultiplicity]⟩

theorem identitySchema_covered {m : Nat} {left right : Tower.Tm m}
    (rule : IdentitySchema left right) :
    ∀ index, 0 < variableMultiplicity index right → 0 < variableMultiplicity index left := by
  cases rule with
  | linear rule => exact linearSchema_covered rule
  | equation type =>
      exact Fin.forall_fin_two.mpr ⟨fun _ => Nat.zero_lt_one, fun _ => Nat.zero_lt_one⟩

theorem eqName_ne_impName (type : HOL.Ty SetProfile.SetBase) :
    SetProfile.eqName type ≠ SetProfile.impName :=
  SetProfile.eqName_ne_of_eqInstance? (by decide) type

/-- The decoder's left side meets no equation of the linearized program. -/
theorem equation_apart (type : HOL.Ty SetProfile.SetBase) {m : Nat} {left right : Tower.Tm m}
    (rule : LinearSchema left right) :
    unifiable (equationLeft type) left = false ∧ unifiable left (equationLeft type) = false := by
  cases rule with
  | implication =>
      constructor <;> simp [unifiable, eqName_ne_impName type, (eqName_ne_impName type).symm]
  | universal other => exact ⟨rfl, rfl⟩
  | native listed =>
      simp only [SetProfile.nativeEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with same | same | same | same <;> cases same <;> exact ⟨rfl, rfl⟩
  | package listed =>
      simp only [linearEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with same | same | same | same | same | same | same | same | same | same |
        same | same | same | same | same <;> cases same <;> exact ⟨rfl, rfl⟩

theorem equation_equation (type type' : HOL.Ty SetProfile.SetBase)
    (meet : unifiable (equationLeft type) (equationLeft type') = true) : type = type' := by
  simp only [unifiable, decide_eq_true_eq, Bool.and_eq_true, Bool.and_true, true_and] at meet
  exact SetProfile.eqName_injective meet

theorem identitySchema_disjoint {m m' : Nat} {left right : Tower.Tm m}
    {left' right' : Tower.Tm m'} (rule : IdentitySchema left right)
    (rule' : IdentitySchema left' right') (meet : unifiable left left' = true) :
    (⟨m, (left, right)⟩ : Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) = ⟨m', (left', right')⟩ := by
  cases rule with
  | linear rule =>
      cases rule' with
      | linear rule' => exact linearSchema_disjoint rule rule' meet
      | equation type => rw [(equation_apart type rule).2] at meet; cases meet
  | equation type =>
      cases rule' with
      | linear rule' => rw [(equation_apart type rule').1] at meet; cases meet
      | equation type' => obtain rfl := equation_equation type type' meet; rfl

noncomputable def identitySystem : System Tower.Head where
  schema := IdentitySchema
  defined := Defined
  arity := arityOf
  left := identitySchema_left
  linear := identitySchema_linear
  covered := identitySchema_covered
  determined := Presentation.ConstructorSystem.determined_of_disjoint
    (fun rule => by
      obtain ⟨name, _, _, side⟩ := identitySchema_left rule
      exact ⟨name, _, side⟩)
    identitySchema_covered identitySchema_disjoint

/-- The linearized identity profile as a definition by constructor patterns. -/
noncomputable def identityConstructors :
    Presentation.ConstructorSystem.ConstructorPresentation identityLinearRules where
  presentation := identityPresentation
  system := identitySystem
  same := fun _ _ => Iff.rfl
  symmetric := Tower.headEq_symmetric

theorem churchRosser : ChurchRosser identityLinearRules := identityConstructors.churchRosser

/-! ## Subject reduction -/

theorem identityUniverses : UniverseRegularity identityLinearRules :=
  universes.includeSignature (declarations SetProfile.signature holdsName)

theorem identityHeads : HeadPreservation identityLinearRules :=
  HeadPreservation.includeSignature heads (declarations SetProfile.signature holdsName)

/-- The linearized identity profile is a host of the linearized program. -/
noncomputable def identityHost : Host :=
  Host.ofConstructors identityLinearRules linearToIdentity identityUniverses identityConstructors

theorem rootPreservation : RootPreservation identityLinearRules := by
  intro n Γ source target displayed formed observed step
  obtain ⟨_, _, _, σ, rule, rfl, rfl⟩ := identitySchema_cover step
  cases rule with
  | linear rule => exact identityHost.linearSchema_preserves rule σ formed observed
  | equation type =>
      rw [equation_instance]
      exact identityStep_preserves SetProfile.signature holdsName identityHost.fromProofFamily
        SetProfile.holdsName_fresh equality identityHost.universes identityHost.piBoundary formed
        observed (IdentityStep.equation type (σ 1) (σ 0))

theorem step_preserves {n : Nat} {Γ : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment identityLinearRules Γ source displayed)
    (step : Step identityLinearRules.headEq source target identityLinearRules.computation) :
    Judgment identityLinearRules Γ target displayed :=
  judgment.step_preserves identityUniverses identityConstructors.piConversionBoundary
    identityConstructors.sigmaConversionBoundary identityHeads rootPreservation step

theorem steps_preserve {n : Nat} {Γ : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment identityLinearRules Γ source displayed)
    (steps : StepStar identityLinearRules source target) :
    Judgment identityLinearRules Γ target displayed :=
  judgment.steps_preserve identityUniverses identityConstructors.piConversionBoundary
    identityConstructors.sigmaConversionBoundary identityHeads rootPreservation steps

/-- Every run of the profile over the draft's program is a run of the
linearized profile. -/
theorem runs_linear {n : Nat} {source target : Tower.Tm n}
    (runs : StepStar identityRules source target) : StepStar identityLinearRules source target := by
  induction runs with
  | refl => exact .refl
  | tail _ step ih =>
      refine .tail ih ?_
      simpa only [Tm.mapHead_id] using
        StepCore.mapHead (fun head => head) identityToLinear.headEq identityToLinear.computation step

/-- Judgments of the profile over the draft's program are judgments of the
linearized profile. -/
theorem judgment_linear {n : Nat} {Γ : Tower.Ctx n} {term type : Tower.Tm n}
    (judgment : Judgment identityRules Γ term type) : Judgment identityLinearRules Γ term type :=
  ⟨by simpa only [Ctx.mapHead_id] using judgment.context.mapHead identityToLinear,
    by simpa only [Ctx.mapHead_id, Tm.mapHead_id] using judgment.typing.mapHead identityToLinear⟩

/-- Every run of the profile keeps the type of the judgment it starts from. -/
theorem runs_preserve {n : Nat} {Γ : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment identityRules Γ source displayed)
    (runs : StepStar identityRules source target) :
    Judgment identityLinearRules Γ target displayed :=
  steps_preserve (judgment_linear judgment) (runs_linear runs)

/-! ## The profile over the draft's program -/

open CertifiedTransformProgram.DraftComparison (Draft packageDraft)
open Presentation.ConstructorSystem (Normal)

/-- The profile over the draft's program is a draft of the linearized profile. -/
noncomputable def identityDraft : Draft identityHost where
  rules := identityRules
  toHost := identityToLinear
  headEq := fun equality => equality
  cover := by
    intro n source target step
    change identityLinearRules.computation.step source target at step
    cases step with
    | inherited linearStep =>
        rcases packageDraft.cover linearStep with drafted | elimination
        · exact .inl (.inherited drafted)
        · exact .inr elimination
    | delta lookup => simp [Signature.valueOf?, declarations, Signature.empty] at lookup
    | declared decoded => exact .inl (.declared decoded)
  diagonal := fun carrier point motive method =>
    .inherited (packageDraft.diagonal carrier point motive method)

theorem identity_unique {n : Nat} {first second : Tower.Tm n}
    (firstNormal : Normal identityLinearRules first) (secondNormal : Normal identityLinearRules second)
    (conversion : Conv identityLinearRules.headEq first second identityLinearRules.computation) :
    first = second :=
  identityConstructors.eq_of_normal firstNormal secondNormal conversion

/-- Runs of the profile over the draft's program from a typed term that stop,
stop at the same term. -/
theorem stopped_unique {n : Nat} {Γ : Tower.Ctx n} {term type first second : Tower.Tm n}
    (judgment : Judgment identityRules Γ term type)
    (firstRuns : StepStar identityRules term first) (firstStopped : Normal identityRules first)
    (secondRuns : StepStar identityRules term second) (secondStopped : Normal identityRules second) :
    first = second :=
  identityDraft.stopped_unique identity_unique steps_preserve (judgment_linear judgment)
    firstRuns firstStopped secondRuns secondStopped

/-- Between typed terms whose runs stop, conversion of the linearized profile is
conversion of the profile over the draft's program. -/
theorem conversion_reflects {n : Nat} {Γ : Tower.Ctx n}
    {left right leftType rightType leftResult rightResult : Tower.Tm n}
    (leftJudgment : Judgment identityRules Γ left leftType)
    (rightJudgment : Judgment identityRules Γ right rightType)
    (conversion : Conv identityLinearRules.headEq left right identityLinearRules.computation)
    (leftRuns : StepStar identityRules left leftResult) (leftStopped : Normal identityRules leftResult)
    (rightRuns : StepStar identityRules right rightResult)
    (rightStopped : Normal identityRules rightResult) :
    Conv identityRules.headEq left right identityRules.computation :=
  identityDraft.conversion_reflects identity_unique steps_preserve (judgment_linear leftJudgment)
    (judgment_linear rightJudgment) conversion leftRuns leftStopped rightRuns rightStopped

#print axioms identityDraft
#print axioms stopped_unique
#print axioms conversion_reflects
#print axioms identitySchema_cover
#print axioms identitySchema_disjoint
#print axioms churchRosser
#print axioms rootPreservation
#print axioms step_preserves
#print axioms steps_preserve
#print axioms runs_preserve

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Metatheory
