import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Runs

/-!
# The package's terms in the linearized program

A term of the package is a term whose constants the package declares. At such
a term the linearized program has exactly the steps of the package, and each
step leads to a term of the package again: the equations of the program that the
package lacks have left sides headed by the proof family's constants. Every
term typed in the package is a term of the package.

So the runs of the linearized program, and of the draft's program, from a term
typed in the package are runs of the package, and the theorems about runs of
the package hold for them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration
open Presentation.AlgebraicSchema (SchemaTable variableMultiplicity)
open Presentation.ConversionCoherence
open Presentation.ConstructorSystem (Normal)
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName numRecZeroEquation numRecSucEquation eqAtEquation
  sucMoveEquation keepEquation transportEquation composeEquation iterZeroEquation iterSucEquation
  returnIterEquation sucStepEquation)
open Confluence (jIotaLinear linearEquations linearRules LinearSchema)

/-! ## Terms of the package -/

/-- The names the package declares. -/
def packageNames : List DeclName := declarations.map Prod.fst

/-- Whether every constant of a term is declared by the package. -/
def inPackage {n : Nat} : Tower.Tm n → Bool
  | .var _ => true
  | .const name => decide (name ∈ packageNames)
  | .head _ => true
  | .pi A B => inPackage A && inPackage B
  | .sigma A B => inPackage A && inPackage B
  | .id A a b => inPackage A && inPackage a && inPackage b
  | .lam body => inPackage body
  | .app g a => inPackage g && inPackage a
  | .pair a b => inPackage a && inPackage b
  | .fst p => inPackage p
  | .snd p => inPackage p
  | .refl a => inPackage a

/-- A term of the package: every constant of it is declared by the package. -/
abbrev InPackage {n : Nat} (t : Tower.Tm n) : Prop := inPackage t = true

section Shapes

variable {n : Nat}

theorem inPackage_pi {A : Tower.Tm n} {B : Tower.Tm (n + 1)} :
    InPackage (.pi A B) ↔ InPackage A ∧ InPackage B := by
  simp only [InPackage, inPackage, Bool.and_eq_true]

theorem inPackage_sigma {A : Tower.Tm n} {B : Tower.Tm (n + 1)} :
    InPackage (.sigma A B) ↔ InPackage A ∧ InPackage B := by
  simp only [InPackage, inPackage, Bool.and_eq_true]

theorem inPackage_id {A a b : Tower.Tm n} :
    InPackage (.id A a b) ↔ (InPackage A ∧ InPackage a) ∧ InPackage b := by
  simp only [InPackage, inPackage, Bool.and_eq_true]

theorem inPackage_app {g a : Tower.Tm n} :
    InPackage (.app g a) ↔ InPackage g ∧ InPackage a := by
  simp only [InPackage, inPackage, Bool.and_eq_true]

theorem inPackage_pair {a b : Tower.Tm n} :
    InPackage (.pair a b) ↔ InPackage a ∧ InPackage b := by
  simp only [InPackage, inPackage, Bool.and_eq_true]

theorem inPackage_const {name : DeclName} :
    InPackage (.const name : Tower.Tm n) ↔ name ∈ packageNames := by
  simp only [InPackage, inPackage, decide_eq_true_eq]

end Shapes

theorem inPackage_rename {n m : Nat} (ρ : Ren n m) (t : Tower.Tm n) :
    inPackage (rename ρ t) = inPackage t := by
  induction t generalizing m with
  | var i => rfl
  | const c => rfl
  | head h => rfl
  | pi A B ihA ihB => simp only [rename, inPackage, ihA, ihB]
  | sigma A B ihA ihB => simp only [rename, inPackage, ihA, ihB]
  | id A a b ihA iha ihb => simp only [rename, inPackage, ihA, iha, ihb]
  | lam body ih => simp only [rename, inPackage, ih]
  | app g a ihg iha => simp only [rename, inPackage, ihg, iha]
  | pair a b iha ihb => simp only [rename, inPackage, iha, ihb]
  | fst p ih => simp only [rename, inPackage, ih]
  | snd p ih => simp only [rename, inPackage, ih]
  | refl a ih => simp only [rename, inPackage, ih]

theorem inPackage_liftSub {n m : Nat} {σ : Sub Tower.Head n m} (values : ∀ i, InPackage (σ i)) :
    ∀ i, InPackage (liftSub σ i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · show inPackage (liftSub σ j.succ) = true
    rw [liftSub_succ, inPackage_rename]
    exact values j

/-- Substituting terms of the package in a term of the package gives one. -/
theorem inPackage_subst {n m : Nat} {σ : Sub Tower.Head n m} (values : ∀ i, InPackage (σ i))
    (t : Tower.Tm n) (inT : InPackage t) : InPackage (subst σ t) := by
  induction t generalizing m with
  | var i => exact values i
  | const c => exact inT
  | head h => rfl
  | pi A B ihA ihB =>
      obtain ⟨hA, hB⟩ := inPackage_pi.mp inT
      exact inPackage_pi.mpr ⟨ihA values hA, ihB (inPackage_liftSub values) hB⟩
  | sigma A B ihA ihB =>
      obtain ⟨hA, hB⟩ := inPackage_sigma.mp inT
      exact inPackage_sigma.mpr ⟨ihA values hA, ihB (inPackage_liftSub values) hB⟩
  | id A a b ihA iha ihb =>
      obtain ⟨⟨hA, ha⟩, hb⟩ := inPackage_id.mp inT
      exact inPackage_id.mpr ⟨⟨ihA values hA, iha values ha⟩, ihb values hb⟩
  | lam body ih => exact ih (inPackage_liftSub values) inT
  | app g a ihg iha =>
      obtain ⟨hg, ha⟩ := inPackage_app.mp inT
      exact inPackage_app.mpr ⟨ihg values hg, iha values ha⟩
  | pair a b iha ihb =>
      obtain ⟨ha, hb⟩ := inPackage_pair.mp inT
      exact inPackage_pair.mpr ⟨iha values ha, ihb values hb⟩
  | fst p ih => exact ih values inT
  | snd p ih => exact ih values inT
  | refl a ih => exact ih values inT

theorem inPackage_inst0 {n : Nat} {a : Tower.Tm n} {body : Tower.Tm (n + 1)}
    (ha : InPackage a) (hbody : InPackage body) : InPackage (inst0 a body) := by
  refine inPackage_subst (fun i => ?_) body hbody
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ha
  · rfl

theorem pos_of_add_pos {a b : Nat} (positive : 0 < a + b) : 0 < a ∨ 0 < b := by
  rcases Nat.eq_zero_or_pos a with zero | pos
  · rw [zero, Nat.zero_add] at positive
    exact .inr positive
  · exact .inl pos

/-- The value of a variable occurring in a term of the package is a term of the
package. -/
theorem inPackage_of_subst {n m : Nat} {σ : Sub Tower.Head n m} (t : Tower.Tm n) (i : Fin n)
    (inT : InPackage (subst σ t)) (occurs : 0 < variableMultiplicity i t) :
    InPackage (σ i) := by
  induction t generalizing m with
  | var j =>
      simp only [variableMultiplicity] at occurs
      by_cases same : j = i
      · subst same
        exact inT
      · rw [if_neg same] at occurs
        exact absurd occurs (Nat.lt_irrefl 0)
  | const c => exact absurd occurs (Nat.lt_irrefl 0)
  | head h => exact absurd occurs (Nat.lt_irrefl 0)
  | pi A B ihA ihB =>
      obtain ⟨hA, hB⟩ := inPackage_pi.mp inT
      rcases pos_of_add_pos occurs with inA | inB
      · exact ihA i hA inA
      · have lifted := ihB i.succ hB inB
        rwa [liftSub_succ, InPackage, inPackage_rename] at lifted
  | sigma A B ihA ihB =>
      obtain ⟨hA, hB⟩ := inPackage_sigma.mp inT
      rcases pos_of_add_pos occurs with inA | inB
      · exact ihA i hA inA
      · have lifted := ihB i.succ hB inB
        rwa [liftSub_succ, InPackage, inPackage_rename] at lifted
  | id A a b ihA iha ihb =>
      obtain ⟨⟨hA, ha⟩, hb⟩ := inPackage_id.mp inT
      rcases pos_of_add_pos occurs with inAa | inb
      · rcases pos_of_add_pos inAa with inA | ina
        · exact ihA i hA inA
        · exact iha i ha ina
      · exact ihb i hb inb
  | lam body ih =>
      have lifted := ih i.succ inT occurs
      rwa [liftSub_succ, InPackage, inPackage_rename] at lifted
  | app g a ihg iha =>
      obtain ⟨hg, ha⟩ := inPackage_app.mp inT
      rcases pos_of_add_pos occurs with ing | ina
      · exact ihg i hg ing
      · exact iha i ha ina
  | pair a b iha ihb =>
      obtain ⟨ha, hb⟩ := inPackage_pair.mp inT
      rcases pos_of_add_pos occurs with ina | inb
      · exact iha i ha ina
      · exact ihb i hb inb
  | fst p ih => exact ih i inT occurs
  | snd p ih => exact ih i inT occurs
  | refl a ih => exact ih i inT occurs

/-! ## The equations stay in the package -/

/-- Every variable of an equation occurs in its left side, and its right side is a
term of the package. -/
theorem equations_closed : ∀ equation ∈ equations,
    (∀ i, 0 < variableMultiplicity i equation.2.1) ∧ inPackage equation.2.2 = true := by
  decide

theorem equation_closed {arity n : Nat} {left right : Tower.Tm arity}
    (rule : equations.family left right) (σ : Sub Tower.Head arity n)
    (inLeft : InPackage (subst σ left)) : InPackage (subst σ right) := by
  obtain ⟨occurs, inRight⟩ := equations_closed _ (equations_family rule)
  exact inPackage_subst (fun i => inPackage_of_subst left i inLeft (occurs i)) right inRight

/-- The equations of the linearized program the package lacks. -/
theorem linearEquations_split : linearEquations =
    [jIotaLinear, numRecZeroEquation, numRecSucEquation, eqAtEquation, sucMoveEquation, keepEquation,
      transportEquation, composeEquation, iterZeroEquation, iterSucEquation, returnIterEquation,
      sucStepEquation] ++
    [Package.holdsAtEquation, Package.holdsMoveEquation, Package.holdsStepEquation] := rfl

theorem const_not_inPackage {n : Nat} {name : DeclName} (outside : name ∉ packageNames) :
    ¬ InPackage (.const name : Tower.Tm n) :=
  fun inside => outside (inPackage_const.mp inside)

/-- A root step of the linearized program at a term of the package is a step of
the package, to a term of the package. -/
theorem root_restrict {n : Nat} {l r : Tower.Tm n} (step : linearRules.computation.step l r)
    (inL : InPackage l) : rules.computation.step l r ∧ InPackage r := by
  obtain ⟨arity, left, right, σ, rule, rfl, rfl⟩ := Confluence.linearSchema_cover step
  have ofEquation : equations.family left right →
      rules.computation.step (subst σ left) (subst σ right) ∧ InPackage (subst σ right) :=
    fun listed => ⟨equation_sound listed σ, equation_closed listed σ inL⟩
  cases rule with
  | implication => exact (const_not_inPackage (by decide) (inPackage_app.mp inL).1).elim
  | universal type => exact (const_not_inPackage (by decide) (inPackage_app.mp inL).1).elim
  | native listed => exact ofEquation (List.mem_append_left _ listed)
  | package listed =>
      rw [linearEquations_split] at listed
      rcases List.mem_append.mp listed with executable | consumer
      · exact ofEquation (List.mem_append_right _ executable)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at consumer
        rcases consumer with same | same | same <;> cases same
        · exact (const_not_inPackage (by decide) (inPackage_app.mp inL).1).elim
        · exact (const_not_inPackage (by decide)
            (inPackage_app.mp (inPackage_app.mp inL).1).1).elim
        · exact (const_not_inPackage (by decide)
            (inPackage_app.mp (inPackage_app.mp inL).1).1).elim

/-- A step of the linearized program from a term of the package is a step of
the package, to a term of the package. -/
theorem step_restrict {n : Nat} {l r : Tower.Tm n}
    (step : Step linearRules.headEq l r linearRules.computation) (inL : InPackage l) :
    Step rules.headEq l r rules.computation ∧ InPackage r := by
  induction step with
  | betaPi body a =>
      obtain ⟨hlam, ha⟩ := inPackage_app.mp inL
      exact ⟨.betaPi body a, inPackage_inst0 ha hlam⟩
  | betaSigmaFst a b => exact ⟨.betaSigmaFst a b, (inPackage_pair.mp inL).1⟩
  | betaSigmaSnd a b => exact ⟨.betaSigmaSnd a b, (inPackage_pair.mp inL).2⟩
  | head same => exact ⟨.head same, rfl⟩
  | root rootStep =>
      obtain ⟨packaged, inR⟩ := root_restrict rootStep inL
      exact ⟨.root packaged, inR⟩
  | congPiDom _ ih =>
      obtain ⟨hA, hB⟩ := inPackage_pi.mp inL
      obtain ⟨s, h⟩ := ih hA
      exact ⟨.congPiDom s, inPackage_pi.mpr ⟨h, hB⟩⟩
  | congPiCod _ ih =>
      obtain ⟨hA, hB⟩ := inPackage_pi.mp inL
      obtain ⟨s, h⟩ := ih hB
      exact ⟨.congPiCod s, inPackage_pi.mpr ⟨hA, h⟩⟩
  | congSigmaDom _ ih =>
      obtain ⟨hA, hB⟩ := inPackage_sigma.mp inL
      obtain ⟨s, h⟩ := ih hA
      exact ⟨.congSigmaDom s, inPackage_sigma.mpr ⟨h, hB⟩⟩
  | congSigmaCod _ ih =>
      obtain ⟨hA, hB⟩ := inPackage_sigma.mp inL
      obtain ⟨s, h⟩ := ih hB
      exact ⟨.congSigmaCod s, inPackage_sigma.mpr ⟨hA, h⟩⟩
  | congIdTy _ ih =>
      obtain ⟨⟨hA, ha⟩, hb⟩ := inPackage_id.mp inL
      obtain ⟨s, h⟩ := ih hA
      exact ⟨.congIdTy s, inPackage_id.mpr ⟨⟨h, ha⟩, hb⟩⟩
  | congIdLeft _ ih =>
      obtain ⟨⟨hA, ha⟩, hb⟩ := inPackage_id.mp inL
      obtain ⟨s, h⟩ := ih ha
      exact ⟨.congIdLeft s, inPackage_id.mpr ⟨⟨hA, h⟩, hb⟩⟩
  | congIdRight _ ih =>
      obtain ⟨⟨hA, ha⟩, hb⟩ := inPackage_id.mp inL
      obtain ⟨s, h⟩ := ih hb
      exact ⟨.congIdRight s, inPackage_id.mpr ⟨⟨hA, ha⟩, h⟩⟩
  | congLam _ ih =>
      obtain ⟨s, h⟩ := ih inL
      exact ⟨.congLam s, h⟩
  | congAppFun _ ih =>
      obtain ⟨hg, ha⟩ := inPackage_app.mp inL
      obtain ⟨s, h⟩ := ih hg
      exact ⟨.congAppFun s, inPackage_app.mpr ⟨h, ha⟩⟩
  | congAppArg _ ih =>
      obtain ⟨hg, ha⟩ := inPackage_app.mp inL
      obtain ⟨s, h⟩ := ih ha
      exact ⟨.congAppArg s, inPackage_app.mpr ⟨hg, h⟩⟩
  | congPairFst _ ih =>
      obtain ⟨ha, hb⟩ := inPackage_pair.mp inL
      obtain ⟨s, h⟩ := ih ha
      exact ⟨.congPairFst s, inPackage_pair.mpr ⟨h, hb⟩⟩
  | congPairSnd _ ih =>
      obtain ⟨ha, hb⟩ := inPackage_pair.mp inL
      obtain ⟨s, h⟩ := ih hb
      exact ⟨.congPairSnd s, inPackage_pair.mpr ⟨ha, h⟩⟩
  | congFst _ ih =>
      obtain ⟨s, h⟩ := ih inL
      exact ⟨.congFst s, h⟩
  | congSnd _ ih =>
      obtain ⟨s, h⟩ := ih inL
      exact ⟨.congSnd s, h⟩
  | congRefl _ ih =>
      obtain ⟨s, h⟩ := ih inL
      exact ⟨.congRefl s, h⟩

/-- Runs of the linearized program from a term of the package are runs of the
package, through terms of the package. -/
theorem runs_restrict {n : Nat} {l r : Tower.Tm n} (runs : StepStar linearRules l r)
    (inL : InPackage l) : StepStar rules l r ∧ InPackage r := by
  induction runs with
  | refl => exact ⟨.refl, inL⟩
  | tail _ step ih =>
      obtain ⟨runs', inMid⟩ := ih
      obtain ⟨step', inR⟩ := step_restrict step inMid
      exact ⟨.tail runs' step', inR⟩

/-- A step of the package is a step of the linearized program. -/
theorem step_linear {n : Nat} {l r : Tower.Tm n}
    (step : Step rules.headEq l r rules.computation) :
    Step linearRules.headEq l r linearRules.computation := by
  simpa only [Tm.mapHead_id] using
    StepCore.mapHead (fun head => head) toLinear.headEq toLinear.computation step

/-- A term of the package without steps of the package has no steps of the
linearized program, and conversely. -/
theorem normal_iff {n : Nat} {t : Tower.Tm n} (inT : InPackage t) :
    Normal linearRules t ↔ Normal rules t :=
  ⟨fun normal _ step => normal (step_linear step),
    fun normal _ step => normal (step_restrict step inT).1⟩

/-! ## Typed terms are terms of the package -/

/-- What a derivable statement says about the package's terms. -/
def StatementIn : Statement Tower.Head → Prop
  | .typing _ t _ => InPackage t
  | .equality _ a b _ => InPackage a ∧ InPackage b
  | .sub _ A B => InPackage A ∧ InPackage B

theorem constant_inPackage {name : DeclName} {type : Tower.Tm 0}
    (declared : rules.constantType name = some type) : name ∈ packageNames := by
  change (if true then allTypes name else none) = some type at declared
  rw [if_pos rfl] at declared
  exact List.mem_map_of_mem (mem_of_lookup (show declarations.lookup name = some type from declared))

/-- The terms of the statements derivable in the package are its terms. -/
theorem derivable_inPackage {st : Statement Tower.Head} (derivation : Derivable rules st) :
    StatementIn st := by
  induction derivation with
  | headType _ => exact rfl
  | var i => exact rfl
  | const declared _ _ _ => exact inPackage_const.mpr (constant_inPackage declared)
  | piForm _ _ _ _ _ ihA ihB => exact inPackage_pi.mpr ⟨ihA, ihB⟩
  | sigmaForm _ _ _ _ _ ihA ihB => exact inPackage_sigma.mpr ⟨ihA, ihB⟩
  | lamIntro _ _ _ _ ihBody => exact ihBody
  | appElim _ _ ihg iha => exact inPackage_app.mpr ⟨ihg, iha⟩
  | pairIntro _ _ _ _ _ iha ihb => exact inPackage_pair.mpr ⟨iha, ihb⟩
  | fstElim _ ih => exact ih
  | sndElim _ ih => exact ih
  | idForm _ _ _ _ ihA iha ihb => exact inPackage_id.mpr ⟨⟨ihA, iha⟩, ihb⟩
  | reflIntro _ ih => exact ih
  | sub _ _ iht _ => exact iht
  | conv _ _ _ iht _ => exact iht
  | refl _ ih => exact ⟨ih, ih⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | convEq _ _ _ ih _ => exact ih
  | subEq _ _ ih _ => exact ih
  | headEq _ _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | piCong _ _ _ _ _ ihA ihB =>
      exact ⟨inPackage_pi.mpr ⟨ihA.1, ihB.1⟩, inPackage_pi.mpr ⟨ihA.2, ihB.2⟩⟩
  | sigmaCong _ _ _ _ _ ihA ihB =>
      exact ⟨inPackage_sigma.mpr ⟨ihA.1, ihB.1⟩, inPackage_sigma.mpr ⟨ihA.2, ihB.2⟩⟩
  | idCong _ _ _ _ ihA iha ihb =>
      exact ⟨inPackage_id.mpr ⟨⟨ihA.1, iha.1⟩, ihb.1⟩, inPackage_id.mpr ⟨⟨ihA.2, iha.2⟩, ihb.2⟩⟩
  | lamCong _ _ _ _ ihBody => exact ihBody
  | appCong _ _ ihf iha =>
      exact ⟨inPackage_app.mpr ⟨ihf.1, iha.1⟩, inPackage_app.mpr ⟨ihf.2, iha.2⟩⟩
  | pairCong _ _ _ _ _ iha ihb =>
      exact ⟨inPackage_pair.mpr ⟨iha.1, ihb.1⟩, inPackage_pair.mpr ⟨iha.2, ihb.2⟩⟩
  | fstCong _ ih => exact ih
  | sndCong _ ih => exact ih
  | reflCong _ ih => exact ih
  | betaPi _ _ _ _ _ ihBody iha =>
      exact ⟨inPackage_app.mpr ⟨ihBody, iha⟩, inPackage_inst0 iha ihBody⟩
  | betaFst _ _ _ _ _ iha ihb => exact ⟨inPackage_pair.mpr ⟨iha, ihb⟩, iha⟩
  | betaSnd _ _ _ _ _ iha ihb => exact ⟨inPackage_pair.mpr ⟨iha, ihb⟩, ihb⟩
  | root _ _ _ ihl ihr => exact ⟨ihl, ihr⟩
  | etaPi _ _ _ ihf ihg _ => exact ⟨ihf, ihg⟩
  | etaSigma _ _ _ _ ihp ihq _ _ => exact ⟨ihp, ihq⟩
  | subEqual _ _ ih => exact ih
  | subUniv _ => exact ⟨rfl, rfl⟩
  | subPi _ _ _ _ _ _ _ ihPi ihPi' _ _ => exact ⟨ihPi, ihPi'⟩
  | subSigma _ _ _ _ _ _ ihSigma ihSigma' _ _ => exact ⟨ihSigma, ihSigma'⟩
  | subTrans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

theorem typed_inPackage {n : Nat} {Γ : Tower.Ctx n} {t T : Tower.Tm n}
    (typing : Typed rules Γ t T) : InPackage t :=
  derivable_inPackage typing

/-! ## Runs of the program from typed terms of the package -/

/-- Runs of the linearized program from a term typed in the package are runs of
the package, and preserve its typing and typed equality. -/
theorem linear_runs_preserve {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed rules Γ)
    {term result T : Tower.Tm n} (typing : Typed rules Γ term T)
    (runs : StepStar linearRules term result) :
    StepStar rules term result ∧ Typed rules Γ result T ∧ Equal rules Γ term result T := by
  have packaged := (runs_restrict runs (typed_inPackage typing)).1
  exact ⟨packaged, reduces_preserve formed packaged typing⟩

/-- Runs of the linearized program from a term typed in the package that stop,
stop at one term, equal to the start in the package's typed equality. -/
theorem linear_stopped_unique {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed rules Γ)
    {term T first second : Tower.Tm n} (typing : Typed rules Γ term T)
    (firstRuns : StepStar linearRules term first) (firstStopped : Normal linearRules first)
    (secondRuns : StepStar linearRules term second) (secondStopped : Normal linearRules second) :
    first = second ∧ Equal rules Γ term first T := by
  obtain ⟨firstPackaged, inFirst⟩ := runs_restrict firstRuns (typed_inPackage typing)
  obtain ⟨secondPackaged, inSecond⟩ := runs_restrict secondRuns (typed_inPackage typing)
  exact stopped_unique formed typing firstPackaged ((normal_iff inFirst).mp firstStopped)
    secondPackaged ((normal_iff inSecond).mp secondStopped)

/-- Runs of the draft's program from a term typed in the package are runs of the
package, and preserve its typing and typed equality. -/
theorem draft_runs_preserve {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed rules Γ)
    {term result T : Tower.Tm n} (typing : Typed rules Γ term T)
    (runs : StepStar Package.packageRules term result) :
    StepStar rules term result ∧ Typed rules Γ result T ∧ Equal rules Γ term result T := by
  refine linear_runs_preserve formed typing ?_
  induction runs with
  | refl => exact .refl
  | @tail mid last _ step ih =>
      have lifted : Step linearRules.headEq mid last linearRules.computation := by
        simpa only [Tm.mapHead_id] using
          StepCore.mapHead (fun head => head) Confluence.packageToLinear.headEq
            Confluence.packageToLinear.computation step
      exact .tail ih lifted

/-- The elimination at `refl (λ n. f n)` is a term of the package. -/
theorem etaElimination_inPackage : InPackage etaElimination := by decide

#print axioms inPackage_of_subst
#print axioms root_restrict
#print axioms step_restrict
#print axioms normal_iff
#print axioms derivable_inPackage
#print axioms linear_runs_preserve
#print axioms linear_stopped_unique
#print axioms draft_runs_preserve

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
