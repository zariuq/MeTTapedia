import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateInference
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.OlderUnknownControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateControls

/-!
# The templating step, decided by the kernel

**The gap firing** (`TemplateControls.gapFiring`): over `X : U₁, f : X, a : U₀` it tells
`X ≐ Π (y : U₀). U₀` and makes `f a` at `U₀`. Its unknown `X` is the oldest declaration, learned by a
homogeneous equation.
* N3's settler leaves it undecided (`gap_tower_undecided`); the older-unknown family settles it
  (`gap_older_settled`).
* **The computable templating step admits it** (`gap_decided`, `gap_admitted`): the inferred template
  is `f' a'` over the answer's frame `f' : Π (y : U₀). U₀, a' : U₀`, synthesizing `U₀`. The converting
  step refuses it for every settler, and the present step refuses it (`gap_computable_separation`). Its
  row is typed at every solution (`gap_typedAfterMatch_computably`).

**Refused**: the same firing making `f a` at `Ground` (`groundRow`). The kernel refuses it
(`gapGround_decided`, `gapGround_refused`), and independently of the decision the row is not typed at
the answer `X ↦ Π (y : U₀). U₀`, since `f' a'` synthesizes `U₀`, which is not usable at `Ground`
(`groundRow_not_typed_at_answer`, `gapGround_not_typedAfterMatch`).

**A function learned by matching**: the gap firing making `f` at `Π (y : U₀). U₀`. The present step
refuses it, the computable templating step admits it (`gapFunction_computable_separation`), deciding the
two dependent function types by their codomains.

**Refused**: the η firing of `AgreementCounterexample`, whose row `h` is made at `Π (x : U₀). U₁` while
`h : Π (x : U₁). U₁`: the domains cannot be equal, so the kernel refuses it (`eta_refused`,
`eta_refused_computably`), as every settler's templating step does
(`TemplateControls.eta_templating_refused`).

**Two pattern variables typed by two earlier unknowns** (`twoFiring`): over `X Y : U₀`, make
`x : X, y : Y, g : Ground, k : Ground → Ground`, tell `(x : X) ≐ (g : Ground)` and
`(y : Y) ≐ (k : Ground → Ground)`, and make `x` at `Ground` and `y` at `Ground → Ground`. N3's settler
leaves it undecided (`two_tower_undecided`); the computable templating step admits it, both unknowns solved
in place (`two_decided`); the present step refuses it (`two_computable_separation`).

**D2's coerce firing** is admitted by the computable templating step as well (`coerce_templating_decided`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.TemplateInference.Controls

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ComputableControls
open OlderUnknown
open TemplateControls (gapFiring gapRow gapFrame gapTarget gapAnswer gapAnswer_solves gap_no_frame_typing
  gap_converting_refused smallArrow smallArrow_typed)

/-! ## The gap firing -/

/-- **N3's settler leaves the gap firing's information undecided**: its unknown is the oldest. -/
theorem gap_tower_undecided : templatingAdmits? towerFamilies gapFiring = none := by decide +kernel

/-- **The older-unknown family settles it.** -/
theorem gap_older_settled : (olderFamily olderFuel gapFiring.information).isSettled = true := by decide +kernel

/-- **Decided by the kernel: the computable templating step admits the gap firing.** -/
theorem gap_decided : templatingAdmits? olderFamilies gapFiring = some true := by decide +kernel

theorem gap_admitted : (templatingStep setting.levels Nat olderSettler).Admits gapFiring :=
  (templatingAdmits?_sound olderFamilies gap_decided).mp rfl

/-- The present step refuses it: `f a` has no typing in its frame. -/
theorem gap_present_refused : ¬ (step setting.levels Nat).Admits gapFiring :=
  fun admitted => gap_no_frame_typing gapRow.type (admitted.1.2.2.2.2 (1, gapRow) (List.mem_singleton_self _))

/-- **The separation**: the computable templating step admits the gap firing; the converting step, with
every settler, and the present step refuse it. -/
theorem gap_computable_separation :
    (templatingStep setting.levels Nat olderSettler).Admits gapFiring ∧
      (∀ settler : Settler setting.levels, ¬ (convertingStep setting.levels Nat settler).Admits gapFiring) ∧
      ¬ (step setting.levels Nat).Admits gapFiring :=
  ⟨gap_admitted, gap_converting_refused, gap_present_refused⟩

/-- **Its row is typed at every solution of its information**, by the soundness of the templating step. -/
theorem gap_typedAfterMatch_computably : TypedAfterMatch setting.levels gapFiring.information gapRow :=
  templating_typedAfterMatch setting.levels olderSettler gap_admitted (1, gapRow) (List.mem_singleton_self _)

/-! ## Refused: `f a` made at `Ground` -/

/-- The row `f a` at `Ground`. -/
def groundRow : Make gapFrame := ⟨groundType _, .app (.var 1) (.var 0)⟩

/-- The gap firing making `f a` at `Ground`. -/
def gapGroundFiring : Firing setting.levels emptyState := { gapFiring with makes := [(1, groundRow)] }

/-- **Decided by the kernel: refused.** -/
theorem gapGround_decided : templatingAdmits? olderFamilies gapGroundFiring = some false := by decide +kernel

theorem gapGround_refused : ¬ (templatingStep setting.levels Nat olderSettler).Admits gapGroundFiring :=
  fun admitted => Bool.false_ne_true ((templatingAdmits?_sound olderFamilies gapGround_decided).mpr admitted)

/-- `f' a'` synthesizes `U₀` over `f' : Π (y : U₀). U₀, a' : U₀`. -/
theorem gap_app_synth :
    Synth setting.R setting.roles gapTarget.raw (.app (.var 1) (.var 0)) (.head (.sort Tower.zero)) := by
  have synthF : Synth setting.R setting.roles gapTarget.raw (.var 1) smallArrow := .var 1
  have red : RedTy setting.R setting.roles gapTarget.raw smallArrow
      (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) :=
    RedTy.refl ⟨(.sort (.succ Tower.zero) : Tower.Head), LevelTower.IsUniverse.sort _, smallArrow_typed _⟩
  have below : Below setting.R gapTarget.raw (.head (.sort Tower.zero)) (.head (.sort Tower.zero)) :=
    below_refl_of_isType ⟨(.sort (.succ Tower.zero) : Tower.Head), LevelTower.IsUniverse.sort _,
      .headType (LevelTower.HeadTyping.sort _)⟩
  have check : KernelTyping setting.R setting.roles .check gapTarget.raw (.var 0) (.head (.sort Tower.zero)) :=
    .switch (.var 0) below
  exact .app synthF red check

/-- **Independently of the decision**: `f' a'` is not of type `Ground` at the answer, since its
synthesized type `U₀` is not usable at `Ground`. -/
theorem groundRow_not_typed_at_answer : ¬ (groundRow.reindex gapAnswer).WellTyped := by
  intro typed
  have notBelow : ¬ Below Tower.rules gapTarget.raw (.head (.sort Tower.zero)) ground := fun le =>
    (below_heads_iff gapTarget.formed (.sort Tower.zero) .legacyGround).mp le
  exact Synth.not_typed (S := setting) TowerModel.facts TowerModel.algebra
    ContextualDependentNormalCheckingTower.head_typing_unique gap_app_synth gapTarget.formed notBelow typed

/-- ... **so the row is not typed after the match**: the answer is a solution. -/
theorem gapGround_not_typedAfterMatch : ¬ TypedAfterMatch setting.levels gapGroundFiring.information groundRow :=
  fun typed => groundRow_not_typed_at_answer
    (((typedAfterMatch_iff setting.levels _ groundRow).mp typed) gapTarget gapAnswer gapAnswer_solves)

/-! ## A function learned by matching: `f` made at `Π (y : U₀). U₀` -/

/-- `Π (y : U₀). U₀`, over the gap frame. -/
def arrowOver : TypeOver gapFrame := ⟨smallArrow, .sort (.succ Tower.zero), .sort _, smallArrow_typed _⟩

/-- The row `f` at `Π (y : U₀). U₀`. -/
def fRow : Make gapFrame := ⟨arrowOver, .var 1⟩

/-- The gap firing making `f` at `Π (y : U₀). U₀`. -/
def gapFunctionFiring : Firing setting.levels emptyState := { gapFiring with makes := [(1, fRow)] }

/-- `f` is not of type `Π (y : U₀). U₀` in its frame: its type is the variable `X`. -/
theorem f_not_arrow : ¬ Typed Tower.rules gapFrame.raw (.var 1) smallArrow := by
  intro typed
  have formed : CtxFormed Tower.rules gapFrame.raw := gapFrame.formed
  have le : TypeLe Tower.rules gapFrame.raw (.var 2) smallArrow := Typed.generation typed
  have isPi : IsType Tower.rules gapFrame.raw smallArrow :=
    ⟨(.sort (.succ Tower.zero) : Tower.Head), LevelTower.IsUniverse.sort _, smallArrow_typed _⟩
  obtain ⟨A₀, B₀, eX, -, -⟩ := Below.pi_inv (S := setting) TowerModel.facts (TypeLe.toBelow le isPi) formed
    (IsType.refl isPi)
  have neutral : Neutral (TowerModel.roles (L := Nat)) (.var 2 : Tower.Tm 3) := .var 2
  exact (TypeEq.neutral_form (TowerModel.facts (L := Nat)) eX formed neutral
    (.inr (.inl ⟨A₀, B₀, rfl⟩))).not_former.2.1 A₀ B₀ rfl

/-- The present step refuses it. -/
theorem gapFunction_present_refused : ¬ (step setting.levels Nat).Admits gapFunctionFiring := by
  rintro ⟨⟨-, -, -, -, typed⟩, -⟩
  exact f_not_arrow (typed _ (List.mem_singleton_self _))

/-- **Decided by the kernel: the computable templating step admits it**, deciding usability between the
dependent function types `Π (y : U₀). U₀` by their codomains. -/
theorem gapFunction_decided : templatingAdmits? olderFamilies gapFunctionFiring = some true := by
  decide +kernel

/-- **The separation for a function learned by matching.** -/
theorem gapFunction_computable_separation :
    (templatingStep setting.levels Nat olderSettler).Admits gapFunctionFiring ∧
      ¬ (step setting.levels Nat).Admits gapFunctionFiring :=
  ⟨(templatingAdmits?_sound olderFamilies gapFunction_decided).mp rfl, gapFunction_present_refused⟩

/-! ## Refused: the η firing -/

/-- **Refused by the kernel**: the η firing makes `h : Π (x : U₁). U₁` at `Π (x : U₀). U₁`, and the domains
`U₁` and `U₀` cannot be equal. -/
theorem eta_refused : templatingAdmits? olderFamilies Eta.etaFiring = some false := by decide +kernel

/-- ... **in agreement with every settler's templating step** (`TemplateControls.eta_templating_refused`). -/
theorem eta_refused_computably : ¬ (templatingStep setting.levels Nat olderSettler).Admits Eta.etaFiring :=
  fun admitted => Bool.false_ne_true ((templatingAdmits?_sound olderFamilies eta_refused).mpr admitted)

/-! ## Two pattern variables typed by two earlier unknowns -/

section Two

open ContextualDependentPatternFiring.Controls (formIn termIn)

/-- `X : U₀, Y : U₀`. -/
abbrev twoBase : Context Tower.rules := extend (extend (empty Tower.rules) (smallUniverse _)) (smallUniverse _)

/-- `X`, over `X Y`. -/
def xTwo : TypeOver twoBase := formIn twoBase (.var 1) (by decide +kernel)

abbrev twoX : Context Tower.rules := extend twoBase xTwo

/-- `Y`, over `X Y x`. -/
def yTwo : TypeOver twoX := formIn twoX (.var 1) (by decide +kernel)

abbrev twoXY : Context Tower.rules := extend twoX yTwo

abbrev twoXYg : Context Tower.rules := extend twoXY (groundType _)

/-- `Ground → Ground`, over any frame. -/
def arrowTy (Γ : Context Tower.rules) : TypeOver Γ := ⟨arrow, .sort Tower.zero, .sort _, arrow_typed _⟩

/-- **The frame `X Y : U₀, x : X, y : Y, g : Ground, k : Ground → Ground`.** -/
abbrev twoFrame : Context Tower.rules := extend twoXYg (arrowTy _)

def xT : TotalTerm twoFrame :=
  termIn twoFrame (formIn twoFrame (.var 5) (by decide +kernel)) (.var 3) (by decide +kernel)

def yT : TotalTerm twoFrame :=
  termIn twoFrame (formIn twoFrame (.var 4) (by decide +kernel)) (.var 2) (by decide +kernel)

def gT : TotalTerm twoFrame := termIn twoFrame (groundType _) (.var 1) (by decide +kernel)

def kT : TotalTerm twoFrame := termIn twoFrame (arrowTy _) (.var 0) (by decide +kernel)

/-- The state `X Y : U₀` with no knowledge and no rows. -/
def twoState : State Tower.rules Nat := ⟨twoBase, [], ∅, fun _ => ⟨smallUniverse _, ⟨.var 0, Derivable.var 0⟩⟩⟩

/-- **Two pattern variables typed by two earlier unknowns**: make `x : X, y : Y, g : Ground,
k : Ground → Ground`, tell `(x : X) ≐ (g : Ground)` and `(y : Y) ≐ (k : Ground → Ground)`, and make `x` at
`Ground` and `y` at `Ground → Ground`. -/
def twoFiring : Firing setting.levels twoState where
  helpers := .cons xTwo (.cons yTwo (.cons (groundType _) (.cons (arrowTy _) (.nil _))))
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(1, ⟨groundType _, (.var 3 : Tower.Tm 6)⟩), (2, ⟨arrowTy _, (.var 2 : Tower.Tm 6)⟩)]
  tells := [(xT, gT), (yT, kT)]
  guards := []
  queries := []

/-- `x` is not of type `Ground` in its frame: its type is the variable `X`. -/
theorem xTwo_not_ground : ¬ Typed Tower.rules twoFrame.raw (.var 3) ground := by
  intro typed
  have le : TypeLe Tower.rules twoFrame.raw (.var 5) ground := Typed.generation typed
  have formed : CtxFormed Tower.rules twoFrame.raw := twoFrame.formed
  have neutral : Neutral (TowerModel.roles (L := Nat)) (.var 5 : Tower.Tm 6) := .var 5
  have equal : TypeEq Tower.rules twoFrame.raw (.var 5) ground :=
    TypeLe.rigid (S := setting) le ⟨.sort Tower.zero, .sort _, ground_typed _⟩ formed
      (fun u _ e => (TypeEq.neutral_form (TowerModel.facts (L := Nat)) e formed neutral
        (.inl ⟨u, rfl⟩)).not_former.1 u rfl)
      (fun A B e => (TypeEq.neutral_form (TowerModel.facts (L := Nat)) e formed neutral
        (.inr (.inl ⟨A, B, rfl⟩))).not_former.2.1 A B rfl)
      (fun A B e => (TypeEq.neutral_form (TowerModel.facts (L := Nat)) e formed neutral
        (.inr (.inr (.inl ⟨A, B, rfl⟩)))).not_former.2.2.1 A B rfl)
  exact (TypeEq.neutral_form (TowerModel.facts (L := Nat)) equal formed neutral
    (.inl ⟨_, rfl⟩)).not_former.1 _ rfl

/-- The present step refuses it. -/
theorem two_present_refused : ¬ (step setting.levels Nat).Admits twoFiring := by
  rintro ⟨⟨-, -, -, -, typed⟩, -⟩
  exact xTwo_not_ground (typed _ (List.mem_cons_self ..))

/-- N3's settler leaves it undecided. -/
theorem two_tower_undecided : templatingAdmits? towerFamilies twoFiring = none := by decide +kernel

/-- **Decided by the kernel: the computable templating step admits it**: both type unknowns are solved in
place, and both rows are typed by their inferred templates. -/
theorem two_decided : templatingAdmits? olderFamilies twoFiring = some true := by decide +kernel

/-- **The separation for two older unknowns.** -/
theorem two_computable_separation :
    (templatingStep setting.levels Nat olderSettler).Admits twoFiring ∧
      ¬ (step setting.levels Nat).Admits twoFiring :=
  ⟨(templatingAdmits?_sound olderFamilies two_decided).mp rfl, two_present_refused⟩

end Two

/-! ## D2's coerce firing -/

/-- **The computable templating step admits D2's coerce firing.** -/
theorem coerce_templating_decided :
    templatingAdmits? olderFamilies ProgrammingOnTheStep.Refinement.coerceFiring = some true := by
  decide +kernel

end NativeTypesOnTheStep.TemplateInference.Controls

#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gap_tower_undecided
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gap_older_settled
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gap_decided
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gap_admitted
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gap_present_refused
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gap_computable_separation
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gap_typedAfterMatch_computably
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gapGround_decided
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gapGround_refused
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gap_app_synth
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.groundRow_not_typed_at_answer
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gapGround_not_typedAfterMatch
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.f_not_arrow
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gapFunction_present_refused
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gapFunction_decided
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.gapFunction_computable_separation
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.eta_refused
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.eta_refused_computably
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.xTwo_not_ground
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.two_present_refused
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.two_tower_undecided
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.two_decided
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.two_computable_separation
#print axioms NativeTypesOnTheStep.TemplateInference.Controls.coerce_templating_decided

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
