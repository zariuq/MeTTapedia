import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerCodes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Renaming

/-!
# Taking codes apart breaks normalization

A trusted rule that takes a quantified code apart, `pred (all f) ⟶ f`, makes
`prop` a retract of `prop → prop`. Codes then interpret the untyped λ-calculus,
with `all` as abstraction and `pred` as application. The code

`Ω = pred ω ω` with `ω = all (λx. pred x x)`

has type `prop` and reduces to itself in two steps: the destructor takes `ω`
apart, and β applies the function inside it to `ω` again. So the package with a
code destructor has a typed term that is not strongly normalizing.

The package of codes itself has no such rule: its decoding steps unfold the
decoder applied to a code into a type, and nothing takes a code apart. The
counterexample uses only the quantifier over codes and the destructor. Its
typing uses only the constants' declared types, abstraction and application,
with no conversion.

A recursor on codes into a universe defines the destructor, with motive
`λ_. prop → prop` and the method at `all f` returning `f`. The same loop
follows (`recursor_not_normalizing`); its typing converts only by the motive's
β-step.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Hazards

open Normalization StrongNormalization

/-- The destructor `d` of the quantifier `a`: `d (a f) ⟶ f`. -/
inductive DestructorStep (d a : DeclName) : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop where
  | mk {n : Nat} (f : Tower.Tm n) :
      DestructorStep d a (.app (.const d) (.app (.const a) f)) f

theorem DestructorStep.rename {d a : DeclName} {n m : Nat} (ρ : Ren n m) {l r : Tower.Tm n}
    (step : DestructorStep d a l r) :
    DestructorStep d a (Presentation.rename ρ l) (Presentation.rename ρ r) := by
  cases step with
  | mk f => exact .mk _

theorem DestructorStep.substitute {d a : DeclName} {n m : Nat} (σ : Sub Tower.Head n m)
    {l r : Tower.Tm n} (step : DestructorStep d a l r) :
    DestructorStep d a (Presentation.subst σ l) (Presentation.subst σ r) := by
  cases step with
  | mk f => exact .mk _

/-- The destructor as a root computation. -/
def destructorComputation (d a : DeclName) : RootComputation Tower.Head where
  step := DestructorStep d a
  rename := by
    intro n m ρ l r step
    exact step.rename ρ
  substitute := by
    intro n m σ l r step
    exact step.substitute σ

/-! ## The smallest package with a destructor -/

/-- Codes with one quantifier, over codes. -/
def codes : Codes Tower.Head where
  proofs := .sort Tower.zero
  prop := `hazard.prop
  holds := `hazard.holds
  imp := `hazard.imp
  quantifiers := fun name => [(`hazard.all, .const `hazard.prop)].lookup name
  equations := fun _ => none
  identity := false

/-- The destructor's name. -/
def predName : DeclName := `hazard.pred

/-- The quantifier's name. -/
def allName : DeclName := `hazard.all

/-- The destructor's steps occur at spines of the destructor of exact arity one, whose
argument, a quantified code, is canonical. -/
theorem destructor_spine {roles : Roles Tower.Head}
    (pred : roles predName = .computes 1 (.split 0 .constructor fun _ => .leaf)) (all : roles allName = .constructor 1) :
    SpineShaped roles (destructorComputation predName allName) := by
  intro n t u step
  cases step with
  | mk =>
      exact ⟨predName, 1, _, [.app (.const allName) _], pred, rfl, rfl,
        InspectTree.accepts_single.mpr ⟨_, rfl, .inr ⟨allName, 1, [_], all, rfl⟩⟩⟩

theorem destructor_deterministic : Deterministic (destructorComputation predName allName) := by
  intro n t u u' step step'
  cases step
  cases step'
  rfl

theorem destructor_reflectsRename :
    RootReflectsRename (destructorComputation predName allName) := by
  intro n m ρ t w step
  change DestructorStep predName allName (Presentation.rename ρ t) w at step
  generalize hs : Presentation.rename ρ t = s at step
  cases step with
  | mk =>
      obtain ⟨h, c, rfl, hh, hc⟩ := rename_eq_app hs
      obtain rfl := rename_eq_const hh
      obtain ⟨g, f', rfl, hg, rfl⟩ := rename_eq_app hc
      obtain rfl := rename_eq_const hg
      exact ⟨f', .mk f', rfl⟩

/-- `pred : prop → prop → prop`: the function inside a quantified code. -/
def predType : Tower.Tm 0 := .pi codes.propT (.pi codes.propT codes.propT)

/-- The package of codes over the tower, with the destructor declared and
computing. -/
def withDestructor : Rules Tower.Head :=
  { codes.extend Tower.rules with
    constantType := fun c =>
      if c = predName then some predType else (codes.extend Tower.rules).constantType c
    computation := RootComputation.union (codes.extend Tower.rules).computation
      (destructorComputation predName allName) }

/-- `ω = all (λx. pred x x)`. -/
def omega {n : Nat} : Tower.Tm n :=
  .app (.const allName) (.lam (.app (.app (.const predName) (.var 0)) (.var 0)))

/-- `Ω = pred ω ω`. -/
def Omega {n : Nat} : Tower.Tm n := .app (.app (.const predName) omega) omega

/-! ## Ω reduces to itself -/

/-- The destructor takes `ω` apart. -/
theorem Omega_step_destructor {n : Nat} :
    StrongNormalization.Reduces withDestructor (Omega : Tower.Tm n)
      (.app (.lam (.app (.app (.const predName) (.var 0)) (.var 0))) omega) :=
  .congAppFun (.root (.inr (DestructorStep.mk _)))

/-- β applies the function inside `ω` to `ω`. -/
theorem Omega_step_beta {n : Nat} :
    StrongNormalization.Reduces withDestructor
      (.app (.lam (.app (.app (.const predName) (.var 0)) (.var 0))) (omega : Tower.Tm n))
      Omega :=
  .betaPi _ _

/-- A term on a reduction cycle is not strongly normalizing. -/
theorem not_sn_of_cycle {R : Rules Tower.Head} {n : Nat} {t u : Tower.Tm n}
    (forward : StrongNormalization.Reduces R t u)
    (back : StrongNormalization.Reduces R u t) : ¬ SN R t := by
  intro sn
  have key : ∀ x, SN R x → x = t ∨ x = u → False := by
    intro x sx
    induction sx with
    | intro x _ ih =>
        rintro (rfl | rfl)
        · exact ih _ forward (.inr rfl)
        · exact ih _ back (.inl rfl)
  exact key t sn (.inl rfl)

/-- `Ω` is not strongly normalizing. -/
theorem Omega_not_sn {n : Nat} : ¬ SN withDestructor (Omega : Tower.Tm n) :=
  not_sn_of_cycle Omega_step_destructor Omega_step_beta

/-! ## Ω is a code -/

section Typing

open Tower

abbrev R₀ : Rules Tower.Head := withDestructor

theorem prop_ne_pred : (`hazard.prop : DeclName) ≠ predName := by decide
theorem all_ne_pred : allName ≠ predName := by decide

theorem constantType_pred : R₀.constantType predName = some predType := by
  simp [R₀, withDestructor]

theorem constantType_prop : R₀.constantType `hazard.prop = some U0 := by
  simp only [R₀, withDestructor, if_neg prop_ne_pred]
  exact codes.extend_constantType_of_code Tower.rules (by simp [codes, Codes.codeType])

theorem constantType_all : R₀.constantType allName = some (codes.allType codes.propT) := by
  simp only [R₀, withDestructor, if_neg all_ne_pred]
  refine codes.extend_constantType_of_code Tower.rules ?_
  exact codes.codeType_all (by decide) (by rfl)

/-- The lowest universe is a type of the next one. -/
theorem U0_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₀ Γ (U0 : Tower.Tm n) (.head (.sort (.succ Tower.zero))) :=
  .headType (HeadTyping.sort _)

/-- `prop` is a type in the lowest universe. -/
theorem prop_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₀ Γ (codes.propT : Tower.Tm n) U0 :=
  .const constantType_prop U0_typed (IsUniverse.sort _)

/-- `prop → prop` is a type. -/
theorem propArrow_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₀ Γ (.pi codes.propT codes.propT : Tower.Tm n)
      (.head (.sort (.max Tower.zero Tower.zero))) :=
  .piForm prop_typed (IsUniverse.sort _) prop_typed (IsUniverse.sort _) (Join.sorts _ _)

theorem allType_typed :
    Typed R₀ .nil (codes.allType codes.propT)
      (.head (.sort (.max (.max Tower.zero Tower.zero) Tower.zero))) :=
  .piForm propArrow_typed (IsUniverse.sort _) prop_typed (IsUniverse.sort _) (Join.sorts _ _)

theorem predType_typed :
    Typed R₀ .nil predType (.head (.sort (.max Tower.zero (.max Tower.zero Tower.zero)))) :=
  .piForm prop_typed (IsUniverse.sort _) propArrow_typed (IsUniverse.sort _) (Join.sorts _ _)

theorem pred_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₀ Γ (.const predName : Tower.Tm n) (.pi codes.propT (.pi codes.propT codes.propT)) :=
  .const constantType_pred predType_typed (IsUniverse.sort _)

theorem all_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₀ Γ (.const allName : Tower.Tm n) (.pi (.pi codes.propT codes.propT) codes.propT) :=
  .const constantType_all allType_typed (IsUniverse.sort _)

/-- `pred a b : prop` for codes `a` and `b`. -/
theorem pred_app_typed {n : Nat} {Γ : Tower.Ctx n} {a b : Tower.Tm n}
    (ha : Typed R₀ Γ a codes.propT) (hb : Typed R₀ Γ b codes.propT) :
    Typed R₀ Γ (.app (.app (.const predName) a) b) codes.propT :=
  .appElim (.appElim pred_typed ha) hb

/-- `λx. pred x x : prop → prop`. -/
theorem selfApp_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₀ Γ (.lam (.app (.app (.const predName) (.var 0)) (.var 0)) : Tower.Tm n)
      (.pi codes.propT codes.propT) :=
  .lamIntro propArrow_typed (IsUniverse.sort _) (pred_app_typed (.var 0) (.var 0))

/-- `ω : prop`. -/
theorem omega_typed {n : Nat} {Γ : Tower.Ctx n} : Typed R₀ Γ (omega : Tower.Tm n) codes.propT :=
  .appElim all_typed selfApp_typed

/-- `Ω : prop`: the looping term is a code of the package with a destructor. -/
theorem Omega_typed {n : Nat} {Γ : Tower.Ctx n} : Typed R₀ Γ (Omega : Tower.Tm n) codes.propT :=
  pred_app_typed omega_typed omega_typed

/-- The package with a code destructor has a typed code that is not strongly
normalizing. -/
theorem destructor_not_normalizing :
    ∃ t : Tower.Tm 0, Typed withDestructor .nil t codes.propT ∧ ¬ SN withDestructor t :=
  ⟨Omega, Omega_typed, Omega_not_sn⟩

end Typing

/-! ## A recursor on codes breaks normalization too

Hazard 2: an eliminator on `prop` into a universe. From a recursor with
motive `λ_. prop → prop`, whose method at a quantified code returns the
function inside it, the destructor is an ordinary term, and the same loop
follows. -/

/-- The recursor on codes. -/
def recName : DeclName := `hazard.propRec

/-- The recursor's steps at the two code constructors:
`rec P mi ma (all f) ⟶ ma f (λx. rec P mi ma (f x))` and
`rec P mi ma (imp p q) ⟶ mi p q (rec P mi ma p) (rec P mi ma q)`. -/
inductive RecStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop where
  | all {n : Nat} (P mi ma f : Tower.Tm n) :
      RecStep (appSpine (.const recName) [P, mi, ma, .app (.const allName) f])
        (.app (.app ma f)
          (.lam (appSpine (.const recName)
            [Presentation.rename wk P, Presentation.rename wk mi, Presentation.rename wk ma,
              .app (Presentation.rename wk f) (.var 0)])))
  | imp {n : Nat} (P mi ma p q : Tower.Tm n) :
      RecStep (appSpine (.const recName) [P, mi, ma, codes.impOf p q])
        (appSpine mi [p, q, appSpine (.const recName) [P, mi, ma, p],
          appSpine (.const recName) [P, mi, ma, q]])

theorem RecStep.rename {n m : Nat} (ρ : Ren n m) {l r : Tower.Tm n} (step : RecStep l r) :
    RecStep (Presentation.rename ρ l) (Presentation.rename ρ r) := by
  cases step with
  | all P mi ma f =>
      have decoded := RecStep.all (Presentation.rename ρ P) (Presentation.rename ρ mi)
        (Presentation.rename ρ ma) (Presentation.rename ρ f)
      have zero : liftRen ρ 0 = 0 := rfl
      simpa only [rename_appSpine, List.map, Presentation.rename, rename_liftRen_wk, zero]
        using decoded
  | imp P mi ma p q =>
      have decoded := RecStep.imp (Presentation.rename ρ P) (Presentation.rename ρ mi)
        (Presentation.rename ρ ma) (Presentation.rename ρ p) (Presentation.rename ρ q)
      simpa only [rename_appSpine, List.map, Presentation.rename] using decoded

theorem RecStep.substitute {n m : Nat} (σ : Sub Tower.Head n m) {l r : Tower.Tm n}
    (step : RecStep l r) : RecStep (Presentation.subst σ l) (Presentation.subst σ r) := by
  cases step with
  | all P mi ma f =>
      have decoded := RecStep.all (Presentation.subst σ P) (Presentation.subst σ mi)
        (Presentation.subst σ ma) (Presentation.subst σ f)
      have zero : liftSub σ 0 = .var 0 := rfl
      simpa only [subst_appSpine, List.map, Presentation.subst, subst_liftSub_wk, zero]
        using decoded
  | imp P mi ma p q =>
      have decoded := RecStep.imp (Presentation.subst σ P) (Presentation.subst σ mi)
        (Presentation.subst σ ma) (Presentation.subst σ p) (Presentation.subst σ q)
      simpa only [subst_appSpine, List.map, Presentation.subst] using decoded

/-- The recursor's steps as a root computation. -/
def recComputation : RootComputation Tower.Head where
  step := RecStep
  rename := by
    intro n m ρ l r step
    exact step.rename ρ
  substitute := by
    intro n m σ l r step
    exact step.substitute σ

/-- The package of codes with the recursor declared and computing (its type
is stated with its typing below). -/
def withRecursor (recType : Tower.Tm 0) : Rules Tower.Head :=
  { codes.extend Tower.rules with
    constantType := fun c =>
      if c = recName then some recType else (codes.extend Tower.rules).constantType c
    computation := RootComputation.union (codes.extend Tower.rules).computation recComputation }

/-- The motive `λ_. prop → prop`. -/
def motive {n : Nat} : Tower.Tm n := .lam (.pi codes.propT codes.propT)

/-- The method at implication, `λ p q _ _. λy. y`. -/
def impCase {n : Nat} : Tower.Tm n := .lam (.lam (.lam (.lam (.lam (.var 0)))))

/-- The method at a quantified code, `λ f _. f`: the function inside. -/
def allCase {n : Nat} : Tower.Tm n := .lam (.lam (.var 1))

/-- The destructor defined from the recursor. -/
def predDerived {n : Nat} : Tower.Tm n :=
  .lam (appSpine (.const recName) [motive, impCase, allCase, .var 0])

/-- The self-application code body `λx. pred' x x`. -/
def selfAppDerived {n : Nat} : Tower.Tm n :=
  .lam (.app (.app predDerived (.var 0)) (.var 0))

/-- `ω' = all (λx. pred' x x)`. -/
def omegaDerived {n : Nat} : Tower.Tm n := .app (.const allName) selfAppDerived

/-- `Ω' = pred' ω' ω'`. -/
def OmegaDerived {n : Nat} : Tower.Tm n := .app (.app predDerived omegaDerived) omegaDerived

/-- A term on a reduction cycle of any positive length is not strongly
normalizing. -/
theorem not_sn_of_transGen_cycle {R : Rules Tower.Head} {n : Nat} {t : Tower.Tm n}
    (cycle : Relation.TransGen (StrongNormalization.Reduces R) t t) : ¬ SN R t := by
  have key : ∀ x : Tower.Tm n, SN R x →
      Relation.TransGen (StrongNormalization.Reduces R) x x → False := by
    intro x sx
    induction sx with
    | intro x _ ih =>
        intro loop
        obtain ⟨y, step, rest⟩ := Relation.TransGen.head'_iff.mp loop
        exact ih y step (Relation.TransGen.tail' rest step)
  exact fun sn => key t sn cycle

theorem OmegaDerived_cycle (recType : Tower.Tm 0) {n : Nat} :
    Relation.TransGen (StrongNormalization.Reduces (withRecursor recType))
      (OmegaDerived : Tower.Tm n) OmegaDerived := by
  -- β: the derived destructor meets its first argument.
  have s1 : StrongNormalization.Reduces (withRecursor recType) (OmegaDerived : Tower.Tm n)
      (.app (appSpine (.const recName) [motive, impCase, allCase, omegaDerived]) omegaDerived) :=
    .congAppFun (.betaPi _ _)
  -- ι: the recursor at a quantified code.
  have s2 : StrongNormalization.Reduces (withRecursor recType)
      (.app (appSpine (.const recName) [motive, impCase, allCase, omegaDerived])
        (omegaDerived : Tower.Tm n))
      (.app (.app (.app allCase selfAppDerived)
          (.lam (appSpine (.const recName)
            [Presentation.rename wk motive, Presentation.rename wk impCase,
              Presentation.rename wk allCase,
              .app (Presentation.rename wk selfAppDerived) (.var 0)])))
        omegaDerived) :=
    .congAppFun (.root (.inr (RecStep.all _ _ _ _)))
  -- β twice: the method returns the function inside.
  have s3 : StrongNormalization.Reduces (withRecursor recType)
      (.app (.app (.app allCase selfAppDerived)
          (.lam (appSpine (.const recName)
            [Presentation.rename wk motive, Presentation.rename wk impCase,
              Presentation.rename wk allCase,
              .app (Presentation.rename wk selfAppDerived) (.var 0)])))
        (omegaDerived : Tower.Tm n))
      (.app (.app (.lam (Presentation.rename wk selfAppDerived))
          (.lam (appSpine (.const recName)
            [Presentation.rename wk motive, Presentation.rename wk impCase,
              Presentation.rename wk allCase,
              .app (Presentation.rename wk selfAppDerived) (.var 0)])))
        omegaDerived) :=
    .congAppFun (.congAppFun (.betaPi _ _))
  have s4 : StrongNormalization.Reduces (withRecursor recType)
      (.app (.app (.lam (Presentation.rename wk selfAppDerived))
          (.lam (appSpine (.const recName)
            [Presentation.rename wk motive, Presentation.rename wk impCase,
              Presentation.rename wk allCase,
              .app (Presentation.rename wk selfAppDerived) (.var 0)])))
        (omegaDerived : Tower.Tm n))
      (.app selfAppDerived omegaDerived) := by
    have h := StepCore.congAppFun (a := (omegaDerived : Tower.Tm n))
      (StepCore.betaPi (root := (withRecursor recType).computation)
        (headEq := StrongNormalization.noHeadSteps) (Presentation.rename wk selfAppDerived)
        (.lam (appSpine (.const recName)
            [Presentation.rename wk motive, Presentation.rename wk impCase,
              Presentation.rename wk allCase,
              .app (Presentation.rename wk selfAppDerived) (.var 0)])))
    simpa only [inst0_rename_wk] using h
  -- β: the function inside `ω'` applied to `ω'` is `Ω'` again.
  have s5 : StrongNormalization.Reduces (withRecursor recType)
      (.app selfAppDerived (omegaDerived : Tower.Tm n)) OmegaDerived :=
    .betaPi _ _
  exact .tail (.tail (.tail (.tail (.single s1) s2) s3) s4) s5

/-- `Ω'` is not strongly normalizing. -/
theorem OmegaDerived_not_sn (recType : Tower.Tm 0) {n : Nat} :
    ¬ SN (withRecursor recType) (OmegaDerived : Tower.Tm n) :=
  not_sn_of_transGen_cycle (OmegaDerived_cycle recType)

/-! ### The recursor's type, and Ω' is a code -/

/-- The method type at implication, in any context extended by the motive
`P`: `Π p q. P p → P q → P (imp p q)`. -/
def miType {n : Nat} : Tower.Tm (n + 1) :=
  .pi codes.propT (.pi codes.propT (.pi (.app (.var 2) (.var 1)) (.pi (.app (.var 3) (.var 1))
    (.app (.var 4) (codes.impOf (.var 3) (.var 2))))))

/-- The method type at a quantified code, in any context extended by `P` and
the first method: `Π f. (Π x. P (f x)) → P (all f)`. -/
def maType {n : Nat} : Tower.Tm (n + 2) :=
  .pi (.pi codes.propT codes.propT)
    (.pi (.pi codes.propT (.app (.var 3) (.app (.var 1) (.var 0))))
      (.app (.var 3) (.app (.const allName) (.var 1))))

/-- The recursor's type in any context:
`Π (P : prop → U0). miType → maType → Π (c : prop). P c`. -/
def recTypeAt {n : Nat} : Tower.Tm n :=
  .pi (.pi codes.propT U0) (.pi miType (.pi maType (.pi codes.propT (.app (.var 3) (.var 0)))))

/-- The recursor's declared (closed) type. -/
def recType : Tower.Tm 0 := recTypeAt

theorem liftClosed_recType {n : Nat} : (liftClosed recType : Tower.Tm n) = recTypeAt := rfl

section RecursorTyping

open Tower Mettapedia.TypeTheory.UniverseLevel

abbrev R₁ : Rules Tower.Head := withRecursor recType

theorem rec_ne_prop : recName ≠ (`hazard.prop : DeclName) := by decide
theorem prop_ne_rec : (`hazard.prop : DeclName) ≠ recName := by decide
theorem all_ne_rec : allName ≠ recName := by decide

theorem constantType_rec₁ : R₁.constantType recName = some recType := by
  simp [R₁, withRecursor]

theorem constantType_prop₁ : R₁.constantType `hazard.prop = some U0 := by
  simp only [R₁, withRecursor, if_neg prop_ne_rec]
  exact codes.extend_constantType_of_code Tower.rules (by simp [codes, Codes.codeType])

theorem constantType_all₁ : R₁.constantType allName = some (codes.allType codes.propT) := by
  simp only [R₁, withRecursor, if_neg all_ne_rec]
  refine codes.extend_constantType_of_code Tower.rules ?_
  exact codes.codeType_all (by decide) (by rfl)

theorem prop_typed₁ {n : Nat} {Γ : Tower.Ctx n} : Typed R₁ Γ (codes.propT : Tower.Tm n) U0 :=
  .const constantType_prop₁ (.headType (HeadTyping.sort _)) (IsUniverse.sort _)

theorem propArrow_typed₁ {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₁ Γ (.pi codes.propT codes.propT : Tower.Tm n) U0 :=
  .sub (.piForm prop_typed₁ (IsUniverse.sort _) prop_typed₁ (IsUniverse.sort _) (Join.sorts _ _))
    (.subUniv fun v => by simp [LevelExpr.eval, Tower.zero])

theorem predicate_typed₁ {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₁ Γ (.pi codes.propT U0 : Tower.Tm n)
      (.head (.sort (.max Tower.zero (.succ Tower.zero)))) :=
  .piForm prop_typed₁ (IsUniverse.sort _) (.headType (HeadTyping.sort _)) (IsUniverse.sort _)
    (Join.sorts _ _)

theorem all_typed₁ {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₁ Γ (.const allName : Tower.Tm n) (.pi (.pi codes.propT codes.propT) codes.propT) :=
  .const constantType_all₁
    (.piForm propArrow_typed₁ (IsUniverse.sort _) prop_typed₁ (IsUniverse.sort _) (Join.sorts _ _))
    (IsUniverse.sort _)

theorem imp_typed₁ {n : Nat} {Γ : Tower.Ctx n} {p q : Tower.Tm n}
    (hp : Typed R₁ Γ p codes.propT) (hq : Typed R₁ Γ q codes.propT) :
    Typed R₁ Γ (codes.impOf p q) codes.propT := by
  have himp : R₁.constantType codes.imp = some codes.impType := by
    have ne : codes.imp ≠ recName := by decide
    simp only [R₁, withRecursor, if_neg ne]
    exact codes.extend_constantType_of_code Tower.rules (codes.codeType_imp (by decide))
  have formed : Typed R₁ .nil codes.impType
      (.head (.sort (.max Tower.zero (.max Tower.zero Tower.zero)))) :=
    .piForm prop_typed₁ (IsUniverse.sort _)
      (.piForm prop_typed₁ (IsUniverse.sort _) prop_typed₁ (IsUniverse.sort _) (Join.sorts _ _))
      (IsUniverse.sort _) (Join.sorts _ _)
  exact .appElim (.appElim (.const himp formed (IsUniverse.sort _)) hp) hq

/-- `P c : U0` for a predicate `P : prop → U0`. -/
theorem pred_app_U0 {n : Nat} {Γ : Tower.Ctx n} {P c : Tower.Tm n}
    (hP : Typed R₁ Γ P (.pi codes.propT U0)) (hc : Typed R₁ Γ c codes.propT) :
    Typed R₁ Γ (.app P c) U0 :=
  .appElim hP hc

/-- A type in some universe. -/
def Formed {n : Nat} (Γ : Tower.Ctx n) (A : Tower.Tm n) : Prop :=
  ∃ u, R₁.isUniverse u ∧ Typed R₁ Γ A (.head u)

theorem Formed.pi {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    (hA : Formed Γ A) (hB : Formed (.snoc Γ A) B) : Formed Γ (.pi A B) := by
  obtain ⟨u, hu, dA⟩ := hA
  obtain ⟨v, hv, dB⟩ := hB
  cases hu with
  | sort l =>
      cases hv with
      | sort r => exact ⟨_, IsUniverse.sort _, .piForm dA (IsUniverse.sort l) dB (IsUniverse.sort r)
          (Join.sorts l r)⟩

theorem Formed.of_U0 {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} (h : Typed R₁ Γ A U0) :
    Formed Γ A :=
  ⟨_, IsUniverse.sort _, h⟩

theorem Formed.typed {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    {body : Tower.Tm (n + 1)} (hPi : Formed Γ (.pi A B)) (hbody : Typed R₁ (.snoc Γ A) body B) :
    Typed R₁ Γ (.lam body) (.pi A B) := by
  obtain ⟨u, hu, d⟩ := hPi
  exact .lamIntro d hu hbody

/-- `motive = λ_. prop → prop : prop → U0`. -/
theorem motive_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₁ Γ (motive : Tower.Tm n) (.pi codes.propT U0) :=
  .lamIntro predicate_typed₁ (IsUniverse.sort _) propArrow_typed₁

/-- `motive c ≡ prop → prop`. -/
theorem motive_app_eq {n : Nat} {Γ : Tower.Ctx n} {c : Tower.Tm n}
    (hc : Typed R₁ Γ c codes.propT) :
    Equal R₁ Γ (.app motive c) (.pi codes.propT codes.propT) U0 :=
  .betaPi predicate_typed₁ (IsUniverse.sort _) propArrow_typed₁ hc

theorem toMotive {n : Nat} {Γ : Tower.Ctx n} {t c : Tower.Tm n}
    (ht : Typed R₁ Γ t (.pi codes.propT codes.propT)) (hc : Typed R₁ Γ c codes.propT) :
    Typed R₁ Γ t (.app motive c) :=
  .conv ht (.symm (motive_app_eq hc)) (IsUniverse.sort _)

theorem fromMotive {n : Nat} {Γ : Tower.Ctx n} {t c : Tower.Tm n}
    (ht : Typed R₁ Γ t (.app motive c)) (hc : Typed R₁ Γ c codes.propT) :
    Typed R₁ Γ t (.pi codes.propT codes.propT) :=
  .conv ht (motive_app_eq hc) (IsUniverse.sort _)

theorem motive_app_formed {n : Nat} {Γ : Tower.Ctx n} {c : Tower.Tm n}
    (hc : Typed R₁ Γ c codes.propT) : Formed Γ (.app motive c) :=
  .of_U0 (pred_app_U0 motive_typed hc)

/-- The implication method's type at the motive. -/
def miTypeM {n : Nat} : Tower.Tm n :=
  .pi codes.propT (.pi codes.propT (.pi (.app motive (.var 1)) (.pi (.app motive (.var 1))
    (.app motive (codes.impOf (.var 3) (.var 2))))))

/-- The quantifier method's type at the motive. -/
def maTypeM {n : Nat} : Tower.Tm n :=
  .pi (.pi codes.propT codes.propT)
    (.pi (.pi codes.propT (.app motive (.app (.var 1) (.var 0))))
      (.app motive (.app (.const allName) (.var 1))))

theorem miTypeM_formed {n : Nat} {Γ : Tower.Ctx n} : Formed Γ (miTypeM : Tower.Tm n) :=
  .pi (.of_U0 prop_typed₁) (.pi (.of_U0 prop_typed₁)
    (.pi (motive_app_formed (.var 1)) (.pi (motive_app_formed (.var 1))
      (motive_app_formed (imp_typed₁ (.var 3) (.var 2))))))

theorem maTypeM_formed {n : Nat} {Γ : Tower.Ctx n} : Formed Γ (maTypeM : Tower.Tm n) :=
  .pi (.of_U0 propArrow_typed₁)
    (.pi (.pi (.of_U0 prop_typed₁)
        (motive_app_formed (.appElim (B := codes.propT) (.var 1) (.var 0))))
      (motive_app_formed (.appElim all_typed₁ (.var 1))))

/-- `λ p q _ _. λy. y` at the implication method's type. -/
theorem impCase_typed {n : Nat} {Γ : Tower.Ctx n} : Typed R₁ Γ (impCase : Tower.Tm n) miTypeM := by
  refine Formed.typed miTypeM_formed ?_
  refine Formed.typed (.pi (.of_U0 prop_typed₁) (.pi (motive_app_formed (.var 1))
    (.pi (motive_app_formed (.var 1)) (motive_app_formed (imp_typed₁ (.var 3) (.var 2)))))) ?_
  refine Formed.typed (.pi (motive_app_formed (.var 1))
    (.pi (motive_app_formed (.var 1)) (motive_app_formed (imp_typed₁ (.var 3) (.var 2))))) ?_
  refine Formed.typed (.pi (motive_app_formed (.var 1))
    (motive_app_formed (imp_typed₁ (.var 3) (.var 2)))) ?_
  exact toMotive (Formed.typed (.of_U0 propArrow_typed₁) (.var 0)) (imp_typed₁ (.var 3) (.var 2))

/-- `λ f _. f` at the quantifier method's type. -/
theorem allCase_typed {n : Nat} {Γ : Tower.Ctx n} : Typed R₁ Γ (allCase : Tower.Tm n) maTypeM := by
  refine Formed.typed maTypeM_formed ?_
  refine Formed.typed (.pi (.pi (.of_U0 prop_typed₁)
      (motive_app_formed (.appElim (B := codes.propT) (.var 1) (.var 0))))
    (motive_app_formed (.appElim all_typed₁ (.var 1)))) ?_
  exact toMotive (.var 1) (.appElim all_typed₁ (.var 1))

theorem recType_formed : Formed .nil recType :=
  .pi ⟨_, IsUniverse.sort _, predicate_typed₁⟩
    (.pi (.pi (.of_U0 prop_typed₁) (.pi (.of_U0 prop_typed₁)
        (.pi (.of_U0 (pred_app_U0 (.var 2) (.var 1))) (.pi (.of_U0 (pred_app_U0 (.var 3) (.var 1)))
          (.of_U0 (pred_app_U0 (.var 4) (imp_typed₁ (.var 3) (.var 2))))))))
      (.pi (.pi (.of_U0 propArrow_typed₁)
          (.pi (.pi (.of_U0 prop_typed₁)
              (.of_U0 (pred_app_U0 (.var 3) (.appElim (B := codes.propT) (.var 1) (.var 0)))))
            (.of_U0 (pred_app_U0 (.var 3) (.appElim all_typed₁ (.var 1))))))
        (.pi (.of_U0 prop_typed₁) (.of_U0 (pred_app_U0 (.var 3) (.var 0))))))

theorem rec_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₁ Γ (.const recName : Tower.Tm n) recTypeAt := by
  obtain ⟨u, hu, d⟩ := recType_formed
  have h := Derivable.const (Γ := Γ) constantType_rec₁ d hu
  rwa [liftClosed_recType] at h

/-- The recursor at the motive and both methods, applied to a code, is a
function on codes. -/
theorem rec_applied_typed {n : Nat} {Γ : Tower.Ctx n} {c : Tower.Tm n}
    (hc : Typed R₁ Γ c codes.propT) :
    Typed R₁ Γ (appSpine (.const recName) [motive, impCase, allCase, c])
      (.pi codes.propT codes.propT) := by
  have h1 : Typed R₁ Γ (.app (.const recName) motive)
      (.pi miTypeM (.pi maTypeM (.pi codes.propT (.app motive (.var 0))))) :=
    .appElim rec_typed motive_typed
  have h2 : Typed R₁ Γ (.app (.app (.const recName) motive) impCase)
      (.pi maTypeM (.pi codes.propT (.app motive (.var 0)))) :=
    .appElim h1 impCase_typed
  have h3 : Typed R₁ Γ (.app (.app (.app (.const recName) motive) impCase) allCase)
      (.pi codes.propT (.app motive (.var 0))) :=
    .appElim h2 allCase_typed
  have h4 : Typed R₁ Γ (appSpine (.const recName) [motive, impCase, allCase, c]) (.app motive c) :=
    .appElim h3 hc
  exact fromMotive h4 hc

/-- The derived destructor `pred' : prop → prop → prop`. -/
theorem predDerived_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₁ Γ (predDerived : Tower.Tm n) (.pi codes.propT (.pi codes.propT codes.propT)) :=
  Formed.typed (.pi (.of_U0 prop_typed₁) (.of_U0 propArrow_typed₁)) (rec_applied_typed (.var 0))

theorem selfAppDerived_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₁ Γ (selfAppDerived : Tower.Tm n) (.pi codes.propT codes.propT) :=
  Formed.typed (.of_U0 propArrow_typed₁)
    (.appElim (B := codes.propT) (.appElim predDerived_typed (.var 0)) (.var 0))

theorem omegaDerived_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₁ Γ (omegaDerived : Tower.Tm n) codes.propT :=
  .appElim all_typed₁ selfAppDerived_typed

/-- `Ω' : prop`. -/
theorem OmegaDerived_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed R₁ Γ (OmegaDerived : Tower.Tm n) codes.propT :=
  .appElim (B := codes.propT) (.appElim predDerived_typed omegaDerived_typed) omegaDerived_typed

/-- The package with a recursor on codes into a universe has a typed code that
is not strongly normalizing. -/
theorem recursor_not_normalizing :
    ∃ t : Tower.Tm 0, Typed (withRecursor recType) .nil t codes.propT ∧
      ¬ SN (withRecursor recType) t :=
  ⟨OmegaDerived, OmegaDerived_typed, OmegaDerived_not_sn recType⟩

end RecursorTyping

end Hazards
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
