import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinControls

/-!
# The glb join's condition is needed, with incomparable codomains

The store `X : U_a → U_a`, `Y : U0 → U_b`, with `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U_{max a b}`, in the tree's tower.
Its one position is usable on both sides (`U_a` below `U_a`, `U0` below `U_b`) and fails the condition: `U_a` is not
below `U_b`.

* **It is solvable**, by the identities and by the constant families at the ground type (`ctr_two_answers`).
* **It has no principal answer** (`ctr_no_principal`). An answer sends `X` to some `bX` and `Y` to some `bY` that agree
  at a local of `U0`. The normal form of `bX x` there is a type of `U_a` and of `U_b`, hence of their greatest lower
  bound `U0`, so `bX` agrees at a local of `U0` with a family `λ x. N` of `U0 → U0`. The identity and the constant
  family both factor through the answer, so `bX` has an instance equal to the identity of `U_a → U_a` and one equal to
  the constant family; no family of `U_a → U_a` that agrees with one of `U0 → U0` at a local of `U0` has both
  (`no_common_answer`).
* **It lies just outside the glb-join fragment, whose solver is stuck on it** (`ctr_not_inside`, `ctr_stuck`).

So the condition is not an artifact of comparable codomains: with incomparable codomains a usable position that fails
it leaves a solvable store without a principal answer. The cross store (`cross_not_glbJoin_inside`) is the comparable
instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-! ## The store -/

/-- `U_a → U_a`, over no unknown. -/
def ctrX : TypeOver (empty setting.R) := formIn (empty setting.R) (.pi (.head Ua) (.head Ua)) (by decide +kernel)
abbrev ctxCtr1 := extend (empty setting.R) ctrX
/-- `U0 → U_b`, over `X`. -/
def ctrY : TypeOver ctxCtr1 := formIn ctxCtr1 (.pi (.head U0) (.head Ub)) (by decide +kernel)
/-- `X : U_a → U_a, Y : U0 → U_b`. -/
abbrev ctxCtr := extend ctxCtr1 ctrY
/-- `Π (x : U0). U_{max a b}`, over `X Y`. -/
def ctrType : TypeOver ctxCtr := formIn ctxCtr (.pi (.head U0) (.head Uab)) (by decide +kernel)

/-- `λ x. X x ≐ λ x. Y x` at `Π (x : U0). U_{max a b}`. -/
def ctrEquation : Equation (TotalTerm ctxCtr) :=
  (termIn ctxCtr ctrType (.lam (.app (.var 2) (.var 0))) (by decide +kernel),
    termIn ctxCtr ctrType (.lam (.app (.var 1) (.var 0))) (by decide +kernel))

def ctrStore : EquationStore (TotalTerm ctxCtr) := [ctrEquation]

theorem ctrAnnotation_code : ctrEquation.1.1.code = famCode [U0] Uab := by decide +kernel
theorem ctrLeft_code : ctrEquation.1.2.code = etaExp 1 (.var (1 : Fin ctxCtr.arity)) := by decide +kernel
theorem ctrRight_code : ctrEquation.2.2.code = etaExp 1 (.var (0 : Fin ctxCtr.arity)) := by decide +kernel
theorem ctrX_declared : Ctx.lookup ctxCtr.raw 1 = famCode [Ua] Ua := by decide +kernel
theorem ctrY_declared : Ctx.lookup ctxCtr.raw 0 = famCode [U0] Ub := by decide +kernel

/-- **The position is usable on both sides and fails the condition.** -/
theorem ctr_usable_fails : setting.R.cumulative Ua Ua ∧ setting.R.cumulative U0 Ub ∧ ¬ setting.R.cumulative Ua Ub ∧
    ¬ CrossAt setting.R Ua Ub Ua U0 := by
  decide +kernel

/-- `X := λ x. x, Y := λ x. x`. -/
def ctrIdentity : empty setting.R ⟶ ctxCtr :=
  Elimination.instantiate (empty setting.R) (termIn (empty setting.R) ctrX (.lam (.var 0)) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxCtr1 (termIn ctxCtr1 ctrY (.lam (.var 0)) (by decide +kernel)).2

/-- `X := λ x. G, Y := λ x. G`, for the ground type `G`. -/
def ctrConstant : empty setting.R ⟶ ctxCtr :=
  Elimination.instantiate (empty setting.R)
      (termIn (empty setting.R) ctrX (.lam (.head .legacyGround)) (by decide +kernel)).2 ≫
    Elimination.instantiate ctxCtr1 (termIn ctxCtr1 ctrY (.lam (.head .legacyGround)) (by decide +kernel)).2

/-- **The store is solved by the identities and by the constant families.** -/
theorem ctr_two_answers : (frames setting.levels).Models ctrIdentity ctrStore ∧
    (frames setting.levels).Models ctrConstant ctrStore :=
  ⟨models_by ctrIdentity ctrEquation.1.2 ctrEquation.2.2 (by decide +kernel),
    models_by ctrConstant ctrEquation.1.2 ctrEquation.2.2 (by decide +kernel)⟩

theorem ctr_solvable : (frames setting.levels).Solvable ctrStore := ⟨_, ctrIdentity, ctr_two_answers.1⟩

/-! ## No principal answer -/

/-- `U_a → U_a`, over `X Y`: the type of `X`. -/
def ctrXWide : TypeOver ctxCtr := formIn ctxCtr (.pi (.head Ua) (.head Ua)) (by decide +kernel)

/-- The unknown `X`, as a term over `X Y`. -/
def ctrXTerm : TotalTerm ctxCtr := termIn ctxCtr ctrXWide (.var 1) (by decide +kernel)

/-- **The tower's greatest lower bound of `U_a` and `U_b` is `U0`.** -/
theorem ctr_glb : IsGlb setting.R U0 Ua Ub := LevelGlb.towerGlb_isGlb towerGlb_Ua_Ub

/-- **The store has no principal answer.** -/
theorem ctr_no_principal {Δ : Context setting.R} (answer : Δ ⟶ ctxCtr) :
    ¬ (frames setting.levels).Principal ctrStore answer := by
  intro principal
  have xCode : ctrX.code = .pi (.head Ua) (.head Ua) := formIn_code _ _ _
  have yCode : ctrY.code = .pi (.head U0) (.head Ub) := formIn_code _ _ _
  have typeCode : ctrEquation.1.1.code = .pi (.head U0) (.head Uab) := formIn_code _ _ _
  have wideCode : ctrXWide.code = .pi (.head Ua) (.head Ua) := formIn_code _ _ _
  -- The declared types of the two components of the answer.
  have tX := answer.typed (⟨1, Nat.one_lt_two⟩ : Fin 2)
  change Typed setting.R Δ.raw (answer.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2))
    (subst answer.substitution (Presentation.rename wk (Presentation.rename wk ctrX.code))) at tX
  rw [xCode] at tX
  have tX' : Typed setting.R Δ.raw (answer.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2)) (famCode [Ua] Ua) := tX
  have tY := answer.typed (⟨0, Nat.zero_lt_two⟩ : Fin 2)
  change Typed setting.R Δ.raw (answer.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2))
    (subst answer.substitution (Presentation.rename wk ctrY.code)) at tY
  rw [yCode] at tY
  have tY' : Typed setting.R Δ.raw (answer.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2)) (famCode [U0] Ub) := tY
  -- The answer solves the store: the two values agree at a local of `U0`.
  have held := principal.sound ctrEquation List.mem_cons_self
  rw [ContextualDependentRigidFormers.solves_raw] at held
  obtain ⟨_, equal⟩ := held
  rw [typeCode] at equal
  have agree : Equal setting.R (.snoc Δ.raw (.head U0))
      (.app (Presentation.rename wk (answer.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2))) (.var 0))
      (.app (Presentation.rename wk (answer.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2))) (.var 0)) (.head Uab) :=
    ContextualDependentUniverseInjective.equal_of_lam (S := setting) TowerModel.facts Δ.formed equal
  -- The value of `X` at a local of `U0` is a type of `U_a` and of `U_b`, hence equal to one of `U0`.
  have formedN : CtxFormed setting.R (.snoc Δ.raw (.head U0)) :=
    Δ.formed.snoc (IsType.head_of_universe (by decide +kernel))
  have sX : Typed setting.R (.snoc Δ.raw (.head U0))
      (.app (Presentation.rename wk (answer.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2))) (.var 0)) (.head Ua) :=
    open_typed tX' (Derivable.cumul (var_head_typed Δ.raw U0) (by decide +kernel))
  have sY : Typed setting.R (.snoc Δ.raw (.head U0))
      (.app (Presentation.rename wk (answer.substitution (⟨0, Nat.zero_lt_two⟩ : Fin 2))) (.var 0)) (.head Ub) :=
    open_typed tY' (var_head_typed Δ.raw U0)
  obtain ⟨N, tN, eN⟩ := small_of_glb TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentNormalCheckingTower.head_typing_unique (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ctr_glb (NarrowsBelow.refl U0 _) formedN formedN sX sX sY ⟨Ua, by decide +kernel, .refl sX⟩
    ⟨Uab, by decide +kernel, agree.symm⟩
  -- The family `λ x. N` of `U0 → U0`, agreeing with `X`'s value at a local of `U0`.
  obtain ⟨u, hu, tPi⟩ := famCode_isType [U0] (fun _ member => (List.mem_singleton.mp member) ▸ (by decide +kernel))
    (show setting.R.isUniverse U0 by decide +kernel) Δ.formed
  have tPi' : Typed setting.R Δ.raw (.pi (.head U0) (.head U0)) (.head u) := tPi
  have tLam : Typed setting.R Δ.raw (.lam N) (.pi (.head U0) (.head U0)) := Derivable.lamIntro tPi' hu tN
  have beta := beta_open_below tPi' hu tN (setting.levels.cumulative_refl (by decide +kernel))
  have agree' : Equal setting.R (.snoc Δ.raw (.head U0)) (.app (Presentation.rename wk (.lam N)) (.var 0))
      (.app (Presentation.rename wk (answer.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2))) (.var 0)) (.head Ua) :=
    (Derivable.cumulEq beta (by decide +kernel)).trans eN.symm
  -- The two solutions factor through the answer.
  obtain ⟨ρ₁, factor₁⟩ := principal.factors _ ctrIdentity ctr_two_answers.1
  obtain ⟨ρ₂, factor₂⟩ := principal.factors _ ctrConstant ctr_two_answers.2
  have identity := (factor₁ ctrXTerm).2
  change Equal setting.R (empty setting.R).raw (ctrIdentity.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2))
    (subst ρ₁.substitution (answer.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2)))
    (subst ctrIdentity.substitution ctrXWide.code) at identity
  rw [wideCode, show ctrIdentity.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2) = .lam (.var 0) from by
    decide +kernel] at identity
  have constant := (factor₂ ctrXTerm).2
  change Equal setting.R (empty setting.R).raw (ctrConstant.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2))
    (subst ρ₂.substitution (answer.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2)))
    (subst ctrConstant.substitution ctrXWide.code) at constant
  rw [wideCode, show ctrConstant.substitution (⟨1, Nat.one_lt_two⟩ : Fin 2) = .lam (.head .legacyGround) from by
    decide +kernel] at constant
  exact ContextualDependentUniverseInjective.no_common_answer (S := setting) TowerModel.facts TowerModel.roots
    TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    (fun _ => rfl) Δ.formed (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) tLam tX'
    agree' (empty setting.R).formed ρ₁.typed identity (empty setting.R).formed ρ₂.typed constant

/-! ## Just outside the fragment -/

/-- **It lies outside the glb-join fragment.** -/
theorem ctr_not_inside : ¬ InGlbJoinFragmentK ctrStore := by
  intro inside
  obtain ⟨group, grouped, compat⟩ := inside.grouped
  obtain ⟨v⟩ := inside.shapes ctrEquation List.mem_cons_self
  have together := grouped ctrEquation List.mem_cons_self v
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans ctrAnnotation_code)
  have sl := v.side_left.symm.trans ctrLeft_code
  have sr := v.side_right.symm.trans ctrRight_code
  rw [hps] at sl sr
  have hl : v.left = 1 := Tm.var.inj (etaExp_inj _ sl)
  have hr : v.right = 0 := Tm.var.inj (etaExp_inj _ sr)
  have dl : Ctx.lookup ctxCtr.raw v.left = famCode [Ua] Ua := by rw [hl]; exact ctrX_declared
  have dr : Ctx.lookup ctxCtr.raw v.right = famCode [U0] Ub := by rw [hr]; exact ctrY_declared
  have different : v.left ≠ v.right := by rw [hl, hr]; decide
  have crossing := compat v.left v.right different together [Ua] Ua [U0] Ub dl dr rfl
  cases crossing with
  | cons here _ => exact ctr_usable_fails.2.2.2 here

/-- **The glb-join solver is stuck on it.** -/
theorem ctr_stuck : isStuck (run glbJoinTowerSolver ctrStore 1) = true := by decide +kernel

/-- **The condition is needed with incomparable codomains**: a store just outside, solvable, without a principal
answer. -/
theorem crossAt_needed : ¬ InGlbJoinFragmentK ctrStore ∧ (frames setting.levels).Solvable ctrStore ∧
    ∀ {Δ : Context setting.R} (answer : Δ ⟶ ctxCtr), ¬ (frames setting.levels).Principal ctrStore answer :=
  ⟨ctr_not_inside, ctr_solvable, fun answer => ctr_no_principal answer⟩

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
