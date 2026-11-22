import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbMeet

/-!
# Flex-rigid equations without the chain: narrowing to greatest lower bounds

The flex-rigid solver of `FlexRigidSolver` needs the declared universes to form a chain: in `X ≐ t` with `X : U_u`,
a misfit unknown `Y : U_w` of `t` (`w` not below `u`) is declared again at `U_u`, which needs `u ≤ w`. Without the
chain, `u` and `w` may be incomparable, as two level variables are. Every solution still sends `Y` to a type of
`U_w` equal to a type of `U_u` (`misfit_forced`), hence, by the least universe of its normal form, to a type of
`U_g` for a greatest lower bound `g` of `u` and `w` (`glb_misfit_forced`, from `small_of_glb`).

* **Lowering to several targets** (`lowerTo`): each chosen declaration declared again at its own universe.
* **Narrow to greatest lower bounds and solve** (`glbNarrowSolveUpdate`, `glbNarrowSolve_exact`): every misfit unknown
  `Y : U_w` of `t` declared again at `U_{glb u w}`, and `X := t`. When `u ≤ w`, `glb u w` is `u` up to the order.
* **The fragment without the chain** (`InFlexRigidGlb`): every declaration is a universe; every equation is a
  flex-rigid equation of a universe unknown and an arrow code; the heads have computed types; the left unknowns are
  distinct. It contains the fragment with the chain (`inFlexRigidGlb_of_chain`).
* **Decided** (`flexRigidGlb_decided`), when every two universes have a greatest lower bound (`total`): the chain
  is dropped.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Lowering to several targets -/

section Lowering

/-- The telescope with every declaration `i` with `target i = some g` replaced by the universe `g`. -/
def lowerTo : {n : Nat} → Ctx Head n → (Fin n → Option Head) → Ctx Head n
  | _, .nil, _ => .nil
  | _, .snoc Γ A, target =>
      .snoc (lowerTo Γ (fun i => target i.succ)) (match target 0 with
        | some g => .head g
        | none => A)

theorem lookup_lowerTo_some : ∀ {n : Nat} (Γ : Ctx Head n) (target : Fin n → Option Head) (i : Fin n) {g : Head},
    target i = some g → Ctx.lookup (lowerTo Γ target) i = .head g := by
  intro n Γ
  induction Γ with
  | nil => intro _ i; exact i.elim0
  | snoc Γ A ih =>
      intro target i g found
      cases i using Fin.cases with
      | zero =>
          simp only [lowerTo, Ctx.lookup_snoc_zero, found]
          rfl
      | succ i =>
          simp only [lowerTo, Ctx.lookup_snoc_succ]
          rw [ih (fun j => target j.succ) i found]
          rfl

theorem lookup_lowerTo_none : ∀ {n : Nat} (Γ : Ctx Head n) (target : Fin n → Option Head) (i : Fin n),
    target i = none → Ctx.lookup (lowerTo Γ target) i = Ctx.lookup Γ i := by
  intro n Γ
  induction Γ with
  | nil => intro _ i; exact i.elim0
  | snoc Γ A ih =>
      intro target i absent
      cases i using Fin.cases with
      | zero => simp only [lowerTo, Ctx.lookup_snoc_zero, absent]
      | succ i =>
          simp only [lowerTo, Ctx.lookup_snoc_succ]
          rw [ih (fun j => target j.succ) i absent]

variable {R : Rules Head}

theorem lowerTo_narrows : ∀ {n : Nat} (Γ : Ctx Head n) (target : Fin n → Option Head),
    (∀ i g, target i = some g → ∃ w, Ctx.lookup Γ i = .head w ∧ R.cumulative g w) →
    CtxNarrows R Γ (lowerTo Γ target) := by
  intro n Γ
  induction Γ with
  | nil => intro _ _; exact .nil
  | snoc Γ A ih =>
      intro target lowerable
      have inner := ih (fun i => target i.succ) (fun i g found => by
        obtain ⟨w, hw, c⟩ := lowerable i.succ g found
        rw [Ctx.lookup_snoc_succ] at hw
        exact ⟨w, rename_wk_inj (hw.trans rfl), c⟩)
      simp only [lowerTo]
      split
      · rename_i g found
        obtain ⟨w, hw, c⟩ := lowerable 0 g found
        rw [Ctx.lookup_snoc_zero] at hw
        have same : A = .head w := rename_wk_inj (hw.trans rfl)
        subst same
        exact .lower inner c
      · exact .same A inner

end Lowering

section LoweringFormed

variable {S : Setting Head L}

theorem lowerTo_formed : ∀ {n : Nat} (Γ : Ctx Head n) (target : Fin n → Option Head),
    (∀ i g, target i = some g → S.R.isUniverse g) → CtxFormed S.R Γ →
    (∀ i g, target i = some g → ∃ w, Ctx.lookup Γ i = .head w ∧ S.R.cumulative g w) →
    CtxFormed S.R (lowerTo Γ target) := by
  intro n Γ
  induction Γ with
  | nil => intro _ _ _ _; exact .nil
  | snoc Γ A ih =>
      intro target universes formed lowerable
      cases formed with
      | snoc formedΓ typeA =>
          have lowerable' : ∀ i g, target i.succ = some g → ∃ w, Ctx.lookup Γ i = .head w ∧ S.R.cumulative g w := by
            intro i g found
            obtain ⟨w, hw, c⟩ := lowerable i.succ g found
            rw [Ctx.lookup_snoc_succ] at hw
            exact ⟨w, rename_wk_inj (hw.trans rfl), c⟩
          have inner := ih (fun i => target i.succ) (fun i g found => universes i.succ g found) formedΓ lowerable'
          simp only [lowerTo]
          split
          · rename_i g found
            exact inner.snoc (IsType.head_of_universe (universes 0 g found))
          · exact inner.snoc (isType_narrow (lowerTo_narrows Γ (fun i => target i.succ) lowerable') typeA)

end LoweringFormed

/-! ## Narrow to greatest lower bounds and solve -/

section Rule

variable {S : Setting Head L} [DecidableRel S.R.cumulative]
variable (glb : Head → Head → Option Head)

/-- **The target of each unknown**: a misfit unknown of `t`, declared at `U_w`, goes to `glb u w`. -/
def glbTarget {n : Nat} (Γ : Ctx Head n) (u : Head) (t : Tm Head n) (i : Fin n) : Option Head :=
  if misfitSet (S := S) Γ u t i = true then (declaredUniverse Γ i).bind (glb u) else none

theorem glbTarget_some {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} {i : Fin n} {g : Head}
    (found : glbTarget (S := S) glb Γ u t i = some g) :
    misfitSet (S := S) Γ u t i = true ∧ ∃ w, Ctx.lookup Γ i = .head w ∧ glb u w = some g := by
  unfold glbTarget at found
  by_cases misfit : misfitSet (S := S) Γ u t i = true
  · rw [if_pos misfit] at found
    refine ⟨misfit, ?_⟩
    cases hd : declaredUniverse Γ i with
    | none => rw [hd] at found; cases found
    | some w =>
        rw [hd] at found
        exact ⟨w, headOf_sound hd, found⟩
  · rw [if_neg misfit] at found
    cases found

theorem glbTarget_none_of_fit {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} {i : Fin n}
    (fit : misfitSet (S := S) Γ u t i = false) : glbTarget (S := S) glb Γ u t i = none := by
  unfold glbTarget
  rw [if_neg (by rw [fit]; decide)]

theorem glbTarget_of_misfit {n : Nat} {Γ : Ctx Head n} {u w g : Head} {t : Tm Head n} {i : Fin n}
    (misfit : misfitSet (S := S) Γ u t i = true) (declared : Ctx.lookup Γ i = .head w) (found : glb u w = some g) :
    glbTarget (S := S) glb Γ u t i = some g := by
  unfold glbTarget declaredUniverse
  rw [if_pos misfit, declared]
  exact found

/-- **The conditions of narrowing to greatest lower bounds and solving** on a read equation: no occurrence of `X`,
heads typed below `u`, every declaration a universe, and a greatest lower bound with `u` for every misfit unknown. -/
structure GlbSolvable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) : Prop where
  absent : v.X ∉ domainVars e.2.2.code
  heads : ∀ h ∈ arrowHeads e.2.2.code, ∃ k, S.R.headTyping h k ∧ S.R.cumulative k v.u
  universes : AllUniverseDecls Θ
  meets : ∀ i, misfitSet (S := S) Θ.raw v.u e.2.2.code i = true → ∀ w, Ctx.lookup Θ.raw i = .head w →
    ∃ g, glb v.u w = some g

variable (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

include spec in
theorem glbTarget_universe {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} :
    ∀ i g, glbTarget (S := S) glb Γ u t i = some g → S.R.isUniverse g := by
  intro i g found
  obtain ⟨_, _, _, hg⟩ := glbTarget_some glb found
  exact (spec hg).1

include spec in
theorem glbTarget_lowerable {n : Nat} {Γ : Ctx Head n} {u : Head} {t : Tm Head n} :
    ∀ i g, glbTarget (S := S) glb Γ u t i = some g → ∃ w, Ctx.lookup Γ i = .head w ∧ S.R.cumulative g w := by
  intro i g found
  obtain ⟨_, w, hw, hg⟩ := glbTarget_some glb found
  exact ⟨w, hw, (spec hg).2.2.1⟩

/-- **The telescope with the misfit unknowns lowered to their greatest lower bounds with `u`.** -/
abbrev glbNarrowed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) : Context S.R where
  arity := Θ.arity
  raw := lowerTo Θ.raw (glbTarget (S := S) glb Θ.raw v.u e.2.2.code)
  formed := lowerTo_formed Θ.raw _ (glbTarget_universe glb spec) Θ.formed (glbTarget_lowerable glb spec)

theorem glbNarrowed_narrows {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) :
    CtxNarrows S.R Θ.raw (glbNarrowed glb spec v).raw :=
  lowerTo_narrows Θ.raw _ (glbTarget_lowerable glb spec)

/-- **The right side is a type of `U_u` over the narrowed telescope.** -/
theorem glbNarrowed_typed (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexArrow e) (ok : GlbSolvable glb v) :
    Typed S.R (glbNarrowed glb spec v).raw e.2.2.code (.head v.u) := by
  refine arrow_typed algebra v.universe_u v.arrow (glbNarrowed glb spec v).formed ?_ ok.heads
  intro Y member
  cases misfit : misfitSet (S := S) Θ.raw v.u e.2.2.code Y with
  | true =>
      obtain ⟨w, hw, _⟩ := ok.universes Y
      obtain ⟨g, hg⟩ := ok.meets Y misfit w hw
      exact ⟨g, lookup_lowerTo_some Θ.raw _ Y (glbTarget_of_misfit glb misfit hw hg), (spec hg).2.1⟩
  | false =>
      obtain ⟨w, hw, _⟩ := ok.universes Y
      exact ⟨w, (lookup_lowerTo_none Θ.raw _ Y (glbTarget_none_of_fit glb misfit)).trans hw,
        misfitSet_out hw misfit member⟩

/-- **`X := t` is a typed substitution from the narrowed telescope.** -/
theorem glbNarrowSolve_typed (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexArrow e) (ok : GlbSolvable glb v) :
    SubstMor S.R Θ.raw (glbNarrowed glb spec v).raw (solveSub v.X e.2.2.code) := by
  intro i
  obtain ⟨w, hw, _⟩ := ok.universes i
  rw [hw]
  change Typed S.R _ (solveSub v.X e.2.2.code i) (.head w)
  by_cases h : i = v.X
  · rw [h, solveSub_self]
    have same : w = v.u := by
      rw [h] at hw
      exact Tm.head.inj (hw.symm.trans v.declared)
    rw [same]
    exact glbNarrowed_typed glb spec algebra v ok
  · rw [solveSub_ne _ h]
    have moved := (glbNarrowed_narrows glb spec v).substMor i
    rw [subst_ids, hw] at moved
    exact moved

/-- **The answer `X := t`**, from the narrowed telescope. -/
def glbNarrowSolve (algebra : CumulativeAlgebra S.R) {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    (v : FlexArrow e) (ok : GlbSolvable glb v) : glbNarrowed glb spec v ⟶ Θ where
  substitution := solveSub v.X e.2.2.code
  typed := glbNarrowSolve_typed glb spec algebra v ok

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

omit [DecidableRel S.R.cumulative] in
include facts roots heads algebra rigid complete headTypingUnique in
/-- **What the equation forces of a misfit unknown, at a greatest lower bound**: every solution sends it to a type
equal, at its own universe, to a type of `U_g`. -/
theorem glb_misfit_forced {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (σ : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves σ e) {Y : Fin Θ.arity} (member : Y ∈ domainVars e.2.2.code) {w g : Head}
    (declared : Ctx.lookup Θ.raw Y = .head w) (universe_w : S.R.isUniverse w) (glbYes : IsGlb S.R g v.u w) :
    ∃ N, Typed S.R Δ.raw N (.head g) ∧ Equal S.R Δ.raw (σ.substitution Y) N (.head w) := by
  obtain ⟨small, tSmall, eSmall⟩ := misfit_forced facts roots heads algebra rigid complete v σ solved member
  have tY : Typed S.R Δ.raw (σ.substitution Y) (.head w) := by
    have typed := σ.typed Y
    rw [declared] at typed
    exact typed
  exact small_of_glb facts roots heads algebra rigid complete headTypingUnique v.universe_u universe_w universe_w
    glbYes (NarrowsBelow.refl g Δ.raw) Δ.formed Δ.formed tY tSmall tY eSmall ⟨w, universe_w, .refl tY⟩

/-- **Narrow to greatest lower bounds and solve**: the misfit unknowns declared again at their greatest lower bounds
with `U_u`, and `X := t`; the solved equation is removed and the rest of the store is instantiated. -/
def glbNarrowSolveUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (ok : GlbSolvable glb v)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := glbNarrowed glb spec v
  answer := glbNarrowSolve glb spec algebra v ok
  remaining := (frames S.levels).applyStore (glbNarrowSolve glb spec algebra v ok) rest
  sound := by
    intro Δ g solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · apply e_of_codes
      · change Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.1.1.code =
          Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.2.1.code
        rw [v.annotation_left, v.annotation_right]
      · change Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.1.2.code =
          Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.2.2.code
        have fixed : Presentation.subst (subComp g.substitution (solveSub v.X e'.2.2.code)) e'.2.2.code =
            Presentation.subst g.substitution e'.2.2.code := by
          change Presentation.subst (fun i => Presentation.subst g.substitution (solveSub v.X e'.2.2.code i))
            e'.2.2.code = _
          rw [← subst_comp, subst_solveSub_fixed _ v.arrow ok.absent]
        rw [fixed, v.side_left]
        change Presentation.subst g.substitution (solveSub v.X e'.2.2.code v.X) = _
        rw [solveSub_self]
    · exact (Frames.models_applyStore (X := frames S.levels) _ g rest).mp solved e' member
  complete := by
    intro Δ f solved
    have equation := solved e List.mem_cons_self
    let chosen := misfitSet (S := S) Θ.raw v.u e.2.2.code
    have smallOf : ∀ i, chosen i = true → ∃ N,
        (∀ g, glbTarget (S := S) glb Θ.raw v.u e.2.2.code i = some g → Typed S.R Δ.raw N (.head g)) ∧
          Equal S.R Δ.raw (f.substitution i) N (Presentation.subst f.substitution (Ctx.lookup Θ.raw i)) := by
      intro i inside
      obtain ⟨w, hw, uw⟩ := ok.universes i
      obtain ⟨g, hg⟩ := ok.meets i inside w hw
      obtain ⟨N, tN, eN⟩ := glb_misfit_forced facts roots heads algebra rigid complete headTypingUnique v f equation
        (misfitSet_mem inside) hw uw (spec hg)
      refine ⟨N, fun g' found => ?_, ?_⟩
      · rw [glbTarget_of_misfit glb inside hw hg] at found
        rw [← Option.some.inj found]
        exact tN
      · rw [hw]
        exact eN
    let value : Sub Head Θ.arity Δ.arity := fun i =>
      if inside : chosen i = true then Classical.choose (smallOf i inside) else f.substitution i
    have valueIn : ∀ i (inside : chosen i = true), value i = Classical.choose (smallOf i inside) :=
      fun i inside => dif_pos inside
    have valueOut : ∀ i, chosen i = false → value i = f.substitution i := by
      intro i outside
      have notIn : ¬ chosen i = true := by rw [outside]; decide
      exact dif_neg notIn
    -- The value agrees with the solution.
    have same : SubstEq S.R Θ.raw Δ.raw f.substitution value := by
      refine ⟨f.typed, fun i => ?_⟩
      cases inside : chosen i with
      | true =>
          rw [valueIn i inside]
          exact (Classical.choose_spec (smallOf i inside)).2
      | false =>
          rw [valueOut i inside]
          exact .refl (f.typed i)
    -- The value is a solution over the narrowed telescope.
    have typed : SubstMor S.R (lowerTo Θ.raw (glbTarget (S := S) glb Θ.raw v.u e.2.2.code)) Δ.raw value := by
      intro i
      cases inside : chosen i with
      | true =>
          obtain ⟨w, hw, _⟩ := ok.universes i
          obtain ⟨g, hg⟩ := ok.meets i inside w hw
          have found := glbTarget_of_misfit glb inside hw hg
          rw [lookup_lowerTo_some Θ.raw _ i found, valueIn i inside]
          exact (Classical.choose_spec (smallOf i inside)).1 g found
      | false =>
          rw [lookup_lowerTo_none Θ.raw _ i (glbTarget_none_of_fit glb inside), valueOut i inside]
          obtain ⟨w, hw, _⟩ := ok.universes i
          have tF := f.typed i
          rw [hw] at tF ⊢
          exact tF
    let g : Δ ⟶ glbNarrowed glb spec v := ⟨value, typed⟩
    -- The solution factors through the answer.
    have factored : homTypedEquality S.R f (g ≫ glbNarrowSolve glb spec algebra v ok) := by
      refine ⟨f.typed, fun i => ?_⟩
      change Equal S.R Δ.raw (f.substitution i) (Presentation.subst value (solveSub v.X e.2.2.code i))
        (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
      by_cases h : i = v.X
      · rw [h, solveSub_self, v.declared]
        have eq := ((equivalent_iff S.levels _ _).mp equation).2
        change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
          (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at eq
        rw [v.side_left, v.annotation_left] at eq
        have tRight : Typed S.R Θ.raw e.2.2.code (.head v.v) := by
          have typed := e.2.2.typed
          rw [v.annotation_right] at typed
          exact typed
        have functional := Typed.functional tRight same
        have atV : Equal S.R Δ.raw (f.substitution v.X) (Presentation.subst value e.2.2.code) (.head v.v) :=
          eq.trans functional
        have tX : Typed S.R Δ.raw (f.substitution v.X) (.head v.u) := by
          have t := f.typed v.X
          rw [v.declared] at t
          exact t
        have tValue : Typed S.R Δ.raw (Presentation.subst value e.2.2.code) (.head v.u) := by
          have moved := (glbNarrowed_typed glb spec algebra v ok).substitute typed
          exact moved
        exact universe_injective facts roots heads algebra rigid complete Δ.formed v.universe_u v.universe_v
          tX tValue atV
      · rw [solveSub_ne _ h]
        exact same.2 i
    refine ⟨g, ?_, act_equal_of_substEq S.levels factored⟩
    apply (Frames.models_applyStore (X := frames S.levels) _ g rest).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels factored) rest).mp
      (fun e' member => solved e' (List.mem_cons_of_mem _ member))

include facts roots heads algebra rigid complete headTypingUnique in
/-- **Narrowing to greatest lower bounds and solving is exact.** -/
theorem glbNarrowSolve_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e)
    (ok : GlbSolvable glb v) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (glbNarrowSolve glb spec algebra v ok)
      ((frames S.levels).applyStore (glbNarrowSolve glb spec algebra v ok) rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨glbNarrowSolveUpdate glb spec facts roots heads algebra rigid complete headTypingUnique v ok rest, rfl, rfl, rfl⟩

end Rule

/-! ## The fragment without the chain -/

section Fragment

variable {S : Setting Head L}

/-- **The fragment of flex-rigid stores without the chain.** -/
structure InFlexRigidGlb (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) : Prop where
  universes : AllUniverseDecls Θ
  shapes : ∀ e ∈ problem, Nonempty (FlexArrow e)
  typedHeads : ∀ e ∈ problem, ∀ h ∈ arrowHeads e.2.2.code, (choices.typing h).isSome = true
  distinct : problem.Pairwise (fun e₁ e₂ => ∀ (v₁ : FlexArrow e₁) (v₂ : FlexArrow e₂), v₁.X ≠ v₂.X)

/-- **The fragment with the chain lies inside.** -/
theorem inFlexRigidGlb_of_chain {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (inside : InFlexRigid choices problem) : InFlexRigidGlb choices problem :=
  ⟨inside.universes, inside.shapes, inside.typedHeads, inside.distinct⟩

theorem inFlexRigidGlb_delete {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InFlexRigidGlb choices (e :: rest)) :
    InFlexRigidGlb choices rest :=
  ⟨inside.universes, fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    fun e' member => inside.typedHeads e' (List.mem_cons_of_mem _ member), (List.pairwise_cons.mp inside.distinct).2⟩

variable [DecidableRel S.R.cumulative] (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b) (algebra : CumulativeAlgebra S.R)

/-- The declaration of an unknown after narrowing: a greatest lower bound where it was a misfit, unchanged
otherwise. -/
theorem glbNarrowed_lookup {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (i : Fin Θ.arity) :
    (∃ g, Ctx.lookup (glbNarrowed glb spec v).raw i = .head g ∧ S.R.isUniverse g) ∨
      Ctx.lookup (glbNarrowed glb spec v).raw i = Ctx.lookup Θ.raw i := by
  cases found : glbTarget (S := S) glb Θ.raw v.u e.2.2.code i with
  | some g => exact Or.inl ⟨g, lookup_lowerTo_some Θ.raw _ i found, glbTarget_universe glb spec i g found⟩
  | none => exact Or.inr (lookup_lowerTo_none Θ.raw _ i found)

/-- **The view of an equation after narrowing and solving.** -/
theorem glbNarrowSolve_view {Θ : Context S.R} {e e' : Equation (TotalTerm Θ)} (v : FlexArrow e)
    (ok : GlbSolvable glb v) (w : FlexArrow e') (ne : w.X ≠ v.X) :
    ∃ t : FlexArrow (((frames S.levels).act (glbNarrowSolve glb spec algebra v ok) e'.1,
        (frames S.levels).act (glbNarrowSolve glb spec algebra v ok) e'.2) :
          Equation (TotalTerm (glbNarrowed glb spec v))), t.X = w.X := by
  have declared : ∃ u', Ctx.lookup (glbNarrowed glb spec v).raw w.X = .head u' ∧ S.R.isUniverse u' := by
    rcases glbNarrowed_lookup glb spec v w.X with low | same
    · exact low
    · exact ⟨w.u, same.trans w.declared, w.universe_u⟩
  obtain ⟨u', hu', uu'⟩ := declared
  exact ⟨{
    v := w.v
    X := w.X
    u := u'
    annotation_left := by
      change Presentation.subst (solveSub v.X e.2.2.code) e'.1.1.code = .head w.v
      rw [w.annotation_left]
      rfl
    annotation_right := by
      change Presentation.subst (solveSub v.X e.2.2.code) e'.2.1.code = .head w.v
      rw [w.annotation_right]
      rfl
    side_left := by
      change Presentation.subst (solveSub v.X e.2.2.code) e'.1.2.code = .var w.X
      rw [w.side_left]
      exact solveSub_ne _ ne
    declared := hu'
    universe_u := uu'
    universe_v := w.universe_v
    arrow := arrow_subst_solve v.arrow w.arrow }, rfl⟩

/-- **Narrowing to greatest lower bounds and solving keeps the fragment.** -/
theorem inFlexRigidGlb_narrowSolve {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InFlexRigidGlb choices (e :: rest))
    (v : FlexArrow e) (ok : GlbSolvable glb v) :
    InFlexRigidGlb choices ((frames S.levels).applyStore (glbNarrowSolve glb spec algebra v ok) rest) := by
  have tail := List.pairwise_cons.mp inside.distinct
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rcases glbNarrowed_lookup glb spec v i with low | same
    · exact low
    · obtain ⟨w, hw, uw⟩ := inside.universes i
      exact ⟨w, same.trans hw, uw⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    obtain ⟨t, _⟩ := glbNarrowSolve_view glb spec algebra v ok w (fun same => tail.1 e' inRest v w same.symm)
    exact ⟨t⟩
  · intro e'' member h hh
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    rcases arrowHeads_subst_solve w.arrow h hh with fromE' | fromE
    · exact inside.typedHeads e' (List.mem_cons_of_mem _ inRest) h fromE'
    · exact inside.typedHeads e List.mem_cons_self h fromE
  · refine List.pairwise_map.mpr (tail.2.imp_of_mem ?_)
    intro e₁ e₂ m₁ m₂ apart t₁ t₂
    obtain ⟨w₁⟩ := inside.shapes e₁ (List.mem_cons_of_mem _ m₁)
    obtain ⟨w₂⟩ := inside.shapes e₂ (List.mem_cons_of_mem _ m₂)
    obtain ⟨s₁, h₁⟩ := glbNarrowSolve_view glb spec algebra v ok w₁ (fun same => tail.1 e₁ m₁ v w₁ same.symm)
    obtain ⟨s₂, h₂⟩ := glbNarrowSolve_view glb spec algebra v ok w₂ (fun same => tail.1 e₂ m₂ v w₂ same.symm)
    rw [FlexArrow.unique t₁ s₁, FlexArrow.unique t₂ s₂, h₁, h₂]
    exact apart w₁ w₂

end Fragment

/-! ## The solver -/

section Solver

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R) (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- A fitting unknown, or a misfit unknown with a greatest lower bound with `u`. -/
def meetsPred {n : Nat} (Γ : Ctx Head n) (u : Head) (t : Tm Head n) (i : Fin n) : Bool :=
  !(misfitSet (S := S) Γ u t i) || (glbTarget (S := S) glb Γ u t i).isSome

/-- **The conditions of narrowing to greatest lower bounds and solving, decided.** -/
def glbSolvableB {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) : Bool :=
  (arrowHeads e.2.2.code).all (fitPred choices v.u) &&
    (List.finRange Θ.arity).all (meetsPred (S := S) glb Θ.raw v.u e.2.2.code) && allUniverseDeclsB Θ

omit [DecidableEq Head] in
theorem glbSolvable_of_B {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e)
    (h : glbSolvableB choices glb v = true) (absent : v.X ∉ domainVars e.2.2.code) : GlbSolvable glb v := by
  simp only [glbSolvableB, Bool.and_eq_true] at h
  obtain ⟨⟨hHeads, hMeets⟩, hAll⟩ := h
  refine ⟨absent, ?_, allUniverseDecls_of_B hAll, ?_⟩
  · intro h member
    have fit := List.all_eq_true.mp hHeads h member
    unfold fitPred at fit
    cases hk : choices.typing h with
    | none => rw [hk] at fit; cases fit
    | some k =>
        rw [hk] at fit
        exact ⟨k.1, k.2, of_decide_eq_true fit⟩
  · intro i misfit w hw
    have m := List.all_eq_true.mp hMeets i (List.mem_finRange i)
    unfold meetsPred at m
    rw [misfit] at m
    simp only [Bool.not_true, Bool.false_or] at m
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp m
    obtain ⟨_, w', hw', found⟩ := glbTarget_some glb hg
    have same : w' = w := Tm.head.inj (hw'.symm.trans hw)
    rw [same] at found
    exact ⟨g, found⟩

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- **One step on a read equation**: delete, refute by occurs or misfit, narrow to greatest lower bounds and solve,
or stuck. -/
def stepFlexRigidGlb {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels storeRank (e :: rest) :=
  if hdel : e.2.2.code = .var v.X then
    .progress (deleteCodes e (v.annotation_left.trans v.annotation_right.symm) (v.side_left.trans hdel.symm) rest)
      (below_of_length (by
        show rest.length < (e :: rest).length
        simp))
  else if hocc : v.X ∈ domainVars e.2.2.code then
    .refuted (occurs_refutes facts roots heads algebra rigid complete v hocc hdel rest)
  else match hmis : (arrowHeads e.2.2.code).find? (misfitPred choices v.u) with
    | some h₀ =>
        .refuted (misfit_refutes facts roots heads algebra rigid complete v (List.mem_of_find?_eq_some hmis)
          (misfit_apart choices headTypingUnique (List.find?_some hmis)) rest)
    | none =>
        if hok : glbSolvableB choices glb v = true then
          .progress (glbNarrowSolveUpdate glb spec facts roots heads algebra rigid complete headTypingUnique v
              (glbSolvable_of_B choices glb v hok hocc) rest)
            (below_of_length (by
              show ((frames S.levels).applyStore _ rest).length < (e :: rest).length
              simp [Frames.applyStore]))
        else .stuck

/-- **The round of the solver**: read the first equation, then step. -/
def flexRigidGlbRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) →
    Round S.levels storeRank problem
  | _, [] => .stuck
  | _, e :: rest =>
      match hd : readFlexArrow e with
      | some _ => stepFlexRigidGlb choices glb spec facts roots heads algebra rigid complete headTypingUnique
          (viewOfArrow hd) rest
      | none => .stuck

/-- **The tree's driver on flex-rigid stores, narrowing to greatest lower bounds.** -/
def flexRigidGlbSolver : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := flexRigidGlbRound choices glb spec facts roots heads algebra rigid complete headTypingUnique

variable (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include total in
/-- **Progress by shape**: on a nonempty store of the fragment, the round is not stuck. -/
theorem flexRigidGlbRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InFlexRigidGlb choices problem) (nonempty : problem ≠ []) :
    flexRigidGlbRound choices glb spec facts roots heads algebra rigid complete headTypingUnique problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      have hd := readFlexArrow_complete v
      simp only [flexRigidGlbRound]
      split
      · rename_i d hd'
        unfold stepFlexRigidGlb
        by_cases hdel : e.2.2.code = .var (viewOfArrow hd').X
        · rw [dif_pos hdel]
          intro h; cases h
        · rw [dif_neg hdel]
          by_cases hocc : (viewOfArrow hd').X ∈ domainVars e.2.2.code
          · rw [dif_pos hocc]
            intro h; cases h
          · rw [dif_neg hocc]
            split
            · intro h; cases h
            · rename_i hmis
              -- the conditions hold in the fragment
              have ok : glbSolvableB choices glb (viewOfArrow hd') = true := by
                simp only [glbSolvableB, Bool.and_eq_true]
                refine ⟨⟨?_, ?_⟩, allUniverseDeclsB_of inside.universes⟩
                · apply List.all_eq_true.mpr
                  intro h member
                  have typed := inside.typedHeads e List.mem_cons_self h member
                  have notMisfit := List.find?_eq_none.mp hmis h member
                  unfold fitPred
                  unfold misfitPred at notMisfit
                  cases hk : choices.typing h with
                  | none => rw [hk] at typed; cases typed
                  | some k =>
                      rw [hk] at notMisfit
                      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_not] at notMisfit
                      exact decide_eq_true notMisfit
                · apply List.all_eq_true.mpr
                  intro i _
                  unfold meetsPred
                  cases misfit : misfitSet (S := S) Γ.raw (viewOfArrow hd').u e.2.2.code i with
                  | false => rfl
                  | true =>
                      obtain ⟨w, hw, uw⟩ := inside.universes i
                      obtain ⟨g, hg⟩ := total (viewOfArrow hd').universe_u uw
                      rw [glbTarget_of_misfit glb misfit hw hg]
                      rfl
              rw [dif_pos ok]
              intro h; cases h
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem flexRigidGlbRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InFlexRigidGlb choices problem)
    (progressed : flexRigidGlbRound choices glb spec facts roots heads algebra rigid complete headTypingUnique
      problem = .progress update smaller) :
    InFlexRigidGlb choices update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [flexRigidGlbRound] at progressed
      split at progressed
      · rename_i d hd
        unfold stepFlexRigidGlb at progressed
        by_cases hdel : e.2.2.code = .var (viewOfArrow hd).X
        · rw [dif_pos hdel] at progressed
          cases progressed
          exact inFlexRigidGlb_delete inside
        · rw [dif_neg hdel] at progressed
          by_cases hocc : (viewOfArrow hd).X ∈ domainVars e.2.2.code
          · rw [dif_pos hocc] at progressed
            cases progressed
          · rw [dif_neg hocc] at progressed
            split at progressed
            · cases progressed
            · by_cases hok : glbSolvableB choices glb (viewOfArrow hd) = true
              · rw [dif_pos hok] at progressed
                cases progressed
                exact inFlexRigidGlb_narrowSolve glb spec algebra inside (viewOfArrow hd) _
              · rw [dif_neg hok] at progressed
                cases progressed
      · cases progressed

/-- **The fragment of the solver.** -/
def flexRigidGlbFragment :
    ContextualDependentWorklist.Fragment
      (flexRigidGlbSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique) where
  holds := InFlexRigidGlb choices
  stable := fun inside progressed =>
    flexRigidGlbRound_stable choices glb spec facts roots heads algebra rigid complete headTypingUnique inside
      progressed
  decisive := fun inside nonempty =>
    flexRigidGlbRound_ne_stuck choices glb spec facts roots heads algebra rigid complete headTypingUnique total inside
      nonempty

include total in
/-- **Decided by shape, without the chain**: on the fragment, the tree's driver with narrowing to greatest lower
bounds, solving and the two refutations reaches, at some budget and at every larger one, a principal answer or a
certified refutation. -/
theorem flexRigidGlb_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InFlexRigidGlb choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (flexRigidGlbSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique) original
          larger =
        run (flexRigidGlbSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique) original
          fuel ∧
        ((∃ state finished,
              run (flexRigidGlbSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique)
                  original larger = .solved state finished ∧
                (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (flexRigidGlbSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique)
              original larger = .refuted absent)) :=
  (flexRigidGlbFragment choices glb spec facts roots heads algebra rigid complete headTypingUnique total).decided
    inside

end Solver

/-! ## Membership, decided -/

section Membership

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
variable (choices : ExecutableChecking.HeadChoices S.R)

/-- **Membership in the fragment without the chain, decided.** -/
def inFlexRigidGlbB {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  allUniverseDeclsB Θ && problem.all (fun e => (readFlexArrow e).isSome) &&
    problem.all (fun e => (arrowHeads e.2.2.code).all fun h => (choices.typing h).isSome) &&
    (problem.map leftOf).Nodup

theorem inFlexRigidGlb_of_B {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inFlexRigidGlbB choices problem = true) : InFlexRigidGlb choices problem := by
  simp only [inFlexRigidGlbB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hAll, hShapes⟩, hHeads⟩, hNodup⟩ := h
  refine ⟨allUniverseDecls_of_B hAll, fun e member => ?_, fun e member h hh => ?_, ?_⟩
  · have he := List.all_eq_true.mp hShapes e member
    cases hd : readFlexArrow e with
    | none => rw [hd] at he; cases he
    | some d => exact ⟨viewOfArrow hd⟩
  · exact List.all_eq_true.mp (List.all_eq_true.mp hHeads e member) h hh
  · have pairwise := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp hNodup)
    refine pairwise.imp ?_
    intro e₁ e₂ different v₁ v₂ same
    apply different
    unfold leftOf
    rw [v₁.side_left, v₂.side_left, same]

end Membership

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
