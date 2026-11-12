import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Families
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeHeads

/-!
# Domain raising in the tree's fibre: the meet of two views when one of them is the meet

In `λ x. G x ≐ λ x. F x` at `Π (x : U_p). U_q`, with `G : Π (x : U_{pG}). U_{cG}` and `F : Π (x : U_{pF}). U_{cF}`,
every solution sends `G` and `F` to families that agree on arguments of `U_p`. When `F` **fits** `G`, that is `F`
takes every argument `G` takes (`pG ≤ pF`) and its values lie in `G`'s codomain (`cF ≤ cG`), the meet of the two
views is `F`'s own, and the answer `G := λ x. F x` raises `G`'s domain to `F`'s and keeps `F`'s codomain.

* **What the equation forces** (`raise_forced`): every solution sends `G` to `λ x. F x`, at `G`'s declaration.
  The equation opens under its binder at `U_p` (`equal_of_lam_left` and a β-step at the fresh variable); the tree's
  context widening (`ContextualDependentCumulative.equal_of_narrows`) carries the opened equality from `x : U_p` to
  `x : U_{pG}`, where both openings are typed; there it holds at `U_{cG}` (`universe_injective`), and η gives it at
  `G`'s declaration.
* **The rule** (`raiseUpdate`, `raise_exact`): `G := λ x. F x` as an update of the tree's driver, hence exact.

Unlike inversion, the answer is an abstraction, not an unknown: the domains differ, and the tree's subtyping relates
function types over equal domains only.
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

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A unary flex-flex equation where `F` fits `G`**: `λ x. G x ≐ λ x. F x` at `Π (x : U_p). U_q`, with
`p ≤ pG ≤ pF` and `cF ≤ cG ≤ q`. -/
structure FitsView {Θ : Context S.R} (e : Equation (TotalTerm Θ)) where
  p : Head
  q : Head
  G : Fin Θ.arity
  F : Fin Θ.arity
  pG : Head
  cG : Head
  pF : Head
  cF : Head
  distinct : F ≠ G
  annotation_left : e.1.1.code = famCode [p] q
  annotation_right : e.2.1.code = famCode [p] q
  side_left : e.1.2.code = etaExp 1 (.var G)
  side_right : e.2.2.code = etaExp 1 (.var F)
  declared_G : Ctx.lookup Θ.raw G = famCode [pG] cG
  declared_F : Ctx.lookup Θ.raw F = famCode [pF] cF
  universe_p : S.R.isUniverse p
  universe_q : S.R.isUniverse q
  universe_pG : S.R.isUniverse pG
  universe_cG : S.R.isUniverse cG
  universe_pF : S.R.isUniverse pF
  universe_cF : S.R.isUniverse cF
  domain_G : S.R.cumulative p pG
  domain_F : S.R.cumulative pG pF
  codomain_F : S.R.cumulative cF cG
  codomain_G : S.R.cumulative cG q

/-! ## Typing -/

section Typing

/-- The fresh variable of a universe binder. -/
theorem var_head_typed {n : Nat} (Γ : Ctx Head n) (d : Head) : Typed S.R (.snoc Γ (.head d)) (.var 0) (.head d) := by
  have typed := Derivable.var (R := S.R) (Γ := .snoc Γ (.head d)) 0
  rw [Ctx.lookup_snoc_zero] at typed
  exact typed

/-- A unary family opened at an argument of its domain. -/
theorem open_typed {n : Nat} {Γ : Ctx Head n} {t : Tm Head n} {d pF cF : Head}
    (tt : Typed S.R Γ t (famCode [pF] cF)) (arg : Typed S.R (.snoc Γ (.head d)) (.var 0) (.head pF)) :
    Typed S.R (.snoc Γ (.head d)) (.app (Presentation.rename wk t) (.var 0)) (.head cF) := by
  have weak := tt.rename (CtxRen.wk Γ (.head d))
  rw [famCode_rename] at weak
  exact Derivable.appElim weak arg

/-- **`λ x. t x` at a raised domain**: a family over `U_{pF}` valued in `U_{cF}`, opened at an argument of
`U_{pG} ≤ U_{pF}`, is a family over `U_{pG}` valued in every `U_c` above `U_{cF}`. -/
theorem raised_typed {n : Nat} {Γ : Ctx Head n} {t : Tm Head n} {pG pF cF c : Head}
    (tt : Typed S.R Γ t (famCode [pF] cF)) (formedPi : IsType S.R Γ (famCode [pG] c))
    (domain : S.R.cumulative pG pF) (codomain : S.R.cumulative cF c) :
    Typed S.R (.snoc Γ (.head pG)) (.app (Presentation.rename wk t) (.var 0)) (.head c) ∧
      Typed S.R Γ (.lam (.app (Presentation.rename wk t) (.var 0))) (famCode [pG] c) := by
  have body : Typed S.R (.snoc Γ (.head pG)) (.app (Presentation.rename wk t) (.var 0)) (.head c) :=
    Derivable.cumul (open_typed tt (Derivable.cumul (var_head_typed Γ pG) domain)) codomain
  obtain ⟨u, hu, tPi⟩ := formedPi
  exact ⟨body, Derivable.lamIntro tPi hu body⟩

/-- A β-step at the fresh variable: `(λ y. t y) x ≡ t x`. -/
theorem beta_fresh {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {c u : Head} {t : Tm Head n}
    (tPi : Typed S.R Γ (.pi A (.head c)) (.head u)) (hu : S.R.isUniverse u)
    (body : Typed S.R (.snoc Γ A) (.app (Presentation.rename wk t) (.var 0)) (.head c)) :
    Equal S.R (.snoc Γ A)
      (.app (Presentation.rename wk (.lam (.app (Presentation.rename wk t) (.var 0)))) (.var 0))
      (.app (Presentation.rename wk t) (.var 0)) (.head c) := by
  have step := Derivable.betaPi (tPi.rename (CtxRen.wk Γ A)) hu (body.rename ((CtxRen.wk Γ A).snoc A))
    (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0)
  rw [Products.fresh_instantiation, Products.fresh_instantiation] at step
  exact step

end Typing

/-! ## What the equation forces -/

section Forcing

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **What the equation forces**: every solution sends `G` to `λ x. F x`, at `G`'s declaration. -/
theorem raise_forced {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (f : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves f e) :
    Equal S.R Δ.raw (f.substitution v.G) (etaExp 1 (f.substitution v.F)) (famCode [v.pG] v.cG) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
    (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at equal
  rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst] at equal
  change Equal S.R Δ.raw (.lam (.app (Presentation.rename wk (f.substitution v.G)) (.var 0)))
    (.lam (.app (Presentation.rename wk (f.substitution v.F)) (.var 0))) (.pi (.head v.p) (.head v.q)) at equal
  -- The declared types of the two values.
  have tG : Typed S.R Δ.raw (f.substitution v.G) (famCode [v.pG] v.cG) := by
    have typed := f.typed v.G
    rw [v.declared_G, famCode_subst] at typed
    exact typed
  have tF : Typed S.R Δ.raw (f.substitution v.F) (famCode [v.pF] v.cF) := by
    have typed := f.typed v.F
    rw [v.declared_F, famCode_subst] at typed
    exact typed
  have isPq : IsType S.R Δ.raw (famCode [v.p] v.q) := by
    have formed := (e.1.1.reindex f).isType
    change IsType S.R Δ.raw (Presentation.subst f.substitution e.1.1.code) at formed
    rw [v.annotation_left, famCode_subst] at formed
    exact formed
  have isG : IsType S.R Δ.raw (famCode [v.pG] v.cG) := Typed.isType tG Δ.formed
  have formedP : CtxFormed S.R (.snoc Δ.raw (.head v.p)) :=
    Δ.formed.snoc (IsType.head_of_universe v.universe_p)
  have formedG : CtxFormed S.R (.snoc Δ.raw (.head v.pG)) :=
    Δ.formed.snoc (IsType.head_of_universe v.universe_pG)
  -- Open the equation at `x : U_p`.
  have opened := equal_of_lam_left facts Δ.formed equal
  obtain ⟨bodyFp, _⟩ := raised_typed tF isPq (algebra.trans v.domain_G v.domain_F)
    (algebra.trans v.codomain_F v.codomain_G)
  obtain ⟨uP, huP, tPiP⟩ := isPq
  have betaP := beta_fresh tPiP huP bodyFp
  have narrowEq : Equal S.R (.snoc Δ.raw (.head v.p))
      (.app (Presentation.rename wk (f.substitution v.G)) (.var 0))
      (.app (Presentation.rename wk (f.substitution v.F)) (.var 0)) (.head v.q) := .trans opened betaP
  -- Widen it to `x : U_{pG}`, where both openings are typed.
  have bodyGq : Typed S.R (.snoc Δ.raw (.head v.pG)) (.app (Presentation.rename wk (f.substitution v.G)) (.var 0))
      (.head v.q) := Derivable.cumul (open_typed tG (var_head_typed Δ.raw v.pG)) v.codomain_G
  have bodyFq : Typed S.R (.snoc Δ.raw (.head v.pG)) (.app (Presentation.rename wk (f.substitution v.F)) (.var 0))
      (.head v.q) :=
    Derivable.cumul (open_typed tF (Derivable.cumul (var_head_typed Δ.raw v.pG) v.domain_F))
      (algebra.trans v.codomain_F v.codomain_G)
  have narrows : CtxNarrows S.R (.snoc Δ.raw (.head v.pG)) (.snoc Δ.raw (.head v.p)) :=
    .lower (CtxNarrows.refl Δ.raw) v.domain_G
  have wide := equal_of_narrows facts roots heads algebra rigid complete narrows formedG formedP bodyGq bodyFq
    narrowEq
  -- There it holds at `U_{cG}`.
  have bodyGc : Typed S.R (.snoc Δ.raw (.head v.pG)) (.app (Presentation.rename wk (f.substitution v.G)) (.var 0))
      (.head v.cG) := open_typed tG (var_head_typed Δ.raw v.pG)
  obtain ⟨bodyFc, tLam⟩ := raised_typed tF isG v.domain_F v.codomain_F
  have lowered := universe_injective facts roots heads algebra rigid complete formedG v.universe_cG v.universe_q
    bodyGc bodyFc wide
  -- η at `G`'s declaration.
  obtain ⟨uG, huG, tPiG⟩ := isG
  have betaG := beta_fresh tPiG huG bodyFc
  exact Derivable.etaPi tG tLam (.trans lowered (.symm betaG))

/-! ## The rule -/

/-- `G := λ x. F x`, the identity elsewhere, on codes. -/
def raiseSub {n : Nat} (F G : Fin n) : Sub Head n n := fun i => if i = G then etaExp 1 (.var F) else .var i

omit [UniverseLevel.LevelOrder L] in
theorem raiseSub_self {n : Nat} (F G : Fin n) : raiseSub (Head := Head) F G G = etaExp 1 (.var F) := by
  simp [raiseSub]

omit [UniverseLevel.LevelOrder L] in
theorem raiseSub_ne {n : Nat} (F G : Fin n) {i : Fin n} (h : i ≠ G) : raiseSub (Head := Head) F G i = .var i := by
  simp [raiseSub, h]

/-- **The answer `G := λ x. F x`** as a typed endomorphism of a telescope of families. -/
def raise (Θ : Context S.R) (all : AllFamilies Θ) {e : Equation (TotalTerm Θ)} (v : FitsView e) : Θ ⟶ Θ where
  substitution := raiseSub v.F v.G
  typed := by
    intro i
    obtain ⟨psi, ci, hi⟩ := all i
    rw [hi, famCode_subst]
    by_cases h : i = v.G
    · rw [h] at hi ⊢
      rw [raiseSub_self, hi.symm.trans v.declared_G]
      have tF : Typed S.R Θ.raw (.var v.F) (famCode [v.pF] v.cF) := by
        have typed := Derivable.var (R := S.R) (Γ := Θ.raw) v.F
        rw [v.declared_F] at typed
        exact typed
      have isG : IsType S.R Θ.raw (famCode [v.pG] v.cG) := v.declared_G ▸ Θ.formed.lookup v.G
      exact (raised_typed tF isG v.domain_F v.codomain_F).2
    · rw [raiseSub_ne _ _ h]
      have typed := Derivable.var (R := S.R) (Γ := Θ.raw) i
      rw [hi] at typed
      exact typed

/-- **Domain raising**: `G := λ x. F x`; the solved equation is removed and the rest is instantiated. -/
def raiseUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := Θ
  answer := raise Θ all v
  remaining := (frames S.levels).applyStore (raise Θ all v) rest
  sound := by
    intro Δ g solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · have isPq : IsType S.R Δ.raw (famCode [v.p] v.q) := by
        have formed := (e'.1.1.reindex (g ≫ raise Θ all v)).isType
        change IsType S.R Δ.raw (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e'.1.1.code)
          at formed
        rw [v.annotation_left, famCode_subst] at formed
        exact formed
      have tF : Typed S.R Δ.raw (g.substitution v.F) (famCode [v.pF] v.cF) := by
        have typed := g.typed v.F
        rw [v.declared_F, famCode_subst] at typed
        exact typed
      have tEta := (raised_typed tF isPq (algebra.trans v.domain_G v.domain_F)
        (algebra.trans v.codomain_F v.codomain_G)).2
      refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
      · change TypeEq S.R Δ.raw (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e'.1.1.code)
          (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e'.2.1.code)
        rw [v.annotation_left, v.annotation_right, famCode_subst]
        exact isPq.refl
      · change Equal S.R Δ.raw (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e'.1.2.code)
          (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e'.2.2.code)
          (Presentation.subst (subComp g.substitution (raiseSub v.F v.G)) e'.1.1.code)
        rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst]
        change Equal S.R Δ.raw (etaExp 1 (Presentation.subst g.substitution (raiseSub v.F v.G v.G)))
          (etaExp 1 (Presentation.subst g.substitution (raiseSub v.F v.G v.F))) (famCode [v.p] v.q)
        rw [raiseSub_self, raiseSub_ne _ _ v.distinct, subst_etaExp]
        exact etaExp_equal [v.p] Δ.formed tEta
    · exact (Frames.models_applyStore (X := frames S.levels) _ g rest).mp solved e' member
  complete := by
    intro Δ f solved
    have key := raise_forced facts roots heads algebra rigid complete v f (solved e List.mem_cons_self)
    have same : homTypedEquality S.R f (f ≫ raise Θ all v) := by
      refine ⟨f.typed, fun i => ?_⟩
      change Equal S.R Δ.raw (f.substitution i) (Presentation.subst f.substitution (raiseSub v.F v.G i))
        (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
      by_cases h : i = v.G
      · rw [h, raiseSub_self, v.declared_G, famCode_subst, subst_etaExp]
        exact key
      · rw [raiseSub_ne _ _ h]
        exact .refl (f.typed i)
    refine ⟨f, ?_, act_equal_of_substEq S.levels same⟩
    apply (Frames.models_applyStore (X := frames S.levels) _ f rest).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels same) rest).mp
      (fun e' member => solved e' (List.mem_cons_of_mem _ member))

include facts roots heads algebra rigid complete in
/-- **Domain raising is exact.** -/
theorem raise_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitsView e) (all : AllFamilies Θ)
    (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (raise Θ all v) ((frames S.levels).applyStore (raise Θ all v) rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨raiseUpdate facts roots heads algebra rigid complete v all rest, rfl, rfl, rfl⟩

end Forcing

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
