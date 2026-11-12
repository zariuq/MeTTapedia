import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Widening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MeetNarrowing

/-!
# The true meet in the tree's fibre: neither unknown fits, and the meet is a new family

In `λ x. A x ≐ λ x. B x` at `Π (x : U_p). U_q`, with `A : Π (x : U_{pA}). U_{cA}` and `B : Π (x : U_{pB}). U_{cB}`,
suppose `A` has the smaller domain and the smaller codomain (`pA ≤ pB`, `cA ≤ cB`). Neither unknown fits the other
when both comparisons are strict. The meet of the two views is `Π (x : U_{pB}). U_{cA}`: the larger domain and the
smaller codomain. It is the view of no unknown of the store.

* **What the equation forces** (`meet_forced`), when `B`'s domain lies below `A`'s codomain (`pB ≤ cA`): every
  solution sends `B` to a family equal, at `B`'s declaration, to a family of the meet. The equation opens under
  its binder and widens to `x : U_{pA}` (the tree's `equal_of_narrows`); there `B x` is equal to `A x`, a type of
  `U_{cA}`; the meet lemma on normal forms (`small_of_widen`) carries this to `x : U_{pB}`, because the widened
  declaration `U_{pB}` lies below `U_{cA}`.
* **The lowering** (`lowered`, `lowerUpdate`, `lower_exact`): `B` declared again, in place, at the meet. The
  identity is a typed morphism from the lowered telescope (`setFamAt_substMor`), and every solution factors
  through it by `meet_forced`; an update of the tree's driver, hence exact.
* **The rule** (`trueMeetUpdate`, `trueMeet_exact`): the lowering, then domain raising `A := λ x. B x` on the lowered store
  with the other equations re-read (`raiseContractUpdate`): over the lowered telescope `B` fits `A`.

The condition `pB ≤ cA` is needed: the cross store (`X : U0 → U0`, `Y : U1 → U1`) has the shape with `pB = 1`
and `cA = 0`, and it has no principal answer (`cross_no_principal`).
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

/-! ## Families are types -/

/-- **A universe family over universes is a type** in every formed telescope. -/
theorem famCode_isType : ∀ (ps : List Head) {c : Head}, (∀ p ∈ ps, S.R.isUniverse p) → S.R.isUniverse c →
    ∀ {n : Nat} {Γ : Ctx Head n}, CtxFormed S.R Γ → IsType S.R Γ (famCode ps c)
  | [], _, _, hc, _, _, _ => IsType.head_of_universe hc
  | p :: ps, c, hps, hc, _, Γ, formed => by
      obtain ⟨u, hu, tP⟩ := (IsType.head_of_universe (hps p List.mem_cons_self) : IsType S.R Γ (.head p))
      obtain ⟨v, hv, tB⟩ := famCode_isType ps (c := c) (fun q member => hps q (List.mem_cons_of_mem _ member)) hc
        (formed.snoc ⟨u, hu, tP⟩)
      obtain ⟨w, join⟩ := S.levels.join_exists hu hv
      exact ⟨w, (S.levels.join_level join).1, Derivable.piForm tP hu tB hv join⟩

/-- A β-step at the fresh variable: `(λ y. N) x ≡ N`. -/
theorem beta_body {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {c u : Head} {N : Tm Head (n + 1)}
    (tPi : Typed S.R Γ (.pi A (.head c)) (.head u)) (hu : S.R.isUniverse u)
    (body : Typed S.R (.snoc Γ A) N (.head c)) :
    Equal S.R (.snoc Γ A) (.app (Presentation.rename wk (.lam N)) (.var 0)) N (.head c) := by
  have step := Derivable.betaPi (tPi.rename (CtxRen.wk Γ A)) hu (body.rename ((CtxRen.wk Γ A).snoc A))
    (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0)
  rw [Products.fresh_instantiation, Products.fresh_instantiation] at step
  exact step

/-! ## What the equation forces at the meet -/

/-- **The two unknowns meet**: the left one has the smaller domain and the smaller codomain, and the right one's
domain lies below the left one's codomain. The meet of the two views is `Π (x : U_{pr}). U_{cl}`. -/
def Meets {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) : Prop :=
  S.R.cumulative v.pl v.pr ∧ S.R.cumulative v.cl v.cr ∧ S.R.cumulative v.pr v.cl

section Forcing

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **What the equation forces at the meet**: every solution sends the right unknown to a family equal, at its own
declaration, to a family of the meet `Π (x : U_{pr}). U_{cl}`. -/
theorem meet_forced {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (f : Δ ⟶ Θ) (solved : (frames S.levels).Solves f e) :
    ∃ h, Typed S.R Δ.raw h (famCode [v.pr] v.cl) ∧
      Equal S.R Δ.raw (f.substitution v.right) h (famCode [v.pr] v.cr) := by
  obtain ⟨lowDomain, lowCodomain, crossing⟩ := meets
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
    (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at equal
  rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst] at equal
  change Equal S.R Δ.raw (.lam (.app (Presentation.rename wk (f.substitution v.left)) (.var 0)))
    (.lam (.app (Presentation.rename wk (f.substitution v.right)) (.var 0))) (.pi (.head v.p) (.head v.q)) at equal
  -- The declared types of the two values.
  have tA : Typed S.R Δ.raw (f.substitution v.left) (famCode [v.pl] v.cl) := by
    have typed := f.typed v.left
    rw [v.declared_left, famCode_subst] at typed
    exact typed
  have tB : Typed S.R Δ.raw (f.substitution v.right) (famCode [v.pr] v.cr) := by
    have typed := f.typed v.right
    rw [v.declared_right, famCode_subst] at typed
    exact typed
  have isPq : IsType S.R Δ.raw (famCode [v.p] v.q) := by
    have formed := (e.1.1.reindex f).isType
    change IsType S.R Δ.raw (Presentation.subst f.substitution e.1.1.code) at formed
    rw [v.annotation_left, famCode_subst] at formed
    exact formed
  have formedP : CtxFormed S.R (.snoc Δ.raw (.head v.p)) :=
    Δ.formed.snoc (IsType.head_of_universe v.universe_p)
  have formedL : CtxFormed S.R (.snoc Δ.raw (.head v.pl)) :=
    Δ.formed.snoc (IsType.head_of_universe v.universe_pl)
  have formedR : CtxFormed S.R (.snoc Δ.raw (.head v.pr)) :=
    Δ.formed.snoc (IsType.head_of_universe v.universe_pr)
  -- Open the equation at `x : U_p`.
  have opened := equal_of_lam_left facts Δ.formed equal
  obtain ⟨bodyBp, _⟩ := raised_typed tB isPq v.domain_right v.codomain_right
  obtain ⟨uP, huP, tPiP⟩ := isPq
  have betaP := beta_fresh tPiP huP bodyBp
  have narrowEq : Equal S.R (.snoc Δ.raw (.head v.p))
      (.app (Presentation.rename wk (f.substitution v.left)) (.var 0))
      (.app (Presentation.rename wk (f.substitution v.right)) (.var 0)) (.head v.q) := .trans opened betaP
  -- Widen it to `x : U_{pl}`, where both openings are typed.
  have bodyAl : Typed S.R (.snoc Δ.raw (.head v.pl))
      (.app (Presentation.rename wk (f.substitution v.left)) (.var 0)) (.head v.cl) :=
    open_typed tA (var_head_typed Δ.raw v.pl)
  have bodyBl : Typed S.R (.snoc Δ.raw (.head v.pl))
      (.app (Presentation.rename wk (f.substitution v.right)) (.var 0)) (.head v.cr) :=
    open_typed tB (Derivable.cumul (var_head_typed Δ.raw v.pl) lowDomain)
  have wide := equal_of_narrows facts roots heads algebra rigid complete
    (.lower (CtxNarrows.refl Δ.raw) v.domain_left) formedL formedP
    (Derivable.cumul bodyAl v.codomain_left) (Derivable.cumul bodyBl v.codomain_right) narrowEq
  -- The meet lemma on normal forms, from `x : U_{pl}` to `x : U_{pr}`.
  have bodyBr : Typed S.R (.snoc Δ.raw (.head v.pr))
      (.app (Presentation.rename wk (f.substitution v.right)) (.var 0)) (.head v.cr) :=
    open_typed tB (var_head_typed Δ.raw v.pr)
  obtain ⟨N, tN, eN⟩ := small_of_widen facts roots heads algebra rigid complete v.universe_cl v.universe_cr
    (.lower (NarrowsBelow.refl v.cl Δ.raw) lowDomain crossing) formedR formedL bodyBr bodyAl
    ⟨v.q, v.universe_q, wide⟩
  -- The family of the meet, `λ x. N`.
  have universes : ∀ p ∈ [v.pr], S.R.isUniverse p := fun _ member => (List.mem_singleton.mp member) ▸ v.universe_pr
  obtain ⟨um, hum, tPiM⟩ := famCode_isType [v.pr] universes v.universe_cl Δ.formed
  have tPiM' : Typed S.R Δ.raw (.pi (.head v.pr) (.head v.cl)) (.head um) := tPiM
  refine ⟨.lam N, Derivable.lamIntro tPiM' hum tN, ?_⟩
  -- η at `B`'s declaration.
  obtain ⟨ub, hub, tPiB⟩ := Typed.isType tB Δ.formed
  have tPiB' : Typed S.R Δ.raw (.pi (.head v.pr) (.head v.cr)) (.head ub) := tPiB
  have tNr : Typed S.R (.snoc Δ.raw (.head v.pr)) N (.head v.cr) := Derivable.cumul tN lowCodomain
  have tHB : Typed S.R Δ.raw (.lam N) (.pi (.head v.pr) (.head v.cr)) := Derivable.lamIntro tPiB' hub tNr
  have beta := beta_body tPiB' hub tNr
  exact Derivable.etaPi tB tHB (.trans eN (.symm beta))

end Forcing

/-! ## The telescope with a family lowered -/

section Lowered

/-- The telescope with the declaration at `j` replaced by the family `Π x̄ : U_{p̄}. U_c`. -/
def setFamAt : {n : Nat} → Ctx Head n → Fin n → List Head → Head → Ctx Head n
  | _, .nil, j, _, _ => j.elim0
  | _, .snoc Γ A, j, ps, c => Fin.cases (.snoc Γ (famCode ps c)) (fun j' => .snoc (setFamAt Γ j' ps c) A) j

theorem lookup_setFamAt_self : ∀ {n : Nat} (Γ : Ctx Head n) (j : Fin n) (ps : List Head) (c : Head),
    Ctx.lookup (setFamAt Γ j ps c) j = famCode ps c := by
  intro n Γ
  induction Γ with
  | nil => intro j; exact j.elim0
  | snoc Γ A ih =>
      intro j ps c
      cases j using Fin.cases with
      | zero => simp only [setFamAt, Fin.cases_zero, Ctx.lookup_snoc_zero, famCode_rename]
      | succ j => simp only [setFamAt, Fin.cases_succ, Ctx.lookup_snoc_succ, ih, famCode_rename]

theorem lookup_setFamAt_ne : ∀ {n : Nat} (Γ : Ctx Head n) (j i : Fin n) (ps : List Head) (c : Head), i ≠ j →
    Ctx.lookup (setFamAt Γ j ps c) i = Ctx.lookup Γ i := by
  intro n Γ
  induction Γ with
  | nil => intro j; exact j.elim0
  | snoc Γ A ih =>
      intro j i ps c ne
      cases j using Fin.cases with
      | zero =>
          cases i using Fin.cases with
          | zero => exact absurd rfl ne
          | succ i => simp only [setFamAt, Fin.cases_zero, Ctx.lookup_snoc_succ]
      | succ j =>
          cases i using Fin.cases with
          | zero => simp only [setFamAt, Fin.cases_succ, Ctx.lookup_snoc_zero]
          | succ i =>
              have ne' : i ≠ j := fun same => ne (by rw [same])
              simp only [setFamAt, Fin.cases_succ, Ctx.lookup_snoc_succ, ih j i ps c ne']

/-- **The identity is a typed substitution into the telescope with one family's codomain lowered.** -/
theorem setFamAt_substMor {n : Nat} (Γ : Ctx Head n) (j : Fin n) {ps : List Head} {c c' : Head}
    (declared : Ctx.lookup Γ j = famCode ps c') (universes : ∀ p ∈ ps, S.R.isUniverse p) (hc : S.R.isUniverse c)
    (hc' : S.R.isUniverse c') (below : S.R.cumulative c c') (formed : CtxFormed S.R (setFamAt Γ j ps c)) :
    SubstMor S.R Γ (setFamAt Γ j ps c) ids := by
  intro i
  rw [subst_ids]
  by_cases h : i = j
  · subst h
    have typed := Derivable.var (R := S.R) (Γ := setFamAt Γ i ps c) i
    rw [lookup_setFamAt_self] at typed
    rw [declared]
    exact .sub typed ((lowers_famCode ps hc hc' below).usable (famCode_isType ps universes hc formed)
      (famCode_isType ps universes hc' formed))
  · have typed := Derivable.var (R := S.R) (Γ := setFamAt Γ j ps c) i
    rw [lookup_setFamAt_ne Γ j i ps c h] at typed
    exact typed

/-- **The telescope with one family's codomain lowered is formed.** -/
theorem setFamAt_formed : ∀ {n : Nat} (Γ : Ctx Head n) (j : Fin n) {ps : List Head} {c c' : Head},
    CtxFormed S.R Γ → Ctx.lookup Γ j = famCode ps c' → (∀ p ∈ ps, S.R.isUniverse p) → S.R.isUniverse c →
    S.R.isUniverse c' → S.R.cumulative c c' → CtxFormed S.R (setFamAt Γ j ps c) := by
  intro n Γ
  induction Γ with
  | nil => intro j; exact j.elim0
  | snoc Γ A ih =>
      intro j ps c c' formed declared universes hc hc' below
      cases formed with
      | snoc formedΓ typeA =>
          cases j using Fin.cases with
          | zero =>
              simp only [setFamAt, Fin.cases_zero]
              exact formedΓ.snoc (famCode_isType ps universes hc formedΓ)
          | succ j =>
              rw [Ctx.lookup_snoc_succ] at declared
              have inner : Ctx.lookup Γ j = famCode ps c' := by
                apply rename_wk_inj
                rw [declared, famCode_rename]
              have formedInner := ih j formedΓ inner universes hc hc' below
              simp only [setFamAt, Fin.cases_succ]
              obtain ⟨u, hu, tA⟩ := typeA
              have moved := Typed.substitute tA
                (setFamAt_substMor Γ j inner universes hc hc' below formedInner)
              rw [subst_ids, subst_ids] at moved
              exact formedInner.snoc ⟨u, hu, moved⟩

/-- **The telescope with the right unknown declared at the meet.** -/
def lowered (Θ : Context S.R) {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v) : Context S.R where
  arity := Θ.arity
  raw := setFamAt Θ.raw v.right [v.pr] v.cl
  formed := setFamAt_formed Θ.raw v.right Θ.formed v.declared_right
    (fun _ member => (List.mem_singleton.mp member) ▸ v.universe_pr) v.universe_cl v.universe_cr meets.2.1

/-- **The lowering**, the identity on codes, as a morphism of telescopes. -/
def lowerHom (Θ : Context S.R) {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v) :
    lowered Θ v meets ⟶ Θ where
  substitution := ids
  typed := setFamAt_substMor Θ.raw v.right v.declared_right
    (fun _ member => (List.mem_singleton.mp member) ▸ v.universe_pr) v.universe_cl v.universe_cr meets.2.1
    (lowered Θ v meets).formed

theorem lowered_self (Θ : Context S.R) {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v) :
    Ctx.lookup (lowered Θ v meets).raw v.right = famCode [v.pr] v.cl :=
  lookup_setFamAt_self Θ.raw v.right [v.pr] v.cl

theorem lowered_ne (Θ : Context S.R) {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    {i : Fin Θ.arity} (ne : i ≠ v.right) : Ctx.lookup (lowered Θ v meets).raw i = Ctx.lookup Θ.raw i :=
  lookup_setFamAt_ne Θ.raw v.right i [v.pr] v.cl ne

/-- Every declaration of the lowered telescope is a universe family. -/
theorem lowered_families {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (all : AllFamilies Θ) : AllFamilies (lowered Θ v meets) := by
  intro i
  by_cases h : i = v.right
  · subst h
    exact ⟨[v.pr], v.cl, lowered_self Θ v meets⟩
  · rw [lowered_ne Θ v meets h]
    exact all i

end Lowered

/-! ## The rule -/

section Rule

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **Lowering to the meet**: the right unknown declared again at the meet; the store is read over the lowered
telescope. -/
def lowerUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := lowered Θ v meets
  answer := lowerHom Θ v meets
  remaining := (frames S.levels).applyStore (lowerHom Θ v meets) (e :: rest)
  sound := by
    intro Δ g solved
    exact (Frames.models_applyStore (X := frames S.levels) _ g (e :: rest)).mp solved
  complete := by
    intro Δ f solved
    obtain ⟨h, tH, eH⟩ := meet_forced facts roots heads algebra rigid complete v meets f (solved e List.mem_cons_self)
    have same : SubstEq S.R Θ.raw Δ.raw f.substitution (replaceAt f.substitution v.right h) := by
      refine ⟨f.typed, fun i => ?_⟩
      by_cases hi : i = v.right
      · rw [hi, replaceAt_self, v.declared_right, famCode_subst]
        exact eH
      · rw [replaceAt_ne _ _ hi]
        exact .refl (f.typed i)
    have typed : SubstMor S.R (setFamAt Θ.raw v.right [v.pr] v.cl) Δ.raw (replaceAt f.substitution v.right h) := by
      intro i
      by_cases hi : i = v.right
      · rw [hi, lookup_setFamAt_self, replaceAt_self, famCode_subst]
        exact tH
      · rw [lookup_setFamAt_ne Θ.raw v.right i [v.pr] v.cl hi, replaceAt_ne _ _ hi]
        obtain ⟨level, hlevel, tDecl⟩ := Θ.formed.lookup i
        have types : TypeEq S.R Δ.raw (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
            (Presentation.subst (replaceAt f.substitution v.right h) (Ctx.lookup Θ.raw i)) :=
          ⟨level, hlevel, Typed.functional tDecl same⟩
        exact Typed.convType (f.typed i) types
    let g : Δ ⟶ lowered Θ v meets := ⟨replaceAt f.substitution v.right h, typed⟩
    have factored : homTypedEquality S.R f (g ≫ lowerHom Θ v meets) := same
    refine ⟨g, ?_, act_equal_of_substEq S.levels factored⟩
    apply (Frames.models_applyStore (X := frames S.levels) _ g (e :: rest)).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels factored) (e :: rest)).mp solved

include facts roots heads algebra rigid complete in
/-- **Lowering to the meet is exact.** -/
theorem lower_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (lowerHom Θ v meets)
      ((frames S.levels).applyStore (lowerHom Θ v meets) (e :: rest)) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨lowerUpdate facts roots heads algebra rigid complete v meets rest, rfl, rfl, rfl⟩

/-- **Over the lowered telescope the right unknown fits the left**: the equation read there, for domain raising
`left := λ x. right x`. -/
def meetFits {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (distinct : v.right ≠ v.left) :
    FitsView (((frames S.levels).act (lowerHom Θ v meets) e.1, (frames S.levels).act (lowerHom Θ v meets) e.2) :
      Equation (TotalTerm (lowered Θ v meets))) where
  p := v.p
  q := v.q
  G := v.left
  F := v.right
  pG := v.pl
  cG := v.cl
  pF := v.pr
  cF := v.cl
  distinct := distinct
  annotation_left := by
    change Presentation.subst ids e.1.1.code = famCode [v.p] v.q
    rw [subst_ids]
    exact v.annotation_left
  annotation_right := by
    change Presentation.subst ids e.2.1.code = famCode [v.p] v.q
    rw [subst_ids]
    exact v.annotation_right
  side_left := by
    change Presentation.subst ids e.1.2.code = etaExp 1 (.var v.left)
    rw [subst_ids]
    exact v.side_left
  side_right := by
    change Presentation.subst ids e.2.2.code = etaExp 1 (.var v.right)
    rw [subst_ids]
    exact v.side_right
  declared_G := by
    rw [lowered_ne Θ v meets (fun same => distinct same.symm)]
    exact v.declared_left
  declared_F := lowered_self Θ v meets
  universe_p := v.universe_p
  universe_q := v.universe_q
  universe_pG := v.universe_pl
  universe_cG := v.universe_cl
  universe_pF := v.universe_pr
  universe_cF := v.universe_cl
  domain_G := v.domain_left
  domain_F := meets.1
  codomain_F := S.levels.cumulative_refl v.universe_cl
  codomain_G := v.codomain_left

variable [DecidableEq Head] [DecidableRel S.R.cumulative]

/-- **The true meet**: lower the right unknown to the meet, then raise `left := λ x. right x` and re-read the
other equations. -/
def trueMeetUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (distinct : v.right ≠ v.left) (all : AllFamilies Θ) (rest : EquationStore (TotalTerm Θ)) :
    Update S.levels (e :: rest) :=
  (lowerUpdate facts roots heads algebra rigid complete v meets rest).then
    (raiseContractUpdate algebra facts roots heads rigid complete (meetFits v meets distinct)
      (lowered_families v meets all) ((frames S.levels).applyStore (lowerHom Θ v meets) rest))

include facts roots heads algebra rigid complete in
/-- **The true meet is exact.** -/
theorem trueMeet_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v)
    (distinct : v.right ≠ v.left) (all : AllFamilies Θ) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (trueMeetUpdate facts roots heads algebra rigid complete v meets distinct all rest).answer
      (trueMeetUpdate facts roots heads algebra rigid complete v meets distinct all rest).remaining :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr ⟨_, rfl, rfl, rfl⟩

end Rule

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
