import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralForcing

/-!
# Several parameters: domain raising and the true meet as exact rules on whole stores

A flex-flex equation of families with several parameters (`FlexK`): `λ x̄. A x̄ ≐ λ x̄. B x̄` at
`Π (x̄ : U_{p̄}). U_q`, with `A : Π (x̄ : U_{p̄A}). U_{cA}` and `B : Π (x̄ : U_{p̄B}). U_{cB}`, the annotation's
domains pointwise below both declared domains, and both declared codomains below `q`.

* **Domain raising** (`raiseContractKUpdate`, `raiseContractK_exact`): when `B` fits `A` (`p̄A ≤ p̄B` pointwise,
  `cB ≤ cA`), the answer `A := λ x̄. B x̄`, forced by `raiseK_forced`. The other equations are re-read: a side
  `λ ȳ. A ȳ` at an annotation that `B` fits becomes `λ ȳ. B ȳ` (`contractSideK`), with no new redex.
* **Lowering to the meet** (`lowerKUpdate`, `lowerK_exact`): when `A` has the smaller domains and the smaller
  codomain and every domain of `B` lies below `cA` (`MeetsK`), `B` is declared again, in place, at the meet
  `Π (x̄ : U_{p̄B}). U_{cA}`; every solution factors, by `meetK_small`.
* **The true meet** (`trueMeetKUpdate`, `trueMeetK_exact`): the lowering, then domain raising on the lowered store.
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

/-! ## Views -/

section Views

/-- **A flex-flex equation of families with several parameters.** -/
structure FlexK {Θ : Context S.R} (e : Equation (TotalTerm Θ)) where
  ps : List Head
  q : Head
  left : Fin Θ.arity
  right : Fin Θ.arity
  psl : List Head
  cl : Head
  psr : List Head
  cr : Head
  annotation_left : e.1.1.code = famCode ps q
  annotation_right : e.2.1.code = famCode ps q
  side_left : e.1.2.code = etaExp ps.length (.var left)
  side_right : e.2.2.code = etaExp ps.length (.var right)
  declared_left : Ctx.lookup Θ.raw left = famCode psl cl
  declared_right : Ctx.lookup Θ.raw right = famCode psr cr
  universes : AllUniverses S.R ps
  universes_left : AllUniverses S.R psl
  universes_right : AllUniverses S.R psr
  universe_q : S.R.isUniverse q
  universe_cl : S.R.isUniverse cl
  universe_cr : S.R.isUniverse cr
  domain_left : List.Forall₂ S.R.cumulative ps psl
  domain_right : List.Forall₂ S.R.cumulative ps psr
  codomain_left : S.R.cumulative cl q
  codomain_right : S.R.cumulative cr q

/-- The view of the swapped equation. -/
def FlexK.swap {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) :
    FlexK ((e.2, e.1) : Equation (TotalTerm Θ)) where
  ps := v.ps
  q := v.q
  left := v.right
  right := v.left
  psl := v.psr
  cl := v.cr
  psr := v.psl
  cr := v.cl
  annotation_left := v.annotation_right
  annotation_right := v.annotation_left
  side_left := v.side_right
  side_right := v.side_left
  declared_left := v.declared_right
  declared_right := v.declared_left
  universes := v.universes
  universes_left := v.universes_right
  universes_right := v.universes_left
  universe_q := v.universe_q
  universe_cl := v.universe_cr
  universe_cr := v.universe_cl
  domain_left := v.domain_right
  domain_right := v.domain_left
  codomain_left := v.codomain_right
  codomain_right := v.codomain_left

/-- **The reading of an equation is unique.** -/
theorem FlexK.unique {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v w : FlexK e) :
    v.left = w.left ∧ v.right = w.right := by
  obtain ⟨hps, _⟩ := famCode_inj (v.annotation_left.symm.trans w.annotation_left)
  have sl := v.side_left.symm.trans w.side_left
  have sr := v.side_right.symm.trans w.side_right
  rw [hps] at sl sr
  exact ⟨Tm.var.inj (etaExp_inj _ sl), Tm.var.inj (etaExp_inj _ sr)⟩

/-- **The right unknown fits the left one**: it takes the left one's arguments and returns into its codomain. -/
def FlexK.Fits {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) : Prop :=
  List.Forall₂ S.R.cumulative v.psl v.psr ∧ S.R.cumulative v.cr v.cl

/-- **The two unknowns meet**: the left one has the smaller domains and the smaller codomain, and every domain of the
right one lies below the left one's codomain. The meet is `Π (x̄ : U_{p̄r}). U_{cl}`. -/
def FlexK.Meets {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) : Prop :=
  List.Forall₂ S.R.cumulative v.psl v.psr ∧ S.R.cumulative v.cl v.cr ∧ ∀ p ∈ v.psr, S.R.cumulative p v.cl

end Views

/-! ## The answer of domain raising -/

section Answer

/-- `G := λ x̄. F x̄` at `k` parameters, the identity elsewhere, on codes. -/
def raiseKSub {n : Nat} (k : Nat) (F G : Fin n) : Sub Head n n :=
  fun i => if i = G then etaExp k (.var F) else .var i

omit [UniverseLevel.LevelOrder L] in
theorem raiseKSub_self {n : Nat} (k : Nat) (F G : Fin n) : raiseKSub (Head := Head) k F G G = etaExp k (.var F) := by
  simp [raiseKSub]

omit [UniverseLevel.LevelOrder L] in
theorem raiseKSub_ne {n : Nat} (k : Nat) (F G : Fin n) {i : Fin n} (h : i ≠ G) :
    raiseKSub (Head := Head) k F G i = .var i := by
  simp [raiseKSub, h]

/-- **The answer `left := λ x̄. right x̄`** as a typed endomorphism of a telescope of families. -/
def raiseK (Θ : Context S.R) (all : AllFamilies Θ) {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits) :
    Θ ⟶ Θ where
  substitution := raiseKSub v.psl.length v.right v.left
  typed := by
    intro i
    obtain ⟨psi, ci, hi⟩ := all i
    rw [hi, famCode_subst]
    by_cases h : i = v.left
    · rw [h] at hi ⊢
      rw [raiseKSub_self, hi.symm.trans v.declared_left]
      have tF : Typed S.R Θ.raw (.var v.right) (famCode v.psr v.cr) := by
        have typed := Derivable.var (R := S.R) (Γ := Θ.raw) v.right
        rw [v.declared_right] at typed
        exact typed
      exact raisedK_typed fits.1 v.universes_left v.universe_cl fits.2 Θ.formed tF
    · rw [raiseKSub_ne _ _ _ h]
      have typed := Derivable.var (R := S.R) (Γ := Θ.raw) i
      rw [hi] at typed
      exact typed

/-- η-expansion is a congruence at smaller domains and a larger codomain, with several parameters. -/
theorem etaExpK_congr : ∀ {ps psG : List Head}, List.Forall₂ S.R.cumulative ps psG →
    ∀ {n : Nat} {Γ : Ctx Head n} {s t : Tm Head n} {cG q : Head}, AllUniverses S.R ps → S.R.isUniverse q →
      S.R.cumulative cG q → CtxFormed S.R Γ → Equal S.R Γ s t (famCode psG cG) →
      Equal S.R Γ (etaExp ps.length s) (etaExp ps.length t) (famCode ps q) := by
  intro ps psG domains
  induction domains with
  | nil =>
      intro n Γ s t cG q _ _ codomain _ equal
      exact Derivable.cumulEq equal codomain
  | @cons p pG ps' psG' head _ ih =>
      intro n Γ s t cG q universes hq codomain formed equal
      have formed' : CtxFormed S.R (.snoc Γ (.head p)) := formed.snoc (IsType.head_of_universe universes.head)
      have weak := equal.rename (CtxRen.wk Γ (.head p))
      rw [famCode_rename] at weak
      have applied := Derivable.appCong weak (.refl (Derivable.cumul (var_head_typed Γ p) head))
      simp only [inst0, famCode_subst] at applied
      have inner := ih universes.tail hq codomain formed' applied
      obtain ⟨u, hu, tPi⟩ := famCode_isType (p :: ps') universes hq formed
      have tPi' : Typed S.R Γ (.pi (.head p) (famCode ps' q)) (.head u) := tPi
      exact Derivable.lamCong tPi' hu inner

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **What domain raising forces at a solution**: the left unknown's value is the right one's, η-expanded. -/
theorem raiseK_value {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits) (f : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves f e) :
    Equal S.R Δ.raw (f.substitution v.left) (etaExp v.psl.length (f.substitution v.right)) (famCode v.psl v.cl) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
    (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at equal
  rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst] at equal
  have tG : Typed S.R Δ.raw (f.substitution v.left) (famCode v.psl v.cl) := by
    have typed := f.typed v.left
    rw [v.declared_left, famCode_subst] at typed
    exact typed
  have tF : Typed S.R Δ.raw (f.substitution v.right) (famCode v.psr v.cr) := by
    have typed := f.typed v.right
    rw [v.declared_right, famCode_subst] at typed
    exact typed
  exact raiseK_forced facts roots heads algebra rigid complete v.domain_left fits.1 v.universes v.universes_left
    v.universe_cl v.universe_cr v.universe_q fits.2 v.codomain_left Δ.formed tG tF equal

end Answer

/-! ## Domain raising on a whole store -/

section Raise

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- The conditions under which a side `λ ȳ. G ȳ` at `Π (ȳ : U_{p̄'}). U_{q'}` is re-read as `λ ȳ. F ȳ`. -/
def RereadsK {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (side : TotalTerm Θ)
    (ps' : List Head) (q' : Head) : Prop :=
  side.1.code = famCode ps' q' ∧ side.2.code = etaExp ps'.length (.var v.left) ∧ AllUniverses S.R ps' ∧
    S.R.isUniverse q' ∧ List.Forall₂ S.R.cumulative ps' v.psl ∧ S.R.cumulative v.cl q'

instance {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (side : TotalTerm Θ) (ps' : List Head)
    (q' : Head) : Decidable (RereadsK v side ps' q') := by
  unfold RereadsK AllUniverses
  infer_instance

variable (algebra : CumulativeAlgebra S.R)

/-- The re-read side: `λ ȳ. F ȳ`, typed at the side's annotation. -/
def rereadTermK {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits) (side : TotalTerm Θ)
    {ps' : List Head} {q' : Head} (h : RereadsK v side ps' q') : Term Θ side.1 :=
  ⟨etaExp ps'.length (.var v.right), by
    rw [h.1]
    have tF : Typed S.R Θ.raw (.var v.right) (famCode v.psr v.cr) := by
      have typed := Derivable.var (R := S.R) (Γ := Θ.raw) v.right
      rw [v.declared_right] at typed
      exact typed
    exact raisedK_typed (forall₂_trans algebra.trans h.2.2.2.2.1 fits.1) h.2.2.1 h.2.2.2.1
      (algebra.trans fits.2 h.2.2.2.2.2) Θ.formed tF⟩

/-- **A side after domain raising**: re-read as `λ ȳ. F ȳ` where it is `λ ȳ. G ȳ` at a fitting annotation, and
instantiated otherwise. -/
def contractSideK {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits) (all : AllFamilies Θ)
    (side : TotalTerm Θ) : TotalTerm Θ :=
  match readFam side.1.code with
  | some (ps', q') =>
      if h : RereadsK v side ps' q' then ⟨side.1, rereadTermK algebra v fits side h⟩
      else side.reindex (raiseK Θ all v fits)
  | none => side.reindex (raiseK Θ all v fits)

/-- The residual store of domain raising. -/
def contractStoreK {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits) (all : AllFamilies Θ)
    (rest : EquationStore (TotalTerm Θ)) : EquationStore (TotalTerm Θ) :=
  rest.map fun e' => (contractSideK algebra v fits all e'.1, contractSideK algebra v fits all e'.2)

theorem contractSideK_cases {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits)
    (all : AllFamilies Θ) (side : TotalTerm Θ) :
    (∃ ps' q' h, contractSideK algebra v fits all side =
        ⟨side.1, rereadTermK algebra v fits side (ps' := ps') (q' := q') h⟩) ∨
      contractSideK algebra v fits all side = side.reindex (raiseK Θ all v fits) := by
  unfold contractSideK
  cases hc : readFam side.1.code with
  | none => exact .inr rfl
  | some pq =>
      cases pq with
      | mk ps' q' =>
          by_cases h : RereadsK v side ps' q'
          · exact .inl ⟨ps', q', h, dif_pos h⟩
          · exact .inr (dif_neg h)

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

include facts in
/-- **The re-read side agrees with the instantiated side for the residual solutions.** -/
theorem contractK_sound {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits)
    (all : AllFamilies Θ) (side : TotalTerm Θ) (g : Δ ⟶ Θ) :
    (frames S.levels).E ((contractSideK algebra v fits all side).reindex g) (side.reindex (g ≫ raiseK Θ all v fits)) := by
  have _ := facts
  rcases contractSideK_cases algebra v fits all side with ⟨ps', q', h, same⟩ | same
  · rw [same]
    have tF : Typed S.R Δ.raw (g.substitution v.right) (famCode v.psr v.cr) := by
      have typed := g.typed v.right
      rw [v.declared_right, famCode_subst] at typed
      exact typed
    have lengths : v.psl.length = ps'.length := (forall₂_length h.2.2.2.2.1).symm
    have tEta := raisedK_typed (forall₂_trans algebra.trans h.2.2.2.2.1 fits.1) h.2.2.1 h.2.2.2.1
      (algebra.trans fits.2 h.2.2.2.2.2) Δ.formed tF
    refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
    · change TypeEq S.R Δ.raw (Presentation.subst g.substitution side.1.code)
        (Presentation.subst (subComp g.substitution (raiseKSub v.psl.length v.right v.left)) side.1.code)
      rw [h.1, famCode_subst, famCode_subst]
      exact (Typed.isType tEta Δ.formed).refl
    · change Equal S.R Δ.raw (Presentation.subst g.substitution (etaExp ps'.length (.var v.right)))
        (Presentation.subst (subComp g.substitution (raiseKSub v.psl.length v.right v.left)) side.2.code)
        (Presentation.subst g.substitution side.1.code)
      rw [h.2.1, h.1, famCode_subst, subst_etaExp, subst_etaExp]
      change Equal S.R Δ.raw (etaExp ps'.length (g.substitution v.right))
        (etaExp ps'.length (Presentation.subst g.substitution (raiseKSub v.psl.length v.right v.left v.left)))
        (famCode ps' q')
      rw [raiseKSub_self, subst_etaExp, lengths]
      exact .symm (etaExp_equal ps' Δ.formed tEta)
  · rw [same, ← ContextualDependentEta.reindex_comp]
    exact ((frames S.levels).equivalence Δ).refl _

include facts roots heads algebra rigid complete in
/-- **The re-read side agrees with the side itself for every original solution.** -/
theorem contractK_complete {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits)
    (all : AllFamilies Θ) (side : TotalTerm Θ) (f : Δ ⟶ Θ) (solved : (frames S.levels).Solves f e)
    (same : homTypedEquality S.R f (f ≫ raiseK Θ all v fits)) :
    (frames S.levels).E ((contractSideK algebra v fits all side).reindex f) (side.reindex f) := by
  rcases contractSideK_cases algebra v fits all side with ⟨ps', q', h, isSame⟩ | isSame
  · rw [isSame]
    have tF : Typed S.R Δ.raw (f.substitution v.right) (famCode v.psr v.cr) := by
      have typed := f.typed v.right
      rw [v.declared_right, famCode_subst] at typed
      exact typed
    have lengths : v.psl.length = ps'.length := (forall₂_length h.2.2.2.2.1).symm
    have tEta := raisedK_typed (forall₂_trans algebra.trans h.2.2.2.2.1 fits.1) h.2.2.1 h.2.2.2.1
      (algebra.trans fits.2 h.2.2.2.2.2) Δ.formed tF
    have key := raiseK_value facts roots heads algebra rigid complete v fits f solved
    rw [lengths] at key
    have congr := etaExpK_congr h.2.2.2.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.2 Δ.formed key
    refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
    · change TypeEq S.R Δ.raw (Presentation.subst f.substitution side.1.code)
        (Presentation.subst f.substitution side.1.code)
      exact (side.1.reindex f).isType.refl
    · change Equal S.R Δ.raw (Presentation.subst f.substitution (etaExp ps'.length (.var v.right)))
        (Presentation.subst f.substitution side.2.code) (Presentation.subst f.substitution side.1.code)
      rw [h.2.1, h.1, famCode_subst, subst_etaExp, subst_etaExp]
      exact .trans (.symm (etaExp_equal ps' Δ.formed tEta)) (.symm congr)
  · rw [isSame, ← ContextualDependentEta.reindex_comp]
    exact ((frames S.levels).equivalence Δ).symm (act_equal_of_substEq S.levels same side)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
include facts algebra in
/-- The solved equation holds after domain raising, for every residual solution. -/
theorem raiseK_head_solved {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits)
    (distinct : v.right ≠ v.left) (all : AllFamilies Θ) (g : Δ ⟶ Θ) :
    (frames S.levels).Solves (g ≫ raiseK Θ all v fits) e := by
  have _ := facts
  have tF : Typed S.R Δ.raw (g.substitution v.right) (famCode v.psr v.cr) := by
    have typed := g.typed v.right
    rw [v.declared_right, famCode_subst] at typed
    exact typed
  have lengths : v.psl.length = v.ps.length := (forall₂_length v.domain_left).symm
  have tEta := raisedK_typed (forall₂_trans algebra.trans v.domain_left fits.1) v.universes v.universe_q
    (algebra.trans fits.2 v.codomain_left) Δ.formed tF
  refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
  · change TypeEq S.R Δ.raw (Presentation.subst (subComp g.substitution (raiseKSub v.psl.length v.right v.left)) e.1.1.code)
      (Presentation.subst (subComp g.substitution (raiseKSub v.psl.length v.right v.left)) e.2.1.code)
    rw [v.annotation_left, v.annotation_right, famCode_subst]
    exact (Typed.isType tEta Δ.formed).refl
  · change Equal S.R Δ.raw (Presentation.subst (subComp g.substitution (raiseKSub v.psl.length v.right v.left)) e.1.2.code)
      (Presentation.subst (subComp g.substitution (raiseKSub v.psl.length v.right v.left)) e.2.2.code)
      (Presentation.subst (subComp g.substitution (raiseKSub v.psl.length v.right v.left)) e.1.1.code)
    rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst]
    change Equal S.R Δ.raw
      (etaExp v.ps.length (Presentation.subst g.substitution (raiseKSub v.psl.length v.right v.left v.left)))
      (etaExp v.ps.length (Presentation.subst g.substitution (raiseKSub v.psl.length v.right v.left v.right)))
      (famCode v.ps v.q)
    rw [raiseKSub_self, raiseKSub_ne _ _ _ distinct, subst_etaExp, lengths]
    exact etaExp_equal v.ps Δ.formed tEta

/-- **Domain raising on a whole store, with several parameters**: `left := λ x̄. right x̄`; the solved equation is
removed and the other sides are re-read. -/
def raiseContractKUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits)
    (distinct : v.right ≠ v.left) (all : AllFamilies Θ) (rest : EquationStore (TotalTerm Θ)) :
    Update S.levels (e :: rest) where
  target := Θ
  answer := raiseK Θ all v fits
  remaining := contractStoreK algebra v fits all rest
  sound := by
    intro Δ g solved e' member
    rcases List.mem_cons.mp member with rfl | member
    · exact raiseK_head_solved algebra facts v fits distinct all g
    · have contracted := solved _ (List.mem_map.mpr ⟨e', member, rfl⟩)
      exact ((frames S.levels).equivalence Δ).trans
        (((frames S.levels).equivalence Δ).symm (contractK_sound algebra facts v fits all e'.1 g))
        (((frames S.levels).equivalence Δ).trans contracted (contractK_sound algebra facts v fits all e'.2 g))
  complete := by
    intro Δ f solved
    have equation := solved e List.mem_cons_self
    have key := raiseK_value facts roots heads algebra rigid complete v fits f equation
    have same : homTypedEquality S.R f (f ≫ raiseK Θ all v fits) := by
      refine ⟨f.typed, fun i => ?_⟩
      change Equal S.R Δ.raw (f.substitution i)
        (Presentation.subst f.substitution (raiseKSub v.psl.length v.right v.left i))
        (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
      by_cases h : i = v.left
      · rw [h, raiseKSub_self, v.declared_left, famCode_subst, subst_etaExp]
        exact key
      · rw [raiseKSub_ne _ _ _ h]
        exact .refl (f.typed i)
    refine ⟨f, ?_, act_equal_of_substEq S.levels same⟩
    intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    have held := solved e' (List.mem_cons_of_mem _ inRest)
    exact ((frames S.levels).equivalence Δ).trans
      (contractK_complete algebra facts roots heads rigid complete v fits all e'.1 f equation same)
      (((frames S.levels).equivalence Δ).trans held
        (((frames S.levels).equivalence Δ).symm
          (contractK_complete algebra facts roots heads rigid complete v fits all e'.2 f equation same)))

include facts roots heads algebra rigid complete in
/-- **Domain raising with several parameters is exact.** -/
theorem raiseContractK_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (fits : v.Fits)
    (distinct : v.right ≠ v.left) (all : AllFamilies Θ) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (raiseK Θ all v fits) (contractStoreK algebra v fits all rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨raiseContractKUpdate algebra facts roots heads rigid complete v fits distinct all rest, rfl, rfl, rfl⟩

end Raise

/-! ## Lowering to the meet -/

section Lower

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **What the equation forces at the meet, with several parameters**: every solution sends the right unknown to a
family equal, at its declaration, to a family of the meet `Π (x̄ : U_{p̄r}). U_{cl}`. -/
theorem meetK_forced {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    (f : Δ ⟶ Θ) (solved : (frames S.levels).Solves f e) :
    ∃ h, Typed S.R Δ.raw h (famCode v.psr v.cl) ∧
      Equal S.R Δ.raw (f.substitution v.right) h (famCode v.psr v.cr) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
    (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at equal
  rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst] at equal
  have tA : Typed S.R Δ.raw (f.substitution v.left) (famCode v.psl v.cl) := by
    have typed := f.typed v.left
    rw [v.declared_left, famCode_subst] at typed
    exact typed
  have tB : Typed S.R Δ.raw (f.substitution v.right) (famCode v.psr v.cr) := by
    have typed := f.typed v.right
    rw [v.declared_right, famCode_subst] at typed
    exact typed
  exact meetK_small facts roots heads algebra rigid complete v.universe_cl v.universe_cr v.universe_q
    v.codomain_left v.codomain_right meets.2.1 v.domain_left meets.1 v.universes v.universes_left v.universes_right
    meets.2.2 (NarrowsBelow.refl v.cl Δ.raw) Δ.formed Δ.formed tA tB equal

/-- **The telescope with the right unknown declared at the meet.** -/
def loweredK (Θ : Context S.R) {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets) : Context S.R where
  arity := Θ.arity
  raw := setFamAt Θ.raw v.right v.psr v.cl
  formed := setFamAt_formed Θ.raw v.right Θ.formed v.declared_right v.universes_right v.universe_cl v.universe_cr
    meets.2.1

/-- **The lowering**, the identity on codes. -/
def lowerKHom (Θ : Context S.R) {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets) :
    loweredK Θ v meets ⟶ Θ where
  substitution := ids
  typed := setFamAt_substMor Θ.raw v.right v.declared_right v.universes_right v.universe_cl v.universe_cr meets.2.1
    (loweredK Θ v meets).formed

theorem loweredK_self (Θ : Context S.R) {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets) :
    Ctx.lookup (loweredK Θ v meets).raw v.right = famCode v.psr v.cl :=
  lookup_setFamAt_self Θ.raw v.right v.psr v.cl

theorem loweredK_ne (Θ : Context S.R) {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    {i : Fin Θ.arity} (ne : i ≠ v.right) : Ctx.lookup (loweredK Θ v meets).raw i = Ctx.lookup Θ.raw i :=
  lookup_setFamAt_ne Θ.raw v.right i v.psr v.cl ne

theorem loweredK_families {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    (all : AllFamilies Θ) : AllFamilies (loweredK Θ v meets) := by
  intro i
  by_cases h : i = v.right
  · subst h
    exact ⟨v.psr, v.cl, loweredK_self Θ v meets⟩
  · rw [loweredK_ne Θ v meets h]
    exact all i

/-- **Lowering to the meet, with several parameters.** -/
def lowerKUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := loweredK Θ v meets
  answer := lowerKHom Θ v meets
  remaining := (frames S.levels).applyStore (lowerKHom Θ v meets) (e :: rest)
  sound := by
    intro Δ g solved
    exact (Frames.models_applyStore (X := frames S.levels) _ g (e :: rest)).mp solved
  complete := by
    intro Δ f solved
    obtain ⟨h, tH, eH⟩ := meetK_forced facts roots heads algebra rigid complete v meets f (solved e List.mem_cons_self)
    have same : SubstEq S.R Θ.raw Δ.raw f.substitution (replaceAt f.substitution v.right h) := by
      refine ⟨f.typed, fun i => ?_⟩
      by_cases hi : i = v.right
      · rw [hi, replaceAt_self, v.declared_right, famCode_subst]
        exact eH
      · rw [replaceAt_ne _ _ hi]
        exact .refl (f.typed i)
    have typed : SubstMor S.R (setFamAt Θ.raw v.right v.psr v.cl) Δ.raw (replaceAt f.substitution v.right h) := by
      intro i
      by_cases hi : i = v.right
      · rw [hi, lookup_setFamAt_self, replaceAt_self, famCode_subst]
        exact tH
      · rw [lookup_setFamAt_ne Θ.raw v.right i v.psr v.cl hi, replaceAt_ne _ _ hi]
        obtain ⟨level, hlevel, tDecl⟩ := Θ.formed.lookup i
        have types : TypeEq S.R Δ.raw (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
            (Presentation.subst (replaceAt f.substitution v.right h) (Ctx.lookup Θ.raw i)) :=
          ⟨level, hlevel, Typed.functional tDecl same⟩
        exact Typed.convType (f.typed i) types
    let g : Δ ⟶ loweredK Θ v meets := ⟨replaceAt f.substitution v.right h, typed⟩
    have factored : homTypedEquality S.R f (g ≫ lowerKHom Θ v meets) := same
    refine ⟨g, ?_, act_equal_of_substEq S.levels factored⟩
    apply (Frames.models_applyStore (X := frames S.levels) _ g (e :: rest)).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels factored) (e :: rest)).mp solved

include facts roots heads algebra rigid complete in
/-- **Lowering to the meet with several parameters is exact.** -/
theorem lowerK_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (lowerKHom Θ v meets)
      ((frames S.levels).applyStore (lowerKHom Θ v meets) (e :: rest)) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨lowerKUpdate facts roots heads algebra rigid complete v meets rest, rfl, rfl, rfl⟩

/-- **The equation read over the lowered telescope**: the same codes; the right unknown at the meet. -/
def meetViewK {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    (distinct : v.right ≠ v.left) :
    FlexK (((frames S.levels).act (lowerKHom Θ v meets) e.1, (frames S.levels).act (lowerKHom Θ v meets) e.2) :
      Equation (TotalTerm (loweredK Θ v meets))) where
  ps := v.ps
  q := v.q
  left := v.left
  right := v.right
  psl := v.psl
  cl := v.cl
  psr := v.psr
  cr := v.cl
  annotation_left := by
    change Presentation.subst ids e.1.1.code = famCode v.ps v.q
    rw [subst_ids]
    exact v.annotation_left
  annotation_right := by
    change Presentation.subst ids e.2.1.code = famCode v.ps v.q
    rw [subst_ids]
    exact v.annotation_right
  side_left := by
    change Presentation.subst ids e.1.2.code = etaExp v.ps.length (.var v.left)
    rw [subst_ids]
    exact v.side_left
  side_right := by
    change Presentation.subst ids e.2.2.code = etaExp v.ps.length (.var v.right)
    rw [subst_ids]
    exact v.side_right
  declared_left := by
    rw [loweredK_ne Θ v meets (fun same => distinct same.symm)]
    exact v.declared_left
  declared_right := loweredK_self Θ v meets
  universes := v.universes
  universes_left := v.universes_left
  universes_right := v.universes_right
  universe_q := v.universe_q
  universe_cl := v.universe_cl
  universe_cr := v.universe_cl
  domain_left := v.domain_left
  domain_right := v.domain_right
  codomain_left := v.codomain_left
  codomain_right := v.codomain_left

/-- Over the lowered telescope the right unknown fits the left one. -/
theorem meetViewK_fits {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    (distinct : v.right ≠ v.left) : (meetViewK v meets distinct).Fits :=
  ⟨meets.1, S.levels.cumulative_refl v.universe_cl⟩

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **The true meet, with several parameters**: lower the right unknown to the meet, then raise
`left := λ x̄. right x̄` and re-read the other equations. -/
def trueMeetKUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    (distinct : v.right ≠ v.left) (all : AllFamilies Θ) (rest : EquationStore (TotalTerm Θ)) :
    Update S.levels (e :: rest) :=
  (lowerKUpdate facts roots heads algebra rigid complete v meets rest).then
    (raiseContractKUpdate algebra facts roots heads rigid complete (meetViewK v meets distinct)
      (meetViewK_fits v meets distinct) distinct (loweredK_families v meets all)
      ((frames S.levels).applyStore (lowerKHom Θ v meets) rest))

include facts roots heads algebra rigid complete in
/-- **The true meet with several parameters is exact.** -/
theorem trueMeetK_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexK e) (meets : v.Meets)
    (distinct : v.right ≠ v.left) (all : AllFamilies Θ) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest)
      (trueMeetKUpdate facts roots heads algebra rigid complete v meets distinct all rest).answer
      (trueMeetKUpdate facts roots heads algebra rigid complete v meets distinct all rest).remaining :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr ⟨_, rfl, rfl, rfl⟩

end Lower

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
