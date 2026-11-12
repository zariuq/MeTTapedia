import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrueMeet
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.LeastUniverse

/-!
# Incomparable codomains: the greatest lower bound

In `λ x. A x ≐ λ x. B x` at `Π (x : U_p). U_q`, with `A : Π (x : U_{pA}). U_{cA}` and `B : Π (x : U_{pB}). U_{cB}`,
the codomains need not be comparable: universes at two level variables are not. A common value of the two unknowns
is then a type of both universes, hence of every greatest lower bound `g` of them, by the least universe of its
normal form (`least_universe`).

* **The normal-form lemma** (`small_of_glb`): over a narrowing below `g`, a type of the wide telescope that is equal,
  over the narrow one, to a type of `U_a` and to a type of `U_b` is equal to a type of `U_g`: its normal form.
* **A lowering** (`CodomainLowering`, `lowerAtUpdate`, `lowerAt_exact`): one family declared again, in place, at a
  lower codomain. It is an update of the tree's driver as soon as every solution sends the family to one at the lower
  codomain.
* **What the equation forces** (`glb_forced_left`, `glb_forced_right`): each unknown is sent to a family valued in
  `U_g`, when its codomain is `g`, or its domain is the annotation's domain, or its domain lies below `g`
  (`LowersTo`). The last two say that the opened equation widens to the unknown's own domain below `g`.
* **The rule** (`glbMeetUpdate`, `glbMeet_exact`): both unknowns lowered to `g`, then domain raising `A := λ x. B x`,
  when `A`'s domain lies below `B`'s.
* **The true meet is the comparable case** (`glbMeets_of_meets`): when `cA ≤ cB` and `pB ≤ cA`, the smaller codomain
  is a greatest lower bound and the conditions hold.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative ContextualDependentEtaLong

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Greatest lower bounds of universes -/

/-- **`g` is a greatest lower bound of the universes `a` and `b`.** -/
def IsGlb (R : Rules Head) (g a b : Head) : Prop :=
  R.isUniverse g ∧ R.cumulative g a ∧ R.cumulative g b ∧
    ∀ u, R.isUniverse u → R.cumulative u a → R.cumulative u b → R.cumulative u g

theorem IsGlb.symm {R : Rules Head} {g a b : Head} (glb : IsGlb R g a b) : IsGlb R g b a :=
  ⟨glb.1, glb.2.2.1, glb.2.1, fun u hu below₁ below₂ => glb.2.2.2 u hu below₂ below₁⟩

/-- **An unknown's family lowers to `g`**: its codomain is `g`, or its domain is the annotation's domain, or its
domain lies below `g`. -/
def LowersTo (R : Rules Head) (g p d c : Head) : Prop := c = g ∨ d = p ∨ R.cumulative d g

/-- A domain that is the annotation's, or lies below `g`, widens the opened equation below `g`. -/
theorem narrowsBelow_of_widens {R : Rules Head} {g p d : Head} (widens : d = p ∨ R.cumulative d g)
    (domain : R.cumulative p d) {n : Nat} (Γ : Ctx Head n) :
    NarrowsBelow R g (.snoc Γ (.head d)) (.snoc Γ (.head p)) := by
  rcases widens with same | below
  · subst same
    exact NarrowsBelow.refl g _
  · exact .lower (NarrowsBelow.refl g Γ) domain below

/-! ## The normal-form lemma at a greatest lower bound -/

section Normal

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

include facts roots heads algebra rigid complete headTypingUnique in
/-- **The normal-form lemma at a greatest lower bound.** A type `t` of `U_v` over `Γ` that is equal, over a narrowing
of `Γ` below `g`, to a type of `U_a` and to a type of `U_b` is equal over `Γ`, at `U_v`, to a type of `U_g`: its
normal form, whose least universe lies below `a` and `b`, hence below `g`. -/
theorem small_of_glb {n : Nat} {Γ Δ : Ctx Head n} {a b g v : Head} (ha : S.R.isUniverse a)
    (hb : S.R.isUniverse b) (hv : S.R.isUniverse v) (glb : IsGlb S.R g a b) (nb : NarrowsBelow S.R g Γ Δ)
    (formedΓ : CtxFormed S.R Γ) (formedΔ : CtxFormed S.R Δ) {t s s' : Tm Head n}
    (tt : Typed S.R Γ t (.head v)) (ts : Typed S.R Δ s (.head a)) (ts' : Typed S.R Δ s' (.head b))
    (equal : TypeEq S.R Δ s t) (equal' : TypeEq S.R Δ s' t) :
    ∃ N, Typed S.R Γ N (.head g) ∧ Equal S.R Γ t N (.head v) := by
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formedΓ ⟨v, hv, tt⟩
  obtain ⟨_, eZ⟩ := atZ hv tt
  have lZΔ := Long.type_narrow facts lZ nb.narrows formedΓ formedΔ
  have eZΔ : TypeEq S.R Δ t Z := ⟨v, hv, equal_narrow nb.narrows eZ⟩
  have zA : Typed S.R Δ Z (.head a) :=
    normal_typed_of_equal facts roots heads algebra rigid complete formedΔ ha ts
      (TypeEq.trans S.levels equal eZΔ) lZΔ
  have zB : Typed S.R Δ Z (.head b) :=
    normal_typed_of_equal facts roots heads algebra rigid complete formedΔ hb ts'
      (TypeEq.trans S.levels equal' eZΔ) lZΔ
  obtain ⟨ℓ, hℓ, tℓ, least⟩ := least_universe facts algebra headTypingUnique Z formedΔ lZΔ
  obtain ⟨hg, _, _, greatest⟩ := glb
  have zG : Typed S.R Δ Z (.head g) := Derivable.cumul tℓ (greatest ℓ hℓ (least a ha zA) (least b hb zB))
  exact ⟨Z, typed_widen facts algebra Z hg nb formedΓ formedΔ lZ zG, eZ⟩

include facts roots heads algebra rigid complete headTypingUnique in
/-- **A common value at a greatest lower bound.** Two unary families `a : Π (x : U_{pA}). U_{cA}` and
`b : Π (x : U_{pB}). U_{cB}` whose openings are equal at `x : U_p`: `a` is equal, at its own type, to a family valued
in `U_g`, when its family lowers to `g`. -/
theorem glb_value {Δ : Context S.R} {p q pA cA pB cB g : Head} {a b : Tm Head Δ.arity}
    (hp : S.R.isUniverse p) (hq : S.R.isUniverse q) (hpA : S.R.isUniverse pA) (hcA : S.R.isUniverse cA)
    (hcB : S.R.isUniverse cB) (tA : Typed S.R Δ.raw a (famCode [pA] cA))
    (tB : Typed S.R Δ.raw b (famCode [pB] cB)) (dA : S.R.cumulative p pA) (dB : S.R.cumulative p pB)
    (glb : IsGlb S.R g cA cB) (lowers : LowersTo S.R g p pA cA)
    (opened : Equal S.R (.snoc Δ.raw (.head p)) (.app (Presentation.rename wk a) (.var 0))
      (.app (Presentation.rename wk b) (.var 0)) (.head q)) :
    ∃ h, Typed S.R Δ.raw h (famCode [pA] g) ∧ Equal S.R Δ.raw a h (famCode [pA] cA) := by
  rcases lowers with same | widens
  · subst same
    exact ⟨a, tA, .refl tA⟩
  have formedP : CtxFormed S.R (.snoc Δ.raw (.head p)) := Δ.formed.snoc (IsType.head_of_universe hp)
  have formedA : CtxFormed S.R (.snoc Δ.raw (.head pA)) := Δ.formed.snoc (IsType.head_of_universe hpA)
  have wideA : Typed S.R (.snoc Δ.raw (.head pA)) (.app (Presentation.rename wk a) (.var 0)) (.head cA) :=
    open_typed tA (var_head_typed Δ.raw pA)
  have narrowA : Typed S.R (.snoc Δ.raw (.head p)) (.app (Presentation.rename wk a) (.var 0)) (.head cA) :=
    open_typed tA (Derivable.cumul (var_head_typed Δ.raw p) dA)
  have narrowB : Typed S.R (.snoc Δ.raw (.head p)) (.app (Presentation.rename wk b) (.var 0)) (.head cB) :=
    open_typed tB (Derivable.cumul (var_head_typed Δ.raw p) dB)
  obtain ⟨N, tN, eN⟩ := small_of_glb facts roots heads algebra rigid complete headTypingUnique hcA hcB hcA glb
    (narrowsBelow_of_widens widens dA Δ.raw) formedA formedP wideA narrowA narrowB ⟨cA, hcA, .refl narrowA⟩
    ⟨q, hq, .symm opened⟩
  -- The family `λ x. N`, valued in `U_g`.
  have universes : ∀ x ∈ [pA], S.R.isUniverse x := fun _ member => (List.mem_singleton.mp member) ▸ hpA
  obtain ⟨um, hum, tPiM⟩ := famCode_isType [pA] universes glb.1 Δ.formed
  have tPiM' : Typed S.R Δ.raw (.pi (.head pA) (.head g)) (.head um) := tPiM
  refine ⟨.lam N, Derivable.lamIntro tPiM' hum tN, ?_⟩
  -- η at `a`'s type.
  obtain ⟨ua, hua, tPiA⟩ := Typed.isType tA Δ.formed
  have tPiA' : Typed S.R Δ.raw (.pi (.head pA) (.head cA)) (.head ua) := tPiA
  have tNa : Typed S.R (.snoc Δ.raw (.head pA)) N (.head cA) := Derivable.cumul tN glb.2.1
  have tHA : Typed S.R Δ.raw (.lam N) (.pi (.head pA) (.head cA)) := Derivable.lamIntro tPiA' hua tNa
  have beta := beta_body tPiA' hua tNa
  exact Derivable.etaPi tA tHA (.trans eN (.symm beta))

end Normal

/-! ## What the equation forces at a greatest lower bound -/

section Forcing

/-- **The two unknowns meet at the greatest lower bound `g` of their codomains**: the left one's domain lies below
the right one's, and both families lower to `g`. -/
def GlbMeets {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (g : Head) : Prop :=
  IsGlb S.R g v.cl v.cr ∧ S.R.cumulative v.pl v.pr ∧ LowersTo S.R g v.p v.pl v.cl ∧ LowersTo S.R g v.p v.pr v.cr

/-- **The true meet is the comparable case**: the smaller codomain is a greatest lower bound. -/
theorem glbMeets_of_meets {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (meets : Meets v) :
    GlbMeets v v.cl :=
  ⟨⟨v.universe_cl, S.levels.cumulative_refl v.universe_cl, meets.2.1, fun _ _ below _ => below⟩, meets.1,
    Or.inl rfl, Or.inr (Or.inr meets.2.2)⟩

variable (facts : FormFacts S.R S.roles)

include facts in
/-- **The equation opened at the annotation's domain.** -/
theorem fitFlex_opened {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (f : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves f e) :
    Equal S.R (.snoc Δ.raw (.head v.p)) (.app (Presentation.rename wk (f.substitution v.left)) (.var 0))
      (.app (Presentation.rename wk (f.substitution v.right)) (.var 0)) (.head v.q) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst f.substitution e.1.2.code)
    (Presentation.subst f.substitution e.2.2.code) (Presentation.subst f.substitution e.1.1.code) at equal
  rw [v.side_left, v.side_right, v.annotation_left, subst_etaExp, subst_etaExp, famCode_subst] at equal
  change Equal S.R Δ.raw (.lam (.app (Presentation.rename wk (f.substitution v.left)) (.var 0)))
    (.lam (.app (Presentation.rename wk (f.substitution v.right)) (.var 0))) (.pi (.head v.p) (.head v.q)) at equal
  have tB : Typed S.R Δ.raw (f.substitution v.right) (famCode [v.pr] v.cr) := by
    have typed := f.typed v.right
    rw [v.declared_right, famCode_subst] at typed
    exact typed
  have isPq : IsType S.R Δ.raw (famCode [v.p] v.q) := by
    have formed := (e.1.1.reindex f).isType
    change IsType S.R Δ.raw (Presentation.subst f.substitution e.1.1.code) at formed
    rw [v.annotation_left, famCode_subst] at formed
    exact formed
  have opened := equal_of_lam_left facts Δ.formed equal
  obtain ⟨bodyBp, _⟩ := raised_typed tB isPq v.domain_right v.codomain_right
  obtain ⟨uP, huP, tPiP⟩ := isPq
  exact .trans opened (beta_fresh tPiP huP bodyBp)

variable (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

theorem fitFlex_left_typed {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (f : Δ ⟶ Θ) :
    Typed S.R Δ.raw (f.substitution v.left) (famCode [v.pl] v.cl) := by
  have typed := f.typed v.left
  rw [v.declared_left, famCode_subst] at typed
  exact typed

theorem fitFlex_right_typed {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) (f : Δ ⟶ Θ) :
    Typed S.R Δ.raw (f.substitution v.right) (famCode [v.pr] v.cr) := by
  have typed := f.typed v.right
  rw [v.declared_right, famCode_subst] at typed
  exact typed

include facts roots heads algebra rigid complete headTypingUnique in
/-- **What the equation forces on the left unknown**: a family valued in `U_g`. -/
theorem glb_forced_left {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) {g : Head}
    (glbm : GlbMeets v g) (f : Δ ⟶ Θ) (solved : (frames S.levels).Solves f e) :
    ∃ h, Typed S.R Δ.raw h (famCode [v.pl] g) ∧
      Equal S.R Δ.raw (f.substitution v.left) h (famCode [v.pl] v.cl) :=
  glb_value facts roots heads algebra rigid complete headTypingUnique v.universe_p v.universe_q v.universe_pl
    v.universe_cl v.universe_cr (fitFlex_left_typed v f) (fitFlex_right_typed v f) v.domain_left v.domain_right
    glbm.1 glbm.2.2.1 (fitFlex_opened facts v f solved)

include facts roots heads algebra rigid complete headTypingUnique in
/-- **What the equation forces on the right unknown**: a family valued in `U_g`. -/
theorem glb_forced_right {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FitFlex e) {g : Head}
    (glbm : GlbMeets v g) (f : Δ ⟶ Θ) (solved : (frames S.levels).Solves f e) :
    ∃ h, Typed S.R Δ.raw h (famCode [v.pr] g) ∧
      Equal S.R Δ.raw (f.substitution v.right) h (famCode [v.pr] v.cr) :=
  glb_value facts roots heads algebra rigid complete headTypingUnique v.universe_p v.universe_q v.universe_pr
    v.universe_cr v.universe_cl (fitFlex_right_typed v f) (fitFlex_left_typed v f) v.domain_right v.domain_left
    glbm.1.symm glbm.2.2.2 (.symm (fitFlex_opened facts v f solved))

end Forcing

/-! ## Lowering one family's codomain -/

section Lowering

/-- **A lowering**: the declaration at `index` is `Π x̄ : U_{p̄}. U_{upper}`; it is declared again at `lower`. -/
structure CodomainLowering (Θ : Context S.R) where
  index : Fin Θ.arity
  ps : List Head
  lower : Head
  upper : Head
  declared : Ctx.lookup Θ.raw index = famCode ps upper
  universes : ∀ p ∈ ps, S.R.isUniverse p
  universe_lower : S.R.isUniverse lower
  universe_upper : S.R.isUniverse upper
  below : S.R.cumulative lower upper

variable {Θ : Context S.R}

/-- The lowered telescope. -/
def CodomainLowering.target (ℓ : CodomainLowering Θ) : Context S.R where
  arity := Θ.arity
  raw := setFamAt Θ.raw ℓ.index ℓ.ps ℓ.lower
  formed := setFamAt_formed Θ.raw ℓ.index Θ.formed ℓ.declared ℓ.universes ℓ.universe_lower ℓ.universe_upper
    ℓ.below

/-- The lowering, the identity on codes, as a morphism of telescopes. -/
def CodomainLowering.hom (ℓ : CodomainLowering Θ) : ℓ.target ⟶ Θ where
  substitution := ids
  typed := setFamAt_substMor Θ.raw ℓ.index ℓ.declared ℓ.universes ℓ.universe_lower ℓ.universe_upper ℓ.below
    ℓ.target.formed

theorem CodomainLowering.lookup_self (ℓ : CodomainLowering Θ) :
    Ctx.lookup ℓ.target.raw ℓ.index = famCode ℓ.ps ℓ.lower :=
  lookup_setFamAt_self Θ.raw ℓ.index ℓ.ps ℓ.lower

theorem CodomainLowering.lookup_ne (ℓ : CodomainLowering Θ) {i : Fin Θ.arity} (ne : i ≠ ℓ.index) :
    Ctx.lookup ℓ.target.raw i = Ctx.lookup Θ.raw i :=
  lookup_setFamAt_ne Θ.raw ℓ.index i ℓ.ps ℓ.lower ne

/-- Every declaration of the lowered telescope is a universe family. -/
theorem CodomainLowering.families (ℓ : CodomainLowering Θ) (all : AllFamilies Θ) : AllFamilies ℓ.target := by
  intro i
  by_cases h : i = ℓ.index
  · subst h
    exact ⟨ℓ.ps, ℓ.lower, ℓ.lookup_self⟩
  · obtain ⟨ps, c, hi⟩ := all i
    exact ⟨ps, c, (ℓ.lookup_ne h).trans hi⟩

/-- **Every solution sends the family to one at the lower codomain.** -/
def CodomainLowering.Forced (ℓ : CodomainLowering Θ) (problem : EquationStore (TotalTerm Θ)) : Prop :=
  ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f problem →
    ∃ h, Typed S.R Δ.raw h (famCode ℓ.ps ℓ.lower) ∧
      Equal S.R Δ.raw (f.substitution ℓ.index) h (famCode ℓ.ps ℓ.upper)

/-- **The lowering as an update**: the family declared again at the lower codomain; the store read over the lowered
telescope. -/
def lowerAtUpdate (ℓ : CodomainLowering Θ) (problem : EquationStore (TotalTerm Θ)) (forced : ℓ.Forced problem) :
    Update S.levels problem where
  target := ℓ.target
  answer := ℓ.hom
  remaining := (frames S.levels).applyStore ℓ.hom problem
  sound := by
    intro Δ g solved
    exact (Frames.models_applyStore (X := frames S.levels) _ g problem).mp solved
  complete := by
    intro Δ f solved
    obtain ⟨h, tH, eH⟩ := forced f solved
    have same : SubstEq S.R Θ.raw Δ.raw f.substitution (replaceAt f.substitution ℓ.index h) := by
      refine ⟨f.typed, fun i => ?_⟩
      by_cases hi : i = ℓ.index
      · rw [hi, replaceAt_self, ℓ.declared, famCode_subst]
        exact eH
      · rw [replaceAt_ne _ _ hi]
        exact .refl (f.typed i)
    have typed : SubstMor S.R (setFamAt Θ.raw ℓ.index ℓ.ps ℓ.lower) Δ.raw
        (replaceAt f.substitution ℓ.index h) := by
      intro i
      by_cases hi : i = ℓ.index
      · rw [hi, lookup_setFamAt_self, replaceAt_self, famCode_subst]
        exact tH
      · rw [lookup_setFamAt_ne Θ.raw ℓ.index i ℓ.ps ℓ.lower hi, replaceAt_ne _ _ hi]
        obtain ⟨level, hlevel, tDecl⟩ := Θ.formed.lookup i
        have types : TypeEq S.R Δ.raw (Presentation.subst f.substitution (Ctx.lookup Θ.raw i))
            (Presentation.subst (replaceAt f.substitution ℓ.index h) (Ctx.lookup Θ.raw i)) :=
          ⟨level, hlevel, Typed.functional tDecl same⟩
        exact Typed.convType (f.typed i) types
    let g : Δ ⟶ ℓ.target := ⟨replaceAt f.substitution ℓ.index h, typed⟩
    have factored : homTypedEquality S.R f (g ≫ ℓ.hom) := same
    refine ⟨g, ?_, act_equal_of_substEq S.levels factored⟩
    apply (Frames.models_applyStore (X := frames S.levels) _ g problem).mpr
    exact (Elimination.models_pointwise S.levels (act_equal_of_substEq S.levels factored) problem).mp solved

/-- **A forced lowering is exact.** -/
theorem lowerAt_exact (ℓ : CodomainLowering Θ) (problem : EquationStore (TotalTerm Θ)) (forced : ℓ.Forced problem) :
    Exact (frames S.levels) problem ℓ.hom ((frames S.levels).applyStore ℓ.hom problem) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr ⟨lowerAtUpdate ℓ problem forced, rfl, rfl, rfl⟩

end Lowering

/-! ## The rule -/

section Rule

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

variable {Θ : Context S.R} {e : Equation (TotalTerm Θ)}

/-- The left unknown lowered to `g`. -/
def glbLowerLeft (v : FitFlex e) {g : Head} (glbm : GlbMeets v g) : CodomainLowering Θ where
  index := v.left
  ps := [v.pl]
  lower := g
  upper := v.cl
  declared := v.declared_left
  universes := fun _ member => (List.mem_singleton.mp member) ▸ v.universe_pl
  universe_lower := glbm.1.1
  universe_upper := v.universe_cl
  below := glbm.1.2.1

/-- Then the right unknown lowered to `g`, over the first lowering. -/
def glbLowerRight (v : FitFlex e) {g : Head} (glbm : GlbMeets v g) (distinct : v.right ≠ v.left) :
    CodomainLowering (glbLowerLeft v glbm).target where
  index := v.right
  ps := [v.pr]
  lower := g
  upper := v.cr
  declared := ((glbLowerLeft v glbm).lookup_ne distinct).trans v.declared_right
  universes := fun _ member => (List.mem_singleton.mp member) ▸ v.universe_pr
  universe_lower := glbm.1.1
  universe_upper := v.universe_cr
  below := glbm.1.2.2.1

include facts roots heads algebra rigid complete headTypingUnique in
theorem glbLowerLeft_forced (v : FitFlex e) {g : Head} (glbm : GlbMeets v g) (rest : EquationStore (TotalTerm Θ)) :
    (glbLowerLeft v glbm).Forced (e :: rest) := fun f solved =>
  glb_forced_left facts roots heads algebra rigid complete headTypingUnique v glbm f (solved e List.mem_cons_self)

include facts roots heads algebra rigid complete headTypingUnique in
theorem glbLowerRight_forced (v : FitFlex e) {g : Head} (glbm : GlbMeets v g) (distinct : v.right ≠ v.left)
    (rest : EquationStore (TotalTerm Θ)) :
    (glbLowerRight v glbm distinct).Forced ((frames S.levels).applyStore (glbLowerLeft v glbm).hom (e :: rest)) := by
  intro Δ f solved
  have back := (Frames.models_applyStore (X := frames S.levels) _ f (e :: rest)).mp solved
  exact glb_forced_right facts roots heads algebra rigid complete headTypingUnique v glbm
    (f ≫ (glbLowerLeft v glbm).hom) (back e List.mem_cons_self)

/-- **Over the twice-lowered telescope the right unknown fits the left**: the equation read there, for domain
raising `left := λ x. right x`. -/
def glbFits (v : FitFlex e) {g : Head} (glbm : GlbMeets v g) (distinct : v.right ≠ v.left) :
    FitsView (((frames S.levels).act (glbLowerRight v glbm distinct).hom
        ((frames S.levels).act (glbLowerLeft v glbm).hom e.1),
      (frames S.levels).act (glbLowerRight v glbm distinct).hom
        ((frames S.levels).act (glbLowerLeft v glbm).hom e.2)) :
      Equation (TotalTerm (glbLowerRight v glbm distinct).target)) where
  p := v.p
  q := v.q
  G := v.left
  F := v.right
  pG := v.pl
  cG := g
  pF := v.pr
  cF := g
  distinct := distinct
  annotation_left := by
    change Presentation.subst ids (Presentation.subst ids e.1.1.code) = famCode [v.p] v.q
    rw [subst_ids, subst_ids]
    exact v.annotation_left
  annotation_right := by
    change Presentation.subst ids (Presentation.subst ids e.2.1.code) = famCode [v.p] v.q
    rw [subst_ids, subst_ids]
    exact v.annotation_right
  side_left := by
    change Presentation.subst ids (Presentation.subst ids e.1.2.code) = etaExp 1 (.var v.left)
    rw [subst_ids, subst_ids]
    exact v.side_left
  side_right := by
    change Presentation.subst ids (Presentation.subst ids e.2.2.code) = etaExp 1 (.var v.right)
    rw [subst_ids, subst_ids]
    exact v.side_right
  declared_G :=
    ((glbLowerRight v glbm distinct).lookup_ne (fun same => distinct same.symm)).trans
      (glbLowerLeft v glbm).lookup_self
  declared_F := (glbLowerRight v glbm distinct).lookup_self
  universe_p := v.universe_p
  universe_q := v.universe_q
  universe_pG := v.universe_pl
  universe_cG := glbm.1.1
  universe_pF := v.universe_pr
  universe_cF := glbm.1.1
  domain_G := v.domain_left
  domain_F := glbm.2.1
  codomain_F := S.levels.cumulative_refl glbm.1.1
  codomain_G := algebra.trans glbm.1.2.1 v.codomain_left

variable [DecidableEq Head] [DecidableRel S.R.cumulative]

/-- **The greatest-lower-bound rule**: both unknowns lowered to `g`, then `left := λ x. right x` with the other
equations re-read. -/
def glbMeetUpdate (v : FitFlex e) {g : Head} (glbm : GlbMeets v g) (distinct : v.right ≠ v.left)
    (all : AllFamilies Θ) (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) :=
  (lowerAtUpdate (glbLowerLeft v glbm) (e :: rest)
      (glbLowerLeft_forced facts roots heads algebra rigid complete headTypingUnique v glbm rest)).then
    ((lowerAtUpdate (glbLowerRight v glbm distinct) _
        (glbLowerRight_forced facts roots heads algebra rigid complete headTypingUnique v glbm distinct rest)).then
      (raiseContractUpdate algebra facts roots heads rigid complete (glbFits algebra v glbm distinct)
        ((glbLowerRight v glbm distinct).families ((glbLowerLeft v glbm).families all))
        ((frames S.levels).applyStore (glbLowerRight v glbm distinct).hom
          ((frames S.levels).applyStore (glbLowerLeft v glbm).hom rest))))

/-- **The greatest-lower-bound rule is exact.** -/
theorem glbMeet_exact (v : FitFlex e) {g : Head} (glbm : GlbMeets v g) (distinct : v.right ≠ v.left)
    (all : AllFamilies Θ) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest)
      (glbMeetUpdate facts roots heads algebra rigid complete headTypingUnique v glbm distinct all rest).answer
      (glbMeetUpdate facts roots heads algebra rigid complete headTypingUnique v glbm distinct all rest).remaining :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr ⟨_, rfl, rfl, rfl⟩

end Rule

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
