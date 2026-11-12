import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinNecessity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.StrictInitiality

/-!
# The glb join's condition is necessary: every usable position that fails it

`CrossAt` asks of a position usable on both sides (`pX` below `cX`, `pY` below `cY`) that each domain lie below the
other side's codomain. Here: **wherever it fails, there is no principal answer**, as soon as the identity and a
constant family solve the store, whatever the setting.

* **No common answer across the condition** (`no_common_answer_cross`): let `aX` be a family of `U_pX → U_cX` and `aY`
  one of `U_pY → U_cY` that agree at a variable of `U_p`, with `p` below both domains, and `pY` not below `cX`. Then
  `aY` has no instance equal to the identity together with an instance equal to a constant family. The normal form
  `Z` of `aY z` is, over `z : U_p`, a type of `U_cX`; the identity makes it neutral; it is not `z` itself, by the
  constant; so it keeps its principal type over `z : U_pY`, where it is a type of `U_cX` equal to `z`, and `z : U_pY`
  is no type of `U_cX`.
* **The store-level theorems** (`no_principal_of_right_apart`, `no_principal_of_left_apart`,
  **`no_principal_of_not_crossAt`**): for a unary flex–flex equation of a store, a failure of `CrossAt` and two
  solutions of the store, one sending both unknowns to the identity and one to a constant family, leave the store
  without a principal answer.
* **Instances** (`ctr_no_principal_general`, `cross_no_principal_general`): the counterexample with incomparable
  codomains and the cross store, both by the general theorem.

With `glbJoinK_exact`, the condition is thus exactly what a principal answer of a unary flex–flex equation needs, in
every setting where the identity and a constant family solve the failing stores.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentUniverseInjective

variable {Head L : Type} [UniverseLevel.LevelOrder L]

section General

variable {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **No answer is common to the identity and to a constant family across a failed condition.** -/
theorem no_common_answer_cross (noConstants : ∀ name, S.R.constantType name = none) {n : Nat} {Δ : Ctx Head n}
    (formed : CtxFormed S.R Δ) {p pX cX pY cY q g : Head} (hp : S.R.isUniverse p) (hcX : S.R.isUniverse cX)
    (hpY : S.R.isUniverse pY) (hcY : S.R.isUniverse cY) (hq : S.R.isUniverse q) (dX : S.R.cumulative p pX)
    (dY : S.R.cumulative p pY) (cYq : S.R.cumulative cY q) (apart : ¬ S.R.cumulative pY cX) {aX aY : Tm Head n}
    (tX : Typed S.R Δ aX (.pi (.head pX) (.head cX))) (tY : Typed S.R Δ aY (.pi (.head pY) (.head cY)))
    (agree : Equal S.R (.snoc Δ (.head p)) (.app (Presentation.rename wk aX) (.var 0))
      (.app (Presentation.rename wk aY) (.var 0)) (.head q))
    {m₁ : Nat} {Γ₁ : Ctx Head m₁} (formed₁ : CtxFormed S.R Γ₁) {ρ₁ : Sub Head n m₁} (typed₁ : SubstMor S.R Δ Γ₁ ρ₁)
    (identity : Equal S.R Γ₁ (.lam (.var 0)) (Presentation.subst ρ₁ aY) (.pi (.head pY) (.head cY)))
    {m₂ : Nat} {Γ₂ : Ctx Head m₂} (formed₂ : CtxFormed S.R Γ₂) {ρ₂ : Sub Head n m₂} (typed₂ : SubstMor S.R Δ Γ₂ ρ₂)
    (constant : Equal S.R Γ₂ (.lam (.head g)) (Presentation.subst ρ₂ aY) (.pi (.head pY) (.head cY))) : False := by
  have isY : ∀ {k : Nat} (Γ : Ctx Head k), IsType S.R Γ (.head pY) := fun _ => IsType.head_of_universe hpY
  have formedW : CtxFormed S.R (.snoc Δ (.head pY)) := formed.snoc (isY Δ)
  have formedN : CtxFormed S.R (.snoc Δ (.head p)) := formed.snoc (IsType.head_of_universe hp)
  have formedE₁ : CtxFormed S.R (.snoc Γ₁ (.head pY)) := formed₁.snoc (isY Γ₁)
  have formedE₂ : CtxFormed S.R (.snoc Γ₂ (.head pY)) := formed₂.snoc (isY Γ₂)
  have narrows : CtxNarrows S.R (.snoc Δ (.head pY)) (.snoc Δ (.head p)) := .lower (CtxNarrows.refl Δ) dY
  have typedT : Typed S.R (.snoc Δ (.head pY)) (.app (Presentation.rename wk aY) (.var 0)) (.head cY) :=
    Derivable.appElim (tY.rename (CtxRen.wk Δ (.head pY))) (Derivable.var (R := S.R) (Γ := .snoc Δ (.head pY)) 0)
  have typedS : Typed S.R (.snoc Δ (.head p)) (.app (Presentation.rename wk aX) (.var 0)) (.head cX) :=
    Derivable.appElim (tX.rename (CtxRen.wk Δ (.head p)))
      (Derivable.cumul (Derivable.var (R := S.R) (Γ := .snoc Δ (.head p)) 0) dX)
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formedW ⟨cY, hcY, typedT⟩
  obtain ⟨_, eZ⟩ := atZ hcY typedT
  have smallN : Typed S.R (.snoc Δ (.head p)) Z (.head cX) :=
    normal_typed_of_equal facts roots heads algebra rigid complete formedN hcX typedS
      ⟨q, hq, .trans agree (Derivable.cumulEq (equal_narrow narrows eZ) cYq)⟩
      (Long.type_narrow facts lZ narrows formedW formedN)
  -- The instances of `Z` under the two factorizations.
  have code : ∀ {m : Nat} (ρ : Sub Head n m),
      Presentation.subst (liftSub ρ) (.app (Presentation.rename wk aY) (.var 0)) =
        .app (Presentation.rename wk (Presentation.subst ρ aY)) (.var 0) := by
    intro m ρ
    change Tm.app (Presentation.subst (liftSub ρ) (Presentation.rename wk aY)) (.var 0) = _
    rw [subst_liftSub_wk]
  have first : Equal S.R (.snoc Γ₁ (.head pY)) (.var 0) (Presentation.subst (liftSub ρ₁) Z) (.head cY) := by
    have opened := equal_of_lam_left facts formed₁ identity
    rw [← code ρ₁] at opened
    exact .trans opened (eZ.substitute (typed₁.lift (.head pY)))
  have second : Equal S.R (.snoc Γ₂ (.head pY)) (.head g) (Presentation.subst (liftSub ρ₂) Z) (.head cY) := by
    have opened := equal_of_lam_left facts formed₂ constant
    rw [← code ρ₂] at opened
    exact .trans opened (eZ.substitute (typed₂.lift (.head pY)))
  have firstType : TypeEq S.R (.snoc Γ₁ (.head pY)) (.var 0) (Presentation.subst (liftSub ρ₁) Z) :=
    ⟨cY, hcY, first⟩
  have formers := var_not_former facts formedE₁ 0 firstType
  -- A type of `U_cX` over the wide declaration contradicts the identity.
  have finish : Typed S.R (.snoc Δ (.head pY)) Z (.head cX) → False := fun small =>
    var_not_small facts roots heads algebra rigid complete formedE₁ rfl hpY hcX apart
      (small.substitute (typed₁.lift (.head pY))) firstType.symm
  cases lZ with
  | head _ => exact formers.1 _ rfl
  | pi _ _ _ => exact formers.2.1 _ _ rfl
  | sigma _ _ _ => exact formers.2.2.1 _ _ rfl
  | id _ _ _ _ => exact formers.2.2.2 _ _ _ rfl
  | neutralType ls htop le =>
      cases ls with
      | var i e =>
          cases i using Fin.cases with
          | zero =>
              have secondType : TypeEq S.R (.snoc Γ₂ (.head pY)) (.var 0) (.head g) := ⟨cY, hcY, .symm second⟩
              exact (var_not_former facts formedE₂ 0 secondType).1 _ rfl
          | succ j =>
              exact finish (spine_small_wide facts algebra narrows formedW formedN (.var j.succ e)
                (.var j.succ (typeEq_narrow narrows e)) htop le smallN)
      | const _ declared _ _ =>
          rw [noConstants] at declared
          cases declared
      | app lf eF la eU =>
          rcases Long.narrow facts lf narrows formedW formedN with kept | ⟨_, _, e, _, _⟩
          · exact finish (spine_small_wide facts algebra narrows formedW formedN (.app lf eF la eU)
              (.app kept (typeEq_narrow narrows eF) (Long.term_narrow facts la narrows formedW formedN)
                (typeEq_narrow narrows eU)) htop le smallN)
          · exact absurd (TypeEq.trans S.levels eF.symm e) (TypeEq.pi_ne_head facts formedW)
      | fst lp eP eU =>
          rcases Long.narrow facts lp narrows formedW formedN with kept | ⟨_, _, e, _, _⟩
          · exact finish (spine_small_wide facts algebra narrows formedW formedN (.fst lp eP eU)
              (.fst kept (typeEq_narrow narrows eP) (typeEq_narrow narrows eU)) htop le smallN)
          · exact absurd (TypeEq.trans S.levels eP.symm e) (TypeEq.sigma_ne_head facts formedW)
      | snd lp eP eU =>
          rcases Long.narrow facts lp narrows formedW formedN with kept | ⟨_, _, e, _, _⟩
          · exact finish (spine_small_wide facts algebra narrows formedW formedN (.snd lp eP eU)
              (.snd kept (typeEq_narrow narrows eP) (typeEq_narrow narrows eU)) htop le smallN)
          · exact absurd (TypeEq.trans S.levels eP.symm e) (TypeEq.sigma_ne_head facts formedW)

/-- The instance of an unknown, read through a factorization of a solution. -/
theorem factored_value {Θ Δ₀ Δ : Context S.R} {f : Δ₀ ⟶ Θ} {answer : Δ ⟶ Θ} {ρ : Δ₀ ⟶ Δ}
    (factor : ∀ t : TotalTerm Θ, (frames S.levels).E (t.reindex f) (t.reindex (ρ ≫ answer))) (i : Fin Θ.arity)
    {ps : List Head} {c : Head} (declared : Ctx.lookup Θ.raw i = famCode ps c) :
    Equal S.R Δ₀.raw (f.substitution i) (Presentation.subst ρ.substitution (answer.substitution i)) (famCode ps c) := by
  have e := (factor (unknownTerm Θ i)).2
  change Equal S.R Δ₀.raw (f.substitution i) (Presentation.subst ρ.substitution (answer.substitution i))
    (Presentation.subst f.substitution (Ctx.lookup Θ.raw i)) at e
  rw [declared, famCode_subst] at e
  exact e

include facts roots heads algebra rigid complete in
/-- **The right domain not below the left codomain**: no principal answer, when the identity and a constant family
solve the store at the right unknown. -/
theorem no_principal_of_right_apart (noConstants : ∀ name, S.R.constantType name = none) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {e : Equation (TotalTerm Θ)} (member : e ∈ problem) (v : FitFlex e)
    (apart : ¬ S.R.cumulative v.pr v.cl)
    {Δ₁ : Context S.R} (f₁ : Δ₁ ⟶ Θ) (solved₁ : (frames S.levels).Models f₁ problem)
    (identity : Equal S.R Δ₁.raw (.lam (.var 0)) (f₁.substitution v.right) (famCode [v.pr] v.cr))
    {Δ₂ : Context S.R} (f₂ : Δ₂ ⟶ Θ) (solved₂ : (frames S.levels).Models f₂ problem) {g : Head}
    (constant : Equal S.R Δ₂.raw (.lam (.head g)) (f₂.substitution v.right) (famCode [v.pr] v.cr))
    {Δ : Context S.R} (answer : Δ ⟶ Θ) : ¬ (frames S.levels).Principal problem answer := by
  intro principal
  have agree := fitFlex_opened facts v answer (principal.sound e member)
  obtain ⟨ρ₁, factor₁⟩ := principal.factors _ f₁ solved₁
  obtain ⟨ρ₂, factor₂⟩ := principal.factors _ f₂ solved₂
  exact no_common_answer_cross facts roots heads algebra rigid complete noConstants Δ.formed v.universe_p
    v.universe_cl v.universe_pr v.universe_cr v.universe_q v.domain_left v.domain_right v.codomain_right apart
    (fitFlex_left_typed v answer) (fitFlex_right_typed v answer) agree Δ₁.formed ρ₁.typed
    (identity.trans (factored_value factor₁ v.right v.declared_right)) Δ₂.formed ρ₂.typed
    (constant.trans (factored_value factor₂ v.right v.declared_right))

include facts roots heads algebra rigid complete in
/-- **The left domain not below the right codomain**: no principal answer, when the identity and a constant family
solve the store at the left unknown. -/
theorem no_principal_of_left_apart (noConstants : ∀ name, S.R.constantType name = none) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {e : Equation (TotalTerm Θ)} (member : e ∈ problem) (v : FitFlex e)
    (apart : ¬ S.R.cumulative v.pl v.cr)
    {Δ₁ : Context S.R} (f₁ : Δ₁ ⟶ Θ) (solved₁ : (frames S.levels).Models f₁ problem)
    (identity : Equal S.R Δ₁.raw (.lam (.var 0)) (f₁.substitution v.left) (famCode [v.pl] v.cl))
    {Δ₂ : Context S.R} (f₂ : Δ₂ ⟶ Θ) (solved₂ : (frames S.levels).Models f₂ problem) {g : Head}
    (constant : Equal S.R Δ₂.raw (.lam (.head g)) (f₂.substitution v.left) (famCode [v.pl] v.cl))
    {Δ : Context S.R} (answer : Δ ⟶ Θ) : ¬ (frames S.levels).Principal problem answer := by
  intro principal
  have agree := fitFlex_opened facts v answer (principal.sound e member)
  obtain ⟨ρ₁, factor₁⟩ := principal.factors _ f₁ solved₁
  obtain ⟨ρ₂, factor₂⟩ := principal.factors _ f₂ solved₂
  exact no_common_answer_cross facts roots heads algebra rigid complete noConstants Δ.formed v.universe_p
    v.universe_cr v.universe_pl v.universe_cl v.universe_q v.domain_right v.domain_left v.codomain_left apart
    (fitFlex_right_typed v answer) (fitFlex_left_typed v answer) agree.symm Δ₁.formed ρ₁.typed
    (identity.trans (factored_value factor₁ v.left v.declared_left)) Δ₂.formed ρ₂.typed
    (constant.trans (factored_value factor₂ v.left v.declared_left))

include facts roots heads algebra rigid complete in
/-- **Wherever the condition fails, there is no principal answer**, when the identity and a constant family solve the
store at both unknowns. -/
theorem no_principal_of_not_crossAt (noConstants : ∀ name, S.R.constantType name = none) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {e : Equation (TotalTerm Θ)} (member : e ∈ problem) (v : FitFlex e)
    (fails : ¬ CrossAt S.R v.cl v.cr v.pl v.pr)
    {Δ₁ : Context S.R} (f₁ : Δ₁ ⟶ Θ) (solved₁ : (frames S.levels).Models f₁ problem)
    (identityL : Equal S.R Δ₁.raw (.lam (.var 0)) (f₁.substitution v.left) (famCode [v.pl] v.cl))
    (identityR : Equal S.R Δ₁.raw (.lam (.var 0)) (f₁.substitution v.right) (famCode [v.pr] v.cr))
    {Δ₂ : Context S.R} (f₂ : Δ₂ ⟶ Θ) (solved₂ : (frames S.levels).Models f₂ problem) {g : Head}
    (constantL : Equal S.R Δ₂.raw (.lam (.head g)) (f₂.substitution v.left) (famCode [v.pl] v.cl))
    (constantR : Equal S.R Δ₂.raw (.lam (.head g)) (f₂.substitution v.right) (famCode [v.pr] v.cr))
    {Δ : Context S.R} (answer : Δ ⟶ Θ) : ¬ (frames S.levels).Principal problem answer := by
  by_cases right : S.R.cumulative v.pr v.cl
  · have left : ¬ S.R.cumulative v.pl v.cr := by
      intro left
      exact fails (fun _ _ => ⟨left, right⟩)
    exact no_principal_of_left_apart facts roots heads algebra rigid complete noConstants member v left f₁ solved₁
      identityL f₂ solved₂ constantL answer
  · exact no_principal_of_right_apart facts roots heads algebra rigid complete noConstants member v right f₁ solved₁
      identityR f₂ solved₂ constantR answer

end General

/-! ## Instances in the tower -/

namespace Controls

open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-- The view of the counterexample's equation: `X : U_a → U_a` on the left, `Y : U0 → U_b` on the right. -/
def ctrView : FitFlex (S := setting) ctrEquation where
  p := U0
  q := Uab
  left := 1
  right := 0
  pl := Ua
  cl := Ua
  pr := U0
  cr := Ub
  annotation_left := by decide +kernel
  annotation_right := by decide +kernel
  side_left := by decide +kernel
  side_right := by decide +kernel
  declared_left := by decide +kernel
  declared_right := by decide +kernel
  universe_p := by decide
  universe_q := by decide
  universe_pl := by decide
  universe_cl := by decide
  universe_pr := by decide
  universe_cr := by decide
  domain_left := by decide +kernel
  domain_right := by decide +kernel
  codomain_left := by decide +kernel
  codomain_right := by decide +kernel

theorem ctrIdentity_values : ctrIdentity.substitution ctrView.left = .lam (.var 0) ∧
    ctrIdentity.substitution ctrView.right = .lam (.var 0) := by decide +kernel

theorem ctrConstant_values : ctrConstant.substitution ctrView.left = .lam (.head .legacyGround) ∧
    ctrConstant.substitution ctrView.right = .lam (.head .legacyGround) := by decide +kernel

/-- **The counterexample with incomparable codomains, by the general theorem.** -/
theorem ctr_no_principal_general {Δ : Context setting.R} (answer : Δ ⟶ ctxCtr) :
    ¬ (frames setting.levels).Principal ctrStore answer := by
  have tL : Typed setting.R (empty setting.R).raw (.lam (.var 0)) (famCode [ctrView.pl] ctrView.cl) := by
    have typed := ctrIdentity.typed ctrView.left
    rw [ctrView.declared_left, famCode_subst, ctrIdentity_values.1] at typed
    exact typed
  have tR : Typed setting.R (empty setting.R).raw (.lam (.var 0)) (famCode [ctrView.pr] ctrView.cr) := by
    have typed := ctrIdentity.typed ctrView.right
    rw [ctrView.declared_right, famCode_subst, ctrIdentity_values.2] at typed
    exact typed
  have gL : Typed setting.R (empty setting.R).raw (.lam (.head .legacyGround)) (famCode [ctrView.pl] ctrView.cl) := by
    have typed := ctrConstant.typed ctrView.left
    rw [ctrView.declared_left, famCode_subst, ctrConstant_values.1] at typed
    exact typed
  have gR : Typed setting.R (empty setting.R).raw (.lam (.head .legacyGround)) (famCode [ctrView.pr] ctrView.cr) := by
    have typed := ctrConstant.typed ctrView.right
    rw [ctrView.declared_right, famCode_subst, ctrConstant_values.2] at typed
    exact typed
  refine no_principal_of_not_crossAt TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete (fun _ => rfl) List.mem_cons_self ctrView
    (by decide +kernel) ctrIdentity ctr_two_answers.1 ?_ ?_ ctrConstant ctr_two_answers.2 (g := .legacyGround) ?_ ?_
    answer
  · rw [ctrIdentity_values.1]
    exact .refl tL
  · rw [ctrIdentity_values.2]
    exact .refl tR
  · rw [ctrConstant_values.1]
    exact .refl gL
  · rw [ctrConstant_values.2]
    exact .refl gR

/-- The view of the cross store's equation: `X : U0 → U0` on the left, `Y : U1 → U1` on the right. -/
def crossViewF : FitFlex (S := setting) crossEquation where
  p := U0
  q := U1
  left := 1
  right := 0
  pl := U0
  cl := U0
  pr := U1
  cr := U1
  annotation_left := by decide +kernel
  annotation_right := by decide +kernel
  side_left := by decide +kernel
  side_right := by decide +kernel
  declared_left := by decide +kernel
  declared_right := by decide +kernel
  universe_p := by decide
  universe_q := by decide
  universe_pl := by decide
  universe_cl := by decide
  universe_pr := by decide
  universe_cr := by decide
  domain_left := by decide +kernel
  domain_right := by decide +kernel
  codomain_left := by decide +kernel
  codomain_right := by decide +kernel

theorem crossIdentity_right : crossIdentity.substitution crossViewF.right = .lam (.var 0) := by decide +kernel
theorem crossConstant_right : crossConstant.substitution crossViewF.right = .lam (.head .legacyGround) := by
  decide +kernel

/-- **The cross store, by the general theorem**: its right domain `U1` is not below the left codomain `U0`. -/
theorem cross_no_principal_general {Δ : Context setting.R} (answer : Δ ⟶ ctxCross) :
    ¬ (frames setting.levels).Principal crossStore answer := by
  have tR : Typed setting.R (empty setting.R).raw (.lam (.var 0)) (famCode [crossViewF.pr] crossViewF.cr) := by
    have typed := crossIdentity.typed crossViewF.right
    rw [crossViewF.declared_right, famCode_subst, crossIdentity_right] at typed
    exact typed
  have gR : Typed setting.R (empty setting.R).raw (.lam (.head .legacyGround))
      (famCode [crossViewF.pr] crossViewF.cr) := by
    have typed := crossConstant.typed crossViewF.right
    rw [crossViewF.declared_right, famCode_subst, crossConstant_right] at typed
    exact typed
  refine no_principal_of_right_apart TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete (fun _ => rfl) List.mem_cons_self crossViewF
    (by decide +kernel) crossIdentity cross_two_answers.2.1 ?_ crossConstant cross_two_answers.2.2
    (g := .legacyGround) ?_ answer
  · rw [crossIdentity_right]
    exact .refl tR
  · rw [crossConstant_right]
    exact .refl gR

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
