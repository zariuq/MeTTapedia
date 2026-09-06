import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.LogicalRelationModel
import Mettapedia.Logic.HOL.Syntax.PartialConstSubstitution

/-!
# Henkin semantics of closed-term constant substitution

Interpreting each source constant by a closed target term gives a Henkin-model
reduct with exactly the target's carriers and admissible domains. Its closure
law follows from the actual `substConst` operation and target term closure.
No full-domain or extensional-congruence assumption is needed for the reduct
or its satisfaction condition.

This is constant-to-term interpretation at fixed simple types. Type-changing
interpretations have separate admissibility obligations. Constants may be
expanded to compound terms; they need not be renamed to other constants.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v v' v'' w

variable {Base : Type u} {Const : Ty Base → Type v}
  {Const' : Ty Base → Type v'} {Const'' : Ty Base → Type v''}

namespace HenkinModel

/-- A closed term is independent of the chosen elimination of the empty
variable context. This also identifies separately elaborated empty valuations. -/
theorem denote_closed_valuation_eq (M : HenkinModel.{u, v, w} Base Const)
    {τ : Ty Base} (term : ClosedTerm Const τ) (first second : M.Valuation []) :
    M.denote term first = M.denote term second := by
  congr 1
  funext type index
  nomatch index

/-- A closed term has the same denotation after weakening into any context. -/
theorem denote_weakenCtx (M : HenkinModel.{u, v', w} Base Const')
    (Γ : Ctx Base) {τ : Ty Base} (term : ClosedTerm Const' τ)
    (valuation : M.Valuation Γ) :
    M.denote (weakenCtx Γ term) valuation =
      M.denote term (fun v => nomatch v) := by
  induction Γ with
  | nil =>
      congr 1
      funext _ v
      nomatch v
  | cons σ Γ ih =>
      rw [weakenCtx_cons, weaken, Soundness.denote_rename]
      exact ih _

/-- Interpret source constants by denotations of the specified closed terms,
without changing the target's carriers or quantifier domains. -/
def constantSubstitutionPreModel
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (M : HenkinModel.{u, v', w} Base Const') : PreModel.{u, v, w} Base Const where
  Carrier := M.Carrier
  adm := M.adm
  base_mem := M.base_mem
  prop_mem := M.prop_mem
  app_mem := M.app_mem
  constDen constant := M.denote (definitions constant) (fun v => nomatch v)
  const_mem constant := M.term_closed (definitions constant) (fun v => nomatch v)
    (by intro _ v; nomatch v)

/-- Intrinsic equality depends on carriers and domains, not on how constants
are presented. -/
theorem eqv_constantSubstitutionPreModel
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (M : HenkinModel.{u, v', w} Base Const') :
    ∀ (τ : Ty Base) (left right : Ty.denote M.Carrier τ),
      (constantSubstitutionPreModel definitions M).Eqv τ left right ↔ M.Eqv τ left right := by
  intro τ
  induction τ with
  | prop => intro _ _; rfl
  | base => intro _ _; rfl
  | arr σ τ _ ih =>
      intro left right
      constructor
      · intro related value admitted
        exact (ih _ _).mp (related value admitted)
      · intro related value admitted
        exact (ih _ _).mpr (related value admitted)

/-- The substitution lemma precedes model closure: it is proved structurally
from `substConst`, including the weakening of each closed replacement. -/
theorem denote_constantSubstitutionPreModel
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (M : HenkinModel.{u, v', w} Base Const') :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ)
      (valuation : M.Valuation Γ),
      (constantSubstitutionPreModel definitions M).denote term valuation =
        M.denote (substConst definitions term) valuation := by
  intro Γ τ term
  induction term with
  | var => intro _; rfl
  | const constant =>
      intro valuation
      exact (denote_weakenCtx M _ (definitions constant) valuation).symm
  | app function argument ihf iha =>
      intro valuation
      simp only [PreModel.denote, HenkinModel.denote, substConst]
      rw [ihf valuation, iha valuation]
  | lam body ih =>
      intro valuation
      funext value
      exact ih (M.extend valuation value)
  | top => intro _; rfl
  | bot => intro _; rfl
  | and left right ihl ihr | or left right ihl ihr | imp left right ihl ihr =>
      intro valuation
      simp only [PreModel.denote, HenkinModel.denote, substConst]
      rw [ihl valuation, ihr valuation]
  | not body ih =>
      intro valuation
      simp only [PreModel.denote, HenkinModel.denote, substConst]
      rw [ih valuation]
  | eq left right ihl ihr =>
      intro valuation
      simp only [PreModel.denote, HenkinModel.denote, substConst]
      rw [ihl valuation, ihr valuation]
      congr 1
      exact propext (eqv_constantSubstitutionPreModel definitions M _ _ _)
  | all body ih =>
      intro valuation
      apply congrArg ULift.up
      apply propext
      constructor
      · intro holds value admitted
        exact (congrArg ULift.down (ih (M.extend valuation value))).mp (holds value admitted)
      · intro holds value admitted
        exact (congrArg ULift.down (ih (M.extend valuation value))).mpr (holds value admitted)
  | ex body ih =>
      intro valuation
      apply congrArg ULift.up
      apply propext
      constructor
      · rintro ⟨value, admitted, holds⟩
        refine ⟨value, admitted, ?_⟩
        exact (congrArg ULift.down (ih (M.extend valuation value))).mp holds
      · rintro ⟨value, admitted, holds⟩
        refine ⟨value, admitted, ?_⟩
        exact (congrArg ULift.down (ih (M.extend valuation value))).mpr holds

/-- Closed-term interpretations induce genuine Henkin reducts: closure is
inherited through the proved substitution lemma, not an extra assumption. -/
def constantSubstitutionReduct
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (M : HenkinModel.{u, v', w} Base Const') : HenkinModel.{u, v, w} Base Const where
  toPreModel := constantSubstitutionPreModel definitions M
  term_closed := by
    intro Γ τ term valuation admitted
    rw [denote_constantSubstitutionPreModel]
    exact M.term_closed (substConst definitions term) valuation admitted

/-- Closed-term substitution commutes exactly with term denotation, even at
non-admissible valuations. Admissibility is needed for closure, not this law. -/
theorem denote_substConst
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (M : HenkinModel.{u, v', w} Base Const') {Γ : Ctx Base} {τ : Ty Base}
    (term : Term Const Γ τ) (valuation : M.Valuation Γ) :
    M.denote (substConst definitions term) valuation =
      (constantSubstitutionReduct definitions M).denote term valuation :=
  (denote_constantSubstitutionPreModel definitions M term valuation).symm

theorem models_substConst
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (M : HenkinModel.{u, v', w} Base Const') (formula : ClosedFormula Const) :
    M.models (substConst definitions formula) ↔
      (constantSubstitutionReduct definitions M).models formula :=
  Iff.of_eq (congrArg ULift.down
    (denote_substConst definitions M formula (fun v => nomatch v)))

theorem eqv_constantSubstitutionReduct
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (M : HenkinModel.{u, v', w} Base Const') (τ : Ty Base)
    (left right : Ty.denote M.Carrier τ) :
    (constantSubstitutionReduct definitions M).Eqv τ left right ↔ M.Eqv τ left right :=
  eqv_constantSubstitutionPreModel definitions M τ left right

/-- Fullness is unchanged, rather than required or manufactured. -/
theorem constantSubstitutionReduct_fullDomains_iff
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (M : HenkinModel.{u, v', w} Base Const') :
    (constantSubstitutionReduct definitions M).FullDomains ↔ M.FullDomains :=
  Iff.rfl

/-- The extensional-congruence property is preserved and reflected. -/
theorem constantSubstitutionReduct_functionsRespectEqv_iff
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (M : HenkinModel.{u, v', w} Base Const') :
    (constantSubstitutionReduct definitions M).FunctionsRespectEqv ↔ M.FunctionsRespectEqv := by
  constructor
  · intro respects σ τ function left right hf hl hr equal
    exact (eqv_constantSubstitutionReduct definitions M τ _ _).mp
      (respects hf hl hr ((eqv_constantSubstitutionReduct definitions M σ _ _).mpr equal))
  · intro respects σ τ function left right hf hl hr equal
    exact (eqv_constantSubstitutionReduct definitions M τ _ _).mpr
      (respects hf hl hr ((eqv_constantSubstitutionReduct definitions M σ _ _).mp equal))

@[simp] theorem constantSubstitutionReduct_id (M : HenkinModel.{u, v, w} Base Const) :
    constantSubstitutionReduct (fun constant => .const constant) M = M := by
  apply ext_data rfl
  · rfl
  · rfl

/-- Successive closed definitions compose as complete model data, with no
normalization or fullness premise. -/
theorem constantSubstitutionReduct_comp
    (first : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (second : ∀ {τ}, Const' τ → ClosedTerm Const'' τ)
    (M : HenkinModel.{u, v'', w} Base Const'') :
    constantSubstitutionReduct first (constantSubstitutionReduct second M) =
      constantSubstitutionReduct (fun constant => substConst second (first constant)) M := by
  apply ext_data
    (M := constantSubstitutionReduct first (constantSubstitutionReduct second M))
    (N := constantSubstitutionReduct (fun constant => substConst second (first constant)) M) rfl
  · rfl
  · apply heq_of_eq
    funext τ constant
    exact denote_constantSubstitutionPreModel second M (first constant) (fun v => nomatch v)

/-- An independently chosen source model is the definition reduct when its
frame agrees with the target frame and every source constant has the declared
definition's denotation. Agreement is required only on individual constants. -/
theorem eq_constantSubstitutionReduct_of_agreement
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (source : HenkinModel.{u, v, w} Base Const)
    (target : HenkinModel.{u, v', w} Base Const')
    (carriers : source.Carrier = target.Carrier)
    (domains : HEq source.adm target.adm)
    (constants : ∀ {τ} (constant : Const τ),
      HEq (source.constDen constant)
        (target.denote (definitions constant) (fun v => nomatch v))) :
    source = constantSubstitutionReduct definitions target := by
  apply ext_data (M := source) (N := constantSubstitutionReduct definitions target) carriers domains
  apply Function.hfunext rfl
  intro τ τ' same_type
  cases eq_of_heq same_type
  apply Function.hfunext rfl
  intro constant constant' same_constant
  cases eq_of_heq same_constant
  exact constants constant

/-- The satisfaction comparison applies to an independently chosen source
model, provided the individual definitions have the stated meanings there. -/
theorem models_substConst_of_agreement
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const' τ)
    (source : HenkinModel.{u, v, w} Base Const)
    (target : HenkinModel.{u, v', w} Base Const')
    (carriers : source.Carrier = target.Carrier)
    (domains : HEq source.adm target.adm)
    (constants : ∀ {τ} (constant : Const τ),
      HEq (source.constDen constant)
        (target.denote (definitions constant) (fun v => nomatch v)))
    (formula : ClosedFormula Const) :
    target.models (substConst definitions formula) ↔ source.models formula := by
  rw [eq_constantSubstitutionReduct_of_agreement definitions source target carriers domains constants]
  exact models_substConst definitions target formula

/-- Replacing definitions inside the same model leaves its interpretation
unchanged exactly when the individual constant denotations agree. -/
theorem constantSubstitutionReduct_eq_self_iff
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const τ)
    (M : HenkinModel.{u, v, w} Base Const) :
    constantSubstitutionReduct definitions M = M ↔
      ∀ {τ} (constant : Const τ),
        M.denote (definitions constant) (fun v => nomatch v) = M.constDen constant := by
  constructor
  · intro same τ constant
    have constants : HEq @(constantSubstitutionReduct definitions M).constDen @M.constDen := by
      rw [same]
    exact congrFun (congrFun (eq_of_heq constants) τ) constant
  · intro constants
    exact (eq_constantSubstitutionReduct_of_agreement definitions M M rfl HEq.rfl
      (fun constant => heq_of_eq (constants constant).symm)).symm

/-- Per-constant denotation agreement proves preservation for every term in
an independently chosen model, including open terms under arbitrary valuations.
This is literal denotation equality, not just intrinsic `Eqv`. -/
theorem denote_substConst_of_constantAgreement
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const τ)
    (M : HenkinModel.{u, v, w} Base Const)
    (constants : ∀ {τ} (constant : Const τ),
      M.denote (definitions constant) (fun v => nomatch v) = M.constDen constant)
    {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) (valuation : M.Valuation Γ) :
    M.denote (substConst definitions term) valuation = M.denote term valuation := by
  have same := (constantSubstitutionReduct_eq_self_iff definitions M).mpr constants
  have denotations : HEq @(constantSubstitutionReduct definitions M).denote @M.denote := by
    rw [same]
  exact (denote_substConst definitions M term valuation).trans
    (congrFun (congrFun (congrFun (congrFun (eq_of_heq denotations) Γ) τ) term) valuation)

/-- Full-term preservation is characterized by independently stated agreement
on constants. Necessity is recovered by testing individual constant terms. -/
theorem substConst_preserves_denotation_iff
    (definitions : ∀ {τ}, Const τ → ClosedTerm Const τ)
    (M : HenkinModel.{u, v, w} Base Const) :
    (∀ {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) (valuation : M.Valuation Γ),
      M.denote (substConst definitions term) valuation = M.denote term valuation) ↔
      ∀ {τ} (constant : Const τ),
        M.denote (definitions constant) (fun v => nomatch v) = M.constDen constant := by
  constructor
  · intro preserves τ constant
    exact preserves (.const constant : ClosedTerm Const τ) (fun v => nomatch v)
  · intro constants Γ τ term valuation
    exact denote_substConst_of_constantAgreement definitions M constants term valuation

/-- A successful partial substitution preserves denotation when each available
replacement has its original constant's meaning. Unavailable entries are completed
by the original constant, without requiring that they occur in the term. -/
theorem denote_substConst?_of_constantAgreement
    (replacements : ∀ {τ : Ty Base}, Const τ → Option (ClosedTerm Const τ))
    (M : HenkinModel.{u, v, w} Base Const)
    (constants : ∀ {τ : Ty Base} (constant : Const τ) (replacement : ClosedTerm Const τ),
      replacements constant = some replacement →
        M.denote replacement (fun v => nomatch v) = M.constDen constant)
    {Γ : Ctx Base} {τ : Ty Base} (term result : Term Const Γ τ)
    (success : substConst? replacements term = some result) (valuation : M.Valuation Γ) :
    M.denote result valuation = M.denote term valuation := by
  let completed : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const τ :=
    fun constant => (replacements constant).getD (.const constant)
  have agreement : ∀ {τ : Ty Base} (constant : Const τ) (replacement : ClosedTerm Const τ),
      replacements constant = some replacement → replacement = completed constant := by
    intro τ constant replacement available
    simp [completed, available]
  rw [substConst?_success_eq replacements completed agreement term result success]
  apply denote_substConst_of_constantAgreement completed M
  intro τ constant
  dsimp only [completed]
  cases available : replacements constant with
  | none => rfl
  | some replacement => exact constants constant replacement available

end HenkinModel

namespace ConstantSubstitutionExample

/-- A named higher-order operation, without a built-in meaning. -/
inductive Constants : Ty Unit → Type where
  | iterate : Constants ((.prop ⇒ .prop) ⇒ .prop ⇒ .prop)

/-- Interpret the operation by a closed lambda-term that applies its argument twice. -/
def twice {τ : Ty Unit} : Constants τ → ClosedTerm MonotoneBooleanModel.Constants τ
  | .iterate => .lam (.lam (.app (.var (.vs .vz))
      (.app (.var (.vs .vz)) (.var .vz))))

/-- A different, equally well-typed declaration applies its argument only once. -/
def once {τ : Ty Unit} : Constants τ → ClosedTerm MonotoneBooleanModel.Constants τ
  | .iterate => .lam (.lam (.app (.var (.vs .vz)) (.var .vz)))

/-- The named operation iterates Boolean negation to the original proposition. -/
def doubleNegation : ClosedFormula Constants :=
  .all (σ := .prop) (.eq
    (.app (.app (.const .iterate) (.lam (.not (.var .vz)))) (.var .vz))
    (.var .vz))

theorem twice_models_doubleNegation :
    (HenkinModel.constantSubstitutionReduct twice MonotoneBooleanModel.model).models
      doubleNegation := by
  classical
  change ∀ proposition : ULift.{1} Prop, True → ((¬¬ proposition.down) ↔ proposition.down)
  simp

/-- Well-typed replacement alone does not preserve a previously chosen meaning. -/
theorem once_refutes_doubleNegation :
    ¬ (HenkinModel.constantSubstitutionReduct once MonotoneBooleanModel.model).models
      doubleNegation := by
  change ¬ (∀ proposition : ULift.{1} Prop, True → ((¬ proposition.down) ↔ proposition.down))
  intro holds
  have impossible := (holds ⟨True⟩ True.intro).mpr True.intro
  exact impossible True.intro

/-- This interpretation genuinely retains non-full Henkin domains. -/
theorem twiceReduct_not_fullDomains :
    ¬ (HenkinModel.constantSubstitutionReduct twice MonotoneBooleanModel.model).FullDomains := by
  rw [HenkinModel.constantSubstitutionReduct_fullDomains_iff]
  exact MonotoneBooleanModel.not_fullDomains

/-- A successful closed-term interpretation transports the specified sentence. -/
theorem substituted_doubleNegation_valid :
    MonotoneBooleanModel.model.models (substConst twice doubleNegation) :=
  (HenkinModel.models_substConst twice MonotoneBooleanModel.model doubleNegation).mpr
    twice_models_doubleNegation

end ConstantSubstitutionExample

#print axioms HenkinModel.constantSubstitutionReduct
#print axioms HenkinModel.denote_substConst
#print axioms HenkinModel.models_substConst
#print axioms HenkinModel.constantSubstitutionReduct_functionsRespectEqv_iff
#print axioms HenkinModel.constantSubstitutionReduct_comp
#print axioms HenkinModel.eq_constantSubstitutionReduct_of_agreement
#print axioms HenkinModel.denote_substConst_of_constantAgreement
#print axioms HenkinModel.substConst_preserves_denotation_iff
#print axioms HenkinModel.denote_substConst?_of_constantAgreement
#print axioms ConstantSubstitutionExample.twice_models_doubleNegation
#print axioms ConstantSubstitutionExample.once_refutes_doubleNegation
#print axioms ConstantSubstitutionExample.twiceReduct_not_fullDomains

end Mettapedia.Logic.HOL
