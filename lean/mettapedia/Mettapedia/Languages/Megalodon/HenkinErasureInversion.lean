import Mettapedia.Languages.Megalodon.HenkinTermInterpretation

/-!
# Inversion of successful native term erasure

Native constructor shapes determine the corresponding intrinsic constructors.
Erasure retains binder types and declaration identity; lookup witnesses are
proof irrelevant. These statements concern exact syntax, not normalization or
semantic equality. The successful-erasure restriction matters because the
additional HOL connectives intentionally have no native constructor image.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTermInterpretation

open MathdataKernel
open Mettapedia.Logic.HOL

theorem erase_app_inv {environment : Environment} {Γ : Ctx Base} {τ : Ty Base}
    {t : Term (Constant environment) Γ τ} {rawFunction rawArgument : Tm}
    (erased : erase t = some (.app rawFunction rawArgument)) :
    ∃ (σ : Ty Base) (function : Term (Constant environment) Γ (σ ⇒ τ))
      (argument : Term (Constant environment) Γ σ),
      t = .app function argument ∧ erase function = some rawFunction ∧
        erase argument = some rawArgument := by
  cases t with
  | var v => simp [erase] at erased
  | const c => cases c <;> simp [erase, Constant.erase] at erased
  | app function argument =>
      cases hf : erase function <;> cases ha : erase argument <;>
        simp [erase, hf, ha] at erased
      obtain ⟨rfl, rfl⟩ := erased
      exact ⟨_, function, argument, rfl, hf, ha⟩
  | lam body => cases hb : erase body <;> simp [erase, hb] at erased
  | imp left right =>
      cases hl : erase left <;> cases hr : erase right <;> simp [erase, hl, hr] at erased
  | all body => cases hb : erase body <;> simp [erase, hb] at erased
  | top | bot | and _ _ | or _ _ | not _ | eq _ _ | ex _ => simp [erase] at erased

theorem erase_lam_inv {environment : Environment} {Γ : Ctx Base} {σ τ : Ty Base}
    {t : Term (Constant environment) Γ (σ ⇒ τ)} {rawType : Tp} {rawBody : Tm}
    (erased : erase t = some (.lam rawType rawBody)) :
    ∃ body : Term (Constant environment) (σ :: Γ) τ,
      t = .lam body ∧ rawType = reifyType σ ∧ erase body = some rawBody := by
  cases t with
  | var v => simp [erase] at erased
  | const c => cases c <;> simp [erase, Constant.erase] at erased
  | app function argument =>
      cases hf : erase function <;> cases ha : erase argument <;>
        simp [erase, hf, ha] at erased
  | lam body =>
      cases hb : erase body <;> simp [erase, hb] at erased
      obtain ⟨rfl, rfl⟩ := erased
      exact ⟨body, rfl, rfl, hb⟩

theorem erase_imp_inv {environment : Environment} {Γ : Ctx Base}
    {t : Term (Constant environment) Γ .prop} {rawLeft rawRight : Tm}
    (erased : erase t = some (.imp rawLeft rawRight)) :
    ∃ left right : Term (Constant environment) Γ .prop,
      t = .imp left right ∧ erase left = some rawLeft ∧ erase right = some rawRight := by
  cases t with
  | var v => simp [erase] at erased
  | const c => cases c <;> simp [erase, Constant.erase] at erased
  | app function argument =>
      cases hf : erase function <;> cases ha : erase argument <;>
        simp [erase, hf, ha] at erased
  | imp left right =>
      cases hl : erase left <;> cases hr : erase right <;> simp [erase, hl, hr] at erased
      obtain ⟨rfl, rfl⟩ := erased
      exact ⟨left, right, rfl, hl, hr⟩
  | all body => cases hb : erase body <;> simp [erase, hb] at erased
  | top | bot | and _ _ | or _ _ | not _ | eq _ _ | ex _ => simp [erase] at erased

theorem erase_all_inv {environment : Environment} {Γ : Ctx Base}
    {t : Term (Constant environment) Γ .prop} {rawType : Tp} {rawBody : Tm}
    (erased : erase t = some (.all rawType rawBody)) :
    ∃ (σ : Ty Base) (body : Term (Constant environment) (σ :: Γ) .prop),
      t = .all body ∧ rawType = reifyType σ ∧ erase body = some rawBody := by
  cases t with
  | var v => simp [erase] at erased
  | const c => cases c <;> simp [erase, Constant.erase] at erased
  | app function argument =>
      cases hf : erase function <;> cases ha : erase argument <;>
        simp [erase, hf, ha] at erased
  | imp left right =>
      cases hl : erase left <;> cases hr : erase right <;> simp [erase, hl, hr] at erased
  | all body =>
      cases hb : erase body <;> simp [erase, hb] at erased
      obtain ⟨rfl, rfl⟩ := erased
      exact ⟨_, body, rfl, rfl, hb⟩
  | top | bot | and _ _ | or _ _ | not _ | eq _ _ | ex _ => simp [erase] at erased

theorem erase_db_inv {environment : Environment} {Γ : Ctx Base} {τ : Ty Base}
    {t : Term (Constant environment) Γ τ} {index : Nat}
    (erased : erase t = some (.db index)) :
    ∃ v : Var Γ τ, t = .var v ∧ variableIndex v = index := by
  cases t with
  | var v => exact ⟨v, rfl, by simpa [erase] using erased⟩
  | const c => cases c <;> simp [erase, Constant.erase] at erased
  | app function argument =>
      cases hf : erase function <;> cases ha : erase argument <;>
        simp [erase, hf, ha] at erased
  | lam body => cases hb : erase body <;> simp [erase, hb] at erased
  | imp left right =>
      cases hl : erase left <;> cases hr : erase right <;> simp [erase, hl, hr] at erased
  | all body => cases hb : erase body <;> simp [erase, hb] at erased
  | top | bot | and _ _ | or _ _ | not _ | eq _ _ | ex _ => simp [erase] at erased

theorem erase_db_zero_inv {environment : Environment} {Γ : Ctx Base} {σ τ : Ty Base}
    {t : Term (Constant environment) (σ :: Γ) τ}
    (erased : erase t = some (.db 0)) :
    σ = τ ∧ HEq t (Term.var (Var.vz : Var (σ :: Γ) σ) : Term (Constant environment) _ _) := by
  obtain ⟨v, rfl, indexed⟩ := erase_db_inv erased
  cases v with
  | vz => exact ⟨rfl, HEq.rfl⟩
  | vs v => simp [variableIndex] at indexed

/-- A context and a de Bruijn index determine both the type and typed variable. -/
theorem variableIndex_heq {Γ : Ctx Base} {σ τ : Ty Base}
    {first : Var Γ σ} {second : Var Γ τ}
    (equal : variableIndex first = variableIndex second) : σ = τ ∧ HEq first second := by
  induction first generalizing τ with
  | vz =>
      cases second with
      | vz => exact ⟨rfl, HEq.rfl⟩
      | vs second => simp [variableIndex] at equal
  | vs first ih =>
      cases second with
      | vz => simp [variableIndex] at equal
      | vs second =>
          obtain ⟨rfl, same⟩ := ih (Nat.succ.inj equal)
          cases same
          exact ⟨rfl, HEq.rfl⟩

/-- The environment lookup determines a retained constant's type and all data;
the lookup and typing witnesses add no distinct syntax. -/
theorem Constant.erase_heq {environment : Environment} {σ τ : Ty Base}
    {first : Constant environment σ} {second : Constant environment τ}
    (equal : first.erase = second.erase) : σ = τ ∧ HEq first second := by
  cases first with
  | named name declaration lookup typed =>
      cases second with
      | named name' declaration' lookup' typed' =>
          simp only [Constant.erase, Tm.named.injEq] at equal
          subst name'
          have declarations := Option.some.inj (lookup.symm.trans lookup')
          subst declaration'
          have types := reifyType_injective (typed.symm.trans typed')
          subst τ
          exact ⟨rfl, HEq.rfl⟩
      | primitive index lookup' => simp [Constant.erase] at equal
  | primitive index lookup =>
      cases second with
      | named name declaration lookup' typed' => simp [Constant.erase] at equal
      | primitive index' lookup' =>
          simp only [Constant.erase, Tm.prim.injEq] at equal
          subst index'
          have types := reifyType_injective (Option.some.inj (lookup.symm.trans lookup'))
          subst τ
          exact ⟨rfl, HEq.rfl⟩

private theorem erase_lam_type {environment : Environment} {Γ : Ctx Base} {type : Ty Base}
    {t : Term (Constant environment) Γ type} {rawType : Tp} {rawBody : Tm}
    (erased : erase t = some (.lam rawType rawBody)) :
    ∃ σ τ : Ty Base, type = σ ⇒ τ := by
  cases t with
  | var v => simp [erase] at erased
  | const c => cases c <;> simp [erase, Constant.erase] at erased
  | app function argument =>
      cases hf : erase function <;> cases ha : erase argument <;>
        simp [erase, hf, ha] at erased
  | lam body => exact ⟨_, _, rfl⟩
  | imp left right =>
      cases hl : erase left <;> cases hr : erase right <;> simp [erase, hl, hr] at erased
  | all body => cases hb : erase body <;> simp [erase, hb] at erased
  | top | bot | and _ _ | or _ _ | not _ | eq _ _ | ex _ => simp [erase] at erased

private theorem erase_imp_type {environment : Environment} {Γ : Ctx Base} {type : Ty Base}
    {t : Term (Constant environment) Γ type} {rawLeft rawRight : Tm}
    (erased : erase t = some (.imp rawLeft rawRight)) : type = .prop := by
  cases t with
  | var v => simp [erase] at erased
  | const c => cases c <;> simp [erase, Constant.erase] at erased
  | app function argument =>
      cases hf : erase function <;> cases ha : erase argument <;>
        simp [erase, hf, ha] at erased
  | lam body => cases hb : erase body <;> simp [erase, hb] at erased
  | top | bot | and _ _ | or _ _ | imp _ _ | not _ | eq _ _ | all _ | ex _ => rfl

private theorem erase_all_type {environment : Environment} {Γ : Ctx Base} {type : Ty Base}
    {t : Term (Constant environment) Γ type} {rawType : Tp} {rawBody : Tm}
    (erased : erase t = some (.all rawType rawBody)) : type = .prop := by
  cases t with
  | var v => simp [erase] at erased
  | const c => cases c <;> simp [erase, Constant.erase] at erased
  | app function argument =>
      cases hf : erase function <;> cases ha : erase argument <;>
        simp [erase, hf, ha] at erased
  | lam body => cases hb : erase body <;> simp [erase, hb] at erased
  | top | bot | and _ _ | or _ _ | imp _ _ | not _ | eq _ _ | all _ | ex _ => rfl

private theorem erase_const_inv {environment : Environment} {Γ : Ctx Base} {σ τ : Ty Base}
    (constant : Constant environment σ) {t : Term (Constant environment) Γ τ}
    (erased : erase t = some constant.erase) :
    ∃ value : Constant environment τ, t = .const value ∧ value.erase = constant.erase := by
  cases t with
  | var v => cases constant <;> simp [erase, Constant.erase] at erased
  | const c => exact ⟨c, rfl, Option.some.inj erased⟩
  | app function argument =>
      cases constant <;> cases hf : erase function <;> cases ha : erase argument <;>
        simp [erase, Constant.erase, hf, ha] at erased
  | lam body =>
      cases constant <;> cases hb : erase body <;> simp [erase, Constant.erase, hb] at erased
  | imp left right =>
      cases constant <;> cases hl : erase left <;> cases hr : erase right <;>
        simp [erase, Constant.erase, hl, hr] at erased
  | all body =>
      cases constant <;> cases hb : erase body <;> simp [erase, Constant.erase, hb] at erased
  | top | bot | and _ _ | or _ _ | not _ | eq _ _ | ex _ => simp [erase] at erased

/-- A successful raw erasure fixes both the intrinsic type and the term, in a
fixed environment and context. No native formation or semantic assumption is
needed: binder annotations and retained lookups already determine the types. -/
theorem erase_heq_of_eq_some {environment : Environment} {Γ : Ctx Base} {σ τ : Ty Base}
    {first : Term (Constant environment) Γ σ} {second : Term (Constant environment) Γ τ}
    {raw : Tm} (first_erased : erase first = some raw) (second_erased : erase second = some raw) :
    σ = τ ∧ HEq first second := by
  induction first generalizing τ raw with
  | var v =>
      cases first_erased
      obtain ⟨w, rfl, indexed⟩ := erase_db_inv second_erased
      obtain ⟨rfl, same⟩ := variableIndex_heq indexed.symm
      cases same
      exact ⟨rfl, HEq.rfl⟩
  | const c =>
      cases first_erased
      obtain ⟨d, rfl, equal⟩ := erase_const_inv c second_erased
      obtain ⟨rfl, same⟩ := Constant.erase_heq equal.symm
      cases same
      exact ⟨rfl, HEq.rfl⟩
  | app function argument ihf iha =>
      cases hf : erase function <;> cases ha : erase argument <;>
        simp [erase, hf, ha] at first_erased
      subst raw
      obtain ⟨_, otherFunction, otherArgument, rfl, ofe, oae⟩ := erase_app_inv second_erased
      obtain ⟨types, functions⟩ := ihf hf ofe
      cases types
      cases functions
      obtain ⟨_, arguments⟩ := iha ha oae
      cases arguments
      exact ⟨rfl, HEq.rfl⟩
  | @lam Γ domain codomain body ih =>
      cases hb : erase body <;> simp [erase, hb] at first_erased
      subst raw
      obtain ⟨otherDomain, otherCodomain, rfl⟩ := erase_lam_type second_erased
      obtain ⟨otherBody, rfl, domains, obe⟩ := erase_lam_inv second_erased
      have domainTypes := reifyType_injective domains
      subst otherDomain
      obtain ⟨rfl, bodies⟩ := ih hb obe
      cases bodies
      exact ⟨rfl, HEq.rfl⟩
  | imp left right ihl ihr =>
      cases hl : erase left <;> cases hr : erase right <;>
        simp [erase, hl, hr] at first_erased
      subst raw
      have type := erase_imp_type second_erased
      subst τ
      obtain ⟨otherLeft, otherRight, rfl, ole, ore⟩ := erase_imp_inv second_erased
      obtain ⟨_, lefts⟩ := ihl hl ole
      obtain ⟨_, rights⟩ := ihr hr ore
      cases lefts
      cases rights
      exact ⟨rfl, HEq.rfl⟩
  | @all Γ domain body ih =>
      cases hb : erase body <;> simp [erase, hb] at first_erased
      subst raw
      have type := erase_all_type second_erased
      subst τ
      obtain ⟨otherDomain, otherBody, rfl, domains, obe⟩ := erase_all_inv second_erased
      have domainTypes := reifyType_injective domains
      subst otherDomain
      obtain ⟨_, bodies⟩ := ih hb obe
      cases bodies
      exact ⟨rfl, HEq.rfl⟩
  | top | bot | and _ _ _ _ | or _ _ _ _ | not _ _ | eq _ _ _ _ | ex _ _ =>
      simp [erase] at first_erased

theorem erase_injective_of_eq_some {environment : Environment} {Γ : Ctx Base} {τ : Ty Base}
    {first second : Term (Constant environment) Γ τ} {raw : Tm}
    (first_erased : erase first = some raw) (second_erased : erase second = some raw) :
    first = second :=
  eq_of_heq (erase_heq_of_eq_some first_erased second_erased).2

namespace ErasureInversionExamples

/-- The closed higher-order iterator uses both an older and a newest binder. -/
def iteration (environment : Environment) :
    Term (Constant environment) [] ((.prop ⇒ .prop) ⇒ (.prop ⇒ .prop)) :=
  .lam (.lam (.app (.var (.vs .vz)) (.app (.var (.vs .vz)) (.var .vz))))

def rawIteration : Tm :=
  .lam (.arr .prop .prop) (.lam .prop (.app (.db 1) (.app (.db 1) (.db 0))))

theorem iteration_erased (environment : Environment) :
    erase (iteration environment) = some rawIteration := rfl

/-- Exact native syntax uniquely identifies the intrinsic higher-order term,
even if its result type is initially unspecified. -/
theorem iteration_unique {environment : Environment} {τ : Ty Base}
    {term : Term (Constant environment) [] τ}
    (erased : erase term = some rawIteration) :
    τ = ((.prop ⇒ .prop) ⇒ (.prop ⇒ .prop)) ∧ HEq term (iteration environment) :=
  erase_heq_of_eq_some erased (iteration_erased environment)

/-- Failure is not a representation: distinct unsupported logical constants
have the same failed erasure. -/
theorem erase_not_injective (environment : Environment) (Γ : Ctx Base) :
    ¬ Function.Injective (erase : Term (Constant environment) Γ .prop → Option Tm) := by
  intro injective
  have impossible := injective (a₁ := .top) (a₂ := .bot) rfl
  cases impossible

end ErasureInversionExamples

#print axioms erase_app_inv
#print axioms erase_lam_inv
#print axioms erase_imp_inv
#print axioms erase_all_inv
#print axioms erase_db_zero_inv
#print axioms erase_heq_of_eq_some
#print axioms erase_injective_of_eq_some
#print axioms ErasureInversionExamples.iteration_unique
#print axioms ErasureInversionExamples.erase_not_injective

end Mettapedia.Languages.Megalodon.HenkinTermInterpretation
