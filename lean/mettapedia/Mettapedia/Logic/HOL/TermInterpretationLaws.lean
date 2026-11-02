import Mettapedia.Logic.HOL.ProofSyntaxInterpretation
import Mettapedia.Logic.HOL.Syntax.ConstantSubstitutionComposition

/-!
# Naturality of typed closed-term interpretations

The type map may replace a base sort by a compound type, and several source
sorts may have the same image. Variable positions remain explicit. Constants
are interpreted by actual closed terms, including compound numeral wrappers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.TermInterpretation
universe u v u' v'
variable {Base : Type u} {Const : Ty Base → Type v}
  {Target : Type u'} {Symbols : Ty Target → Type v'}
  (interpretation : TermInterpretation Base Const Target Symbols)
  {Γ Δ : Ctx Base} {type domain codomain : Ty Base}

@[simp] theorem term_var (index : Var Γ type) :
    interpretation.term (.var index) = .var (index.mapTypes interpretation.types) := rfl

@[simp] theorem term_const (constant : Const type) :
    interpretation.term (Γ := Γ) (.const constant) =
      weakenCtx (Γ.map (Ty.substitute interpretation.types)) (interpretation.constants constant) := rfl

@[simp] theorem term_app (function : Term Const Γ (domain ⇒ codomain)) (argument : Term Const Γ domain) :
    interpretation.term (.app function argument) = .app (interpretation.term function) (interpretation.term argument) := rfl

@[simp] theorem term_lam (body : Term Const (domain :: Γ) codomain) :
    interpretation.term (.lam body) = .lam (interpretation.term body) := rfl

@[simp] theorem term_top : interpretation.term (Γ := Γ) .top = .top := rfl
@[simp] theorem term_bot : interpretation.term (Γ := Γ) .bot = .bot := rfl
@[simp] theorem term_and (first second : Formula Const Γ) :
    interpretation.term (.and first second) = .and (interpretation.term first) (interpretation.term second) := rfl
@[simp] theorem term_or (first second : Formula Const Γ) :
    interpretation.term (.or first second) = .or (interpretation.term first) (interpretation.term second) := rfl
@[simp] theorem term_imp (first second : Formula Const Γ) :
    interpretation.term (.imp first second) = .imp (interpretation.term first) (interpretation.term second) := rfl
@[simp] theorem term_not (body : Formula Const Γ) :
    interpretation.term (.not body) = .not (interpretation.term body) := rfl
@[simp] theorem term_eq (first second : Term Const Γ type) :
    interpretation.term (.eq first second) = .eq (interpretation.term first) (interpretation.term second) := rfl
@[simp] theorem term_all (body : Formula Const (domain :: Γ)) :
    interpretation.term (.all body) = .all (interpretation.term body) := rfl
@[simp] theorem term_ex (body : Formula Const (domain :: Γ)) :
    interpretation.term (.ex body) = .ex (interpretation.term body) := rfl

@[simp] theorem term_weaken (term : Term Const Γ type) :
    interpretation.term (weaken (σ := domain) term) =
      weaken (σ := Ty.substitute interpretation.types domain) (interpretation.term term) := by
  simp only [TermInterpretation.term, mapTypes_weaken, substConst_weaken]

@[simp] theorem term_weakenCtx (context : Ctx Base) (term : ClosedTerm Const type) :
    interpretation.term (weakenCtx context term) =
      weakenCtx (context.map (Ty.substitute interpretation.types)) (interpretation.term term) := by
  simp only [TermInterpretation.term, mapTypes_weakenCtx, substConst_weakenCtx]

theorem term_rename (rho : Rename Base Γ Δ)
    (mapped : Rename Target (Γ.map (Ty.substitute interpretation.types)) (Δ.map (Ty.substitute interpretation.types)))
    (compatible : ∀ {type} (index : Var Γ type),
      (rho index).mapTypes interpretation.types = mapped (index.mapTypes interpretation.types))
    (term : Term Const Γ type) :
    interpretation.term (HOL.rename rho term) = HOL.rename mapped (interpretation.term term) := by
  unfold TermInterpretation.term
  rw [mapTypes_rename _ _ rho mapped compatible, substConst_rename]

theorem term_subst (theta : Subst Const Γ Δ)
    (mapped : Subst Symbols (Γ.map (Ty.substitute interpretation.types)) (Δ.map (Ty.substitute interpretation.types)))
    (compatible : ∀ {type} (index : Var Γ type),
      interpretation.term (theta index) = mapped (index.mapTypes interpretation.types))
    (term : Term Const Γ type) :
    interpretation.term (HOL.subst theta term) = HOL.subst mapped (interpretation.term term) := by
  induction term generalizing Δ with
  | var index => exact compatible index
  | const constant => simp only [HOL.subst, term_const, HOL.subst_weakenCtx]
  | app function argument first second =>
      simp only [HOL.subst, term_app, first theta mapped compatible, second theta mapped compatible]
  | lam body hypothesis =>
      apply congrArg Term.lam
      apply hypothesis (Subst.lift theta) (Subst.lift mapped)
      intro type index
      cases index with
      | vz => rfl
      | vs index =>
          change interpretation.term (weaken (theta index)) = weaken (mapped (index.mapTypes interpretation.types))
          rw [term_weaken, compatible]
  | all body hypothesis =>
      apply congrArg Term.all
      apply hypothesis (Subst.lift theta) (Subst.lift mapped)
      intro type index
      cases index with
      | vz => rfl
      | vs index =>
          change interpretation.term (weaken (theta index)) = weaken (mapped (index.mapTypes interpretation.types))
          rw [term_weaken, compatible]
  | ex body hypothesis =>
      apply congrArg Term.ex
      apply hypothesis (Subst.lift theta) (Subst.lift mapped)
      intro type index
      cases index with
      | vz => rfl
      | vs index =>
          change interpretation.term (weaken (theta index)) = weaken (mapped (index.mapTypes interpretation.types))
          rw [term_weaken, compatible]
  | top => rfl
  | bot => rfl
  | and first second firstHyp secondHyp =>
      simp only [HOL.subst, term_and, firstHyp theta mapped compatible, secondHyp theta mapped compatible]
  | or first second firstHyp secondHyp =>
      simp only [HOL.subst, term_or, firstHyp theta mapped compatible, secondHyp theta mapped compatible]
  | imp first second firstHyp secondHyp =>
      simp only [HOL.subst, term_imp, firstHyp theta mapped compatible, secondHyp theta mapped compatible]
  | eq first second firstHyp secondHyp =>
      simp only [HOL.subst, term_eq, firstHyp theta mapped compatible, secondHyp theta mapped compatible]
  | not body hypothesis =>
      simpa only [HOL.subst, term_not] using congrArg Term.not (hypothesis theta mapped compatible)

theorem term_instantiate (value : Term Const Γ domain) (body : Term Const (domain :: Γ) codomain) :
    interpretation.term (instantiate value body) = instantiate (interpretation.term value) (interpretation.term body) := by
  apply term_subst
  intro type index
  cases index <;> rfl

theorem term_subst_heq (theta : Subst Const Γ Δ)
    (mapped : Subst Symbols (Γ.map (Ty.substitute interpretation.types)) (Δ.map (Ty.substitute interpretation.types)))
    (compatible : ∀ {type} (index : Var Γ type),
      interpretation.term (theta index) = mapped (index.mapTypes interpretation.types))
    {targetType : Ty Target} (same : Ty.substitute interpretation.types type = targetType)
    (source : Term Const Γ type)
    (target : Term Symbols (Γ.map (Ty.substitute interpretation.types)) targetType)
    (terms : HEq (interpretation.term source) target) :
    HEq (interpretation.term (HOL.subst theta source)) (HOL.subst mapped target) := by
  rw [term_subst interpretation theta mapped compatible]
  cases same
  exact heq_of_eq (congrArg (HOL.subst mapped) (eq_of_heq terms))

#print axioms term_subst
#print axioms term_rename
end Mettapedia.Logic.HOL.TermInterpretation
