import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalTreeSubstitution
import Mettapedia.OSLF.Syntax.PositionEnumeration

/-!
# Rule-local beta data and overlapping declaration controls

The first rule is general beta with a body and an argument. The second is
its identity-body specialization with only an argument. Their telescopes
have different lengths, yet both are constructors of the same polynomial.
An identity application admits both labels; the resulting histories remain
distinct even though their endpoints agree.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalControls

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial

inductive Op : Unit → Type where
  | lam : Op ()
  | app : Op ()
  | symbol (name : Nat) : Op ()

def sig : Signature where
  Srt := Unit
  Op := Op
  arity := fun {_} op => match op with
    | .lam => [([()], ())]
    | .app => [([], ()), ([], ())]
    | .symbol _ => []

abbrev Tm (Γ : Ctx sig) := Term sig Γ ()

def lam {Γ : Ctx sig} (body : Tm (() :: Γ)) : Tm Γ :=
  .op .lam (.cons body .nil)

def app {Γ : Ctx sig} (function argument : Tm Γ) : Tm Γ :=
  .op .app (.cons function (.cons argument .nil))

def symbol {Γ : Ctx sig} (name : Nat) : Tm Γ := .op (.symbol name) .nil

abbrev betaMetas : List (MetaArity sig) := [([()], ()), ([], ())]
abbrev identityMetas : List (MetaArity sig) := [([], ())]

def schemaLam {M : List (MetaArity sig)} {Γ : Ctx sig}
    (body : Term (withMetas sig M) (() :: Γ) ()) : Term (withMetas sig M) Γ () :=
  .op (Sum.inl Op.lam) (.cons body .nil)

def schemaApp {M : List (MetaArity sig)} {Γ : Ctx sig}
    (function argument : Term (withMetas sig M) Γ ()) :
    Term (withMetas sig M) Γ () :=
  .op (Sum.inl Op.app) (.cons function (.cons argument .nil))

def betaBody {Γ : Ctx sig} (argument : Term (withMetas sig betaMetas) Γ ()) :
    Term (withMetas sig betaMetas) Γ () :=
  .op (Sum.inr (MetaOp.mk (M := betaMetas) 0)) (.cons argument .nil)

def betaArgument {Γ : Ctx sig} : Term (withMetas sig betaMetas) Γ () :=
  .op (Sum.inr (MetaOp.mk (M := betaMetas) 1)) .nil

def identityArgument {Γ : Ctx sig} : Term (withMetas sig identityMetas) Γ () :=
  .op (Sum.inr (MetaOp.mk (M := identityMetas) 0)) .nil

def beta : IntrinsicScopedConditionalPolynomial.Rule sig betaMetas where
  conclusion :=
    let lhs := schemaApp (schemaLam (betaBody (.var .zero))) betaArgument
    ⟨[], (), lhs, betaBody betaArgument, rootPosition lhs⟩
  premises := []

def identityBeta : IntrinsicScopedConditionalPolynomial.Rule sig identityMetas where
  conclusion :=
    let lhs := schemaApp (schemaLam (.var .zero)) identityArgument
    ⟨[], (), lhs, identityArgument, rootPosition lhs⟩
  premises := []

def family : List (LocalRule sig) := [⟨betaMetas, beta⟩, ⟨identityMetas, identityBeta⟩]

abbrev algebra := BindingCloneAlgebra.terms sig
abbrev BetaValuation (Γ : Ctx sig) := Valuation (M := betaMetas) algebra Γ

def betaValuation {Γ : Ctx sig} (body : Tm (() :: Γ)) (argument : Tm Γ) :
    BetaValuation Γ
  | ⟨0, _⟩ => body
  | ⟨1, _⟩ => argument

/-- The complete beta valuation is determined by its body and argument.
There is no third component in which to vary an irrelevant assignment. -/
theorem betaValuation_ext {Γ : Ctx sig} {first second : BetaValuation Γ}
    (body : first 0 = second 0) (argument : first 1 = second 1) : first = second :=
  funext fun
    | ⟨0, _⟩ => body
    | ⟨1, _⟩ => argument

def betaValuationEquiv (Γ : Ctx sig) :
    BetaValuation Γ ≃ Tm (() :: Γ) × Tm Γ where
  toFun valuation := (valuation 0, valuation 1)
  invFun values := betaValuation values.1 values.2
  left_inv _ := betaValuation_ext rfl rfl
  right_inv values := by cases values; rfl

def emptyClose (Γ : Ctx sig) : Sub sig [] Γ := fun _ var => nomatch var

def betaOccurrence {Γ : Ctx sig} (body : Tm (() :: Γ)) (argument : Tm Γ) :
    Instance family algebra where
  index := ⟨0, by decide⟩
  ambient := Γ
  valuation := betaValuation body argument
  close := emptyClose Γ

def identityOccurrence {Γ : Ctx sig} (argument : Tm Γ) : Instance family algebra where
  index := ⟨1, by decide⟩
  ambient := Γ
  valuation := fun ⟨0, _⟩ => argument
  close := emptyClose Γ

def eval0 {Γ : Ctx sig} (valuation : BetaValuation Γ)
    (term : Term (withMetas sig betaMetas) [] ()) : Tm Γ :=
  interpretSchema algebra valuation (fun _ v => .var v) (emptyClose Γ) term

@[simp] theorem eval0_argument {Γ : Ctx sig} (valuation : BetaValuation Γ) :
    eval0 valuation betaArgument = valuation 1 := bind_id _

@[simp] theorem eval0_body {Γ : Ctx sig} (valuation : BetaValuation Γ)
    (argument : Term (withMetas sig betaMetas) [] ()) :
    eval0 valuation (betaBody argument) = inst (valuation 0) (eval0 valuation argument) := by
  change bind _ (valuation 0) = bind (extend (eval0 valuation argument)) (valuation 0)
  congr 1
  funext sort var
  cases var <;> rfl

theorem eval_binder_body {Γ : Ctx sig} (valuation : BetaValuation Γ) :
    interpretSchema algebra valuation
        (weakenEnvironment algebra [()] (fun _ v => .var v))
        (algebra.substitution.liftEnvironment (emptyClose Γ) [()])
        (betaBody (.var .zero)) = valuation 0 := by
  change bind _ (valuation 0) = valuation 0
  trans bind (fun _ v => Term.var v) (valuation 0)
  · congr 1
    funext sort var
    cases var <;> rfl
  · exact bind_id _

theorem beta_conclusion {Γ : Ctx sig} (body : Tm (() :: Γ)) (argument : Tm Γ) :
    conclusionJudgment family algebra (betaOccurrence body argument) =
      (⟨Γ, (), app (lam body) argument, inst body argument⟩ : Judgment algebra) := by
  change (⟨Γ, (),
    app (lam (interpretSchema algebra (betaValuation body argument)
      (weakenEnvironment algebra [()] (fun _ v => .var v))
      (algebra.substitution.liftEnvironment (emptyClose Γ) [()])
      (betaBody (.var .zero))))
      (eval0 (betaValuation body argument) betaArgument),
    eval0 (betaValuation body argument) (betaBody betaArgument)⟩ : Judgment algebra) = _
  rw [eval_binder_body, eval0_body, eval0_argument]
  rfl

theorem identity_conclusion {Γ : Ctx sig} (argument : Tm Γ) :
    conclusionJudgment family algebra (identityOccurrence argument) =
      (⟨Γ, (), app (lam (.var .zero)) argument, argument⟩ : Judgment algebra) := by
  change (⟨Γ, (), app (lam (.var .zero)) (bind (fun _ v => .var v) argument),
    bind (fun _ v => .var v) argument⟩ : Judgment algebra) = _
  exact congrArg (fun result : Tm Γ =>
    (⟨Γ, (), app (lam (.var .zero)) result, result⟩ : Judgment algebra)) (bind_id argument)

/-- Fixing the rule address and the entire redex recovers the local beta
valuation in the free term model. This statement is specific to beta. -/
theorem beta_redex_recovers_assignment {Γ : Ctx sig}
    (body₁ body₂ : Tm (() :: Γ)) (argument₁ argument₂ : Tm Γ)
    (same : app (lam body₁) argument₁ = app (lam body₂) argument₂) :
    betaValuation body₁ argument₁ = betaValuation body₂ argument₂ := by
  cases same
  rfl

/-- The general and specialized beta labels overlap at identity bodies. -/
theorem overlapping_endpoints {Γ : Ctx sig} (argument : Tm Γ) :
    conclusionJudgment family algebra (betaOccurrence (.var .zero) argument) =
      conclusionJudgment family algebra (identityOccurrence argument) := by
  rw [beta_conclusion, identity_conclusion]
  rfl

/-- Local telescopes retain genuine declaration choice. -/
theorem overlapping_instances_distinct {Γ : Ctx sig} (argument : Tm Γ) :
    betaOccurrence (.var .zero) argument ≠ identityOccurrence argument := by
  intro same
  have indices := congrArg (fun occurrence : Instance family algebra => occurrence.index) same
  cases indices

def betaTree {Γ : Ctx sig} (body : Tm (() :: Γ)) (argument : Tm Γ) :
    Tree family algebra (conclusionJudgment family algebra (betaOccurrence body argument)) :=
  .roll ⟨betaOccurrence body argument, rfl⟩ (fun position => Fin.elim0 position)

def identityTree {Γ : Ctx sig} (argument : Tm Γ) :
    Tree family algebra (conclusionJudgment family algebra (identityOccurrence argument)) :=
  .roll ⟨identityOccurrence argument, rfl⟩ (fun position => Fin.elim0 position)

/-- Even after transporting the equal endpoints, the two histories differ. -/
theorem overlapping_trees_distinct {Γ : Ctx sig} (argument : Tm Γ) :
    (overlapping_endpoints argument ▸ betaTree (.var .zero) argument) ≠
      identityTree argument := by
  intro same
  let rootIndex : ∀ j : Judgment algebra, Tree family algebra j → Fin family.length :=
    fun _ tree => (IndexedPolynomial.Fix.out (rules family algebra) tree).1.1.index
  have castIndex {first second : Judgment algebra} (same : first = second)
      (tree : Tree family algebra first) :
      rootIndex second (same ▸ tree) = rootIndex first tree := by
    cases same
    rfl
  have indices := congrArg (rootIndex _) same
  have indices' := (castIndex (overlapping_endpoints argument)
    (betaTree (.var .zero) argument)).symm.trans indices
  have impossible : (0 : Nat) = 1 := congrArg Fin.val indices'
  cases impossible

#print axioms betaValuationEquiv
#print axioms beta_conclusion
#print axioms beta_redex_recovers_assignment
#print axioms overlapping_trees_distinct

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalControls
