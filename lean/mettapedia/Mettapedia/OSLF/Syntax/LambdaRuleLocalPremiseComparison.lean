import Mettapedia.OSLF.Syntax.LambdaRuleDerivationPolynomial
import Mettapedia.OSLF.Syntax.BinderLocalPremise

/-!
# Local premises of the Chapter 7 lambda rule polynomial

The recursive positions of the indexed polynomial have the same premise
contexts as the general binder-local premise interface. Beta has no premise;
application congruence has a root premise; abstraction congruence has a
premise under exactly one term binder. This comparison keeps the premise
context explicit before compiling rules from a canonical authored language.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaRuleLocalPremiseComparison

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.LambdaRuleDerivationPolynomial
open Mettapedia.OSLF.Binding.BinderLocalPremise

/-- The semantic premise carried by each contextual rule constructor. -/
def localPremise : {j : Judgment} → RuleShape j →
    Option (LocalStepPremise sig j.1)
  | _, .beta _ _ => none
  | _, .appCongL source target _ =>
      some (LocalStepPremise.root source target)
  | _, .appCongR _ source target =>
      some (LocalStepPremise.root source target)
  | _, .lamCong source target =>
      some {
        binders := [.term]
        sort := .term
        source := source
        target := target }

/-- Recursive positions occur exactly for constructors with a local step
premise; the comparison is independent of a particular target relation. -/
theorem has_position_iff_localPremise {j : Judgment}
    (shape : RuleShape j) :
    Nonempty (premisePosition shape) ↔
      (localPremise shape).isSome := by
  cases shape <;> simp [premisePosition, localPremise] <;> exact ⟨()⟩

/-- Every recursive child index is precisely the judgment of its declared
local premise, including the context extension under a lambda binder. -/
theorem child_index_is_local_premise {j : Judgment}
    (shape : RuleShape j) (position : premisePosition shape) :
    ∃ premise : LocalStepPremise sig j.1,
      localPremise shape = some premise ∧
      premiseJudgment shape position =
        judgment premise.source premise.target := by
  cases shape with
  | beta body arg => exact position.elim
  | appCongL source target arg =>
      exact ⟨LocalStepPremise.root source target, rfl, rfl⟩
  | appCongR funTerm source target =>
      exact ⟨LocalStepPremise.root source target, rfl, rfl⟩
  | lamCong source target =>
      let premise : LocalStepPremise sig _ :=
        { binders := [.term], sort := .term,
          source := source, target := target }
      exact ⟨premise, rfl, rfl⟩

/-- The Chapter 7 relation as a sort-indexed relation for the general local
premise interface. The source signature has one sort, so this adds no cases. -/
def contextualStep (Γ : Ctx sig) (sort : Srt)
    (source target : Term sig Γ sort) : Prop :=
  match sort with
  | .term => LambdaContextualRung.Step Γ source target

/-- The existing intrinsic substitution theorem supplies exactly the
stability required by the generic binder-local premise semantics. -/
theorem contextualStep_substitution_stable :
    SubstitutionStable contextualStep := by
  intro Γ Δ sort sigma source target firing
  cases sort
  exact LambdaContextualRung.substitute sigma firing

/-- The abstraction premise's actual binder extension commutes with
substitution of ambient variables. -/
theorem lamCong_premise_map {Γ Δ : Ctx sig}
    (sigma : Sub sig Γ Δ)
    (source target : Term sig (.term :: Γ) .term) :
    (localPremise (RuleShape.lamCong source target)).map
        (LocalStepPremise.map sigma) =
      localPremise (RuleShape.lamCong
        (bind (liftSub sigma [.term]) source)
        (bind (liftSub sigma [.term]) target)) := rfl

/-- Root application congruence uses the zero-binder case of the same
premise transport, rather than a separate substitution convention. -/
theorem appCongL_premise_map {Γ Δ : Ctx sig}
    (sigma : Sub sig Γ Δ)
    (source target arg : Term sig Γ .term) :
    (localPremise (RuleShape.appCongL source target arg)).map
        (LocalStepPremise.map sigma) =
      localPremise (RuleShape.appCongL
        (bind sigma source) (bind sigma target) (bind sigma arg)) := rfl

/-- A recursive child tree supplies the relation required by the matching
binder-local premise. This reads the actual child, not endpoint existence. -/
theorem child_tree_discharge {j : Judgment}
    (shape : RuleShape j) (position : premisePosition shape)
    (child : rules.Fix () (premiseJudgment shape position)) :
    ∃ premise : LocalStepPremise sig j.1,
      localPremise shape = some premise ∧
      Holds contextualStep premise := by
  cases shape with
  | beta body arg => exact position.elim
  | appCongL source target arg =>
      exact ⟨LocalStepPremise.root source target, rfl, toStep _ child⟩
  | appCongR funTerm source target =>
      exact ⟨LocalStepPremise.root source target, rfl, toStep _ child⟩
  | lamCong source target =>
      let premise : LocalStepPremise sig _ :=
        { binders := [.term], sort := .term,
          source := source, target := target }
      exact ⟨premise, rfl, toStep _ child⟩

/-- Discharging a real recursive child remains valid after any ambient
substitution. Its local binder context is transported by `liftSub`. -/
theorem child_tree_discharge_after_substitution {j : Judgment}
    (shape : RuleShape j) (position : premisePosition shape)
    (child : rules.Fix () (premiseJudgment shape position))
    {Δ : Ctx sig} (sigma : Sub sig j.1 Δ) :
    ∃ premise : LocalStepPremise sig j.1,
      localPremise shape = some premise ∧
      Holds contextualStep (premise.map sigma) := by
  obtain ⟨premise, declared, firing⟩ :=
    child_tree_discharge shape position child
  exact ⟨premise, declared,
    holds_map contextualStep_substitution_stable sigma premise firing⟩

/-- The actual open beta child of the closed LamCong tree satisfies the
one-binder premise, retaining the enclosing variable in both endpoints. -/
theorem closedLamTree_child_is_local_step :
    Holds contextualStep
      ({ binders := [.term]
         sort := .term
         source := appT
           (lamT (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term)))
           (Term.var (Var.zero : Var [Srt.term] Srt.term))
         target := inst
           (Term.var (Var.zero : Var [Srt.term, Srt.term] Srt.term))
           (Term.var (Var.zero : Var [Srt.term] Srt.term)) } :
        LocalStepPremise sig []) := by
  exact toStep _ openBetaTree

/-- A context-indexed predicate model supplies an action for every displayed
rule constructor, using its children at their actual premise indices. -/
def ClosedUnderRules (relation : Judgment → Prop) : Prop :=
  ∀ (j : Judgment) (shape : RuleShape j),
    (∀ position : premisePosition shape,
      relation (premiseJudgment shape position)) → relation j

/-- The existing source reduction relation has precisely these four rule
actions, including abstraction congruence below a binder. -/
theorem contextualStep_closed :
    ClosedUnderRules (fun j =>
      LambdaContextualRung.Step j.1 j.2.1 j.2.2) := by
  intro j shape premises
  cases shape with
  | beta body arg => exact LambdaContextualRung.Step.beta body arg
  | appCongL source target arg =>
      exact LambdaContextualRung.Step.appCongL arg (premises ())
  | appCongR funTerm source target =>
      exact LambdaContextualRung.Step.appCongR funTerm (premises ())
  | lamCong source target =>
      exact LambdaContextualRung.Step.lamCong (premises ())

/-- The source relation is least among all predicates closed under the
four rule actions. The recursive proof consumes the retained constructor
tree supplied by the source-step/tree correspondence. -/
theorem contextualStep_least
    (relation : Judgment → Prop) (closed : ClosedUnderRules relation)
    {Γ : Ctx sig} {source target : Term sig Γ .term}
    (step : LambdaContextualRung.Step Γ source target) :
    relation (judgment source target) := by
  obtain ⟨tree⟩ := step_iff_derivation.mp step
  exact IndexedPolynomial.Fix.eliminate rules
    (fun _ j _ => relation j)
    (fun _ j shape _children hypotheses => closed j shape hypotheses)
    () (judgment source target) tree

/-- The constant-false predicate is not a rule model: root beta gives a
genuine closed constructor with no premise to discharge. -/
theorem false_not_closed :
    ¬ ClosedUnderRules (fun _ => False) := by
  intro closed
  let identityBody : Term sig [Srt.term] .term := .var .zero
  let identity : Term sig [] .term := lamT identityBody
  exact closed
    (judgment (appT (lamT identityBody) identity)
      (inst identityBody identity))
    (RuleShape.beta identityBody identity)
    (fun impossible => impossible.elim)

/-- The abstraction-congruence premise is not a root premise: its body
judgment lives under the binder introduced by the source lambda. -/
theorem lamCong_uses_one_local_binder {Γ : Ctx sig}
    (source target : Term sig (.term :: Γ) .term) :
    (localPremise (RuleShape.lamCong source target)).map
      LocalStepPremise.binders = some [.term] := rfl

#print axioms has_position_iff_localPremise
#print axioms child_index_is_local_premise
#print axioms child_tree_discharge
#print axioms lamCong_uses_one_local_binder
#print axioms contextualStep_substitution_stable
#print axioms lamCong_premise_map
#print axioms child_tree_discharge_after_substitution
#print axioms closedLamTree_child_is_local_step
#print axioms contextualStep_least
#print axioms false_not_closed

end Mettapedia.OSLF.Binding.LambdaRuleLocalPremiseComparison
