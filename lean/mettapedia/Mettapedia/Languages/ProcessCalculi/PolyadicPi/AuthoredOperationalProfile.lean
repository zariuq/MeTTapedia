import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalPolynomial

/-!
# The active operational profile of the scoped polyadic presentation

Communication reuses the two original intrinsic rewrite declarations.
Parallel descent and restriction descent are conditional rules in the
existing binder-local rule format. The restriction premise opens its private
name before instantiating communication. Inputs and replication have no
descent rule in this profile.

The generated firing trees are compared with the independently defined
runtime relation at their supplied endpoints. Unrestricted closed-root
context closure is a different reading of the same raw schemas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredOperationalProfile

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualAssignment
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial (LocalRule Instance Tree)
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredCommunication

/-- The root declarations retain the exact source and target schemas. -/
def rootRule (rule : UnpositionedRewrite schemaSig) :
    IntrinsicScopedConditionalPolynomial.Rule sig metas where
  conclusion := {
    ctx := rule.ctx
    sort := rule.sort
    lhs := rule.lhs
    rhs := rule.rhs
    position := rootPosition rule.lhs }
  premises := []

private abbrev plainSig := withMetas sig []

private def schemaPar {Γ : Ctx plainSig}
    (first second : Term plainSig Γ .pr) : Term plainSig Γ .pr :=
  .op (.inl .par) (.cons first (.cons second .nil))

/-- Descent in the selected left operand retains the right operand. -/
def parLeft : IntrinsicScopedConditionalPolynomial.Rule sig [] where
  conclusion := {
    ctx := [.pr, .pr, .pr]
    sort := .pr
    lhs := schemaPar (.var .zero) (.var (.succ (.succ .zero)))
    rhs := schemaPar (.var (.succ .zero)) (.var (.succ (.succ .zero)))
    position := rootPosition _ }
  premises := [{
    binders := []
    sort := .pr
    source := .var .zero
    target := .var (.succ .zero) }]

def parRight : IntrinsicScopedConditionalPolynomial.Rule sig [] where
  conclusion := {
    ctx := [.pr, .pr, .pr]
    sort := .pr
    lhs := schemaPar (.var (.succ (.succ .zero))) (.var .zero)
    rhs := schemaPar (.var (.succ (.succ .zero))) (.var (.succ .zero))
    position := rootPosition _ }
  premises := [{
    binders := []
    sort := .pr
    source := .var .zero
    target := .var (.succ .zero) }]

abbrev scopeMetas : List (MetaArity sig) := [([Srt.nm], Srt.pr), ([Srt.nm], Srt.pr)]
private abbrev scopeSig := withMetas sig scopeMetas

private def scopeBody : Fin scopeMetas.length → Term scopeSig [Srt.nm] .pr
  | ⟨0, _⟩ => .op (.inr (MetaOp.mk (M := scopeMetas) 0)) (.cons (.var .zero) .nil)
  | ⟨1, _⟩ => .op (.inr (MetaOp.mk (M := scopeMetas) 1)) (.cons (.var .zero) .nil)
  | ⟨n + 2, impossible⟩ => by simp [scopeMetas] at impossible

private def schemaNu (body : Term scopeSig [Srt.nm] .pr) : Term scopeSig [] .pr :=
  .op (.inl .nu) (.cons body .nil)

/-- The child judgment lives under the actual private-name binder. -/
def underScope : IntrinsicScopedConditionalPolynomial.Rule sig scopeMetas where
  conclusion := {
    ctx := []
    sort := .pr
    lhs := schemaNu (scopeBody 0)
    rhs := schemaNu (scopeBody 1)
    position := rootPosition _ }
  premises := [{
    binders := [Srt.nm]
    sort := .pr
    source := scopeBody 0
    target := scopeBody 1 }]

/-- One runtime profile of the existing signature and communication schemas.
Each selected declaration retains its own metavariable telescope. -/
def rules : List (LocalRule sig) :=
  [⟨metas, rootRule comm1⟩, ⟨metas, rootRule comm2⟩,
   ⟨[], parLeft⟩, ⟨[], parRight⟩, ⟨scopeMetas, underScope⟩]

theorem ordered_premise_binders :
    rules.map (fun declaration => declaration.2.premises.map (fun premise => premise.binders)) =
      [[], [], [[]], [[]], [[Srt.nm]]] := rfl

/-- Interpretation in the raw clone uses the existing contextual instantiator. -/
theorem conclusion_as_syntax (occurrence : Instance rules (BindingCloneAlgebra.terms sig)) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment rules (BindingCloneAlgebra.terms sig) occurrence =
      (⟨occurrence.ambient, (rules.get occurrence.index).2.conclusion.sort,
        ContextualAssignment.instantiate occurrence.valuation (fun _ x => .var x)
          occurrence.close (rules.get occurrence.index).2.conclusion.lhs,
        ContextualAssignment.instantiate occurrence.valuation (fun _ x => .var x)
          occurrence.close (rules.get occurrence.index).2.conclusion.rhs⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨occurrence.ambient, (rules.get occurrence.index).2.conclusion.sort,
    interpretSchema (BindingCloneAlgebra.terms sig) occurrence.valuation (fun _ x => .var x)
      occurrence.close (rules.get occurrence.index).2.conclusion.lhs,
    interpretSchema (BindingCloneAlgebra.terms sig) occurrence.valuation (fun _ x => .var x)
      occurrence.close (rules.get occurrence.index).2.conclusion.rhs⟩ :
      Judgment (BindingCloneAlgebra.terms sig)) = _
  exact congrArg₂ (fun source target =>
    (⟨occurrence.ambient, (rules.get occurrence.index).2.conclusion.sort, source, target⟩ :
      Judgment (BindingCloneAlgebra.terms sig)))
    (interpretSchema_terms (S := sig) occurrence.valuation (fun _ x => .var x)
      occurrence.close (rules.get occurrence.index).2.conclusion.lhs)
    (interpretSchema_terms (S := sig) occurrence.valuation (fun _ x => .var x)
      occurrence.close (rules.get occurrence.index).2.conclusion.rhs)

/-- The premise's explicit binder extension is retained by the same comparison. -/
theorem child_as_syntax (occurrence : Instance rules (BindingCloneAlgebra.terms sig))
    (position : Fin (rules.get occurrence.index).2.premises.length) :
    IntrinsicScopedLocalPolynomial.childJudgment rules (BindingCloneAlgebra.terms sig) occurrence position =
      let premise := (rules.get occurrence.index).2.premises.get position
      (⟨premise.binders ++ occurrence.ambient, premise.sort,
        ContextualAssignment.instantiate occurrence.valuation
          (weakenSub (S := sig) premise.binders (fun _ x => .var x : Sub sig occurrence.ambient occurrence.ambient))
          (liftSub (S := sig) occurrence.close premise.binders) premise.source,
        ContextualAssignment.instantiate occurrence.valuation
          (weakenSub (S := sig) premise.binders (fun _ x => .var x : Sub sig occurrence.ambient occurrence.ambient))
          (liftSub (S := sig) occurrence.close premise.binders) premise.target⟩ :
          Judgment (BindingCloneAlgebra.terms sig)) := by
  change interpretPremise (BindingCloneAlgebra.terms sig) occurrence.valuation
    occurrence.close ((rules.get occurrence.index).2.premises.get position) = _
  exact interpretPremise_terms occurrence.valuation occurrence.close
    ((rules.get occurrence.index).2.premises.get position)

def unaryOccurrence {Γ : Ctx sig} (firing : ContextualRootEvents.Instance comm1 Γ) :
    Instance rules (BindingCloneAlgebra.terms sig) where
  index := ⟨0, by decide⟩
  ambient := Γ
  valuation := firing.body
  close := firing.close

def binaryOccurrence {Γ : Ctx sig} (firing : ContextualRootEvents.Instance comm2 Γ) :
    Instance rules (BindingCloneAlgebra.terms sig) where
  index := ⟨1, by decide⟩
  ambient := Γ
  valuation := firing.body
  close := firing.close

def parallelOccurrence {Γ : Ctx sig} (left : Bool) (source target frame : Proc Γ) :
    Instance rules (BindingCloneAlgebra.terms sig) where
  index := if left then ⟨2, by decide⟩ else ⟨3, by decide⟩
  ambient := Γ
  valuation := by cases left <;> exact fun index => nomatch index
  close := by
    cases left <;> exact argsToSub (S := sig) (bs := [Srt.pr, Srt.pr, Srt.pr])
      (.cons source (.cons target (.cons frame .nil)))

def scopeSupply {Γ : Ctx sig} (source target : Proc (.nm :: Γ)) :
    ContextualAssignment sig scopeMetas Γ
  | ⟨0, _⟩ => source
  | ⟨1, _⟩ => target
  | ⟨n + 2, impossible⟩ => by simp [scopeMetas] at impossible

def scopeOccurrence {Γ : Ctx sig} (source target : Proc (.nm :: Γ)) :
    Instance rules (BindingCloneAlgebra.terms sig) where
  index := ⟨4, by decide⟩
  ambient := Γ
  valuation := scopeSupply source target
  close := fun _ x => nomatch x

theorem unary_conclusion {Γ : Ctx sig} (firing : ContextualRootEvents.Instance comm1 Γ) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment rules (BindingCloneAlgebra.terms sig)
      (unaryOccurrence firing) =
      (⟨Γ, Srt.pr, firing.source, firing.target⟩ : Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨Γ, Srt.pr,
    interpretSchema (BindingCloneAlgebra.terms sig) firing.body
      (fun _ x => .var x) firing.close comm1.lhs,
    interpretSchema (BindingCloneAlgebra.terms sig) firing.body
      (fun _ x => .var x) firing.close comm1.rhs⟩ : Judgment (BindingCloneAlgebra.terms sig)) = _
  exact congrArg₂ (fun source target =>
    (⟨Γ, Srt.pr, source, target⟩ : Judgment (BindingCloneAlgebra.terms sig)))
    (interpretSchema_terms (S := sig) (M := metas) firing.body
      (fun _ x => .var x) firing.close comm1.lhs)
    (interpretSchema_terms (S := sig) (M := metas) firing.body
      (fun _ x => .var x) firing.close comm1.rhs)

theorem binary_conclusion {Γ : Ctx sig} (firing : ContextualRootEvents.Instance comm2 Γ) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment rules (BindingCloneAlgebra.terms sig)
      (binaryOccurrence firing) =
      (⟨Γ, Srt.pr, firing.source, firing.target⟩ : Judgment (BindingCloneAlgebra.terms sig)) := by
  change (⟨Γ, Srt.pr,
    interpretSchema (BindingCloneAlgebra.terms sig) firing.body
      (fun _ x => .var x) firing.close comm2.lhs,
    interpretSchema (BindingCloneAlgebra.terms sig) firing.body
      (fun _ x => .var x) firing.close comm2.rhs⟩ : Judgment (BindingCloneAlgebra.terms sig)) = _
  exact congrArg₂ (fun source target =>
    (⟨Γ, Srt.pr, source, target⟩ : Judgment (BindingCloneAlgebra.terms sig)))
    (interpretSchema_terms (S := sig) (M := metas) firing.body
      (fun _ x => .var x) firing.close comm2.lhs)
    (interpretSchema_terms (S := sig) (M := metas) firing.body
      (fun _ x => .var x) firing.close comm2.rhs)

theorem parallel_child {Γ : Ctx sig} (left : Bool) (source target frame : Proc Γ)
    (position : Fin (rules.get (parallelOccurrence left source target frame).index).2.premises.length) :
    IntrinsicScopedLocalPolynomial.childJudgment rules (BindingCloneAlgebra.terms sig)
      (parallelOccurrence left source target frame) position =
      (⟨Γ, Srt.pr, source, target⟩ : Judgment (BindingCloneAlgebra.terms sig)) := by
  rw [child_as_syntax]
  cases left <;> have zero : position =
      ⟨0, by simp [rules, parallelOccurrence, parLeft, parRight]⟩ := Fin.eq_zero position
  all_goals subst position; rfl

theorem parallel_conclusion {Γ : Ctx sig} (left : Bool) (source target frame : Proc Γ) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment rules (BindingCloneAlgebra.terms sig)
      (parallelOccurrence left source target frame) =
      (⟨Γ, Srt.pr, if left then par source frame else par frame source,
        if left then par target frame else par frame target⟩ : Judgment (BindingCloneAlgebra.terms sig)) := by
  rw [conclusion_as_syntax]
  cases left <;> rfl

private theorem scope_identity {Γ : Ctx sig} :
    joinSub (S := sig) (Γ := Γ) (Δ := Srt.nm :: Γ) (dependencies := [Srt.nm])
      (argsToSub (S := sig) (bs := [Srt.nm]) (.cons (.var .zero) .nil))
      (weakenSub (S := sig) [Srt.nm] (fun _ x => .var x : Sub sig Γ Γ)) =
      (fun _ x => .var x) := by
  funext s x
  cases x <;> rfl

theorem scope_child {Γ : Ctx sig} (source target : Proc (.nm :: Γ))
    (position : Fin (rules.get (scopeOccurrence source target).index).2.premises.length) :
    IntrinsicScopedLocalPolynomial.childJudgment rules (BindingCloneAlgebra.terms sig)
      (scopeOccurrence source target) position =
      (⟨Srt.nm :: Γ, Srt.pr, source, target⟩ : Judgment (BindingCloneAlgebra.terms sig)) := by
  rw [child_as_syntax]
  have zero : position = ⟨0, by simp [rules, scopeOccurrence, underScope]⟩ := Fin.eq_zero position
  subst position
  dsimp only [rules, List.get, underScope, scopeBody, scopeOccurrence, scopeSupply,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply]
  change (⟨Srt.nm :: Γ, Srt.pr,
    Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := sig) (bs := [Srt.nm]) (.cons (.var .zero) .nil))
        (weakenSub [Srt.nm] (fun _ x => .var x : Sub sig Γ Γ))) source,
    Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := sig) (bs := [Srt.nm]) (.cons (.var .zero) .nil))
        (weakenSub [Srt.nm] (fun _ x => .var x : Sub sig Γ Γ))) target⟩ :
      Judgment (BindingCloneAlgebra.terms sig)) = _
  rw [scope_identity, bind_id, bind_id]

theorem scope_conclusion {Γ : Ctx sig} (source target : Proc (.nm :: Γ)) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment rules (BindingCloneAlgebra.terms sig)
      (scopeOccurrence source target) =
      (⟨Γ, Srt.pr, nu source, nu target⟩ : Judgment (BindingCloneAlgebra.terms sig)) := by
  rw [conclusion_as_syntax]
  dsimp only [rules, List.get, scopeOccurrence, underScope, schemaNu, scopeBody, scopeSupply,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply]
  change (⟨Γ, Srt.pr,
    nu (Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := sig) (bs := [Srt.nm]) (.cons (.var .zero) .nil))
        (weakenSub [Srt.nm] (fun _ x => .var x : Sub sig Γ Γ))) source),
    nu (Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := sig) (bs := [Srt.nm]) (.cons (.var .zero) .nil))
        (weakenSub [Srt.nm] (fun _ x => .var x : Sub sig Γ Γ))) target)⟩ :
      Judgment (BindingCloneAlgebra.terms sig)) = _
  rw [scope_identity, bind_id, bind_id]

/-- The independently defined runtime predicate at each sorted judgment. -/
def sourceStep : Judgment (BindingCloneAlgebra.terms sig) → Prop
  | ⟨_, .nm, _, _⟩ => False
  | ⟨_, .pr, source, target⟩ => Step source target

/-- Every authored profile constructor is sound when all of its actual,
binder-local child judgments are sound. -/
theorem sourceStep_ruleClosed
    (occurrence : Instance rules (BindingCloneAlgebra.terms sig))
    (children : ∀ position : Fin (rules.get occurrence.index).2.premises.length,
      sourceStep (IntrinsicScopedLocalPolynomial.childJudgment rules
        (BindingCloneAlgebra.terms sig) occurrence position)) :
    sourceStep (IntrinsicScopedLocalPolynomial.conclusionJudgment rules
      (BindingCloneAlgebra.terms sig) occurrence) := by
  rcases occurrence with ⟨⟨index, bounded⟩, Γ, valuation, close⟩
  have small : index < 5 := by simpa [rules] using bounded
  interval_cases index
  · let firing : ContextualRootEvents.Instance comm1 Γ := ⟨valuation, close⟩
    change sourceStep (IntrinsicScopedLocalPolynomial.conclusionJudgment rules
      (BindingCloneAlgebra.terms sig) (unaryOccurrence firing))
    rw [unary_conclusion]
    change Step firing.source firing.target
    rw [arbitrary_unary_source, arbitrary_unary_target]
    exact .comm1 _ _ _
  · let firing : ContextualRootEvents.Instance comm2 Γ := ⟨valuation, close⟩
    change sourceStep (IntrinsicScopedLocalPolynomial.conclusionJudgment rules
      (BindingCloneAlgebra.terms sig) (binaryOccurrence firing))
    rw [binary_conclusion]
    change Step firing.source firing.target
    rw [arbitrary_binary_source, arbitrary_binary_target]
    exact .comm2 _ _ _ _
  · have child := children ⟨0, by simp [rules, parLeft]⟩
    rw [child_as_syntax] at child
    change Step (close .pr .zero) (close .pr (.succ .zero)) at child
    rw [conclusion_as_syntax]
    change Step
      (par (close .pr .zero) (close .pr (.succ (.succ .zero))))
      (par (close .pr (.succ .zero)) (close .pr (.succ (.succ .zero))))
    exact .parL _ child
  · have child := children ⟨0, by simp [rules, parRight]⟩
    rw [child_as_syntax] at child
    change Step (close .pr .zero) (close .pr (.succ .zero)) at child
    rw [conclusion_as_syntax]
    change Step
      (par (close .pr (.succ (.succ .zero))) (close .pr .zero))
      (par (close .pr (.succ (.succ .zero))) (close .pr (.succ .zero)))
    exact .parR _ child
  · have normalized :
        (⟨⟨4, bounded⟩, Γ, valuation, close⟩ : Instance rules (BindingCloneAlgebra.terms sig)) =
          scopeOccurrence (valuation (⟨0, by simp [rules]⟩)) (valuation (⟨1, by simp [rules]⟩)) := by
      have values : valuation = scopeSupply (valuation (⟨0, by simp [rules]⟩)) (valuation (⟨1, by simp [rules]⟩)) := by
        funext index
        rcases index with ⟨index, bound⟩
        have small : index < 2 := bound
        interval_cases index <;> rfl
      calc
        _ = (⟨⟨4, bounded⟩, Γ,
          scopeSupply (valuation (⟨0, by simp [rules]⟩)) (valuation (⟨1, by simp [rules]⟩)),
          close⟩ : Instance rules (BindingCloneAlgebra.terms sig)) :=
          congrArg (fun assigned =>
            (⟨⟨4, bounded⟩, Γ, assigned, close⟩ : Instance rules (BindingCloneAlgebra.terms sig))) values
        _ = _ := by
          unfold scopeOccurrence
          congr 1
          funext s x
          nomatch x
    rw [normalized] at children ⊢
    have child := children ⟨0, by simp [rules, scopeOccurrence, underScope]⟩
    have actual : Step (valuation (⟨0, by simp [rules]⟩)) (valuation (⟨1, by simp [rules]⟩)) :=
      (congrArg sourceStep (scope_child _ _ ⟨0, by simp [rules, scopeOccurrence, underScope]⟩)).mp child
    exact (congrArg sourceStep (scope_conclusion _ _)).mpr (Step.nu actual)

/-- A complete generated tree supplies an actual runtime step at exactly
the tree's endpoints. -/
theorem tree_sound (judgment : Judgment (BindingCloneAlgebra.terms sig))
    (tree : Tree rules (BindingCloneAlgebra.terms sig) judgment) : sourceStep judgment := by
  refine Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate
    (IntrinsicScopedLocalPolynomial.rules rules (BindingCloneAlgebra.terms sig))
    (fun _ j _ => sourceStep j) ?_ () judgment tree
  intro base j shape descendants premises
  obtain ⟨occurrence, same⟩ := shape
  subst same
  exact sourceStep_ruleClosed occurrence premises

/-- Endpoint image of the independently generated profile's firing trees. -/
def Reduces (judgment : Judgment (BindingCloneAlgebra.terms sig)) : Prop :=
  Nonempty (Tree rules (BindingCloneAlgebra.terms sig) judgment)

private theorem reduces_ruleClosed (occurrence : Instance rules (BindingCloneAlgebra.terms sig))
    (children : ∀ position : Fin (rules.get occurrence.index).2.premises.length,
      Reduces (IntrinsicScopedLocalPolynomial.childJudgment rules
        (BindingCloneAlgebra.terms sig) occurrence position)) :
    Reduces (IntrinsicScopedLocalPolynomial.conclusionJudgment rules
      (BindingCloneAlgebra.terms sig) occurrence) := by
  exact ⟨.roll ⟨occurrence, rfl⟩ (fun position => Classical.choice (children position))⟩

/-- Every actual runtime communication and active descent is generated by
the profile, including reduction under private names. -/
theorem step_complete {Γ : Ctx sig} {source target : Proc Γ}
    (step : Step source target) : Reduces ⟨Γ, Srt.pr, source, target⟩ := by
  induction step with
  | comm1 channel datum body =>
      let firing := unaryInstance channel datum body
      have generated := reduces_ruleClosed (unaryOccurrence firing)
        (by intro position; nomatch position)
      rw [unary_conclusion, unary_source, unary_target] at generated
      exact generated
  | comm2 channel first second body =>
      let firing := binaryInstance channel first second body
      have generated := reduces_ruleClosed (binaryOccurrence firing)
        (by intro position; nomatch position)
      rw [binary_conclusion, binary_source, binary_target] at generated
      exact generated
  | parL frame _ ih =>
      have generated := reduces_ruleClosed (parallelOccurrence true _ _ frame) (by
        intro position
        rw [parallel_child]
        exact ih)
      rw [parallel_conclusion] at generated
      exact generated
  | parR frame _ ih =>
      have generated := reduces_ruleClosed (parallelOccurrence false _ _ frame) (by
        intro position
        rw [parallel_child]
        exact ih)
      rw [parallel_conclusion] at generated
      exact generated
  | nu _ ih =>
      have generated := reduces_ruleClosed (scopeOccurrence _ _) (by
        intro position
        rw [scope_child]
        exact ih)
      rw [scope_conclusion] at generated
      exact generated

/-- The actual supplied runtime endpoints are exactly the raw endpoint
image of the authored binder-local profile. -/
theorem step_iff_tree {Γ : Ctx sig} (source target : Proc Γ) :
    Step source target ↔
      Nonempty (Tree rules (BindingCloneAlgebra.terms sig) ⟨Γ, Srt.pr, source, target⟩) := by
  constructor
  · exact step_complete
  · rintro ⟨tree⟩
    exact tree_sound _ tree

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredOperationalProfile
