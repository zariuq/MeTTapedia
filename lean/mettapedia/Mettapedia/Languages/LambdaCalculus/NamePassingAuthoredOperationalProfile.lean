import Mettapedia.Languages.LambdaCalculus.NamePassingAuthoredEquations
import Mettapedia.Languages.LambdaCalculus.NamePassingOperationalOccurrenceComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalRawReadout

/-!
# Independently authored name-passing root and active-position rules

Beta and fetch are unconditional schemas. Application, definition and
carrier each have one ordered step premise; the definition premise has
exactly one reference binder, while its stored value is outside it.
Generated rule evidence is compared with the actual supplied active-edge
occurrences. Abstraction and the stored-value positions have no active rule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.AuthoredOperationalProfile

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualAssignment
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial (LocalRule Instance Tree)
open Presentation

private def schemaAbs {M : List (MetaArity signature)} {Γ : Ctx (withMetas signature M)}
    (body : Term (withMetas signature M) (.nm :: Γ) .tm) :
    Term (withMetas signature M) Γ .tm := .op (.inl .abstraction) (.cons body .nil)

private def schemaApp {M : List (MetaArity signature)} {Γ : Ctx (withMetas signature M)}
    (function : Term (withMetas signature M) Γ .tm)
    (argument : Term (withMetas signature M) Γ .nm) :
    Term (withMetas signature M) Γ .tm :=
  .op (.inl .application) (.cons function (.cons argument .nil))

private def schemaDef {M : List (MetaArity signature)} {Γ : Ctx (withMetas signature M)}
    (value : Term (withMetas signature M) Γ .tm)
    (body : Term (withMetas signature M) (.nm :: Γ) .tm) :
    Term (withMetas signature M) Γ .tm :=
  .op (.inl .definition) (.cons value (.cons body .nil))

private def schemaCarrier {M : List (MetaArity signature)} {Γ : Ctx (withMetas signature M)}
    (name : Term (withMetas signature M) Γ .nm)
    (value body : Term (withMetas signature M) Γ .tm) :
    Term (withMetas signature M) Γ .tm :=
  .op (.inl .carrier) (.cons name (.cons value (.cons body .nil)))

private def schemaRef {M : List (MetaArity signature)} {Γ : Ctx (withMetas signature M)}
    (name : Term (withMetas signature M) Γ .nm) :
    Term (withMetas signature M) Γ .tm := .op (.inl .reference) (.cons name .nil)

abbrev betaMetas : List (MetaArity signature) := [([Srt.nm], Srt.tm)]

private def betaBody {Γ : Ctx (withMetas signature betaMetas)}
    (argument : Term (withMetas signature betaMetas) Γ .nm) :
    Term (withMetas signature betaMetas) Γ .tm :=
  .op (.inr (MetaOp.mk (M := betaMetas) 0)) (.cons argument .nil)

def beta : IntrinsicScopedConditionalPolynomial.Rule signature betaMetas where
  conclusion := {
    ctx := [.nm]
    sort := .tm
    lhs := schemaApp (schemaAbs (betaBody (.var .zero))) (.var .zero)
    rhs := betaBody (.var .zero)
    position := rootPosition _ }
  premises := []

def fetch : IntrinsicScopedConditionalPolynomial.Rule signature [] where
  conclusion := {
    ctx := [.nm, .tm]
    sort := .tm
    lhs := schemaCarrier (.var .zero) (.var (.succ .zero)) (schemaRef (.var .zero))
    rhs := .var (.succ .zero)
    position := rootPosition _ }
  premises := []

def application : IntrinsicScopedConditionalPolynomial.Rule signature [] where
  conclusion := {
    ctx := [.tm, .tm, .nm]
    sort := .tm
    lhs := schemaApp (.var .zero) (.var (.succ (.succ .zero)))
    rhs := schemaApp (.var (.succ .zero)) (.var (.succ (.succ .zero)))
    position := rootPosition _ }
  premises := [{binders := [], sort := .tm, source := .var .zero, target := .var (.succ .zero)}]

abbrev definitionMetas : List (MetaArity signature) :=
  [([Srt.nm], Srt.tm), ([Srt.nm], Srt.tm)]

private def definitionBody {Γ : Ctx (withMetas signature definitionMetas)}
    (index : Fin definitionMetas.length) (argument : Term (withMetas signature definitionMetas) Γ .nm) :
    Term (withMetas signature definitionMetas) Γ .tm := by
  rcases index with ⟨index, bound⟩
  have small : index < 2 := bound
  interval_cases index
  · exact .op (.inr (MetaOp.mk (M := definitionMetas) 0)) (.cons argument .nil)
  · exact .op (.inr (MetaOp.mk (M := definitionMetas) 1)) (.cons argument .nil)

def definition : IntrinsicScopedConditionalPolynomial.Rule signature definitionMetas where
  conclusion := {
    ctx := [.tm]
    sort := .tm
    lhs := schemaDef (.var .zero) (definitionBody 0 (.var .zero))
    rhs := schemaDef (.var .zero) (definitionBody 1 (.var .zero))
    position := rootPosition _ }
  premises := [{
    binders := [.nm]
    sort := .tm
    source := definitionBody 0 (.var .zero)
    target := definitionBody 1 (.var .zero) }]

def carrier : IntrinsicScopedConditionalPolynomial.Rule signature [] where
  conclusion := {
    ctx := [.nm, .tm, .tm, .tm]
    sort := .tm
    lhs := schemaCarrier (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))
    rhs := schemaCarrier (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ (.succ .zero))))
    position := rootPosition _ }
  premises := [{
    binders := []
    sort := .tm
    source := .var (.succ (.succ .zero))
    target := .var (.succ (.succ (.succ .zero))) }]

def rules : List (LocalRule signature) :=
  [⟨betaMetas, beta⟩, ⟨[], fetch⟩, ⟨[], application⟩,
    ⟨definitionMetas, definition⟩, ⟨[], carrier⟩]

theorem ordered_premise_binders :
    rules.map (fun declaration => declaration.2.premises.map (fun premise => premise.binders)) =
      [[], [], [[]], [[Srt.nm]], [[]]] := rfl

abbrev raw := BindingCloneAlgebra.terms signature

private theorem binder_identity {Γ : Ctx signature} :
    joinSub (S := signature) (Γ := Γ) (Δ := Srt.nm :: Γ) (dependencies := [Srt.nm])
      (argsToSub (S := signature) (bs := [Srt.nm]) (.cons (.var .zero) .nil))
      (weakenSub (S := signature) [Srt.nm] (fun _ x => .var x : Sub signature Γ Γ)) =
      (fun _ x => .var x) := by
  funext sort position
  cases position <;> rfl

def betaOccurrence {Γ : Ctx signature} (body : Program (.nm :: Γ)) (argument : Name Γ) :
    Instance rules raw :=
  ⟨⟨0, by decide⟩, Γ, AuthoredEquations.supply body,
    argsToSub (S := signature) (bs := [Srt.nm]) (.cons argument .nil)⟩

def fetchOccurrence {Γ : Ctx signature} (name : Name Γ) (value : Program Γ) : Instance rules raw :=
  ⟨⟨1, by decide⟩, Γ, (fun index => nomatch index),
    argsToSub (S := signature) (bs := [Srt.nm, Srt.tm]) (.cons name (.cons value .nil))⟩

def applicationOccurrence {Γ : Ctx signature} (first last : Program Γ) (argument : Name Γ) :
    Instance rules raw :=
  ⟨⟨2, by decide⟩, Γ, (fun index => nomatch index),
    argsToSub (S := signature) (bs := [Srt.tm, Srt.tm, Srt.nm])
      (.cons first (.cons last (.cons argument .nil)))⟩

def definitionSupply {Γ : Ctx signature} (first last : Program (.nm :: Γ)) :
    ContextualAssignment signature definitionMetas Γ
  | ⟨0, _⟩ => first
  | ⟨1, _⟩ => last
  | ⟨n + 2, impossible⟩ => by simp [definitionMetas] at impossible

def definitionOccurrence {Γ : Ctx signature} (value : Program Γ) (first last : Program (.nm :: Γ)) :
    Instance rules raw :=
  ⟨⟨3, by decide⟩, Γ, definitionSupply first last,
    argsToSub (S := signature) (bs := [Srt.tm]) (.cons value .nil)⟩

def carrierOccurrence {Γ : Ctx signature} (name : Name Γ) (value first last : Program Γ) :
    Instance rules raw :=
  ⟨⟨4, by decide⟩, Γ, (fun index => nomatch index),
    argsToSub (S := signature) (bs := [Srt.nm, Srt.tm, Srt.tm, Srt.tm])
      (.cons name (.cons value (.cons first (.cons last .nil))))⟩

theorem beta_conclusion {Γ : Ctx signature} (body : Program (.nm :: Γ)) (argument : Name Γ) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment rules raw (betaOccurrence body argument) =
      (⟨Γ, Srt.tm, Presentation.application (abstraction body) argument, inst body argument⟩ : Judgment raw) := by
  rw [IntrinsicScopedLocalRawReadout.conclusion]
  dsimp only [rules, List.get, betaOccurrence, beta, schemaApp, schemaAbs, betaBody,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, AuthoredEquations.supply]
  change (⟨Γ, Srt.tm,
    Presentation.application (abstraction (Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := signature) (bs := [Srt.nm]) (.cons (.var .zero) .nil))
        (weakenSub [Srt.nm] (fun _ x => .var x : Sub signature Γ Γ))) body)) argument,
    Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := signature) (bs := [Srt.nm]) (.cons argument .nil))
        (fun _ x => .var x : Sub signature Γ Γ)) body⟩ : Judgment raw) = _
  rw [binder_identity, bind_id]
  have plugged : joinSub (S := signature) (dependencies := [Srt.nm])
      (argsToSub (S := signature) (bs := [Srt.nm]) (.cons argument .nil))
      (fun _ x => .var x : Sub signature Γ Γ) =
      Mettapedia.OSLF.Binding.extend argument := by
    funext sort position
    cases position <;> rfl
  rw [plugged]
  rfl

theorem fetch_conclusion {Γ : Ctx signature} (name : Name Γ) (value : Program Γ) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment rules raw (fetchOccurrence name value) =
      (⟨Γ, Srt.tm, Presentation.carrier name value (reference name), value⟩ : Judgment raw) := by
  rw [IntrinsicScopedLocalRawReadout.conclusion]
  rfl

theorem application_conclusion {Γ : Ctx signature} (first last : Program Γ) (argument : Name Γ) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment rules raw (applicationOccurrence first last argument) =
      (⟨Γ, Srt.tm, Presentation.application first argument, Presentation.application last argument⟩ : Judgment raw) := by
  rw [IntrinsicScopedLocalRawReadout.conclusion]
  rfl

theorem application_child {Γ : Ctx signature} (first last : Program Γ) (argument : Name Γ)
    (position : Fin (rules.get (applicationOccurrence first last argument).index).2.premises.length) :
    IntrinsicScopedLocalPolynomial.childJudgment rules raw (applicationOccurrence first last argument) position =
      (⟨Γ, Srt.tm, first, last⟩ : Judgment raw) := by
  rw [IntrinsicScopedLocalRawReadout.child]
  have zero : position = ⟨0, by simp [rules, applicationOccurrence, application]⟩ := Fin.eq_zero position
  subst position
  rfl

theorem definition_conclusion {Γ : Ctx signature} (value : Program Γ) (first last : Program (.nm :: Γ)) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment rules raw (definitionOccurrence value first last) =
      (⟨Γ, Srt.tm, Presentation.definition value first, Presentation.definition value last⟩ : Judgment raw) := by
  rw [IntrinsicScopedLocalRawReadout.conclusion]
  dsimp only [rules, List.get, definitionOccurrence, definition, schemaDef, definitionBody,
    definitionSupply, ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply]
  change (⟨Γ, Srt.tm,
    Presentation.definition value (Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := signature) (bs := [Srt.nm]) (.cons (.var .zero) .nil))
        (weakenSub [Srt.nm] (fun _ x => .var x : Sub signature Γ Γ))) first),
    Presentation.definition value (Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := signature) (bs := [Srt.nm]) (.cons (.var .zero) .nil))
        (weakenSub [Srt.nm] (fun _ x => .var x : Sub signature Γ Γ))) last)⟩ : Judgment raw) = _
  rw [binder_identity, bind_id, bind_id]

theorem definition_child {Γ : Ctx signature} (value : Program Γ) (first last : Program (.nm :: Γ))
    (position : Fin (rules.get (definitionOccurrence value first last).index).2.premises.length) :
    IntrinsicScopedLocalPolynomial.childJudgment rules raw (definitionOccurrence value first last) position =
      (⟨Srt.nm :: Γ, Srt.tm, first, last⟩ : Judgment raw) := by
  rw [IntrinsicScopedLocalRawReadout.child]
  have zero : position = ⟨0, by simp [rules, definitionOccurrence, definition]⟩ := Fin.eq_zero position
  subst position
  dsimp only [rules, List.get, definitionOccurrence, definition, definitionBody, definitionSupply,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs, ContextualAssignment.apply]
  change (⟨Srt.nm :: Γ, Srt.tm,
    Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := signature) (bs := [Srt.nm]) (.cons (.var .zero) .nil))
        (weakenSub [Srt.nm] (fun _ x => .var x : Sub signature Γ Γ))) first,
    Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := signature) (bs := [Srt.nm]) (.cons (.var .zero) .nil))
        (weakenSub [Srt.nm] (fun _ x => .var x : Sub signature Γ Γ))) last⟩ : Judgment raw) = _
  rw [binder_identity, bind_id, bind_id]

theorem carrier_conclusion {Γ : Ctx signature} (name : Name Γ) (value first last : Program Γ) :
    IntrinsicScopedLocalPolynomial.conclusionJudgment rules raw (carrierOccurrence name value first last) =
      (⟨Γ, Srt.tm, Presentation.carrier name value first, Presentation.carrier name value last⟩ : Judgment raw) := by
  rw [IntrinsicScopedLocalRawReadout.conclusion]
  rfl

theorem carrier_child {Γ : Ctx signature} (name : Name Γ) (value first last : Program Γ)
    (position : Fin (rules.get (carrierOccurrence name value first last).index).2.premises.length) :
    IntrinsicScopedLocalPolynomial.childJudgment rules raw (carrierOccurrence name value first last) position =
      (⟨Γ, Srt.tm, first, last⟩ : Judgment raw) := by
  rw [IntrinsicScopedLocalRawReadout.child]
  have zero : position = ⟨0, by simp [rules, carrierOccurrence, carrier]⟩ := Fin.eq_zero position
  subst position
  rfl

theorem beta_normalization {Γ : Ctx signature}
    (valuation : ContextualAssignment signature betaMetas Γ)
    (close : Sub signature [.nm] Γ) (bounded : 0 < rules.length) :
    (⟨⟨0, bounded⟩, Γ, valuation, close⟩ : Instance rules raw) =
      betaOccurrence (valuation 0) (close .nm .zero) := by
  have values : valuation = AuthoredEquations.supply (valuation 0) := by
    funext index
    have zero : index = 0 := Fin.eq_zero index
    subst index
    rfl
  have names : close = argsToSub (S := signature) (bs := [Srt.nm])
      (.cons (close .nm .zero) .nil) := by
    funext sort position
    cases position with
    | zero => rfl
    | succ impossible => nomatch impossible
  rw [values, names]
  rfl

theorem definition_normalization {Γ : Ctx signature}
    (valuation : ContextualAssignment signature definitionMetas Γ)
    (close : Sub signature [.tm] Γ) (bounded : 3 < rules.length) :
    (⟨⟨3, bounded⟩, Γ, valuation, close⟩ : Instance rules raw) =
      definitionOccurrence (close .tm .zero) (valuation 0) (valuation 1) := by
  have values : valuation = definitionSupply (valuation 0) (valuation 1) := by
    funext index
    rcases index with ⟨index, bounded⟩
    have small : index < 2 := bounded
    interval_cases index <;> rfl
  have stored : close = argsToSub (S := signature) (bs := [Srt.tm])
      (.cons (close .tm .zero) .nil) := by
    funext sort position
    cases position with
    | zero => rfl
    | succ impossible => nomatch impossible
  rw [values, stored]
  rfl

/-- The independent runtime edge assertion retains a supplied active occurrence. -/
def sourceStep : Judgment raw → Prop
  | ⟨_, .nm, _, _⟩ => False
  | ⟨_, .tm, first, last⟩ => Nonempty (ActiveEdge first last)

/-- Arbitrary contextual assignments, not only hand-picked controls, validate
each authored constructor at the complete premise endpoints. -/
theorem sourceStep_ruleClosed (occurrence : Instance rules raw)
    (children : ∀ position : Fin (rules.get occurrence.index).2.premises.length,
      sourceStep (IntrinsicScopedLocalPolynomial.childJudgment rules raw occurrence position)) :
    sourceStep (IntrinsicScopedLocalPolynomial.conclusionJudgment rules raw occurrence) := by
  rcases occurrence with ⟨⟨index, bounded⟩, Γ, valuation, close⟩
  have small : index < 5 := by simpa [rules] using bounded
  interval_cases index
  · rw [beta_normalization valuation close bounded, beta_conclusion]
    exact ⟨.root (.beta _ _)⟩
  · rw [IntrinsicScopedLocalRawReadout.conclusion]
    change Nonempty (ActiveEdge
      (Presentation.carrier (close .nm .zero) (close .tm (.succ .zero))
        (reference (close .nm .zero))) (close .tm (.succ .zero)))
    exact ⟨.root (.fetch _ _)⟩
  · have child := children ⟨0, by simp [rules, application]⟩
    rw [IntrinsicScopedLocalRawReadout.child] at child
    change Nonempty (ActiveEdge (close .tm .zero) (close .tm (.succ .zero))) at child
    rw [IntrinsicScopedLocalRawReadout.conclusion]
    change Nonempty (ActiveEdge
      (Presentation.application (close .tm .zero) (close .nm (.succ (.succ .zero))))
      (Presentation.application (close .tm (.succ .zero)) (close .nm (.succ (.succ .zero)))))
    exact child.map (ActiveEdge.application _)
  · rw [definition_normalization valuation close bounded] at children ⊢
    have child := children ⟨0, by simp [rules, definitionOccurrence, definition]⟩
    rw [definition_child] at child
    rw [definition_conclusion]
    exact child.map (ActiveEdge.definition _)
  · have child := children ⟨0, by simp [rules, carrier]⟩
    rw [IntrinsicScopedLocalRawReadout.child] at child
    change Nonempty (ActiveEdge (close .tm (.succ (.succ .zero)))
      (close .tm (.succ (.succ (.succ .zero))))) at child
    rw [IntrinsicScopedLocalRawReadout.conclusion]
    change Nonempty (ActiveEdge
      (Presentation.carrier (close .nm .zero) (close .tm (.succ .zero)) (close .tm (.succ (.succ .zero))))
      (Presentation.carrier (close .nm .zero) (close .tm (.succ .zero))
        (close .tm (.succ (.succ (.succ .zero))))))
    exact child.map (ActiveEdge.carrier _ _)

theorem tree_sound (judgment : Judgment raw) (tree : Tree rules raw judgment) : sourceStep judgment := by
  refine Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate
    (IntrinsicScopedLocalPolynomial.rules rules raw)
    (fun _ j _ => sourceStep j) ?_ () judgment tree
  intro base j shape descendants premises
  obtain ⟨occurrence, same⟩ := shape
  subst same
  exact sourceStep_ruleClosed occurrence premises

def Generated (judgment : Judgment raw) : Prop := Nonempty (Tree rules raw judgment)

private theorem generated_ruleClosed (occurrence : Instance rules raw)
    (children : ∀ position : Fin (rules.get occurrence.index).2.premises.length,
      Generated (IntrinsicScopedLocalPolynomial.childJudgment rules raw occurrence position)) :
    Generated (IntrinsicScopedLocalPolynomial.conclusionJudgment rules raw occurrence) :=
  ⟨.roll ⟨occurrence, rfl⟩ (fun position => Classical.choice (children position))⟩

/-- Every supplied root or active-position edge has generated rule evidence.
The only selection in this existence statement selects supplied child trees. -/
theorem active_complete {Γ : Ctx signature} {first last : Program Γ}
    (edge : ActiveEdge first last) : Generated ⟨Γ, Srt.tm, first, last⟩ := by
  induction edge with
  | root root =>
      cases root with
      | beta body argument =>
          have generated := generated_ruleClosed (betaOccurrence body argument)
            (by intro position; nomatch position)
          rw [beta_conclusion] at generated
          exact generated
      | fetch name value =>
          rw [← fetch_conclusion]
          exact generated_ruleClosed _ (by intro position; nomatch position)
  | application argument edge ih =>
      have generated := generated_ruleClosed (applicationOccurrence _ _ argument) (by
        intro position
        rw [application_child]
        exact ih)
      rw [application_conclusion] at generated
      exact generated
  | definition value edge ih =>
      have generated := generated_ruleClosed (definitionOccurrence value _ _) (by
        intro position
        rw [definition_child]
        exact ih)
      rw [definition_conclusion] at generated
      exact generated
  | carrier name value edge ih =>
      have generated := generated_ruleClosed (carrierOccurrence name value _ _) (by
        intro position
        rw [carrier_child]
        exact ih)
      rw [carrier_conclusion] at generated
      exact generated

theorem active_iff_tree {Γ : Ctx signature} (first last : Program Γ) :
    Nonempty (ActiveEdge first last) ↔ Generated ⟨Γ, Srt.tm, first, last⟩ := by
  constructor
  · rintro ⟨edge⟩
    exact active_complete edge
  · rintro ⟨tree⟩
    exact tree_sound _ tree

end Mettapedia.Languages.LambdaCalculus.NamePassing.AuthoredOperationalProfile
