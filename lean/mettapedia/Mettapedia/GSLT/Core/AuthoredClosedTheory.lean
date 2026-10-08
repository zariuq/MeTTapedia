import Mettapedia.GSLT.Core.ProgramReductionTheory

/-!
# Authored local diagrams over closed program theories

Constructor meanings, rule meanings and selected positions are individual
local diagrams. Rule origins and position origins are independently indexed;
equal endpoints in the monic reduction relation do not identify origins.

A closed theory map transports each actual rule action. A selected position
is transported using the inverse canonical product comparison, so its
decomposition remains valid under changes of categorical choices. These
semantic diagrams are not a syntax or a free-extension universal property.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.AuthoredClosedTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open ProgramReductionTheory

universe u v a

structure Constructor (theory : Theory.{u,v}) where
  parameters : theory.closed.Obj
  value : parameters ⟶ theory.program

structure Rule (theory : Theory.{u,v}) where
  parameters : theory.closed.Obj
  left : parameters ⟶ theory.program
  right : parameters ⟶ theory.program
  action : parameters ⟶ theory.Event
  source : action ≫ theory.source = left
  target : action ≫ theory.target = right

namespace Rule

theorem action_unique {theory : Theory.{u,v}} (rule : Rule theory)
    (supplied : rule.parameters ⟶ theory.Event)
    (source : supplied ≫ theory.source = rule.left)
    (target : supplied ≫ theory.target = rule.right) : supplied = rule.action :=
  theory.endpoint_joint_cancel (source.trans rule.source.symm) (target.trans rule.target.symm)

def transport {first second : Theory.{u,v}} (mapping : Map first second)
    (rule : Rule first) : Rule second where
  parameters := mapping.closed.functor.obj rule.parameters
  left := mapping.closed.functor.map rule.left ≫ mapping.program.hom
  right := mapping.closed.functor.map rule.right ≫ mapping.program.hom
  action := mapping.closed.functor.map rule.action ≫ mapping.reduction
  source := by
    rw [Category.assoc, mapping.source, ← Category.assoc,
      ← _root_.CategoryTheory.Functor.map_comp, rule.source]
  target := by
    rw [Category.assoc, mapping.target, ← Category.assoc,
      ← _root_.CategoryTheory.Functor.map_comp, rule.target]

@[simp] theorem transport_action {first second : Theory.{u,v}}
    (mapping : Map first second) (rule : Rule first) :
    (transport mapping rule).action = mapping.closed.functor.map rule.action ≫ mapping.reduction := rfl

@[simp] theorem transport_left {first second : Theory.{u,v}}
    (mapping : Map first second) (rule : Rule first) :
    (transport mapping rule).left = mapping.closed.functor.map rule.left ≫ mapping.program.hom := rfl

@[simp] theorem transport_right {first second : Theory.{u,v}}
    (mapping : Map first second) (rule : Rule first) :
    (transport mapping rule).right = mapping.closed.functor.map rule.right ≫ mapping.program.hom := rfl

@[ext] theorem ext {theory : Theory.{u,v}} {first second : Rule theory}
    (parameters : first.parameters = second.parameters)
    (left : HEq first.left second.left) (right : HEq first.right second.right) : first = second := by
  cases first with
  | mk firstParameters firstLeft firstRight firstAction firstSource firstTarget =>
    cases second with
    | mk secondParameters secondLeft secondRight secondAction secondSource secondTarget =>
      cases parameters
      cases eq_of_heq left
      cases eq_of_heq right
      have same : firstAction = secondAction := theory.endpoint_joint_cancel
        (firstSource.trans secondSource.symm) (firstTarget.trans secondTarget.symm)
      cases same
      rfl

theorem transport_identity {theory : Theory.{u,v}} (rule : Rule theory) :
    transport (Map.identity theory) rule = rule := by
  apply ext (first := transport (Map.identity theory) rule) (second := rule) rfl
  · exact heq_of_eq (Category.comp_id rule.left)
  · exact heq_of_eq (Category.comp_id rule.right)

theorem transport_compose {first second third : Theory.{u,v}}
    (before : Map first second) (after : Map second third) (rule : Rule first) :
    transport after (transport before rule) = transport (Map.compose before after) rule := by
  apply ext (first := transport after (transport before rule))
    (second := transport (Map.compose before after) rule) rfl
  · exact heq_of_eq (by
      change after.closed.functor.map (before.closed.functor.map rule.left ≫
        before.program.hom) ≫ after.program.hom =
        after.closed.functor.map (before.closed.functor.map rule.left) ≫
          (after.closed.functor.map before.program.hom ≫ after.program.hom)
      rw [_root_.CategoryTheory.Functor.map_comp, Category.assoc])
  · exact heq_of_eq (by
      change after.closed.functor.map (before.closed.functor.map rule.right ≫
        before.program.hom) ≫ after.program.hom =
        after.closed.functor.map (before.closed.functor.map rule.right) ≫
          (after.closed.functor.map before.program.hom ≫ after.program.hom)
      rw [_root_.CategoryTheory.Functor.map_comp, Category.assoc])

end Rule

/-- A supplied decomposition; shared variables need not split as a product
of disjoint rely and focus-variable contexts. -/
structure Position {theory : Theory.{u,v}} (rule : Rule theory) where
  environment : theory.closed.Obj
  carrier : theory.closed.Obj
  relies : rule.parameters ⟶ environment
  focus : rule.parameters ⟶ carrier
  plug : environment ⨯ carrier ⟶ theory.program
  decomposition : prod.lift relies focus ≫ plug = rule.left

namespace Position

theorem pair_comparison_inverse {first second : Theory.{u,v}}
    (mapping : Map first second) {context environment carrier : first.closed.Obj}
    (relies : context ⟶ environment) (focus : context ⟶ carrier) :
    prod.lift (mapping.closed.functor.map relies) (mapping.closed.functor.map focus) ≫
      inv (prodComparison mapping.closed.functor environment carrier) =
        mapping.closed.functor.map (prod.lift relies focus) := by
  apply (cancel_mono (prodComparison mapping.closed.functor environment carrier)).mp
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply prod.hom_ext
  · simp only [prod.lift_fst, Category.assoc, prodComparison_fst,
      ← _root_.CategoryTheory.Functor.map_comp]
  · simp only [prod.lift_snd, Category.assoc, prodComparison_snd,
      ← _root_.CategoryTheory.Functor.map_comp]

def transport {first second : Theory.{u,v}} (mapping : Map first second)
    {rule : Rule first} (position : Position rule) : Position (Rule.transport mapping rule) where
  environment := mapping.closed.functor.obj position.environment
  carrier := mapping.closed.functor.obj position.carrier
  relies := mapping.closed.functor.map position.relies
  focus := mapping.closed.functor.map position.focus
  plug := inv (prodComparison mapping.closed.functor position.environment position.carrier) ≫
    mapping.closed.functor.map position.plug ≫ mapping.program.hom
  decomposition := by
    change prod.lift (mapping.closed.functor.map position.relies)
      (mapping.closed.functor.map position.focus) ≫
        (inv (prodComparison mapping.closed.functor position.environment position.carrier) ≫
          mapping.closed.functor.map position.plug ≫ mapping.program.hom) =
        mapping.closed.functor.map rule.left ≫ mapping.program.hom
    rw [← Category.assoc, ← Category.assoc, pair_comparison_inverse,
      ← _root_.CategoryTheory.Functor.map_comp, position.decomposition]

theorem transport_focus {first second : Theory.{u,v}} (mapping : Map first second)
    {rule : Rule first} (position : Position rule) :
    (transport mapping position).focus = mapping.closed.functor.map position.focus := rfl

theorem transport_plug {first second : Theory.{u,v}} (mapping : Map first second)
    {rule : Rule first} (position : Position rule) :
    (transport mapping position).plug =
      inv (prodComparison mapping.closed.functor position.environment position.carrier) ≫
        mapping.closed.functor.map position.plug ≫ mapping.program.hom := rfl

end Position

/-- Independently named local meanings; names remain separate from the
actual monic reduction readout. -/
structure Presentation (theory : Theory.{u,v}) where
  ConstructorOrigin : Type a
  constructor : ConstructorOrigin → Constructor theory
  RuleOrigin : Type a
  rule : RuleOrigin → Rule theory
  PositionOrigin : RuleOrigin → Type a
  position : (origin : RuleOrigin) → PositionOrigin origin → Position (rule origin)

set_option linter.checkUnivs false in
/-- The input keeps the semantic theory and the selected presentation
separate. Descent along presentation changes is an additional theorem. -/
structure GenerationInput where
  theory : Theory.{u,v}
  presentation : Presentation.{u,v,a} theory

def Presentation.transport {first second : Theory.{u,v}}
    (mapping : Map first second) (presentation : Presentation.{u,v,a} first) :
    Presentation.{u,v,a} second where
  ConstructorOrigin := presentation.ConstructorOrigin
  constructor origin :=
    ⟨mapping.closed.functor.obj (presentation.constructor origin).parameters,
      mapping.closed.functor.map (presentation.constructor origin).value ≫ mapping.program.hom⟩
  RuleOrigin := presentation.RuleOrigin
  rule origin := Rule.transport mapping (presentation.rule origin)
  PositionOrigin := presentation.PositionOrigin
  position origin name := Position.transport mapping (presentation.position origin name)

theorem transported_rule_origin {first second : Theory.{u,v}}
    (mapping : Map first second) (presentation : Presentation.{u,v,a} first) :
    (presentation.transport mapping).RuleOrigin = presentation.RuleOrigin := rfl

theorem transported_position_origin {first second : Theory.{u,v}}
    (mapping : Map first second) (presentation : Presentation.{u,v,a} first)
    (origin : presentation.RuleOrigin) :
    (presentation.transport mapping).PositionOrigin origin = presentation.PositionOrigin origin := rfl

end Mettapedia.GSLT.Core.AuthoredClosedTheory
