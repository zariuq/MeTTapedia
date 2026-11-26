import Mettapedia.GSLT.Compilation.Uniform.StateRulesOnTheStep

/-!
# Binding selected queries to the state they read

The caller fixes a structural projection from the taken term. Selected
conditions receive that projection; neither the authored rewrite nor its
result changes. Relating the selected call at this view to the ordinary
relation gives exact readback of the whole firing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.ScopedQueriesOnTheStep

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic (Tm RowFunction inst head tail)
open RuleSyntax.ComputedConditions

inductive Side where
  | left | right

def expressionAt : List Side → Expr → Option Expr
  | [], e => some e
  | .left :: more, .app l _ => expressionAt more l
  | .right :: more, .app _ r => expressionAt more r
  | _, _ => none

def termAt : List Side → Tm → Option Tm
  | [], t => some t
  | .left :: more, .app .app parts => termAt more (parts head)
  | .right :: more, .app .app parts => termAt more (parts tail)
  | _, _ => none

theorem expression_at_inst (path : List Side) (assign : Nat → Expr) (term keep : Tm)
    (found : termAt path term = some keep) :
    expressionAt path (inst assign term) = some (inst assign keep) := by
  induction path generalizing term with
  | nil =>
    have same : term = keep := Option.some.inj found
    subst term
    rfl
  | cons side more ih =>
    cases term with
    | var => cases side <;> cases found
    | const => cases side <;> cases found
    | app symbol arguments =>
      cases symbol <;> cases side <;> first
      | exact ih _ found
      | cases found

def attach (usesScope : Nat → Bool) (scope : Tm) (condition : Condition Nat Tm) : Condition Nat Tm :=
  { condition with arguments :=
      (if usesScope condition.name then scope :: condition.arguments else condition.arguments) }

def rule (usesScope : Nat → Bool) (scope : Tm) (source : RuleWithCondition Nat Tm) : RuleWithCondition Nat Tm :=
  { source with conditions := source.conditions.map (attach usesScope scope) }

theorem still_restricted (usesScope : Nat → Bool) (scope : Tm) (source : RuleWithCondition Nat Tm)
    (restricted : source.RangeRestrictedWith) : (rule usesScope scope source).RangeRestrictedWith := by
  intro term written name used
  rcases restricted term written name used with direct | computed
  · exact Or.inl direct
  · obtain ⟨condition, present, supplied⟩ := computed
    exact Or.inr ⟨attach usesScope scope condition, List.mem_map_of_mem present, supplied⟩

private theorem attach_arguments (usesScope : Nat → Bool) (scope : Tm) (condition : Condition Nat Tm)
    (assign : Nat → Expr) :
    (attach usesScope scope condition).arguments.map (inst assign) =
      if usesScope condition.name then inst assign scope :: condition.arguments.map (inst assign)
        else condition.arguments.map (inst assign) := by
  by_cases reads : usesScope condition.name = true <;> simp [attach, reads]

/-- All selected conditions read the same structural view. This theorem
does not assume that the base relation is independent of that view. -/
theorem exact_step (usesScope : Nat → Bool) (scope : Tm) (source : RuleWithCondition Nat Tm)
    (lifted ordinary : Relations) (before after : Multiset Expr) (view : Expr)
    (matches_view : ∀ assign rest, (source.rule.body.take.map (inst assign) : Multiset Expr) + rest = before →
      inst assign scope = view)
    (relation : ∀ name inputs value, lifted name (if usesScope name then view :: inputs else inputs) value ↔
      ordinary name inputs value) :
    RelationStep lifted (rule usesScope scope source) before after ↔ RelationStep ordinary source before after := by
  constructor
  · rintro ⟨assign, rest, taken, reads, checks, holds, made⟩
    refine ⟨assign, rest, taken, reads, checks, ?_, made⟩
    intro condition present
    have scopedStep := holds (attach usesScope scope condition) (List.mem_map_of_mem present)
    change lifted condition.name ((attach usesScope scope condition).arguments.map (inst assign))
      (inst assign condition.value) at scopedStep
    rw [attach_arguments, matches_view assign rest taken] at scopedStep
    exact (relation ..).mp scopedStep
  · rintro ⟨assign, rest, taken, reads, checks, holds, made⟩
    refine ⟨assign, rest, taken, reads, checks, ?_, made⟩
    intro scopedCondition present
    obtain ⟨condition, known, rfl⟩ := List.mem_map.mp present
    change lifted condition.name ((attach usesScope scope condition).arguments.map (inst assign))
      (inst assign condition.value)
    rw [attach_arguments, matches_view assign rest taken]
    exact (relation ..).mpr (holds condition known)

end Mettapedia.GSLT.Compilation.Uniform.ScopedQueriesOnTheStep
