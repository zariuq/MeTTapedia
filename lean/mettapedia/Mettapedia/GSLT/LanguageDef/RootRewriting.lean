import Mettapedia.GSLT.LanguageDef.DecidableRelations.Stores
import Mettapedia.GSLT.Contracts.ScopedAliasDispatch
import Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction

/-!
# Dispatch in the theory at one cut

The equations of a cut already have a meaning: the generated
`EquationEquiv`. Acyclicity licenses one *implementation of keys*,
not the meaning of a rewrite at that cut. This file uses the existing
authored step and distinguishes an ordered list of eligible rule
occurrences from the relation on their results.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RootRewriting

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
open DecidableRelations (FirstOrder)
open EquationSemantics
open Mettapedia.GSLT.Contracts.ScopedAliasDispatch (moduloRead index lookup lookup_index)

private theorem literalArgs (ps : List Pattern)
    (one : ∀ p ∈ ps, ∀ t : Pattern, matchPattern p t = if p = t then [[]] else []) (ts : List Pattern) :
    matchArgs ps ts = if ps = ts then [[]] else [] := by
  induction ps generalizing ts with
  | nil => cases ts <;> simp [matchArgs]
  | cons p ps ih =>
    cases ts with
    | nil => simp [matchArgs]
    | cons t ts =>
      rw [matchArgs, one p List.mem_cons_self, ih (fun x hx => one x (List.mem_cons_of_mem _ hx))]
      by_cases hp : p = t <;> by_cases ht : ps = ts <;> simp [hp, ht, mergeBindings]

private theorem free_args (xs : List Pattern) (free : ∀ x ∈ xs, binderFree x = true) :
    binderFreeList xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [binderFreeList, free x List.mem_cons_self, ih (fun y hy => free y (List.mem_cons_of_mem _ hy))]

theorem ground_match {p : Pattern} (closed : FirstOrder p) :
    binderFree p = true ∧ (∀ bs, applyBindings bs p = p) ∧
      ∀ t : Pattern, matchPattern p t = if p = t then [[]] else [] := by
  induction closed with
  | @apply h xs _ ih =>
    refine ⟨free_args xs (fun x hx => (ih x hx).1), ?_, ?_⟩
    · intro bs
      rw [applyBindings]
      exact congrArg (Pattern.apply h) ((List.map_congr_left (g := id)
        (fun x hx => (ih x hx).2.1 bs)).trans (List.map_id _))
    · intro t
      cases t with
      | apply k ys =>
        rw [matchPattern, literalArgs xs (fun x hx => (ih x hx).2.2) ys]
        by_cases head : h = k <;> by_cases args : xs = ys <;>
          simp [head, args]
      | _ => simp [matchPattern]

/-- Evaluate at a ready root, not under arbitrary dialect contexts. For
unconditional depth-aligned rules the source step uses the actual matcher
on a representative. It is not sound to use a rigid root of the displayed
representative as a rejection test in arbitrary compound theories. -/
theorem root_instantiation_iff (base : BasePremiseEvaluator) (l : LanguageDef)
    (ready : isUnconditionalAligned l = true) (q y : Pattern) :
    StepModuloEquations base l q y ↔
      ∃ rule ∈ l.rewrites, ∃ representative σ,
        EquationEquiv base l q representative ∧
        σ ∈ matchPattern rule.left representative ∧
        EquationEquiv base l (applyBindings σ rule.right) y := by
  constructor
  · rintro ⟨representative, result, before, firing, after⟩
    obtain ⟨rule, member, out⟩ := List.mem_flatMap.mp
      ((step_iff_mem_rootReducts base l ready _ _).mp firing)
    obtain ⟨σ, matched, rfl⟩ := List.mem_map.mp out
    exact ⟨rule, member, representative, σ, before, matched, after⟩
  · rintro ⟨rule, member, representative, σ, before, matched, after⟩
    refine ⟨representative, applyBindings σ rule.right, before, ?_, after⟩
    exact (step_iff_mem_rootReducts base l ready _ _).mpr
      (List.mem_flatMap.mpr ⟨rule, member, List.mem_map.mpr ⟨σ, matched, rfl⟩⟩)

/-- Literal root dispatch replaces the search for representatives by one
class-membership test per rule. There is no equation-normalizer hypothesis. -/
def LiteralRoots (l : LanguageDef) : Prop :=
  ∀ rule ∈ l.rewrites, rule.premises = [] ∧ FirstOrder rule.left ∧ FirstOrder rule.right

theorem LiteralRoots.unconditional {l : LanguageDef} (literal : LiteralRoots l) :
    isUnconditionalAligned l = true := by
  apply List.all_eq_true.mpr
  intro r hr
  obtain ⟨unconditional, left, right⟩ := literal r hr
  simp [unconditional, ruleDepthAligned_of_binderFree r
    (ground_match left).1 (ground_match right).1]

theorem literal_root_iff (base : BasePremiseEvaluator) (l : LanguageDef)
    (literal : LiteralRoots l) (q y : Pattern) :
    StepModuloEquations base l q y ↔
      ∃ rule ∈ moduloRead base l RewriteRule.left q l.rewrites,
        EquationEquiv base l rule.right y := by
  classical
  rw [root_instantiation_iff base l literal.unconditional q y]
  constructor
  · rintro ⟨rule, member, representative, σ, before, matched, after⟩
    obtain ⟨_, left, right⟩ := literal rule member
    rw [(ground_match left).2.2] at matched
    split at matched
    next same =>
      subst representative
      refine ⟨rule, ?_, ?_⟩
      · exact List.mem_filter.mpr ⟨member,
          decide_eq_true ((equationSetoid base l).iseqv.symm before)⟩
      · simpa only [(ground_match right).2.1] using after
    next => cases matched
  · rintro ⟨rule, picked, after⟩
    obtain ⟨member, matchClass⟩ := List.mem_filter.mp picked
    obtain ⟨_, left, right⟩ := literal rule member
    refine ⟨rule, member, rule.left, [], ?_, ?_, ?_⟩
    · exact (equationSetoid base l).iseqv.symm
        (of_decide_eq_true (p := EquationEquiv base l rule.left q) matchClass)
    · simp [(ground_match left).2.2]
    · simpa only [(ground_match right).2.1] using after

/-- An index needs class correctness only for its actual comparisons.
Its keys need not choose normal forms, or even be keys for every term.
This preserves the ordered rule occurrences, not just the successor set. -/
theorem keys_exact {K : Type*} [DecidableEq K] (base : BasePremiseEvaluator)
    (l : LanguageDef) (q : Pattern) (key : Pattern → K)
    (law : ∀ r ∈ l.rewrites, key r.left = key q ↔ EquationEquiv base l r.left q) :
    lookup (key q) (index id (key ∘ RewriteRule.left) l.rewrites) =
      moduloRead base l RewriteRule.left q l.rewrites := by
  simp only [lookup_index, id_eq, Function.comp_apply]
  unfold moduloRead
  apply List.filter_congr
  intro r hr
  simpa only [decide_eq_decide] using law r hr

theorem indexed_step_iff {K : Type*} [DecidableEq K] (base : BasePremiseEvaluator)
    (l : LanguageDef) (literal : LiteralRoots l) (q y : Pattern) (key : Pattern → K)
    (law : ∀ r ∈ l.rewrites, key r.left = key q ↔ EquationEquiv base l r.left q) :
    StepModuloEquations base l q y ↔
      ∃ r ∈ lookup (key q) (index id (key ∘ RewriteRule.left) l.rewrites),
        EquationEquiv base l r.right y := by
  rw [keys_exact base l q key law, literal_root_iff base l literal]

/-- If the occurrence stream itself has not moved, reusing an ordered
dispatch frontier across theory edits is exact iff every candidate's
admission bit agrees. It is unnecessary to preserve unrelated equation
classes or the spelling of their representatives. This concerns selection;
result equality and evaluation after entry are separate observations. -/
theorem admission_bits_iff (base : BasePremiseEvaluator) (old new : LanguageDef)
    (q : Pattern) (rs : List RewriteRule) :
    moduloRead base old RewriteRule.left q rs = moduloRead base new RewriteRule.left q rs ↔
      ∀ r ∈ rs, EquationEquiv base old r.left q ↔ EquationEquiv base new r.left q := by
  constructor
  · intro same r member
    have preserves := congrArg (fun out => r ∈ out) same
    simpa only [moduloRead, List.mem_filter, member, true_and, decide_eq_true_eq] using
      Iff.of_eq preserves
  · intro same
    apply List.filter_congr
    intro r member
    simpa only [decide_eq_decide] using same r member

end Mettapedia.GSLT.LanguageDef.RootRewriting
