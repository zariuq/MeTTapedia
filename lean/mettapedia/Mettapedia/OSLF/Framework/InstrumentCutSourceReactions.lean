import Mettapedia.OSLF.Framework.InstrumentCutReactions
import Mettapedia.CategoryTheory.GroundPathContextCongruence

/-!
# Proper source reactions and the exact administrative probe boundary

Proper redexes and reacta are traversed source constructor trees. They may
include the selected original binary cut. An actual IPO argument, followed by
the retained constructor readout, excludes proper reactions from administrative
probe-labelled steps. Fresh names alone do not establish this result.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.CategoryTheory.GroundPath
open Mettapedia.GSLT.RedexRelativeCongruence

universe u w

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentCutSourceReactionsQuiver : Quiver (Srt Symbols arity) := frameQuiver (signature arity)

theorem embedSource_injective : Function.Injective (embedSource arity) := by
  intro first
  induction first with
  | node constructor arguments inductionHypothesis =>
    intro second same
    cases second with
    | node other otherArguments =>
      have heads := Term.head_eq (signature := signature arity) _ _ same
      have constructorEq : constructor = other := Constructor.original.inj heads
      subst other
      have argumentEq := Term.node.inj same
      apply congrArg (InstrumentObservations.Tree.node constructor)
      funext position
      exact inductionHypothesis position (congrFun argumentEq position)

inductive RootSymbol where
  | original (constructor : Symbols)
  | arguments (constructor : Symbols)
  | probe (instrument : Probe Symbols arity)
  | interaction

def rootSymbol (sourceCut : OriginalCut Symbols arity) : Constructor Symbols arity → RootSymbol arity := by
  classical
  intro supplied
  exact match supplied with
  | .original constructor => if constructor = sourceCut.symbol then .interaction else .original constructor
  | .arguments constructor => .arguments constructor
  | .probe instrument => .probe instrument
  | .cut _ => .interaction

theorem original_cut_symbol (sourceCut : OriginalCut Symbols arity) (first second : Value arity .base) :
    rootSymbol arity sourceCut (originalCut arity sourceCut first second).head = .interaction := by
  simp [originalCut, original, Term.head, rootSymbol]

theorem observer_cut_symbol (sourceCut : OriginalCut Symbols arity) (instrument : Probe Symbols arity)
    (suppliedProbe : Value arity (.probe instrument)) (body : Value arity (receiver arity instrument)) :
    rootSymbol arity sourceCut (cut arity instrument suppliedProbe body).head = .interaction := rfl

structure SourceRule where
  redex : InstrumentObservations.Tree Symbols arity
  reactum : InstrumentObservations.Tree Symbols arity

def SourceRule.reaction (rule : SourceRule arity) : ReactionRule (.origin : ContextObject (signature arity)) where
  codomain := .interface .base
  redex := termArrow (signature arity) (embedSource arity rule.redex)
  reactum := termArrow (signature arity) (embedSource arity rule.reactum)

def extendedRules (Origins : Type w) (proper : SourceRule arity → Prop)
    (rule : ReactionRule (.origin : ContextObject (signature arity))) : Prop :=
  administrativeRules arity Origins rule ∨ ∃ sourceRule, proper sourceRule ∧ rule = sourceRule.reaction

theorem extended_administrative_step_iff (Origins : Type w) (proper : SourceRule arity → Prop)
    (instrument : Probe Symbols arity) (source : Value arity (receiver arity instrument))
    (target : Value arity (result arity instrument)) :
    ActIPO (extendedRules arity Origins proper)
      (contextArrow (signature arity) (probeContext arity instrument))
      (termArrow (signature arity) source) (termArrow (signature arity) target) ↔
      ∃ occurrence : AdministrativeOccurrence arity Origins instrument,
        source = occurrence.instance_.body ∧ target = occurrence.instance_.output := by
  constructor
  · rintro ⟨rule, membership, reaction, square, ipo, targetEq⟩
    rcases membership with administrative | ⟨sourceRule, _, rfl⟩
    · exact (administrative_step_iff arity Origins instrument source target).mp
        ⟨rule, administrative, reaction, square, ipo, targetEq⟩
    · cases reaction with
      | context path =>
        have zero := probe_ipo_reaction_length arity instrument source
          (embedSource arity sourceRule.redex) (by intro impossible; cases impossible) path square ipo
        have values := Arrow.value.inj square
        have heads := (Term.head_eq (signature := signature arity) _ _ values).trans
          (zero_path_head arity path (embedSource arity sourceRule.redex) zero)
        cases sourceRead : sourceRule.redex with
        | node constructor arguments =>
          rw [sourceRead] at heads
          change Constructor.cut instrument = Constructor.original constructor at heads
          cases heads
  · intro exposed
    obtain ⟨rule, membership, reaction, square, ipo, targetEq⟩ :=
      (administrative_step_iff arity Origins instrument source target).mpr exposed
    exact ⟨rule, Or.inl membership, reaction, square, ipo, targetEq⟩

/-- Every actual context preserves the shared literal-label bisimilarity of
the chosen proper and administrative rules. RPO existence is discharged by
the context category, including origin-identity spans. -/
theorem extended_context_congruence (Origins : Type w) (proper : SourceRule arity → Prop)
    {first second : ContextObject (signature arity)}
    (left right : (.origin : ContextObject (signature arity)) ⟶ first)
    (related : IPOBisimilar (extendedRules arity Origins proper) left right) (context : first ⟶ second) :
    IPOBisimilar (extendedRules arity Origins proper) (left ≫ context) (right ≫ context) :=
  context_bisimulation_congruence (action (signature arity)) (extendedRules arity Origins proper)
    left right related context

end Mettapedia.OSLF.Framework.InstrumentCutContexts
