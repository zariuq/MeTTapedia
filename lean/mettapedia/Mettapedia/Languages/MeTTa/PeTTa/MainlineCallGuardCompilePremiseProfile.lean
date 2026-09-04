import Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT

/-!
# Source-bound premise profile for the PeTTa call-guard compiler

The cold compiler has fifteen authored transition occurrences.  Eight are
premise-free and seven carry one deterministic classification query.  This
module proves, from the literal source rules, that every such query argument
is an ordinary schema variable already bound by the rewrite source.  The
independent sorting derivation for that exact root then supplies its authored
carrier.

Consequently every selected star/box occurrence has an ordered typed premise
signature, while relation truth remains exclusively in the cold relation
environment.  The profile grants no query answer and performs no guard
decision.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseProfile

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileSourceIndexedNTT

/-- Every literal cold root uses only relation queries whose arguments occur
in that root's left-hand source.  This finite proof inspects the fifteen
authored rules, not generated typing rows. -/
theorem rootPremises_sourceBound
    (index : Fin coldSource.language.rewrites.length) :
    PremisesSourceBound (rootTyping index).site.rewrite := by
  apply
    (allPremisesSourceBoundCheck_eq_true_iff
      (rootTyping index).site.rewrite).mp
  fin_cases index <;>
    simp [allPremisesSourceBoundCheck, premiseSourceBoundCheck,
      argumentSourceBoundCheck, rootTyping, DisplayedRewriteSite.rewrite,
      DisplayedRewriteSite.root, coldSource, language, transitions,
      finishTransition, skipHeadTransition, skipArityTransition,
      beginDeclarationTransition, argumentsFinishedTransition,
      rawInputTransition, undefinedInputTransition, holeInputTransition,
      checkedInputTransition, openInputTransition,
      undefinedResultTransition, holeResultTransition, atomResultTransition,
      checkedResultTransition, openResultTransition,
      inputStepTransition, resultStepTransition, query, v,
      compileRunning, compileArguments, compileResult,
      declarationsCons, declarationPattern, termsCons,
      Pattern.freeFvarNames]

/-- Independent root sorting upgrades structural source-boundness into exact
ordered typed decoding for every authored premise. -/
theorem rootPremises_supported
    (index : Fin coldSource.language.rewrites.length) :
    allPremisesSupported (rootTyping index).site.rewrite = true :=
  allPremisesSupported_of_sourceBound (rootTyping index)
    (rootPremises_sourceBound index)

/-- Universe endpoint selection never changes the underlying premise
contract: all thirty selected star/box occurrences inherit the same exact
root-local support proof. -/
theorem selectedOccurrencePremises_supported (slot : Occurrence demand) :
    allPremisesSupported (typingAt demand slot).site.rewrite = true := by
  rw [typingAt_eq_rootTyping]
  exact rootPremises_supported _

/-- Exact premise-count profile.  In authored order the nonempty entries are
precisely skip-head, skip-arity, begin-declaration, checked/open input, and
checked/open result. -/
def premiseCounts : List Nat :=
  List.ofFn fun index : Fin coldSource.language.rewrites.length =>
    (rootTyping index).site.rewrite.premises.length

theorem premiseCounts_exact :
    premiseCounts = [0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1] := by
  simp [premiseCounts, rootTyping, DisplayedRewriteSite.rewrite,
    DisplayedRewriteSite.root, coldSource, language, transitions,
    finishTransition, skipHeadTransition, skipArityTransition,
    beginDeclarationTransition, argumentsFinishedTransition,
    rawInputTransition, undefinedInputTransition, holeInputTransition,
    checkedInputTransition, openInputTransition,
    undefinedResultTransition, holeResultTransition, atomResultTransition,
    checkedResultTransition, openResultTransition,
    inputStepTransition, resultStepTransition]

/-- There are exactly seven guarded transition occurrences; profile endpoint
duplication does not change this source fact. -/
theorem guardedRoot_count :
    (premiseCounts.filter fun count => count != 0).length = 7 := by
  rw [premiseCounts_exact]
  decide

/-! ## Exact authored query-wire inventory -/

/-- Diagnostic projection of the literal first-order query wire.  It carries
no relation result. -/
def relationWire? : Premise → Option (String × List String)
  | .relationQuery relation arguments => do
      let names ← arguments.mapM fun
        | .fvar name => some name
        | _ => none
      pure (relation, names)
  | _ => none

/-- One exact ordered query-wire row per authored root. -/
def rootRelationWires :
    List (Option (List (String × List String))) :=
  List.ofFn fun index : Fin coldSource.language.rewrites.length =>
    (rootTyping index).site.rewrite.premises.mapM relationWire?

/-- The seven query wires are precisely the cold compiler's structural and
type-classification questions, in authored transition and argument order. -/
theorem rootRelationWires_exact :
    rootRelationWires =
      [ some []
      , some [(notEqualRelation, ["declarationHead", "head"])]
      , some [(arityDiffersRelation, ["inputs", "arity"])]
      , some [(arityMatchesRelation, ["inputs", "arity"])]
      , some []
      , some []
      , some []
      , some []
      , some [(checkedInputRelation, ["expected"])]
      , some [(openInputRelation, ["expected"])]
      , some []
      , some []
      , some []
      , some [(checkedResultRelation, ["output"])]
      , some [(openResultRelation, ["output"])] ] := by
  simp [rootRelationWires, relationWire?, rootTyping,
    DisplayedRewriteSite.rewrite, DisplayedRewriteSite.root, coldSource,
    language, transitions, finishTransition, skipHeadTransition,
    skipArityTransition, beginDeclarationTransition,
    argumentsFinishedTransition, rawInputTransition,
    undefinedInputTransition, holeInputTransition,
    checkedInputTransition, openInputTransition,
    undefinedResultTransition, holeResultTransition, atomResultTransition,
    checkedResultTransition, openResultTransition,
    inputStepTransition, resultStepTransition, query, v]

#print axioms rootPremises_sourceBound
#print axioms rootPremises_supported
#print axioms selectedOccurrencePremises_supported
#print axioms premiseCounts_exact
#print axioms guardedRoot_count
#print axioms rootRelationWires_exact

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseProfile
