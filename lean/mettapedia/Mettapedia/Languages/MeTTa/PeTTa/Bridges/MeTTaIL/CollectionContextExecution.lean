import Mettapedia.Languages.MeTTa.PeTTa.EquationEquality
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionSelectionExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobExecution
import Mettapedia.OSLF.MeTTaIL.CollectionContextVariants

/-!
# Native collection contexts over the shared scoped runtime

The source constructs residual variants of an already licensed typed site.
The original site is retained beside every variant; the existing wire carries
its dependent focus, binder context and grammar-declaration frames.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContextExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts GeneralTypedSites CollectionSelection
open InferenceCettaWire (encodePattern encodeCollectionType encodeRest)
open InferenceCettaWire.ContextObservation (contextTerm)
open ScopedRuleJobReadoutExecution (siteTerm)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_contexts.metta"
    sha256 "81fee57af76a29ea16a1419c43fbb063be3ec88a6fc58e90eedfe03ab860ac93"

def library : BridgeKit.Library :=
  RetainedMatchingWire.interpretedLibrary

set_option maxRecDepth 100000 in
theorem checked : library.check = true := RetainedMatchingWire.interpreted_checked

section ProofMetadata

private local instance contextEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

/-- Direct outward calls derived from the actual context-operation bodies. -/
def contextProofInheritedHeads : List String :=
  ["gslt:automata:append", "gslt:rule:scope-match-erase-at", "gslt:rule:scope-fill", "gslt:automata:length"]

theorem contextProofInheritedHeads_derived :
    ((source.program.equations.flatMap (fun row => CompleteExecution.sourceLiteralHeads row.body)).filter
      (fun head => head.startsWith "gslt:" && !(source.program.equations.map (·.head)).contains head)).eraseDups =
        contextProofInheritedHeads := by decide +kernel

private def contextMetadataBase : SpaceSemantics.Program where
  equations := [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[118]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[120]'(by decide +kernel)]
  declarations := [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[118]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[120]'(by decide +kernel)]

/-- Bounded source metadata for context operations and their actual fill body. -/
def contextProofLibrary : Library :=
  ⟨{equations := [], declarations := []}, contextMetadataBase.append source.program,
    ["gslt:collection-context:"] ++ contextProofInheritedHeads⟩

def contextProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || head.startsWith "gslt:collection-context:" || contextProofInheritedHeads.contains head

theorem contextProof_checked : contextProofLibrary.check = true := by decide +kernel

theorem contextProof_agreement :
    ProgramAgreementOn contextProofHeads contextProofLibrary.runtime library.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

#print axioms contextProofInheritedHeads_derived
#print axioms contextProof_checked
#print axioms contextProof_agreement

end ProofMetadata

def variantTerm (variant : SiteVariant) : Term :=
  .application "CollectionSiteVariant" [siteTerm variant.original, siteTerm variant.site]

private def wrapInner (frame inner : OneHoleContext) : OneHoleContext :=
  match frame with
  | .hole => inner
  | .apply label before _ after => .apply label before inner after
  | .lambda display _ => .lambda display inner
  | .multiLambda arity displays _ => .multiLambda arity displays inner
  | .substBody _ replacement => .substBody inner replacement
  | .substReplacement body _ => .substReplacement body inner
  | .collection kind before _ after rest => .collection kind before inner after rest

syntax "contexts_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| contexts_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in contextProof_checked using contextProof_agreement; metta_eval [$facts,*] with contextProof_checked in contextProof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        variantTerm, siteTerm, contextTerm, encodeList, encodeOption,
        InferenceCettaWire.encodePatterns_eq_encodeList, $extra,*]))

@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (state : State)
    (left right : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right))) := by
  exact CollectionSelectionExecution.scoped_append_returns element state left right

@[metta_head "gslt:automata:length"]
theorem length_returns {α : Type} (element : α → Term) (state : State) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:length" [encoded (encodeList element items)]) state (number items.length) := by
  exact CollectionSelectionExecution.scoped_length_returns element state items

@[metta_head "gslt:rule:scope-match-erase-at"]
theorem erase_returns {α : Type} (element : α → Term) (state : State) (items : List α) (index : Nat) :
    PureReturns library.runtime [] state
      (apply "gslt:rule:scope-match-erase-at" [number index, encoded (encodeList element items)])
      state (encoded (encodeList element (items.eraseIdx index))) := by
  exact CollectionSelectionExecution.scoped_erase_returns element state items index

@[metta_head "gslt:rule:scope-fill"]
theorem fill_returns (state : State) (context : OneHoleContext) (pattern : Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:rule:scope-fill" [encoded (contextTerm context), encoded (encodePattern pattern)])
      state (encoded (encodePattern (context.fill pattern))) := by
  induction context with
  | hole => contexts_eval unfolding [OneHoleContext.fill]
  | apply label before inner after ih =>
    contexts_eval [ih, append_returns encodePattern state before (inner.fill pattern :: after)]
      unfolding [OneHoleContext.fill, encodePattern]
  | lambda display inner ih | multiLambda arity display inner ih =>
    contexts_eval [ih] unfolding [OneHoleContext.fill, encodePattern]
  | substBody inner replacement ih | substReplacement body inner ih =>
    contexts_eval [ih] unfolding [OneHoleContext.fill, encodePattern]
  | collection kind before inner after rest ih =>
    contexts_eval [ih, append_returns encodePattern state before (inner.fill pattern :: after)]
      unfolding [OneHoleContext.fill, encodePattern]

@[metta_head "gslt:collection-context:wrap"]
private theorem wrap_returns (state : State) (frame inner : OneHoleContext) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-context:wrap" [encoded (contextTerm frame), encoded (contextTerm inner)])
      state (encoded (contextTerm (wrapInner frame inner))) := by
  cases frame <;> contexts_eval unfolding [wrapInner]

@[metta_head "gslt:collection-context:map-frame"]
private theorem map_frame_returns (state : State) (frame : OneHoleContext) :
    ∀ contexts : List OneHoleContext,
    PureReturns library.runtime [] state
      (apply "gslt:collection-context:map-frame"
        [encoded (contextTerm frame), encoded (encodeList contextTerm contexts)])
      state (encoded (encodeList contextTerm (contexts.map (wrapInner frame))))
  | [] => by contexts_eval
  | inner :: tail => by
    contexts_eval [wrap_returns state frame inner, map_frame_returns state frame tail]
      unfolding [List.map_cons]

@[metta_head "gslt:collection-context:row"]
theorem row_returns (state : State) (kind : CollType) (rest : Option String) (inner : OneHoleContext) :
    ∀ residuals : List (List Pattern),
    PureReturns library.runtime [] state
      (apply "gslt:collection-context:row" [encoded (encodeCollectionType kind), encoded (encodeRest rest),
        encoded (contextTerm inner), encoded (encodeList (encodeList encodePattern) residuals)])
      state (encoded (encodeList contextTerm
        (residuals.map (fun residual => .collection kind [] inner residual rest))))
  | [] => by contexts_eval
  | first :: tail => by
    contexts_eval [row_returns state kind rest inner tail] unfolding [List.map_cons]

@[metta_head "gslt:collection-context:cross"]
theorem cross_returns (state : State) (kind : CollType) (rest : Option String)
    (residuals : List (List Pattern)) : ∀ contexts : List OneHoleContext,
    PureReturns library.runtime [] state
      (apply "gslt:collection-context:cross" [encoded (encodeCollectionType kind), encoded (encodeRest rest),
        encoded (encodeList contextTerm contexts), encoded (encodeList (encodeList encodePattern) residuals)])
      state (encoded (encodeList contextTerm
        (contexts.flatMap fun inner => residuals.map (fun residual => .collection kind [] inner residual rest))))
  | [] => by contexts_eval
  | inner :: tail => by
    contexts_eval [row_returns state kind rest inner residuals,
      cross_returns state kind rest residuals tail,
      append_returns contextTerm state
        (residuals.map (fun residual => .collection kind [] inner residual rest))
        (tail.flatMap fun child => residuals.map (fun residual => .collection kind [] child residual rest))]
      unfolding [List.flatMap_cons]

@[metta_head "gslt:collection-context:residuals"]
theorem residuals_returns (state : State) (kind : CollType) (items : List Pattern) (index : Nat) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-context:residuals"
        [encoded (encodeCollectionType kind), encoded (encodeList encodePattern items), number index])
      state (encoded (encodeList (encodeList encodePattern) (kindResiduals kind items index))) := by
  cases kind <;> contexts_eval [erase_returns encodePattern state items index]
    unfolding [kindResiduals, residuals, encodeCollectionType]

/-- The native operation computes exactly the source-level context variants,
including retained original copies at every nested set frame. -/
@[metta_head "gslt:collection-context:variants"]
theorem variants_returns (state : State) (focus : Pattern) : ∀ context : OneHoleContext,
    PureReturns library.runtime [] state
      (apply "gslt:collection-context:variants" [encoded (encodePattern focus), encoded (contextTerm context)])
      state (encoded (encodeList contextTerm (contextVariants focus context)))
  | .hole => by contexts_eval unfolding [contextVariants]
  | .apply label before inner after => by
    have mapped := map_frame_returns state (.apply label before inner after) (contextVariants focus inner)
    rw [contextVariants]
    contexts_eval [variants_returns state focus inner, mapped]
  | .lambda display inner => by
    have mapped := map_frame_returns state (.lambda display inner) (contextVariants focus inner)
    rw [contextVariants]
    contexts_eval [variants_returns state focus inner, mapped]
  | .multiLambda arity displays inner => by
    have mapped := map_frame_returns state (.multiLambda arity displays inner) (contextVariants focus inner)
    rw [contextVariants]
    contexts_eval [variants_returns state focus inner, mapped]
  | .substBody inner replacement => by
    have mapped := map_frame_returns state (.substBody inner replacement) (contextVariants focus inner)
    rw [contextVariants]
    contexts_eval [variants_returns state focus inner, mapped]
  | .substReplacement body inner => by
    have mapped := map_frame_returns state (.substReplacement body inner) (contextVariants focus inner)
    rw [contextVariants]
    contexts_eval [variants_returns state focus inner, mapped]
  | .collection kind before inner after rest => by
    cases kind with
    | vec =>
      have mapped := map_frame_returns state (.collection .vec before inner after rest) (contextVariants focus inner)
      rw [contextVariants]
      rw [List.map_eq_flatMap] at mapped
      contexts_eval [variants_returns state focus inner, mapped] unfolding [encodeCollectionType]
    | hashBag =>
      rw [contextVariants]
      contexts_eval [variants_returns state focus inner, fill_returns state inner focus,
        append_returns encodePattern state before (inner.fill focus :: after),
        length_returns encodePattern state before,
        residuals_returns state .hashBag (before ++ inner.fill focus :: after) before.length,
        cross_returns state .hashBag rest
          (kindResiduals .hashBag (before ++ inner.fill focus :: after) before.length)
          (contextVariants focus inner)] unfolding [encodeCollectionType]
    | hashSet =>
      rw [contextVariants]
      contexts_eval [variants_returns state focus inner, fill_returns state inner focus,
        append_returns encodePattern state before (inner.fill focus :: after),
        length_returns encodePattern state before,
        residuals_returns state .hashSet (before ++ inner.fill focus :: after) before.length,
        cross_returns state .hashSet rest
          (kindResiduals .hashSet (before ++ inner.fill focus :: after) before.length)
          (contextVariants focus inner)] unfolding [encodeCollectionType]

@[metta_head "gslt:collection-context:address"]
theorem address_returns (state : State) : ∀ context : OneHoleContext,
    PureReturns library.runtime [] state
      (apply "gslt:collection-context:address" [encoded (contextTerm context)])
      state (encoded (encodeList Term.natural (contextAddress context)))
  | .hole => by contexts_eval unfolding [contextAddress]
  | .apply label before inner after => by
    contexts_eval [address_returns state inner, length_returns encodePattern state before]
      unfolding [contextAddress]
  | .lambda display inner => by
    contexts_eval [address_returns state inner] unfolding [contextAddress]
  | .multiLambda arity displays inner => by
    contexts_eval [address_returns state inner] unfolding [contextAddress]
  | .substBody inner replacement => by
    contexts_eval [address_returns state inner] unfolding [contextAddress]
  | .substReplacement body inner => by
    contexts_eval [address_returns state inner] unfolding [contextAddress]
  | .collection kind before inner after rest => by
    contexts_eval [address_returns state inner, length_returns encodePattern state before]
      unfolding [contextAddress]

@[metta_head "gslt:collection-context:sites"]
theorem sites_returns (state : State) (site : SiteData) : ∀ contexts : List OneHoleContext,
    PureReturns library.runtime [] state
      (apply "gslt:collection-context:sites" [encoded (siteTerm site), encoded (encodeList contextTerm contexts)])
      state (encoded (encodeList variantTerm (contexts.map (fun context => ⟨site, recontext site context⟩))))
  | [] => by contexts_eval
  | context :: tail => by
    contexts_eval [address_returns state context, sites_returns state site tail]
      unfolding [List.map_cons, recontext]

/-- Both the original occurrence and the reconstructed typed site survive
native execution in the same list order and multiplicity as the Lean function. -/
@[metta_head "gslt:collection-context:site-variants"]
theorem site_variants_returns (state : State) (site : SiteData) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-context:site-variants" [encoded (siteTerm site)])
      state (encoded (encodeList variantTerm (siteVariants site))) := by
  contexts_eval [variants_returns state site.focus site.context,
    sites_returns state site (contextVariants site.focus site.context)] unfolding [siteVariants]

#print axioms append_returns
#print axioms length_returns
#print axioms erase_returns
#print axioms fill_returns
#print axioms wrap_returns
#print axioms map_frame_returns
#print axioms row_returns
#print axioms cross_returns
#print axioms residuals_returns
#print axioms variants_returns
#print axioms address_returns
#print axioms sites_returns
#print axioms site_variants_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContextExecution
