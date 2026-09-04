import Mettapedia.OSLF.Framework.DisplayedRewriteVariableProfile

/-!
# Source-bound relation premises for selected native types

An authored relation premise may be internalized as a typed local obligation
only when every argument is an ordinary schema variable already supplied by
the rewrite source and typed by that rewrite's exact authored type context.
This module recognizes precisely that fragment.

The decoder is deliberately fail-closed.  It does not flatten binders,
congruence, freshness, or quantified premises into relation queries, and it
does not deduplicate repeated arguments.  Successful decoding therefore
retains the authored relation name, argument order, multiplicity, and exact
first-match source types without granting any evidence that the relation is
true.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- First-match source type, available only for an ordinary schema variable
already supplied by the rewrite source. -/
def argumentType? (rewrite : RewriteRule) : Pattern → Option TypeExpr
  | .fvar name =>
      if name ∈ rewrite.left.freeFvarNames then
        FreeTypeContext.ofList rewrite.typeContext name
      else
        none
  | _ => none

/-- Successful argument typing is exactly source occurrence plus authored
first-match type lookup. -/
theorem argumentType?_eq_some_iff (rewrite : RewriteRule)
    (pattern : Pattern) (type : TypeExpr) :
    argumentType? rewrite pattern = some type ↔
      ∃ name,
        pattern = .fvar name ∧
        name ∈ rewrite.left.freeFvarNames ∧
        FreeTypeContext.ofList rewrite.typeContext name = some type := by
  cases pattern <;> simp [argumentType?]

/-- A relation premise together with its exact ordered argument wire and the
ordered carriers recovered from the authored source schema. -/
structure View (rewrite : RewriteRule) where
  relation : String
  arguments : List Pattern
  argumentTypes : List TypeExpr
deriving DecidableEq

namespace View

/-- Reconstruct the exact authored premise without changing argument order or
multiplicity. -/
def encode {rewrite : RewriteRule} (view : View rewrite) : Premise :=
  .relationQuery view.relation view.arguments

/-- Compact diagnostic projection which forgets the typing proof but not
order or multiplicity. -/
def signature {rewrite : RewriteRule} (view : View rewrite) :
    String × List TypeExpr :=
  (view.relation, view.argumentTypes)

/-- Independent admission predicate for a decoded view.  It says exactly that
the ordered carrier row came from the authored source schema; it says nothing
about whether the named relation holds. -/
def WellTyped {rewrite : RewriteRule} (view : View rewrite) : Prop :=
  view.arguments.mapM (argumentType? rewrite) = some view.argumentTypes

end View

/-- Decode exactly the supported source-bound relation-query fragment. -/
def decode? (rewrite : RewriteRule) : Premise → Option (View rewrite)
  | .relationQuery relation arguments =>
      match arguments.mapM (argumentType? rewrite) with
      | none => none
      | some argumentTypes => some
          { relation := relation
            arguments := arguments
            argumentTypes := argumentTypes }
  | _ => none

theorem decode?_encode {rewrite : RewriteRule}
    (view : View rewrite) (typed : view.WellTyped) :
    decode? rewrite view.encode = some view := by
  unfold View.WellTyped at typed
  simp only [View.encode, decode?]
  rw [typed]

/-- Every successfully decoded view carries the independent source-typing
admission predicate. -/
theorem wellTyped_of_decode?_eq_some {rewrite : RewriteRule}
    {premise : Premise} {view : View rewrite}
    (decoded : decode? rewrite premise = some view) :
    view.WellTyped := by
  cases premise with
  | freshness condition => simp [decode?] at decoded
  | congruence left right => simp [decode?] at decoded
  | forAll collection parameter body => simp [decode?] at decoded
  | relationQuery relation arguments =>
      cases typed : arguments.mapM (argumentType? rewrite) with
      | none => simp [decode?, typed] at decoded
      | some argumentTypes =>
          simp only [decode?, typed, Option.some.injEq] at decoded
          cases decoded
          exact typed

/-- Successful premise decoding reconstructs the complete original premise.
No unsupported premise can be silently approximated by a relation query. -/
theorem encode_of_decode?_eq_some {rewrite : RewriteRule}
    {premise : Premise} {view : View rewrite}
    (decoded : decode? rewrite premise = some view) :
    view.encode = premise := by
  cases premise with
  | freshness condition => simp [decode?] at decoded
  | congruence left right => simp [decode?] at decoded
  | forAll collection parameter body => simp [decode?] at decoded
  | relationQuery relation arguments =>
      cases typed : arguments.mapM (argumentType? rewrite) with
      | none => simp [decode?, typed] at decoded
      | some argumentTypes =>
          simp only [decode?, typed, Option.some.injEq] at decoded
          cases decoded
          rfl

/-- Proof-erased diagnostic decoder.  It is derived from the exact typed view
rather than reimplementing its acceptance test. -/
def signature? (rewrite : RewriteRule) (premise : Premise) :
    Option (String × List TypeExpr) :=
  (decode? rewrite premise).map View.signature

/-- Decode every authored premise in order, rejecting the whole list if any
premise lies outside the supported fragment. -/
def signatures? (rewrite : RewriteRule) :
    Option (List (String × List TypeExpr)) :=
  rewrite.premises.mapM (signature? rewrite)

/-- Boolean boundary used by finite source-language profile checks. -/
def allPremisesSupported (rewrite : RewriteRule) : Bool :=
  (signatures? rewrite).isSome

/-! ## Source-derived support and typed decoding -/

/-- Structural fragment recognized before looking up an authored carrier. -/
def ArgumentSourceBound (rewrite : RewriteRule) (argument : Pattern) : Prop :=
  ∃ name,
    argument = .fvar name ∧ name ∈ rewrite.left.freeFvarNames

/-- Every argument of one relation query is already supplied by matching the
authored rewrite source. -/
def PremiseSourceBound (rewrite : RewriteRule) (premise : Premise) : Prop :=
  ∃ relation arguments,
    premise = .relationQuery relation arguments ∧
      ∀ argument ∈ arguments, ArgumentSourceBound rewrite argument

/-- Entire ordered authored premise row lies in the source-bound relation
fragment. -/
def PremisesSourceBound (rewrite : RewriteRule) : Prop :=
  ∀ premise ∈ rewrite.premises, PremiseSourceBound rewrite premise

/-- Executable structural check used only to reconstruct finite source
admission evidence. -/
def argumentSourceBoundCheck (rewrite : RewriteRule) : Pattern → Bool
  | .fvar name => decide (name ∈ rewrite.left.freeFvarNames)
  | _ => false

/-- Executable check for one source-bound relation premise. -/
def premiseSourceBoundCheck (rewrite : RewriteRule) : Premise → Bool
  | .relationQuery _ arguments =>
      arguments.all (argumentSourceBoundCheck rewrite)
  | _ => false

/-- Executable check for the complete authored premise row. -/
def allPremisesSourceBoundCheck (rewrite : RewriteRule) : Bool :=
  rewrite.premises.all (premiseSourceBoundCheck rewrite)

@[simp] theorem argumentSourceBoundCheck_eq_true_iff
    (rewrite : RewriteRule) (argument : Pattern) :
    argumentSourceBoundCheck rewrite argument = true ↔
      ArgumentSourceBound rewrite argument := by
  cases argument <;>
    simp [argumentSourceBoundCheck, ArgumentSourceBound]

@[simp] theorem premiseSourceBoundCheck_eq_true_iff
    (rewrite : RewriteRule) (premise : Premise) :
    premiseSourceBoundCheck rewrite premise = true ↔
      PremiseSourceBound rewrite premise := by
  cases premise <;>
    simp [premiseSourceBoundCheck, PremiseSourceBound,
      List.all_eq_true]

theorem allPremisesSourceBoundCheck_eq_true_iff
    (rewrite : RewriteRule) :
    allPremisesSourceBoundCheck rewrite = true ↔
      PremisesSourceBound rewrite := by
  simp [allPremisesSourceBoundCheck, PremisesSourceBound,
    List.all_eq_true]

/-- A source-bound argument receives a carrier from the independently supplied
sorting derivation for the exact authored rewrite. -/
theorem argumentType?_exists_of_sourceBound
    {source : ValidatedLanguageDef}
    (typing : Mettapedia.OSLF.Framework.DisplayedRewriteTyping source)
    {argument : Pattern}
    (sourceBound : ArgumentSourceBound typing.site.rewrite argument) :
    ∃ type, argumentType? typing.site.rewrite argument = some type := by
  rcases sourceBound with ⟨name, rfl, membership⟩
  obtain ⟨type, typed⟩ :=
    Mettapedia.OSLF.Framework.DisplayedRewriteVariableProfile.variableType?_exists
      typing membership
  refine ⟨type, ?_⟩
  simpa [argumentType?, membership,
    Mettapedia.OSLF.Framework.DisplayedRewriteVariableProfile.variableType?]
    using typed

private theorem mapM_exists_of_forall_exists
    {alpha beta : Type} (items : List alpha) (function : alpha → Option beta)
    (total : ∀ item ∈ items, ∃ result, function item = some result) :
    ∃ results, items.mapM function = some results := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons item items inductionHypothesis =>
      obtain ⟨head, headEq⟩ := total item (by simp)
      obtain ⟨tail, tailEq⟩ := inductionHypothesis fun other membership =>
        total other (by simp [membership])
      exact ⟨head :: tail, by simp [headEq, tailEq]⟩

/-- Structural source-boundness plus independent rewrite sorting produces a
decoded typed view.  No relation evidence is assumed or manufactured. -/
theorem exists_decode?_eq_some_of_sourceBound
    {source : ValidatedLanguageDef}
    (typing : Mettapedia.OSLF.Framework.DisplayedRewriteTyping source)
    {premise : Premise}
    (sourceBound : PremiseSourceBound typing.site.rewrite premise) :
    ∃ view : View typing.site.rewrite,
      decode? typing.site.rewrite premise = some view := by
  rcases sourceBound with
    ⟨relation, arguments, rfl, argumentsSourceBound⟩
  obtain ⟨argumentTypes, typed⟩ := mapM_exists_of_forall_exists
    arguments (argumentType? typing.site.rewrite) fun argument membership =>
      argumentType?_exists_of_sourceBound typing
        (argumentsSourceBound argument membership)
  let view : View typing.site.rewrite :=
    { relation := relation
      arguments := arguments
      argumentTypes := argumentTypes }
  refine ⟨view, ?_⟩
  simp [decode?, typed, view]

/-- Every source-bound authored premise row has an ordered typed signature
row. -/
theorem exists_signatures?_eq_some_of_sourceBound
    {source : ValidatedLanguageDef}
    (typing : Mettapedia.OSLF.Framework.DisplayedRewriteTyping source)
    (sourceBound : PremisesSourceBound typing.site.rewrite) :
    ∃ signatures,
      signatures? typing.site.rewrite = some signatures := by
  apply mapM_exists_of_forall_exists
  intro premise membership
  obtain ⟨view, decoded⟩ := exists_decode?_eq_some_of_sourceBound typing
    (sourceBound premise membership)
  exact ⟨view.signature, by simp [signature?, decoded]⟩

/-- Finite source-bound checking followed by independent sorting proves that
the complete authored premise row is supported. -/
theorem allPremisesSupported_of_sourceBound
    {source : ValidatedLanguageDef}
    (typing : Mettapedia.OSLF.Framework.DisplayedRewriteTyping source)
    (sourceBound : PremisesSourceBound typing.site.rewrite) :
    allPremisesSupported typing.site.rewrite = true := by
  obtain ⟨signatures, decoded⟩ :=
    exists_signatures?_eq_some_of_sourceBound typing sourceBound
  simp [allPremisesSupported, decoded]

theorem decode?_is_relationQuery {rewrite : RewriteRule}
    {premise : Premise} {view : View rewrite}
  (decoded : decode? rewrite premise = some view) :
    ∃ relation arguments,
      premise = .relationQuery relation arguments := by
  exact ⟨view.relation, view.arguments,
    (encode_of_decode?_eq_some decoded).symm⟩

/-! ## Exact ordered view rows -/

/-- Mechanically decode the complete authored premise row.  Failure of any
premise rejects the whole row; successful decoding preserves order and
duplicates. -/
def decodeViews? (rewrite : RewriteRule) : Option (List (View rewrite)) :=
  rewrite.premises.mapM (decode? rewrite)

private theorem mapM_decode_encode {rewrite : RewriteRule}
    {premises : List Premise} {views : List (View rewrite)}
    (decoded : premises.mapM (decode? rewrite) = some views) :
    views.map View.encode = premises := by
  induction premises generalizing views with
  | nil =>
      simp at decoded
      subst views
      rfl
  | cons premise premises inductionHypothesis =>
      cases headDecoded : decode? rewrite premise with
      | none => simp [headDecoded] at decoded
      | some view =>
          cases tailDecoded : premises.mapM (decode? rewrite) with
          | none => simp [headDecoded, tailDecoded] at decoded
          | some tailViews =>
              simp [headDecoded, tailDecoded] at decoded
              subst views
              exact congrArg₂ List.cons
                (encode_of_decode?_eq_some headDecoded)
                (inductionHypothesis tailDecoded)

/-- Successful row decoding reconstructs the literal authored premise row. -/
theorem encodeViews_of_decodeViews?_eq_some {rewrite : RewriteRule}
    {views : List (View rewrite)}
    (decoded : decodeViews? rewrite = some views) :
    views.map View.encode = rewrite.premises :=
  mapM_decode_encode decoded

private theorem mapM_decode_typed {rewrite : RewriteRule}
    {premises : List Premise} {views : List (View rewrite)}
    (decoded : premises.mapM (decode? rewrite) = some views) :
    ∀ view ∈ views, view.WellTyped := by
  induction premises generalizing views with
  | nil =>
      simp at decoded
      subst views
      simp
  | cons premise premises inductionHypothesis =>
      cases headDecoded : decode? rewrite premise with
      | none => simp [headDecoded] at decoded
      | some headView =>
          cases tailDecoded : premises.mapM (decode? rewrite) with
          | none => simp [headDecoded, tailDecoded] at decoded
          | some tailViews =>
              simp [headDecoded, tailDecoded] at decoded
              subst views
              intro view membership
              simp only [List.mem_cons] at membership
              rcases membership with rfl | tailMembership
              · exact wellTyped_of_decode?_eq_some headDecoded
              · exact inductionHypothesis tailDecoded view tailMembership

/-- Every view in a successfully decoded row retains its independently
checked authored source typing. -/
theorem wellTyped_of_mem_decodeViews?_eq_some {rewrite : RewriteRule}
    {views : List (View rewrite)}
    (decoded : decodeViews? rewrite = some views) :
    ∀ view ∈ views, view.WellTyped :=
  mapM_decode_typed decoded

/-- Source-boundness and an independent sorting derivation make the complete
ordered view decoder succeed. -/
theorem exists_decodeViews?_eq_some_of_sourceBound
    {source : ValidatedLanguageDef}
    (typing : Mettapedia.OSLF.Framework.DisplayedRewriteTyping source)
    (sourceBound : PremisesSourceBound typing.site.rewrite) :
    ∃ views, decodeViews? typing.site.rewrite = some views := by
  apply mapM_exists_of_forall_exists
  intro premise membership
  exact exists_decode?_eq_some_of_sourceBound typing
    (sourceBound premise membership)

/-! ## Discriminating canaries -/

namespace Canary

private def rewrite : RewriteRule where
  name := "bound-premise-canary"
  typeContext := [("x", .base "X"), ("y", .base "Y")]
  premises := []
  left := .apply "pair" [.fvar "x", .fvar "y"]
  right := .fvar "x"

private def duplicateView : View rewrite where
  relation := "same"
  arguments := [.fvar "x", .fvar "x"]
  argumentTypes := [.base "X", .base "X"]

/-- Repeated arguments remain repeated in the exact wire and its type
projection. -/
theorem duplicate_arguments_are_preserved :
    duplicateView.encode =
        .relationQuery "same" [.fvar "x", .fvar "x"] ∧
      duplicateView.argumentTypes = [.base "X", .base "X"] ∧
      duplicateView.WellTyped := by
  simp [duplicateView, View.encode, View.WellTyped, argumentType?, rewrite,
    Pattern.freeFvarNames, FreeTypeContext.ofList]

/-- The positive duplicate-preserving view passes the exact decoder. -/
theorem duplicate_view_decodes :
    decode? rewrite duplicateView.encode = some duplicateView := by
  apply decode?_encode
  exact duplicate_arguments_are_preserved.2.2

/-- A compound argument is not silently flattened into the supported local
schema-variable fragment. -/
theorem compound_argument_rejected :
    decode? rewrite (.relationQuery "r" [.apply "box" [.fvar "x"]]) =
      none := by
  rfl

/-- A typed name absent from the rewrite source is not yet bound when its
premise is checked. -/
theorem unbound_argument_rejected :
    decode? rewrite (.relationQuery "r" [.fvar "z"]) = none := by
  have blocked :
      [.fvar "z"].mapM (argumentType? rewrite) = none := by
    simp [argumentType?, rewrite, Pattern.freeFvarNames]
  simp only [decode?]
  rw [blocked]

/-- A source variable lacking an authored type cannot be assigned an
invented carrier. -/
theorem untyped_argument_rejected :
    let untyped : RewriteRule :=
      { name := "untyped"
        typeContext := []
        premises := []
        left := .fvar "x"
        right := .fvar "x" }
    decode? untyped (.relationQuery "r" [.fvar "x"]) = none := by
  dsimp only
  have blocked :
      [.fvar "x"].mapM (argumentType?
        { name := "untyped"
          typeContext := []
          premises := []
          left := .fvar "x"
          right := .fvar "x" }) = none := by
    simp [argumentType?, FreeTypeContext.ofList, Pattern.freeFvarNames]
  simp only [decode?]
  rw [blocked]

/-- Other premise constructors remain outside this relation-query view. -/
theorem congruence_rejected :
    decode? rewrite (.congruence (.fvar "x") (.fvar "y")) = none := by
  rfl

/-- Freshness is not reclassified as a relation query. -/
theorem freshness_rejected :
    decode? rewrite
      (.freshness { varName := "x", term := .fvar "y" }) = none := by
  rfl

/-- Quantified premises require a binder-safe construction and remain outside
this first-order fragment. -/
theorem quantified_rejected :
    decode? rewrite (.forAll "xs" "x"
      (.relationQuery "r" [.fvar "x"])) = none := by
  rfl

end Canary

end Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
