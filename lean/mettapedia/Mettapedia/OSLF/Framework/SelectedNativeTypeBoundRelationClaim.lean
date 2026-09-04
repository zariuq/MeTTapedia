import Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
import Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationEvidence
import Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim
import Mettapedia.OSLF.Framework.SelectedNativeTypeSemanticDecoding
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport

/-!
# Occurrence-indexed claims for source-bound relation premises

An authored relation premise is an assumption of a rewrite, not evidence that
the rewrite has already fired.  This module gives every supported premise a
private formula constructor indexed by both its selected rewrite occurrence
and its exact position in the authored premise row.

The profile is computed from the source `LanguageDef`.  It retains relation
names, argument order, repeated arguments, source carrier types, and premise
positions, but contains no relation answer.  Ground claim meaning is supplied
independently by the selected cold `RelationEnv` and is proved equivalent to
the existing proof-relevant ordered-premise interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationEvidence
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport

abbrev Occurrence {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

/-! ## Exact source-derived premise profile -/

/-- Evidence that every selected occurrence has a complete decoded premise
row.  The row itself is computed by `decodeViews?`; the profile stores only
the proof that this source computation succeeded. -/
structure Profile {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : Prop where
  supported : ∀ slot : Occurrence demand,
    (decodeViews? (typingAt demand slot).site.rewrite).isSome = true

/-- Exact ordered source-computed view row for one selected occurrence. -/
def viewsAt {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) :
    List (SelectedNativeTypeBoundRelationPremise.View
      (typingAt demand slot).site.rewrite) :=
  (decodeViews? (typingAt demand slot).site.rewrite).get
    (profile.supported slot)

/-- The profile row is definitionally tied to successful source decoding. -/
theorem viewsAt_decoded {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) :
    decodeViews? (typingAt demand slot).site.rewrite =
      some (viewsAt profile slot) :=
  (Option.some_get (profile.supported slot)).symm

/-- Every retained view reconstructs an authored premise in the same ordered
row. -/
theorem viewsAt_encoded {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) :
    (viewsAt profile slot).map
        SelectedNativeTypeBoundRelationPremise.View.encode =
      (typingAt demand slot).site.rewrite.premises :=
  encodeViews_of_decodeViews?_eq_some (viewsAt_decoded profile slot)

/-- Every retained view carries the source-derived authored carrier row. -/
theorem viewsAt_typed {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) :
    ∀ view ∈ viewsAt profile slot, view.WellTyped :=
  wellTyped_of_mem_decodeViews?_eq_some (viewsAt_decoded profile slot)

/-- Exact source view at one retained premise occurrence. -/
def sourceView {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) :
    SelectedNativeTypeBoundRelationPremise.View
      (typingAt demand slot).site.rewrite :=
  (viewsAt profile slot).get premise

/-- A view selected by an exact premise position retains its independently
checked source typing. -/
theorem sourceView_typed {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) :
    (sourceView profile slot premise).WellTyped :=
  viewsAt_typed profile slot _ (List.get_mem _ premise)

private theorem length_eq_of_mapM_eq_some {α β : Type}
    (f : α → Option β) {source : List α} {target : List β}
    (mapped : source.mapM f = some target) :
    source.length = target.length := by
  induction source generalizing target with
  | nil =>
      simp at mapped
      subst target
      rfl
  | cons head tail inductionHypothesis =>
      cases headMapped : f head with
      | none => simp [headMapped] at mapped
      | some value =>
          cases tailMapped : tail.mapM f with
          | none => simp [headMapped, tailMapped] at mapped
          | some values =>
              simp [headMapped, tailMapped] at mapped
              subst target
              simp [inductionHypothesis tailMapped]

/-- Decoding cannot change arity while recovering source carriers. -/
theorem sourceView_argument_length_eq_types {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) :
    (sourceView profile slot premise).arguments.length =
      (sourceView profile slot premise).argumentTypes.length :=
  length_eq_of_mapM_eq_some _ (sourceView_typed profile slot premise)

private theorem exists_source_of_mem_mapM_result {alpha beta : Type}
    (f : alpha → Option beta) :
    ∀ {source : List alpha} {target : List beta},
      source.mapM f = some target →
      ∀ {value}, value ∈ target →
        ∃ input, input ∈ source ∧ f input = some value := by
  intro source
  induction source with
  | nil =>
      intro target mapped value membership
      simp at mapped
      subst target
      simp at membership
  | cons head tail inductionHypothesis =>
      intro target mapped value membership
      cases headMapped : f head with
      | none => simp [headMapped] at mapped
      | some headValue =>
          cases tailMapped : tail.mapM f with
          | none => simp [headMapped, tailMapped] at mapped
          | some tailValues =>
              simp [headMapped, tailMapped] at mapped
              subst target
              simp only [List.mem_cons] at membership
              rcases membership with rfl | tailMembership
              · exact ⟨head, by simp, headMapped⟩
              · obtain ⟨input, inputMembership, inputMapped⟩ :=
                  inductionHypothesis tailMapped tailMembership
                exact ⟨input, by simp [inputMembership], inputMapped⟩

private theorem ofList_eq_some_snd_mem
    (context : List (String × TypeExpr)) (name : String) {type : TypeExpr}
    (lookup : FreeTypeContext.ofList context name = some type) :
    type ∈ context.map Prod.snd := by
  induction context with
  | nil => simp [FreeTypeContext.ofList] at lookup
  | cons entry context inductionHypothesis =>
      rcases entry with ⟨entryName, entryType⟩
      by_cases equality : entryName = name
      · subst name
        simp [FreeTypeContext.ofList] at lookup
        subst type
        simp
      · simp only [FreeTypeContext.ofList, equality, if_false] at lookup
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr (inductionHypothesis lookup)

/-- Every carrier recovered for a source-bound query argument is literally
drawn from the authored rewrite type context.  The profile cannot invent a
carrier while decoding relation premises. -/
theorem sourceView_argumentType_mem_authored {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) {type : TypeExpr}
    (membership : type ∈ (sourceView profile slot premise).argumentTypes) :
    type ∈ SelectedNativeTypeFoundation.authoredVariableCarrierTypes
      (typingAt demand slot) := by
  obtain ⟨argument, _argumentMembership, argumentMapped⟩ :=
    exists_source_of_mem_mapM_result
      (argumentType? (typingAt demand slot).site.rewrite)
      (sourceView_typed profile slot premise) membership
  obtain ⟨name, _argumentExact, _sourceMembership, lookup⟩ :=
    (argumentType?_eq_some_iff _ _ _).mp argumentMapped
  unfold SelectedNativeTypeFoundation.authoredVariableCarrierTypes
  exact ofList_eq_some_snd_mem _ name lookup

/-! ## Compact private coordinate namespace -/

namespace Naming

/-- Parse a canonical unary occurrence coordinate followed by a canonical
unary premise coordinate.  The two coordinates remain separate rather than
being folded into one potentially large unary number. -/
def parseCoordinateSuffix : List Char → Nat → Option (Nat × Nat)
  | 's' :: suffix, slot => parseCoordinateSuffix suffix (slot + 1)
  | 'p' :: suffix, slot =>
      if suffix = List.replicate suffix.length 'i' then
        some (slot, suffix.length)
      else
        none
  | _, _ => none

/-- Private formula label for one selected occurrence and authored premise
position. -/
def label (slot premise : Nat) : String :=
  String.ofList ('$' :: 'q' :: ':' ::
    (List.replicate slot 's' ++ 'p' :: List.replicate premise 'i'))

private theorem parseCoordinateSuffix_encoded
    (slot premise offset : Nat) :
    parseCoordinateSuffix
        (List.replicate slot 's' ++ 'p' :: List.replicate premise 'i')
        offset =
      some (offset + slot, premise) := by
  induction slot generalizing offset with
  | zero => simp [parseCoordinateSuffix]
  | succ slot inductionHypothesis =>
      simp only [List.replicate_succ, List.cons_append,
        parseCoordinateSuffix]
      rw [inductionHypothesis]
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      rw [Nat.add_assoc, Nat.add_comm 1 slot]

/-- Decode only a canonical private premise label.  Re-encoding after the raw
parse prevents aliases from acquiring generated authority. -/
def coordinate? (name : String) : Option (Nat × Nat) :=
  match name.toList with
  | '$' :: 'q' :: ':' :: suffix =>
      match parseCoordinateSuffix suffix 0 with
      | none => none
      | some coordinate =>
          if label coordinate.1 coordinate.2 = name then some coordinate
          else none
  | _ => none

@[simp] theorem coordinate?_label (slot premise : Nat) :
    coordinate? (label slot premise) = some (slot, premise) := by
  simp [coordinate?, label, parseCoordinateSuffix_encoded]

theorem label_of_coordinate?_eq_some {name : String}
    {coordinate : Nat × Nat}
    (decoded : coordinate? name = some coordinate) :
    label coordinate.1 coordinate.2 = name := by
  unfold coordinate? at decoded
  split at decoded
  next suffix equation =>
    split at decoded
    next => simp at decoded
    next parsed raw =>
      split at decoded
      next canonical =>
        simp only [Option.some.injEq] at decoded
        subst coordinate
        exact canonical
      next notCanonical => simp at decoded
  next => simp at decoded

theorem label_injective :
    Function.Injective fun coordinate : Nat × Nat =>
      label coordinate.1 coordinate.2 := by
  intro first second equality
  have decoded := congrArg coordinate? equality
  simpa using decoded

theorem label_eq_iff
    (firstSlot firstPremise secondSlot secondPremise : Nat) :
    label firstSlot firstPremise = label secondSlot secondPremise ↔
      firstSlot = secondSlot ∧ firstPremise = secondPremise := by
  constructor
  · intro equality
    exact Prod.mk.inj (label_injective equality)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Premise claims, occurrence-step claims, and modal constructors occupy
disjoint private namespaces. -/
theorem label_ne_occurrenceStep (slot premise stepSlot : Nat) :
    label slot premise ≠
      SelectedNativeTypeOccurrenceStepClaim.Naming.label stepSlot := by
  intro equality
  have lists := congrArg String.toList equality
  simp [label, SelectedNativeTypeOccurrenceStepClaim.Naming.label] at lists

theorem label_ne_modal (slot premise modalSlot : Nat) :
    label slot premise ≠ SelectedModalNaming.label modalSlot := by
  intro equality
  have lists := congrArg String.toList equality
  simp [label, SelectedModalNaming.label] at lists

end Naming

/-! ## Generated formula constructors -/

/-- Constructor declaration for one exact authored premise occurrence. -/
def termAt {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) : GrammarRule where
  label := Naming.label slot.val premise.val
  category := ContextualInference.formulaType.name
  params := List.ofFn fun argument :
      Fin (sourceView profile slot premise).argumentTypes.length =>
    .simple (indexedMetavariable "query-argument" argument.val)
      (.base (SelectedNativeTypeSourceIndexedCarrierSupport.resolve demand
        ((sourceView profile slot premise).argumentTypes.get argument)))
  syntaxPattern := []

/-- Constructor row for one selected rewrite occurrence, in authored premise
order. -/
def termsAt {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) : List GrammarRule :=
  List.ofFn (termAt profile slot)

@[simp] theorem length_termsAt {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) :
    (termsAt profile slot).length = (viewsAt profile slot).length := by
  simp [termsAt]

/-- Constructor arity is exactly the authored query arity. -/
theorem termAt_parameter_count {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) :
    (termAt profile slot premise).params.length =
      (sourceView profile slot premise).arguments.length := by
  simp [termAt]
  exact (sourceView_argument_length_eq_types profile slot premise).symm

/-- Complete selected-occurrence/premise constructor inventory. -/
def terms {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    List GrammarRule :=
  (List.ofFn fun slot : Occurrence demand => termsAt profile slot).flatten

/-- The generated inventory size is the sum of exact authored premise-row
sizes over selected occurrences. -/
theorem length_terms {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    (terms profile).length =
      (List.ofFn fun slot : Occurrence demand =>
        (viewsAt profile slot).length).sum := by
  rw [terms, List.length_flatten]
  congr 1
  simp only [List.map_ofFn]
  rw [List.ofFn_inj]
  funext slot
  exact length_termsAt profile slot

/-- All premise constructors occupy the private generated namespace. -/
theorem termLabels_private {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    ∀ name ∈ (terms profile).map GrammarRule.label,
      name.toList.head? = some '$' := by
  intro name membership
  obtain ⟨term, termMembership, rfl⟩ := List.mem_map.mp membership
  obtain ⟨row, rowMembership, termMembership⟩ :=
    List.mem_flatten.mp termMembership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
  obtain ⟨premise, rfl⟩ := List.mem_ofFn.mp termMembership
  simp [termAt, Naming.label]

/-- Exact premise coordinates give duplicate-free generated constructor
labels.  The proof separates injectivity within one rewrite occurrence from
disjointness between distinct occurrences, so clients need not normalize a
completed generated signature. -/
theorem termLabels_nodup {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    ((terms profile).map GrammarRule.label).Nodup := by
  rw [terms, List.map_flatten, List.nodup_flatten]
  constructor
  · intro labels labelsMembership
    obtain ⟨rows, rowsMembership, rfl⟩ :=
      List.mem_map.mp labelsMembership
    obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowsMembership
    simp only [termsAt, List.map_ofFn, Function.comp_def]
    apply List.nodup_ofFn_ofInjective
    intro first second equality
    apply Fin.ext
    exact (Naming.label_eq_iff slot.val first.val slot.val second.val).mp
      equality |>.2
  · rw [List.pairwise_map, List.pairwise_ofFn]
    intro first second before
    apply List.disjoint_left.mpr
    intro label firstMembership secondMembership
    obtain ⟨firstTerm, firstTermMembership, rfl⟩ :=
      List.mem_map.mp firstMembership
    obtain ⟨firstPremise, rfl⟩ :=
      List.mem_ofFn.mp firstTermMembership
    obtain ⟨secondTerm, secondTermMembership, equality⟩ :=
      List.mem_map.mp secondMembership
    obtain ⟨secondPremise, rfl⟩ :=
      List.mem_ofFn.mp secondTermMembership
    have coordinateEquality :
        Naming.label first.val firstPremise.val =
          Naming.label second.val secondPremise.val := by
      simpa [termAt] using equality.symm
    have slotEquality :=
      (Naming.label_eq_iff first.val firstPremise.val second.val
        secondPremise.val).mp coordinateEquality |>.1
    exact (Fin.ne_of_lt before) (Fin.ext slotEquality)

/-- Term-only extension.  It introduces formula syntax but no proof rule or
operational transition. -/
def extension {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    CalculusLanguageExtension where
  newTerms := terms profile

@[simp] theorem extension_terms {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    (extension profile).newTerms = terms profile :=
  rfl

@[simp] theorem extension_types_empty {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    (extension profile).newTypes = [] :=
  rfl

@[simp] theorem extension_judgments_empty {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    (extension profile).newJudgments = [] :=
  rfl

@[simp] theorem extension_rules_empty {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    (extension profile).newRules = [] :=
  rfl

@[simp] theorem extension_equations_empty {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    (extension profile).newEquations = [] :=
  rfl

@[simp] theorem extension_rewrites_empty {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    (extension profile).newRewrites = [] :=
  rfl

/-! ## Claims, decoding, and independent meaning -/

/-- Formula at an exact selected occurrence and authored premise position. -/
def claim {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {profile : Profile demand}
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length)
    (arguments : List Pattern) : Pattern :=
  .apply (Naming.label slot.val premise.val) arguments

/-- Literal source-premise arguments renamed into the exact selected
occurrence namespace. -/
def authoredArguments {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) : List Pattern :=
  (sourceView profile slot premise).arguments.map
    (authoredPattern demand slot)

/-- Open claim appearing in a generated rule schema. -/
def authoredClaim {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) : Pattern :=
  claim slot premise (authoredArguments profile slot premise)

/-- Complete authored claim row in exact premise order. -/
def authoredClaims {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) : List Pattern :=
  List.ofFn (authoredClaim profile slot)

@[simp] theorem length_authoredClaims {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) :
    (authoredClaims profile slot).length = (viewsAt profile slot).length := by
  simp [authoredClaims]

/-- Decoded claim with its source occurrence, authored premise position, and
actual argument row.  The arity equation is structural admission only. -/
structure View {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) where
  occurrence : Occurrence demand
  premise : Fin (viewsAt profile occurrence).length
  arguments : List Pattern
  arity : arguments.length =
    (sourceView profile occurrence premise).arguments.length

def View.encode {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {profile : Profile demand}
    (view : View profile) : Pattern :=
  claim view.occurrence view.premise view.arguments

/-- The open source formula is itself an admitted decoded view. -/
def authoredView {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) : View profile where
  occurrence := slot
  premise := premise
  arguments := authoredArguments profile slot premise
  arity := by simp [authoredArguments]

@[simp] theorem authoredView_encode {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) :
    (authoredView profile slot premise).encode =
      authoredClaim profile slot premise := by
  rfl

/-- Independent ground meaning of one decoded claim.  It consults the cold
relation table at the exact source relation name; generated derivability and
checker acceptance do not occur in this definition. -/
def View.Meaning {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {profile : Profile demand}
    (relations : RelationEnv) (view : View profile) : Prop :=
  view.arguments ∈
    relations.tuples
      (sourceView profile view.occurrence view.premise).relation
      view.arguments

/-- Bound a raw premise position by the exact source-computed row. -/
def premise? {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) (index : Nat) :
    Option (Fin (viewsAt profile slot).length) :=
  if bound : index < (viewsAt profile slot).length then
    some ⟨index, bound⟩
  else
    none

@[simp] theorem premise?_val {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) :
    premise? profile slot premise.val = some premise := by
  simp [premise?]

/-- Fail-closed decoder for source-indexed premise claims. -/
def decode? {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand) :
    Pattern → Option (View profile)
  | .apply name arguments =>
      match Naming.coordinate? name with
      | none => none
      | some coordinate =>
          match SelectedNativeTypeSemanticDecoding.occurrence?
              demand coordinate.1 with
          | none => none
          | some occurrence =>
              match premise? profile occurrence coordinate.2 with
              | none => none
              | some premise =>
                  if arity : arguments.length =
                      (sourceView profile occurrence premise).arguments.length
                  then some { occurrence, premise, arguments, arity }
                  else none
  | _ => none

@[simp] theorem decode?_encode {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {profile : Profile demand}
    (view : View profile) :
    decode? profile view.encode = some view := by
  unfold View.encode
  simp only [claim, decode?, Naming.coordinate?_label,
    SelectedNativeTypeSemanticDecoding.occurrence?_val, premise?_val]
  split
  next => congr
  next notArity => exact (notArity view.arity).elim

/-- Successful decoding reconstructs the complete original formula wire. -/
theorem encode_of_decode?_eq_some {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {profile : Profile demand}
    {pattern : Pattern} {view : View profile}
    (decoded : decode? profile pattern = some view) :
    view.encode = pattern := by
  cases pattern with
  | apply name arguments =>
      unfold decode? at decoded
      cases coordinateDecode : Naming.coordinate? name with
      | none => simp [coordinateDecode] at decoded
      | some coordinate =>
          cases occurrenceDecode :
              SelectedNativeTypeSemanticDecoding.occurrence?
                demand coordinate.1 with
          | none => simp [coordinateDecode, occurrenceDecode] at decoded
          | some occurrence =>
              cases premiseDecode :
                  premise? profile occurrence coordinate.2 with
              | none =>
                  simp [coordinateDecode, occurrenceDecode, premiseDecode]
                    at decoded
              | some premise =>
                  simp only [coordinateDecode, occurrenceDecode,
                    premiseDecode] at decoded
                  split at decoded
                  next arity =>
                    simp only [Option.some.injEq] at decoded
                    cases decoded
                    unfold View.encode claim
                    have occurrenceValue :
                        occurrence.val = coordinate.1 := by
                      have mapped := congrArg (Option.map Fin.val)
                        occurrenceDecode
                      simp [SelectedNativeTypeSemanticDecoding.occurrence?]
                        at mapped
                      exact mapped.2.symm
                    have premiseValue : premise.val = coordinate.2 := by
                      have mapped := congrArg (Option.map Fin.val)
                        premiseDecode
                      simp [premise?] at mapped
                      exact mapped.2.symm
                    rw [occurrenceValue, premiseValue,
                      Naming.label_of_coordinate?_eq_some coordinateDecode]
                  next => simp at decoded
  | _ => simp [decode?] at decoded

@[simp] theorem decode?_authoredClaim {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length) :
    decode? profile (authoredClaim profile slot premise) =
      some (authoredView profile slot premise) := by
  rw [← authoredView_encode]
  exact decode?_encode _

/-- Ground a source premise claim with the concrete values supplied by one
binding environment. -/
def groundedView {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length)
    (bindings : Bindings) : View profile where
  occurrence := slot
  premise := premise
  arguments := (sourceView profile slot premise).arguments.map
    (applyBindings bindings)
  arity := by simp

/-- Complete grounded guard row in authored premise order.  Repeated source
premises remain repeated list positions. -/
def groundedClaims {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) (bindings : Bindings) : List Pattern :=
  List.ofFn fun premise : Fin (viewsAt profile slot).length =>
    (groundedView profile slot premise bindings).encode

@[simp] theorem length_groundedClaims {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) (bindings : Bindings) :
    (groundedClaims profile slot bindings).length =
      (viewsAt profile slot).length := by
  simp [groundedClaims]

@[simp] theorem groundedClaims_get {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) (bindings : Bindings)
    (premise : Fin (viewsAt profile slot).length) :
    (groundedClaims profile slot bindings).get
        ⟨premise.val, by
          rw [length_groundedClaims]
          exact premise.isLt⟩ =
      (groundedView profile slot premise bindings).encode := by
  simp [groundedClaims]

/-- Ground claim meaning is exactly the previously independent source-bound
relation meaning at the same binding environment. -/
theorem groundedView_meaning_iff
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length)
    (relations : RelationEnv) (bindings : Bindings) :
    (groundedView profile slot premise bindings).Meaning relations ↔
      SelectedNativeTypeBoundRelationEvidence.Meaning relations bindings
        (sourceView profile slot premise) := by
  rfl

/-- Independent meaning of the complete generated claim row.  Quantification
by `Fin` retains authored order and repeated premise occurrences. -/
def GroundMeanings {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (relations : RelationEnv) (slot : Occurrence demand)
    (bindings : Bindings) : Prop :=
  ∀ premise : Fin (viewsAt profile slot).length,
    (groundedView profile slot premise bindings).Meaning relations

/-- Exact bridge from generated claim-row meaning to the existing ordered
source-premise meaning. -/
theorem groundMeanings_iff_relationMeanings
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (relations : RelationEnv) (slot : Occurrence demand)
    (bindings : Bindings) :
    GroundMeanings profile relations slot bindings ↔
      SelectedNativeTypeBoundRelationEvidence.ContractRow.Meanings
        relations bindings (viewsAt profile slot) := by
  rw [SelectedNativeTypeBoundRelationEvidence.ContractRow.meanings_iff_forall_get]
  rfl

/-! ## Discriminating controls -/

/-- Carrier-indexed contextual claims cannot be confused with exact authored
premise claims.  The namespaces are disjoint before any argument or semantic
inspection occurs. -/
@[simp] theorem decode?_contextualCarrierClaim
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (kind : ContextualCarrierClaims.ClaimKind) (carrier : String)
    (arguments : List Pattern) :
    decode? profile
        (.apply (ContextualCarrierClaims.claimLabel kind carrier) arguments) =
      none := by
  cases kind <;>
    simp [decode?, Naming.coordinate?, ContextualCarrierClaims.claimLabel,
      ContextualCarrierClaims.ClaimKind.tag]

/-- Exact occurrence-step claims and exact authored-premise claims occupy
different private namespaces. -/
@[simp] theorem decode?_occurrenceStepClaim
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) (before after : Pattern) :
    decode? profile
        (SelectedNativeTypeOccurrenceStepClaim.claim slot before after) =
      none := by
  simp [decode?, Naming.coordinate?,
    SelectedNativeTypeOccurrenceStepClaim.claim,
    SelectedNativeTypeOccurrenceStepClaim.Naming.label]

/-- The first raw occurrence outside the selected demand cannot decode. -/
theorem firstOccurrenceOutOfRange_rejected
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (arguments : List Pattern) :
    decode? profile
      (.apply (Naming.label demand.occurrences.length 0) arguments) = none := by
  simp [decode?, SelectedNativeTypeSemanticDecoding.occurrence?]

/-- The first premise position outside an occurrence's exact authored row
cannot decode. -/
theorem firstPremiseOutOfRange_rejected
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand) (arguments : List Pattern) :
    decode? profile
      (.apply (Naming.label slot.val (viewsAt profile slot).length)
        arguments) = none := by
  simp [decode?, premise?]

/-- A structurally wrong argument count cannot acquire premise meaning. -/
theorem wrongArity_rejected
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (profile : Profile demand)
    (slot : Occurrence demand)
    (premise : Fin (viewsAt profile slot).length)
    (arguments : List Pattern)
    (wrong : arguments.length ≠
      (sourceView profile slot premise).arguments.length) :
    decode? profile
      (.apply (Naming.label slot.val premise.val) arguments) = none := by
  simp [decode?, premise?, wrong]

/-- Equal argument rows do not collapse two selected rewrite occurrences. -/
theorem distinct_occurrences_have_distinct_claims
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {profile : Profile demand}
    {first second : Occurrence demand} (different : first ≠ second)
    (firstPremise : Fin (viewsAt profile first).length)
    (secondPremise : Fin (viewsAt profile second).length)
    (arguments : List Pattern) :
    claim first firstPremise arguments ≠
      claim second secondPremise arguments := by
  intro equality
  apply different
  apply Fin.ext
  have labels := (Pattern.apply.inj equality).1
  exact (Naming.label_eq_iff _ _ _ _).mp labels |>.1

/-- Two positions in the same authored premise row remain distinct even when
their formula arguments are extensionally equal. -/
theorem distinct_premises_have_distinct_claims
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {profile : Profile demand}
    (slot : Occurrence demand)
    {first second : Fin (viewsAt profile slot).length}
    (different : first ≠ second) (arguments : List Pattern) :
    claim slot first arguments ≠ claim slot second arguments := by
  intro equality
  apply different
  apply Fin.ext
  have labels := (Pattern.apply.inj equality).1
  exact (Naming.label_eq_iff _ _ _ _).mp labels |>.2

#print axioms viewsAt_encoded
#print axioms viewsAt_typed
#print axioms Naming.label_injective
#print axioms sourceView_argument_length_eq_types
#print axioms sourceView_argumentType_mem_authored
#print axioms termAt_parameter_count
#print axioms length_terms
#print axioms termLabels_private
#print axioms termLabels_nodup
#print axioms decode?_encode
#print axioms encode_of_decode?_eq_some
#print axioms decode?_authoredClaim
#print axioms groundedView_meaning_iff
#print axioms groundMeanings_iff_relationMeanings
#print axioms decode?_contextualCarrierClaim
#print axioms decode?_occurrenceStepClaim
#print axioms firstOccurrenceOutOfRange_rejected
#print axioms firstPremiseOutOfRange_rejected
#print axioms wrongArity_rejected
#print axioms distinct_occurrences_have_distinct_claims
#print axioms distinct_premises_have_distinct_claims

end Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim
