import Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
import Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim
import Mettapedia.OSLF.Framework.SelectedNativeTypeSemanticDecoding
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction

/-!
# Occurrence-indexed claims for authored endpoint variables

Grounding an ordinary carrier claim erases the name of the schema variable
that produced its value.  That is insufficient for occurrence-sensitive modal
rules: two endpoint variables with the same carrier could exchange their
ground values while leaving the row of ordinary carrier claims satisfiable.

This module gives every authored endpoint-variable position a private formula
constructor indexed by both its selected rewrite occurrence and its exact
position in the ordered endpoint support.  The value remains the constructor's
only argument.  Thus grounding preserves the coordinate without exposing
schema-variable names at runtime.

The constructor inventory and decoder are computed from the selected source
language.  They add syntax only; independent carrier meaning is supplied by a
downstream displayed model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredVariableClaim

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCarrierSupport
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction

abbrev Occurrence {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

abbrev Binding {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :=
  Fin (authoredBindings demand slot).length

/-- Exact source binding at one ordered endpoint-support position. -/
def sourceBinding {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (binding : Binding demand slot) : String × TypeExpr :=
  (authoredBindings demand slot).get binding

/-! ## Compact private coordinate namespace -/

namespace Naming

/-- Parse a canonical unary occurrence coordinate followed by a canonical
unary binding coordinate. -/
def parseCoordinateSuffix : List Char → Nat → Option (Nat × Nat)
  | 's' :: suffix, slot => parseCoordinateSuffix suffix (slot + 1)
  | 'b' :: suffix, slot =>
      if suffix = List.replicate suffix.length 'i' then
        some (slot, suffix.length)
      else
        none
  | _, _ => none

/-- Private formula label for one selected occurrence and authored binding
position. -/
def label (slot binding : Nat) : String :=
  String.ofList ('$' :: 'v' :: ':' ::
    (List.replicate slot 's' ++ 'b' :: List.replicate binding 'i'))

private theorem parseCoordinateSuffix_encoded
    (slot binding offset : Nat) :
    parseCoordinateSuffix
        (List.replicate slot 's' ++ 'b' :: List.replicate binding 'i')
        offset =
      some (offset + slot, binding) := by
  induction slot generalizing offset with
  | zero => simp [parseCoordinateSuffix]
  | succ slot inductionHypothesis =>
      simp only [List.replicate_succ, List.cons_append,
        parseCoordinateSuffix]
      rw [inductionHypothesis]
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      rw [Nat.add_assoc, Nat.add_comm 1 slot]

/-- Decode only a canonical private authored-variable label.  The re-encoding
check prevents noncanonical aliases from acquiring generated authority. -/
def coordinate? (name : String) : Option (Nat × Nat) :=
  match name.toList with
  | '$' :: 'v' :: ':' :: suffix =>
      match parseCoordinateSuffix suffix 0 with
      | none => none
      | some coordinate =>
          if label coordinate.1 coordinate.2 = name then some coordinate
          else none
  | _ => none

@[simp] theorem coordinate?_label (slot binding : Nat) :
    coordinate? (label slot binding) = some (slot, binding) := by
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
    (firstSlot firstBinding secondSlot secondBinding : Nat) :
    label firstSlot firstBinding = label secondSlot secondBinding ↔
      firstSlot = secondSlot ∧ firstBinding = secondBinding := by
  constructor
  · intro equality
    exact Prod.mk.inj (label_injective equality)
  · rintro ⟨rfl, rfl⟩
    rfl

end Naming

/-! ## Generated constructors and open claims -/

/-- Constructor declaration for one exact authored binding position. -/
def termAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (binding : Binding demand slot) : GrammarRule where
  label := Naming.label slot.val binding.val
  category := ContextualInference.formulaType.name
  params :=
    [ .simple "value" (.base
        (SelectedNativeTypeSourceIndexedCarrierSupport.resolve demand
          (sourceBinding demand slot binding).2)) ]
  syntaxPattern := []

def termsAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List GrammarRule :=
  List.ofFn (termAt demand slot)

@[simp] theorem length_termsAt {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (termsAt demand slot).length = (authoredBindings demand slot).length := by
  simp [termsAt]

/-- Complete occurrence/binding constructor inventory. -/
def terms {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : List GrammarRule :=
  (List.ofFn fun slot : Occurrence demand => termsAt demand slot).flatten

theorem termLabels_private {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    ∀ name ∈ (terms demand).map GrammarRule.label,
      name.toList.head? = some '$' := by
  intro name membership
  obtain ⟨term, termMembership, rfl⟩ := List.mem_map.mp membership
  obtain ⟨row, rowMembership, termMembership⟩ :=
    List.mem_flatten.mp termMembership
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowMembership
  obtain ⟨binding, rfl⟩ := List.mem_ofFn.mp termMembership
  simp [termAt, Naming.label]

theorem termLabels_nodup {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) :
    ((terms demand).map GrammarRule.label).Nodup := by
  rw [terms, List.map_flatten, List.nodup_flatten]
  constructor
  · intro labels labelsMembership
    obtain ⟨rows, rowsMembership, rfl⟩ :=
      List.mem_map.mp labelsMembership
    obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp rowsMembership
    simp only [List.map_ofFn, Function.comp_def, termsAt, termAt]
    apply List.nodup_ofFn_ofInjective
    intro first second equality
    apply Fin.ext
    exact (Naming.label_eq_iff slot.val first.val slot.val second.val).mp equality |>.2
  · rw [List.pairwise_map, List.pairwise_ofFn]
    intro first second before
    apply List.disjoint_left.mpr
    intro name firstName secondName
    obtain ⟨firstTerm, firstTermMembership, rfl⟩ :=
      List.mem_map.mp firstName
    obtain ⟨firstBinding, rfl⟩ := List.mem_ofFn.mp firstTermMembership
    obtain ⟨secondTerm, secondTermMembership, equality⟩ :=
      List.mem_map.mp secondName
    obtain ⟨secondBinding, rfl⟩ := List.mem_ofFn.mp secondTermMembership
    have slotEquality : first.val = second.val :=
      (Naming.label_eq_iff first.val firstBinding.val second.val
        secondBinding.val).mp (by simpa [termAt] using equality.symm) |>.1
    exact (Fin.ne_of_lt before) (Fin.ext slotEquality)

/-- Formula at one exact occurrence and binding position. -/
def claim {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (slot : Occurrence demand)
    (binding : Binding demand slot) (value : Pattern) : Pattern :=
  .apply (Naming.label slot.val binding.val) [value]

/-- Open occurrence-local claim used by generated rule schemas. -/
def authoredClaim {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (binding : Binding demand slot) : Pattern :=
  claim slot binding
    (.fvar (renameVariable demand slot
      (sourceBinding demand slot binding).1))

/-- Complete exact binding row in authored endpoint-support order. -/
def authoredClaims {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    List Pattern :=
  List.ofFn (authoredClaim demand slot)

@[simp] theorem length_authoredClaims {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (authoredClaims demand slot).length = (authoredBindings demand slot).length := by
  simp [authoredClaims]

/-! ## Exact-image decoding -/

structure View {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) where
  occurrence : Occurrence demand
  binding : Binding demand occurrence
  value : Pattern
deriving DecidableEq

def View.encode {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (view : View demand) : Pattern :=
  claim view.occurrence view.binding view.value

def binding? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (index : Nat) : Option (Binding demand slot) :=
  if bound : index < (authoredBindings demand slot).length then
    some ⟨index, bound⟩
  else
    none

@[simp] theorem binding?_val {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (binding : Binding demand slot) :
    binding? demand slot binding.val = some binding := by
  simp [binding?]

/-- Fail-closed decoder for occurrence-indexed authored-variable claims. -/
def decode? {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) : Pattern → Option (View demand)
  | .apply name [value] =>
      match Naming.coordinate? name with
      | none => none
      | some coordinate =>
          match SelectedNativeTypeSemanticDecoding.occurrence?
              demand coordinate.1 with
          | none => none
          | some occurrence =>
              match binding? demand occurrence coordinate.2 with
              | none => none
              | some binding => some { occurrence, binding, value }
  | _ => none

@[simp] theorem decode?_encode {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (view : View demand) :
    decode? demand view.encode = some view := by
  simp [View.encode, claim, decode?, Naming.coordinate?_label,
    SelectedNativeTypeSemanticDecoding.occurrence?_val, binding?_val]

/-- Successful decoding reconstructs the complete original formula wire. -/
theorem encode_of_decode?_eq_some {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} {pattern : Pattern}
    {view : View demand} (decoded : decode? demand pattern = some view) :
    view.encode = pattern := by
  cases pattern with
  | apply name arguments =>
      cases arguments with
      | nil => simp [decode?] at decoded
      | cons value tail =>
          cases tail with
          | cons other rest => simp [decode?] at decoded
          | nil =>
              unfold decode? at decoded
              cases coordinateDecode : Naming.coordinate? name with
              | none => simp [coordinateDecode] at decoded
              | some coordinate =>
                  cases occurrenceDecode :
                      SelectedNativeTypeSemanticDecoding.occurrence?
                        demand coordinate.1 with
                  | none => simp [coordinateDecode, occurrenceDecode] at decoded
                  | some occurrence =>
                      cases bindingDecode :
                          binding? demand occurrence coordinate.2 with
                      | none =>
                          simp [coordinateDecode, occurrenceDecode,
                            bindingDecode] at decoded
                      | some binding =>
                          simp only [coordinateDecode, occurrenceDecode,
                            bindingDecode, Option.some.injEq] at decoded
                          cases decoded
                          unfold View.encode claim
                          have occurrenceValue : occurrence.val = coordinate.1 := by
                            have mapped := congrArg (Option.map Fin.val)
                              occurrenceDecode
                            simp [SelectedNativeTypeSemanticDecoding.occurrence?]
                              at mapped
                            exact mapped.2.symm
                          have bindingValue : binding.val = coordinate.2 := by
                            have mapped := congrArg (Option.map Fin.val)
                              bindingDecode
                            simp [binding?] at mapped
                            exact mapped.2.symm
                          rw [occurrenceValue, bindingValue,
                            Naming.label_of_coordinate?_eq_some coordinateDecode]
  | _ => simp [decode?] at decoded

def authoredView {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (binding : Binding demand slot) : View demand where
  occurrence := slot
  binding := binding
  value := .fvar (renameVariable demand slot
    (sourceBinding demand slot binding).1)

@[simp] theorem authoredView_encode {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (binding : Binding demand slot) :
    (authoredView demand slot binding).encode =
      authoredClaim demand slot binding :=
  rfl

@[simp] theorem decode?_authoredClaim {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (binding : Binding demand slot) :
    decode? demand (authoredClaim demand slot binding) =
      some (authoredView demand slot binding) := by
  rw [← authoredView_encode]
  exact decode?_encode _

/-- Ground one exact authored-variable claim using a source binding
environment. -/
def groundedView {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (binding : Binding demand slot) (bindings : Bindings) : View demand where
  occurrence := slot
  binding := binding
  value := applyBindings bindings
    (.fvar (sourceBinding demand slot binding).1)

/-- Complete grounded authored-variable row in the same exact order as the
source-derived open claim row. -/
def groundedClaims {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (bindings : Bindings) : List Pattern :=
  List.ofFn fun binding : Binding demand slot =>
    (groundedView demand slot binding bindings).encode

@[simp] theorem length_groundedClaims {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (bindings : Bindings) :
    (groundedClaims demand slot bindings).length =
      (authoredBindings demand slot).length := by
  simp [groundedClaims]

@[simp] theorem groundedClaims_get {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (bindings : Bindings) (binding : Binding demand slot) :
    (groundedClaims demand slot bindings).get
        ⟨binding.val, by
          rw [length_groundedClaims]
          exact binding.isLt⟩ =
      (groundedView demand slot binding bindings).encode := by
  simp [groundedClaims]

@[simp] theorem groundedView_encode {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (binding : Binding demand slot) (bindings : Bindings) :
    (groundedView demand slot binding bindings).encode =
      claim slot binding
        (applyBindings bindings
          (.fvar (sourceBinding demand slot binding).1)) :=
  rfl

/-! ## Discriminating controls -/

/-- Carrier-indexed contextual claims cannot be confused with exact authored
variable claims.  Their constructor namespaces are disjoint before values or
carrier meanings are inspected. -/
@[simp] theorem decode?_contextualCarrierClaim
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (kind : ContextualCarrierClaims.ClaimKind) (carrier : String)
    (arguments : List Pattern) :
    decode? demand
        (.apply (ContextualCarrierClaims.claimLabel kind carrier) arguments) =
      none := by
  cases kind <;> cases arguments with
  | nil => rfl
  | cons _ tail =>
      cases tail with
      | nil =>
          simp [decode?, Naming.coordinate?,
            ContextualCarrierClaims.claimLabel,
            ContextualCarrierClaims.ClaimKind.tag,
            String.toList_append]
      | cons _ _ => rfl

/-- Exact occurrence-step claims and exact authored-variable claims occupy
different private namespaces. -/
@[simp] theorem decode?_occurrenceStepClaim
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (slot : Occurrence demand) (before after : Pattern) :
    decode? demand
        (SelectedNativeTypeOccurrenceStepClaim.claim slot before after) =
      none := by
  rfl

/-- Exact authored relation-premise claims and exact authored-variable claims
also occupy different private namespaces. -/
@[simp] theorem decode?_boundRelationClaim
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (profile : SelectedNativeTypeBoundRelationClaim.Profile demand)
    (slot : Occurrence demand)
    (premise : Fin
      (SelectedNativeTypeBoundRelationClaim.viewsAt profile slot).length)
    (arguments : List Pattern) :
    decode? demand
        (SelectedNativeTypeBoundRelationClaim.claim slot premise arguments) =
      none := by
  cases arguments with
  | nil => rfl
  | cons _ tail =>
      cases tail with
      | nil =>
          simp [decode?, Naming.coordinate?,
            SelectedNativeTypeBoundRelationClaim.claim,
            SelectedNativeTypeBoundRelationClaim.Naming.label,
            String.toList_append]
      | cons _ _ => rfl

theorem distinct_occurrences_have_distinct_claims
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    {first second : Occurrence demand} (different : first ≠ second)
    (firstBinding : Binding demand first)
    (secondBinding : Binding demand second) (firstValue secondValue : Pattern) :
    claim first firstBinding firstValue ≠
      claim second secondBinding secondValue := by
  intro equality
  injection equality with headEquality _
  have slots := (Naming.label_eq_iff first.val firstBinding.val second.val
    secondBinding.val).mp headEquality |>.1
  exact different (Fin.ext slots)

theorem distinct_bindings_have_distinct_claims
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source} (slot : Occurrence demand)
    {first second : Binding demand slot} (different : first ≠ second)
    (firstValue secondValue : Pattern) :
    claim slot first firstValue ≠ claim slot second secondValue := by
  intro equality
  injection equality with headEquality _
  have bindings := (Naming.label_eq_iff slot.val first.val slot.val second.val).mp
    headEquality |>.2
  exact different (Fin.ext bindings)

theorem wrongArity_rejected {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand)
    (binding : Binding demand slot) (first second : Pattern) :
    decode? demand (.apply (Naming.label slot.val binding.val) [first, second]) =
      none := by
  rfl

#print axioms Naming.label_injective
#print axioms termLabels_nodup
#print axioms encode_of_decode?_eq_some
#print axioms decode?_contextualCarrierClaim
#print axioms decode?_occurrenceStepClaim
#print axioms decode?_boundRelationClaim
#print axioms distinct_occurrences_have_distinct_claims
#print axioms distinct_bindings_have_distinct_claims
#print axioms wrongArity_rejected

end Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredVariableClaim
