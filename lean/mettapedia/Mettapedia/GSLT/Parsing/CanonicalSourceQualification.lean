import Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration

/-!
# Structural qualification of canonical source inventories

Successful decoding can be checked one occurrence at a time. The field
equation below is available only after the complete source has decoded;
`filterMap` therefore discards no occurrence. These lemmas normalize proof
computation without introducing a second source representation or parser.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CanonicalSourceQualification

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration

theorem decodeList_isSome_iff {α : Type} (decoder : SExpr → Option α)
    (items : List SExpr) :
    (decodeList decoder items).isSome = true ↔
      ∀ item ∈ items, (decoder item).isSome = true := by
  induction items with
  | nil => simp [decodeList]
  | cons item items ih =>
    cases head : decoder item <;> cases tail : decodeList decoder items <;>
      simp_all [decodeList]

theorem decodeList_eq_filterMap {α : Type} (decoder : SExpr → Option α)
    (items : List SExpr)
    (accepted : (decodeList decoder items).isSome = true) :
    decodeList decoder items = some (items.filterMap decoder) := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    have facts := (decodeList_isSome_iff decoder (item :: items)).mp accepted
    have headSome := facts item (by simp)
    have tailSome := (decodeList_isSome_iff decoder items).mpr
      (fun next member => facts next (by simp [member]))
    cases head : decoder item with
    | none => simp [head] at headSome
    | some value => simp [decodeList, head, ih tailSome]

/-- The normalized field retains every occurrence, including equal rows. -/
theorem decoded_filterMap_length {α : Type} (decoder : SExpr → Option α)
    (items : List SExpr)
    (accepted : (decodeList decoder items).isSome = true) :
    (items.filterMap decoder).length = items.length := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    have facts := (decodeList_isSome_iff decoder (item :: items)).mp accepted
    have headSome := facts item (by simp)
    have tailSome := (decodeList_isSome_iff decoder items).mpr
      (fun next member => facts next (by simp [member]))
    cases head : decoder item with
    | none => simp [head] at headSome
    | some value => simp [head, ih tailSome]

theorem decode_fields_isSome_iff (name : String)
    (operators equations rewrites : List SExpr) :
    (decode (.list [.atom "gslt-presentation-v1", .atom name,
      .list (.atom "signature" :: operators),
      .list (.atom "equations" :: equations),
      .list (.atom "rewrites" :: rewrites)])).isSome = true ↔
      (∀ operator ∈ operators, (decodeOperator operator).isSome = true) ∧
      (∀ rewrite ∈ rewrites, (decodeRewrite rewrite).isSome = true) := by
  rw [← decodeList_isSome_iff, ← decodeList_isSome_iff]
  cases operatorsResult : decodeList decodeOperator operators <;>
    cases rewritesResult : decodeList decodeRewrite rewrites <;>
    simp [decode, atomToken?, operatorsResult, rewritesResult]

theorem source_eq_of_decode {name : String}
    {operators equations rewrites : List SExpr} {source : Source}
    (accepted : decode (.list [.atom "gslt-presentation-v1", .atom name,
      .list (.atom "signature" :: operators),
      .list (.atom "equations" :: equations),
      .list (.atom "rewrites" :: rewrites)]) = some source) :
    source = Source.mk name (operators.filterMap decodeOperator)
      equations (rewrites.filterMap decodeRewrite) := by
  have valid := (decode_fields_isSome_iff name operators equations rewrites).mp
    (by rw [accepted]; rfl)
  have operatorsExact := decodeList_eq_filterMap decodeOperator operators
    ((decodeList_isSome_iff decodeOperator operators).mpr valid.1)
  have rewritesExact := decodeList_eq_filterMap decodeRewrite rewrites
    ((decodeList_isSome_iff decodeRewrite rewrites).mpr valid.2)
  simpa [decode, atomToken?, operatorsExact, rewritesExact] using accepted.symm

theorem source_field_lengths {name : String}
    {operators equations rewrites : List SExpr} {source : Source}
    (accepted : decode (.list [.atom "gslt-presentation-v1", .atom name,
      .list (.atom "signature" :: operators),
      .list (.atom "equations" :: equations),
      .list (.atom "rewrites" :: rewrites)]) = some source) :
    source.name = name ∧ source.operators.length = operators.length ∧
      source.equations.length = equations.length ∧ source.rewrites.length = rewrites.length := by
  have valid := (decode_fields_isSome_iff name operators equations rewrites).mp
    (by rw [accepted]; rfl)
  rw [source_eq_of_decode accepted]
  exact ⟨rfl, decoded_filterMap_length decodeOperator operators
    ((decodeList_isSome_iff decodeOperator operators).mpr valid.1), rfl,
    decoded_filterMap_length decodeRewrite rewrites
      ((decodeList_isSome_iff decodeRewrite rewrites).mpr valid.2)⟩

theorem elaborateRewrites_isSome_iff (rewrites : List Rewrite) :
    (elaborateRewrites? rewrites).isSome = true ↔
      ∀ rewrite ∈ rewrites, (elaborateRewrite? rewrite).isSome = true := by
  induction rewrites with
  | nil => simp [elaborateRewrites?]
  | cons rewrite rewrites ih =>
    cases head : elaborateRewrite? rewrite <;>
      cases tail : elaborateRewrites? rewrites <;>
      simp_all [elaborateRewrites?]

theorem elaborateRewrites_isSome_iff_indices (rewrites : List Rewrite) :
    (elaborateRewrites? rewrites).isSome = true ↔
      (List.range rewrites.length).all (fun index =>
        ((rewrites[index]?).bind elaborateRewrite?).isSome) = true := by
  rw [elaborateRewrites_isSome_iff, List.all_eq_true]
  constructor
  · intro accepted index member
    have bound := List.mem_range.mp member
    simpa only [List.getElem?_eq_getElem bound, Option.bind_some] using
      accepted (rewrites[index]) (List.getElem_mem bound)
  · intro accepted rewrite member
    obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
    have checked := accepted index (List.mem_range.mpr bound)
    simpa only [List.getElem?_eq_getElem bound, same, Option.bind_some] using checked

example : decodeList atomToken? [.atom "same", .atom "same"] =
    some ["same", "same"] := rfl

example : decodeList atomToken? [.atom "same", .list []] = none := rfl

#print axioms decoded_filterMap_length
#print axioms source_eq_of_decode
#print axioms elaborateRewrites_isSome_iff

end Mettapedia.GSLT.Parsing.CanonicalSourceQualification
