import Mettapedia.Languages.MeTTa.SpaceTheory.NativeVocabulary
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Checking the declarations of an Atom space against its carrier

An Atom-space contribution is not a separately named LangDef file.
In particular, two stored copies contribute two function definitions,
even if their presentation labels coincide. Check the actual sides of
each contribution against its declared native Atom carrier. Do not
turn this check into a certificate for a different syntax validator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.NativeValidation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Syntax (LanguageDef Pattern TypeExpr)
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted (checkHasType checkHasType_sound checkHasType_eq_true_iff)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)
open Mettapedia.GSLT.LanguageDef.LiveModuleEdits (Order)
open Atoms (Content)
open Presentation (Contribution PresentedSpace assemble contribution_rule_origin)
open NativeVocabulary (AtomSides contribution parts)
open NativeTyping (atomSort schema_isObject)

def checkSides (language : LanguageDef) (context : List (String × TypeExpr))
    (left right : Pattern) : Bool :=
  checkHasType language (fun name => context.lookup name) [] left atomSort &&
    checkHasType language (fun name => context.lookup name) [] right atomSort

theorem check_sides_sound {language : LanguageDef} {context : List (String × TypeExpr)} {left right : Pattern}
    (accepted : checkSides language context left right = true) : AtomSides language context left right := by
  simp only [checkSides, Bool.and_eq_true] at accepted
  obtain ⟨l, r⟩ := accepted
  exact ⟨checkHasType_sound l, checkHasType_sound r⟩

theorem check_sides_iff (language : LanguageDef) (context : List (String × TypeExpr)) (left right : Pattern)
    (leftObject : isObjectPattern left = true) (rightObject : isObjectPattern right = true) :
    checkSides language context left right = true ↔ AtomSides language context left right := by
  simp only [checkSides, Bool.and_eq_true, checkHasType_eq_true_iff leftObject,
    checkHasType_eq_true_iff rightObject, AtomSides]

def checkPart (language : LanguageDef) (part : Contribution) : Bool :=
  part.rewrites.all (fun r => checkSides language r.typeContext r.left r.right) &&
    part.equations.all (fun e => checkSides language e.typeContext e.left e.right)

theorem check_part_sound {language : LanguageDef} {part : Contribution} (accepted : checkPart language part = true) :
    (∀ r ∈ part.rewrites, AtomSides language r.typeContext r.left r.right) ∧
    (∀ e ∈ part.equations, AtomSides language e.typeContext e.left e.right) := by
  simp only [checkPart, Bool.and_eq_true] at accepted
  obtain ⟨rewrites, equations⟩ := accepted
  exact ⟨fun _ member => check_sides_sound (List.all_eq_true.mp rewrites _ member),
    fun _ member => check_sides_sound (List.all_eq_true.mp equations _ member)⟩

private theorem objectMember {atoms : List Atom} {member : Pattern}
    (present : member ∈ GroundData.encodeList atoms) : isObjectPattern member = true := by
  induction atoms with
  | nil => simp [GroundData.encodeList] at present
  | cons a tail ih =>
    rw [GroundData.encodeList, List.mem_cons] at present
    rcases present with rfl | rest
    · exact GroundData.encode_isObject _
    · exact ih rest

private theorem equationObjects {written : Content} {part : Contribution}
    (compiled : contribution written = some part) {e} (member : e ∈ part.equations) :
    isObjectPattern e.left = true ∧ isObjectPattern e.right = true := by
  cases written
  case equation preference first second tail =>
    cases compiled
    obtain ⟨pattern, here, rfl⟩ := List.mem_map.mp member
    exact ⟨GroundData.encode_isObject first, objectMember here⟩
  all_goals cases compiled <;> cases member

/-- A base providing the native carrier accepts all authored native
contributions, including grounded literals and repeated definitions. -/
theorem check_native_part (language : LanguageDef)
    (types : GroundData.dataLanguage.types ⊆ language.types)
    (terms : GroundData.dataLanguage.terms ⊆ language.terms)
    (written : Content) {part : Contribution} (compiled : contribution written = some part) :
    checkPart language part = true := by
  simp only [checkPart, Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro r member
    obtain ⟨lhs, rhs, _, left, right, _, _⟩ :=
      contribution_rule_origin (definitionTerm := some ∘ GroundData.schema) compiled member
    have leftObject := (Option.some.inj left) ▸ schema_isObject lhs
    have rightObject := (Option.some.inj right) ▸ schema_isObject rhs
    have typed := NativeVocabulary.contribution_definition_typed written compiled member
    exact (check_sides_iff language _ _ _ leftObject rightObject).mpr
      ⟨typed.1.of_signature_inclusion types terms, typed.2.of_signature_inclusion types terms⟩
  · apply List.all_eq_true.mpr
    intro e member
    have object := equationObjects compiled member
    have typed := NativeVocabulary.contribution_equation_typed written compiled member
    exact (check_sides_iff language _ _ _ object.1 object.2).mpr
      ⟨typed.1.of_signature_inclusion types terms, typed.2.of_signature_inclusion types terms⟩

def prepare? (order : Order) (base : LanguageDef) (atoms : List Atom) : Option PresentedSpace := do
  let contributions ← parts atoms
  let language := assemble order base contributions
  if contributions.all (checkPart language) then some ⟨atoms, language⟩ else none

theorem prepare_with_carrier (order : Order) (base : LanguageDef) (atoms : List Atom)
    (types : GroundData.dataLanguage.types ⊆ base.types) (terms : GroundData.dataLanguage.terms ⊆ base.terms) :
    prepare? order base atoms = NativeVocabulary.present order base atoms := by
  cases found : parts atoms with
  | none => simp [prepare?, NativeVocabulary.present, found]
  | some contributions =>
    have checked : contributions.all (checkPart (assemble order base contributions)) = true := by
      apply List.all_eq_true.mpr
      intro part member
      obtain ⟨written, _, compiled⟩ := Mettapedia.Data.List.option_mapM_origin contribution
        (atoms.map Atoms.content) _ found _ member
      exact check_native_part (assemble order base contributions) types terms written compiled
    unfold prepare? NativeVocabulary.present
    rw [found]
    change (if contributions.all (checkPart (assemble order base contributions)) = true then
      some (⟨atoms, assemble order base contributions⟩ : PresentedSpace) else none) =
        some (⟨atoms, assemble order base contributions⟩ : PresentedSpace)
    rw [if_pos checked]

theorem prepared_declarations_typed (order : Order) (base : LanguageDef) (atoms : List Atom)
    {prepared : PresentedSpace} (accepted : prepare? order base atoms = some prepared) :
    (∀ r ∈ prepared.language.rewrites, r ∉ base.rewrites →
      AtomSides prepared.language r.typeContext r.left r.right) ∧
    (∀ e ∈ prepared.language.equations, e ∉ base.equations →
      AtomSides prepared.language e.typeContext e.left e.right) := by
  unfold prepare? at accepted
  cases found : parts atoms with
  | none => simp [found] at accepted
  | some contributions =>
    rw [found] at accepted
    change (if contributions.all (checkPart (assemble order base contributions)) = true then
      some ⟨atoms, assemble order base contributions⟩ else none) = some prepared at accepted
    split at accepted
    · rename_i checked
      cases accepted
      constructor
      · intro r member notBase
        have contributed : r ∈ contributions.flatMap Contribution.rewrites := by
          cases order
          · exact (List.mem_append.mp member).resolve_right notBase
          · exact (List.mem_append.mp member).resolve_left notBase
        obtain ⟨part, present, fires⟩ := List.mem_flatMap.mp contributed
        exact (check_part_sound (List.all_eq_true.mp checked _ present)).1 _ fires
      · intro e member notBase
        have contributed : e ∈ contributions.flatMap Contribution.equations :=
          (List.mem_append.mp member).resolve_left notBase
        obtain ⟨part, present, holds⟩ := List.mem_flatMap.mp contributed
        exact (check_part_sound (List.all_eq_true.mp checked _ present)).2 _ holds
    · cases accepted

section Controls

private def authored : Atom := (Content.definition
  (.expression [.symbol "add", .var "x", .grounded (.int 3)]) (.var "x")).syntax

/-- Native typing does not discard an occurrence just because its
generated label coincides with another occurrence's label. -/
theorem repeated_grounded_definitions_are_checked :
    ∃ space, prepare? .back GroundData.dataLanguage [authored, authored] = some space ∧
      space.language.rewrites.length = 2 ∧ space.language.validate ≠ [] := by
  rw [prepare_with_carrier _ _ _ (List.Subset.refl _) (List.Subset.refl _)]
  refine ⟨_, rfl, rfl, ?_⟩
  intro ordinaryValid
  have distinct := LanguageDef.rewriteNames_nodup_of_validate_eq_nil _ ordinaryValid
  change (["space definition", "space definition"] : List String).Nodup at distinct
  simp at distinct

theorem dropped_carrier_cannot_check_native_definition :
    (prepare? .back {GroundData.dataLanguage with types := [], terms := []} [authored]).isNone = true := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.NativeValidation
