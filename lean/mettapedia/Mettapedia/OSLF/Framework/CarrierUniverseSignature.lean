import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Basic
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Per-carrier universe-code signature

The first syntactic layer of the Stay--Wells native type theory freely adds
two closed codes at every authored carrier `X`: `∗X` and `□X`.  This module
generates exactly that constructor signature.  The carrier-indexed typing
relation `::X` and its inference rules are a separate proof-calculus layer.

The generated language is a standalone signature sharing the source carrier
declarations.  It does not copy source constructors, equations, or rewrites;
combining those layers is an explicit gluing operation.  Generated labels
encode the carrier name reversibly, avoiding positional renumbering when an
unrelated carrier is appended.
-/

namespace Mettapedia.OSLF.Framework

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef

namespace CarrierUniverseSignature

/-- The two universe codes freely added at each authored carrier. -/
inductive Code where
  | star
  | box
deriving Repr, DecidableEq

instance : Fintype Code :=
  Fintype.ofList [.star, .box] (by
    intro code
    cases code <;> simp)

/-- Private wire tag for one universe-code family. -/
def Code.tag : Code → Char
  | .star => 's'
  | .box => 'b'

/-- Stable generated constructor name for one code at one carrier. -/
def label (code : Code) (carrier : String) : String :=
  String.ofList
    ('$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' :: 'u' :: ':' ::
      code.tag :: carrier.toList)

/-- Decode exactly the generated universe-code namespace. -/
def decode? (name : String) : Option (Code × String) :=
  match name.toList with
  | '$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' :: 'u' :: ':' :: 's' :: rest =>
      some (.star, String.ofList rest)
  | '$' :: 'o' :: 's' :: 'l' :: 'f' :: ':' :: 'u' :: ':' :: 'b' :: rest =>
      some (.box, String.ofList rest)
  | _ => none

@[simp]
theorem decode_label (code : Code) (carrier : String) :
    decode? (label code carrier) = some (code, carrier) := by
  cases code <;> simp [decode?, label, Code.tag]

/-- Successful decoding reconstructs the original generated label. -/
theorem label_of_decode_eq_some {name : String} {code : Code}
    {carrier : String} (decoded : decode? name = some (code, carrier)) :
    label code carrier = name := by
  unfold decode? at decoded
  split at decoded <;> try { simp at decoded }
  all_goals
    cases decoded
    rw [← String.ofList_toList (s := name)]
    simp_all [label, Code.tag]

/-- The code/carrier pair is recoverable from its generated label. -/
theorem label_pair_injective :
    Function.Injective
      (fun entry : Code × String => label entry.1 entry.2) := by
  intro first second equality
  have decoded := congrArg decode? equality
  simpa using decoded

theorem label_injective (code : Code) :
    Function.Injective (label code) := by
  intro first second equality
  have pairsEqual := label_pair_injective (show
    label (code, first).1 (code, first).2 =
      label (code, second).1 (code, second).2 from equality)
  exact congrArg Prod.snd pairsEqual

/-- The two codes at one carrier are observably distinct. -/
theorem star_label_ne_box_label (first second : String) :
    label .star first ≠ label .box second := by
  intro equality
  have decoded := congrArg decode? equality
  simp at decoded

/-- Closed declaration of one universe code at one carrier. -/
def rule (code : Code) (carrier : String) : GrammarRule where
  label := label code carrier
  category := carrier
  params := []
  syntaxPattern := []

/-- Generated declarations in deterministic carrier-major order.  Keeping
the two codes for one carrier adjacent makes append-only carrier generation
an exact list append rather than an insertion into an earlier artifact. -/
def termsFor (carriers : List String) : List GrammarRule :=
  carriers.flatMap fun carrier => [rule .star carrier, rule .box carrier]

/-- Generated universe-code declarations for all authored carriers. -/
def terms (source : ValidatedLanguageDef) : List GrammarRule :=
  termsFor source.language.typeNames

@[simp]
theorem termsFor_append (first second : List String) :
    termsFor (first ++ second) = termsFor first ++ termsFor second := by
  simp [termsFor]

@[simp]
theorem length_termsFor (carriers : List String) :
    (termsFor carriers).length = 2 * carriers.length := by
  simp [termsFor]
  omega

@[simp]
theorem length_terms (source : ValidatedLanguageDef) :
    (terms source).length = 2 * source.language.types.length := by
  simp [terms, LanguageDef.typeNames]

theorem termLabelsFor (carriers : List String) :
    (termsFor carriers).map (·.label) =
      carriers.flatMap fun carrier =>
        [label .star carrier, label .box carrier] := by
  unfold termsFor
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro carrier _
  simp [rule]

/-- Distinct carrier names generate a duplicate-free constructor namespace. -/
theorem termLabelsFor_nodup (carriers : List String)
    (carrierNamesNodup : carriers.Nodup) :
    ((termsFor carriers).map (·.label)).Nodup := by
  rw [termLabelsFor]
  apply (List.nodup_flatMap).2
  constructor
  · intro carrier _
    simpa using star_label_ne_box_label carrier carrier
  · refine List.Nodup.pairwise_of_forall_ne carrierNamesNodup ?_
    intro first _ second _ distinct
    change List.Disjoint
      [label Code.star first, label Code.box first]
      [label Code.star second, label Code.box second]
    rw [List.disjoint_left]
    intro generated firstMembership secondMembership
    have firstCases : generated = label .star first ∨
        generated = label .box first := by
      simpa using firstMembership
    have secondCases : generated = label .star second ∨
        generated = label .box second := by
      simpa using secondMembership
    rcases firstCases with rfl | rfl
    · rcases secondCases with equality | equality
      · exact distinct (label_injective .star equality)
      · exact star_label_ne_box_label first second equality
    · rcases secondCases with equality | equality
      · exact star_label_ne_box_label second first equality.symm
      · exact distinct (label_injective .box equality)

theorem termLabels (source : ValidatedLanguageDef) :
    (terms source).map (·.label) =
      source.language.typeNames.flatMap fun carrier =>
        [label .star carrier, label .box carrier] := by
  exact termLabelsFor source.language.typeNames

theorem termLabels_nodup (source : ValidatedLanguageDef) :
    ((terms source).map (·.label)).Nodup := by
  have carrierNamesNodup : source.language.typeNames.Nodup :=
    LanguageDef.typeNames_nodup_of_validate_eq_nil
      source.language source.valid
  exact termLabelsFor_nodup source.language.typeNames carrierNamesNodup

/-- Standalone per-carrier universe-code signature. -/
def language (source : ValidatedLanguageDef) : LanguageDef :=
  { name := "$oslf:carrier-universe:" ++ source.language.name
    types := source.language.types
    terms := terms source
    equations := []
    rewrites := [] }

theorem language_validate (source : ValidatedLanguageDef) :
    (language source).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly
  · rfl
  · rfl
  · change source.language.typeNames.Nodup
    exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      source.language source.valid
  · simpa [language] using termLabels_nodup source
  · intro term membership
    change term.category ∈ source.language.typeNames
    change term ∈ terms source at membership
    unfold terms termsFor at membership
    obtain ⟨carrier, carrierMembership, localMembership⟩ :=
      List.mem_flatMap.mp membership
    have localCases : term = rule .star carrier ∨
        term = rule .box carrier := by
      simpa using localMembership
    rcases localCases with rfl | rfl <;>
      simpa [rule] using carrierMembership
  · intro term membership parameter parameterMembership
      typeName typeNameMembership
    change term ∈ terms source at membership
    unfold terms termsFor at membership
    obtain ⟨carrier, _, localMembership⟩ := List.mem_flatMap.mp membership
    have localCases : term = rule .star carrier ∨
        term = rule .box carrier := by
      simpa using localMembership
    rcases localCases with rfl | rfl <;>
      simp [rule] at parameterMembership
  · intro term membership
    change term ∈ terms source at membership
    unfold terms termsFor at membership
    obtain ⟨carrier, _, localMembership⟩ := List.mem_flatMap.mp membership
    have localCases : term = rule .star carrier ∨
        term = rule .box carrier := by
      simpa using localMembership
    rcases localCases with rfl | rfl <;> exact Or.inl rfl

/-- Validated standalone universe-code language. -/
def validatedLanguage (source : ValidatedLanguageDef) : ValidatedLanguageDef :=
  ⟨language source, language_validate source⟩

/-! ## Positive and negative controls -/

namespace Canary

private def firstType : TypeDecl :=
  TypeDecl.plain "carrier-universe-canary:First"

private def secondType : TypeDecl :=
  TypeDecl.plain "carrier-universe-canary:Second"

private def sourceLanguage : LanguageDef :=
  { name := "carrier-universe-canary"
    types := [firstType, secondType]
    terms := []
    equations := []
    rewrites := [] }

private theorem sourceLanguage_valid : sourceLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [sourceLanguage, LanguageDef.typeNames, firstType, secondType,
      TypeDecl.plain]

private def source : ValidatedLanguageDef :=
  ⟨sourceLanguage, sourceLanguage_valid⟩

/-- Two source carriers generate exactly four code declarations. -/
theorem two_carriers_generate_four_codes :
    (language source).terms.length = 4 := by
  decide

/-- A generated code remembers its carrier; distinct source carriers cannot
silently share the same star code. -/
theorem distinct_carriers_have_distinct_star_codes :
    label .star firstType.name ≠ label .star secondType.name := by
  apply ne_of_apply_ne decode?
  simp [firstType, secondType, TypeDecl.plain]

/-- The star and box codes remain distinct even at the same carrier. -/
theorem one_carrier_has_two_distinct_codes :
    label .star firstType.name ≠ label .box firstType.name :=
  star_label_ne_box_label _ _

end Canary

#print axioms decode_label
#print axioms label_of_decode_eq_some
#print axioms label_pair_injective
#print axioms termsFor_append
#print axioms length_termsFor
#print axioms termLabels_nodup
#print axioms language_validate
#print axioms Canary.two_carriers_generate_four_codes
#print axioms Canary.distinct_carriers_have_distinct_star_codes
#print axioms Canary.one_carrier_has_two_distinct_codes

end CarrierUniverseSignature

end Mettapedia.OSLF.Framework
