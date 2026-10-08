import Mettapedia.GSLT.LanguageDef.ModuleFormat.Linking

/-!
# Qualified exports and composition with proof declarations

Qualification in this catalog is the pair of declared module name and export
name. It preserves opaque specifications and source order. Dependency
references and native binding authority use their own interfaces.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.OSLF.MeTTaIL.Syntax

structure QualifiedExport where
  owner : String
  name : String
  spec : Value
  deriving Repr, DecidableEq

def qualify (owner : String) (entry : Export) : QualifiedExport :=
  ⟨owner, entry.name, entry.spec⟩

def qualifiedExports {limits : Limits} (catalog : Catalog limits) : List QualifiedExport :=
  catalog.val.flatMap fun module => module.val.exports.map (qualify module.val.name)

/-- No export appears without an authored module and an authored export
occurrence, and every authored occurrence appears with its full payload. -/
theorem mem_qualifiedExports_iff {limits : Limits} (catalog : Catalog limits)
    (entry : QualifiedExport) :
    entry ∈ qualifiedExports catalog ↔
      ∃ module ∈ catalog.val, ∃ original ∈ module.val.exports,
        qualify module.val.name original = entry := by
  simp only [qualifiedExports, List.mem_flatMap, List.mem_map]

/-- Module and export admission jointly make every qualified key unique. -/
theorem qualified_key_unique {limits : Limits} (catalog : Catalog limits)
    (first second : QualifiedExport) (firstIn : first ∈ qualifiedExports catalog)
    (secondIn : second ∈ qualifiedExports catalog)
    (ownerEqual : first.owner = second.owner) (nameEqual : first.name = second.name) :
    first = second := by
  rcases (mem_qualifiedExports_iff catalog first).mp firstIn with
    ⟨firstModule, firstMember, firstExport, firstExportIn, rfl⟩
  rcases (mem_qualifiedExports_iff catalog second).mp secondIn with
    ⟨secondModule, secondMember, secondExport, secondExportIn, rfl⟩
  have moduleEqual := List.inj_on_of_nodup_map catalog.property
    firstMember secondMember ownerEqual
  subst secondModule
  have exportEqual := List.inj_on_of_nodup_map
    firstModule.property.2.2.2.2.2.2.2 firstExportIn secondExportIn nameEqual
  subst secondExport
  rfl

def lookupExport? {limits : Limits} (catalog : Catalog limits)
    (owner name : String) : Option QualifiedExport :=
  (qualifiedExports catalog).find? fun entry => decide (entry.owner = owner ∧ entry.name = name)

theorem lookupExport_sound {limits : Limits} (catalog : Catalog limits)
    (owner name : String) (entry : QualifiedExport)
    (found : lookupExport? catalog owner name = some entry) :
    entry ∈ qualifiedExports catalog ∧ entry.owner = owner ∧ entry.name = name := by
  unfold lookupExport? at found
  have member := List.mem_of_find?_eq_some found
  have matched := List.find?_some found
  exact ⟨member, of_decide_eq_true matched⟩

/-- Exact lookup: presence of an authored qualified export suffices, and a
successful lookup cannot invent or silently replace its specification. -/
theorem lookupExport_eq_some_iff {limits : Limits} (catalog : Catalog limits)
    (owner name : String) (entry : QualifiedExport) :
    lookupExport? catalog owner name = some entry ↔
      entry ∈ qualifiedExports catalog ∧ entry.owner = owner ∧ entry.name = name := by
  constructor
  · exact lookupExport_sound catalog owner name entry
  · rintro ⟨member, ownerEqual, nameEqual⟩
    have available : (lookupExport? catalog owner name).isSome := by
      simp only [lookupExport?, List.find?_isSome, decide_eq_true_eq]
      exact ⟨entry, member, ownerEqual, nameEqual⟩
    cases found : lookupExport? catalog owner name with
    | none => simp [found] at available
    | some selected =>
        have correct := lookupExport_sound catalog owner name selected found
        have equal := qualified_key_unique catalog selected entry correct.1 member
          (correct.2.1.trans ownerEqual.symm) (correct.2.2.trans nameEqual.symm)
        rw [← equal]

/-- Successful catalog assembly preserves the exact ordered concatenation of
qualified exports, including their specification payloads. -/
theorem qualifiedExports_merge {limits : Limits} (first second merged : Catalog limits)
    (assembled : (catalogSystem limits).merge first second = some merged) :
    qualifiedExports merged = qualifiedExports first ++ qualifiedExports second := by
  change admitCatalog? limits (first.val ++ second.val) = some merged at assembled
  unfold admitCatalog? at assembled
  split at assembled
  · cases assembled
    simp [qualifiedExports, List.flatMap_append]
  · contradiction

/-- A concrete use of the existing layer product: structured module catalogs
and the established proof-calculus authoring language share a term-language
base while retaining separate payloads and their complete authored theories. -/
def moduleCalculusLayer (limits : Limits) : CompositionalLayer LanguageDef :=
  (catalogLayer LanguageDef limits).product calculusLayer

/-- Canonical mixed quotation recovers both complete components. -/
theorem moduleCalculus_roundtrip (limits : Limits) (language : LanguageDef)
    (catalog : Catalog limits) (calculus : ProofCalculus) :
    (moduleCalculusLayer limits).elaborate language
        ((moduleCalculusLayer limits).quote language (catalog, calculus)) =
      some (catalog, calculus) :=
  (moduleCalculusLayer limits).elaborate_quote language (catalog, calculus)

/-- Module-only authoring supplies precisely the authored empty calculus;
it cannot fabricate proof declarations from export spelling or payload data. -/
theorem moduleCalculus_modules_only (limits : Limits) (language : LanguageDef)
    (source : (catalogSystem limits).authoring.theory.Term) :
    (moduleCalculusLayer limits).elaborate language [Sum.inl source] =
      (elaborateCatalog? limits source).map fun catalog => (catalog, ProofCalculus.empty) :=
  (catalogLayer LanguageDef limits).product_elaborates_left_only calculusLayer language source

end Mettapedia.GSLT.LanguageDef.ModuleFormat
