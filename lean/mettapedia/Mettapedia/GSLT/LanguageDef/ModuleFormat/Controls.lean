import Mettapedia.GSLT.LanguageDef.ModuleFormat

/-!
# Module-format controls

These examples exercise envelope admission, ordered payload retention,
reference normalization, dependency linking, qualification and mixed coGSLT
composition. Opaque specifications intentionally include non-language values:
module admission alone must not certify an export's language schema.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.Controls

open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.OSLF.MeTTaIL.Syntax

def commitment : List UInt8 := List.replicate 32 66

def payload : Value := .record [
  ("mettail", .string "language/2"), ("name", .string "Left"),
  ("types", .list [.string "Expr"]),
  ("opaque", .list [.integer (-17), .floatBits 4607182418800017408,
    .boolean true, .nil, .bytes [0, 255]])]

def baseRaw : RawModule := ⟨"Base", [], [⟨"Expr", .string "retained base payload"⟩]⟩
def pairRaw : RawModule := ⟨"Pair", [⟨.registry "base", commitment⟩],
  [⟨"Left", payload⟩, ⟨"Right", .list [.integer 42, .string "unchanged"]⟩]⟩

def baseModule : Module upstreamLimits := ⟨baseRaw, by decide⟩
def pairModule : Module upstreamLimits := ⟨pairRaw, by decide⟩
def pairCatalog : Catalog upstreamLimits := ⟨[pairModule], by decide⟩
def baseCatalog : Catalog upstreamLimits := ⟨[baseModule], by decide⟩
def combinedCatalog : Catalog upstreamLimits := ⟨[pairModule, baseModule], by decide⟩

def snapshot : Snapshot upstreamLimits :=
  ⟨[⟨.registry "base", commitment, baseModule⟩], by decide⟩

def replaceField (value : Value) (key : String) (replacement : Value) : Value :=
  match value with
  | .record fields => .record (fields.map fun field =>
      if field.1 = key then (key, replacement) else field)
  | other => other

def addField (value : Value) (key : String) (entry : Value) : Value :=
  match value with
  | .record fields => .record (fields ++ [(key, entry)])
  | other => other

def removeField (value : Value) (key : String) : Value :=
  match value with
  | .record fields => .record (fields.filter fun field => field.1 != key)
  | other => other

def dependencyValue (uri : String) (bytes : List UInt8) : Value :=
  .record [("commitment", .bytes bytes), ("uri", .string uri)]

def pairValue : Value := encodeRaw pairRaw

def fixtures : List (String × Value × Bool) := [
  ("ordered opaque payloads", pairValue, true),
  ("no dependencies", encodeRaw baseRaw, true),
  ("bare file path", replaceField pairValue "dependencies"
    (.list [dependencyValue "base.mettail" commitment]), true),
  ("explicit file path", replaceField pairValue "dependencies"
    (.list [dependencyValue "file:base.mettail" commitment]), true),
  ("prefix with internal colon", replaceField pairValue "dependencies"
    (.list [dependencyValue "rho:a:b" commitment]), true),
  ("opaque non-language export", encodeRaw {pairRaw with exports := [⟨"Left", .integer 17⟩]}, true),
  ("schema mismatch", replaceField pairValue "mettail" (.string "module/2"), false),
  ("schema wrong carrier", replaceField pairValue "mettail" (.integer 1), false),
  ("unknown envelope field", addField pairValue "surprise" .nil, false),
  ("missing envelope field", removeField pairValue "dependencies", false),
  ("empty module name", encodeRaw {pairRaw with name := ""}, false),
  ("digit first module name", encodeRaw {pairRaw with name := "1Pair"}, false),
  ("non-ASCII module name", encodeRaw {pairRaw with name := "Páir"}, false),
  ("empty exports", encodeRaw {pairRaw with exports := []}, false),
  ("duplicate export", encodeRaw {pairRaw with exports := [⟨"Left", payload⟩, ⟨"Left", .nil⟩]}, false),
  ("invalid export name", encodeRaw {pairRaw with exports := [⟨"Left-x", payload⟩]}, false),
  ("commitment too short", replaceField pairValue "dependencies"
    (.list [dependencyValue "rho:base" (List.replicate 31 66)]), false),
  ("commitment too long", replaceField pairValue "dependencies"
    (.list [dependencyValue "rho:base" (List.replicate 33 66)]), false),
  ("empty registry reference", replaceField pairValue "dependencies"
    (.list [dependencyValue "rho:" commitment]), false),
  ("unsupported reference scheme", replaceField pairValue "dependencies"
    (.list [dependencyValue "https:base" commitment]), false),
  ("duplicate normalized file reference", replaceField pairValue "dependencies"
    (.list [dependencyValue "base.mettail" commitment,
      dependencyValue "file:base.mettail" commitment]), false)]

/-- A single kernel-checked table covers independently specified expectations. -/
theorem fixtures_pass :
    fixtures.all (fun fixture =>
      (decode? upstreamLimits fixture.2.1).isSome == fixture.2.2) = true := by decide

theorem duplicate_record_occurrence_rejected :
    decode? upstreamLimits (addField pairValue "name" (.string "Pair")) = none := by decide

theorem collection_policy_enforced : decode? ⟨0, 1⟩ pairValue = none := by decide

theorem reference_aliases_normalize :
    ModuleRef.parse? "base.mettail" = ModuleRef.parse? "file:base.mettail" := by decide

theorem exact_envelope_roundtrip :
    decode? upstreamLimits pairValue = some pairModule := by decide

theorem exact_ordered_exports :
    (decode? upstreamLimits pairValue).map (fun module => module.val.exports) =
      some [⟨"Left", payload⟩, ⟨"Right", .list [.integer 42, .string "unchanged"]⟩] := by decide

theorem compatible_assembly :
    (catalogSystem upstreamLimits).merge pairCatalog baseCatalog = some combinedCatalog := by decide

theorem conflicting_assembly_rejected :
    (catalogSystem upstreamLimits).merge pairCatalog pairCatalog = none := by decide

theorem linked_dependency_matches :
    (linkDependencies? snapshot pairModule).map (fun entries => entries.map RegistryEntry.declaration) =
      some [baseModule] := by decide

theorem changed_commitment_rejected :
    resolve? snapshot ⟨.registry "base", List.replicate 32 67⟩ = none := by decide

theorem invented_reference_rejected :
    resolve? snapshot ⟨.registry "other", commitment⟩ = none := by decide

theorem exact_export_lookup :
    lookupExport? combinedCatalog "Pair" "Left" = some ⟨"Pair", "Left", payload⟩ := by decide

theorem constructed_spelling_grants_nothing :
    lookupExport? combinedCatalog "rho:Pair" "Left" = none := by decide

theorem malformed_declaration_rejects_bundle :
    elaborateDocument? upstreamLimits (.bundle [.declaration pairValue, .declaration .nil]) =
      none := by
  apply append_rejected_right
  simp [elaborateDocument?, DeclarationDocument.values, decode?, decodeRaw?, Value.record?]

def termLanguage : LanguageDef := {
  name := "Core"
  types := ["Expr"]
  terms := []
  equations := []
  rewrites := [] }

def proofCalculus : ProofCalculus := { judgments := [⟨"Proves", 2⟩] }

/-- This uses the existing proof-calculus layer alongside the new module
layer, with a nonempty proof declaration and nonempty module catalog. -/
theorem mixed_layer_roundtrip :
    (moduleCalculusLayer upstreamLimits).elaborate termLanguage
        ((moduleCalculusLayer upstreamLimits).quote termLanguage (pairCatalog, proofCalculus)) =
      some (pairCatalog, proofCalculus) :=
  moduleCalculus_roundtrip upstreamLimits termLanguage pairCatalog proofCalculus

/-- Opaque export content still supplies no
proof declarations through module-only composition. -/
theorem module_data_does_not_add_proofs :
    (moduleCalculusLayer upstreamLimits).elaborate termLanguage
      [Sum.inl (quoteModules upstreamLimits [pairModule])] =
      some (pairCatalog, ProofCalculus.empty) := by
  have quoted : elaborateCatalog? upstreamLimits
      (quoteModules upstreamLimits [pairModule]) = some pairCatalog :=
    (catalogSystem upstreamLimits).elaboration.elaborate_quote pairCatalog
  exact (moduleCalculus_modules_only upstreamLimits termLanguage
    (quoteModules upstreamLimits [pairModule])).trans (by rw [quoted]; rfl)

def otherRaw : RawModule := ⟨"Other", [], [⟨"Left", .string "other payload"⟩]⟩
def otherModule : Module upstreamLimits := ⟨otherRaw, by decide⟩
def repeatedExportCatalog : Catalog upstreamLimits := ⟨[pairModule, otherModule], by decide⟩

/-- Equal export spellings in distinct module namespaces are permitted and
resolve to their own complete specifications. -/
theorem repeated_export_spelling_is_qualified :
    lookupExport? repeatedExportCatalog "Pair" "Left" = some ⟨"Pair", "Left", payload⟩ ∧
    lookupExport? repeatedExportCatalog "Other" "Left" =
      some ⟨"Other", "Left", .string "other payload"⟩ := by decide

def changedModule : Module upstreamLimits :=
  ⟨{ pairRaw with exports := [⟨"Left", .string "changed payload"⟩] }, by decide⟩
def changedCatalog : Catalog upstreamLimits := ⟨[changedModule], by decide⟩

theorem retained_name_does_not_preserve_payload :
    lookupExport? changedCatalog "Pair" "Left" ≠ lookupExport? pairCatalog "Pair" "Left" := by decide

def emptySnapshot : Snapshot upstreamLimits := ⟨[], by decide⟩

def availablePair : AvailableModule snapshot := ⟨pairModule, by decide⟩

theorem snapshot_admission_accepts :
    decodeAvailable? snapshot pairValue = some availablePair := by decide

theorem snapshot_admission_rejects_missing :
    decodeAvailable? emptySnapshot pairValue = none := by decide

theorem snapshot_layer_roundtrip :
    (availableLayer upstreamLimits).elaborate snapshot
        ((availableLayer upstreamLimits).quote snapshot [availablePair]) = some [availablePair] :=
  (availableLayer upstreamLimits).elaborate_quote snapshot [availablePair]

theorem missing_dependencies_reject_authored_module :
    elaborateAvailable? emptySnapshot (.declaration pairValue) = none := by
  simp [elaborateAvailable?, DeclarationDocument.values, snapshot_admission_rejects_missing]

def checkedPair : CheckedCatalog snapshot := ⟨pairCatalog, by decide⟩

theorem combined_checks_roundtrip :
    (checkedCatalogLayer upstreamLimits).elaborate snapshot
        ((checkedCatalogLayer upstreamLimits).quote snapshot checkedPair) = some checkedPair :=
  (checkedCatalogLayer upstreamLimits).elaborate_quote snapshot checkedPair

theorem combined_checks_reject_missing_dependencies :
    elaborateCheckedCatalog? emptySnapshot (quoteModules upstreamLimits [pairModule]) = none := by
  have quoted : elaborateCatalog? upstreamLimits
      (quoteModules upstreamLimits [pairModule]) = some pairCatalog :=
    (catalogSystem upstreamLimits).elaboration.elaborate_quote pairCatalog
  simp only [elaborateCheckedCatalog?, quoted, Option.bind_some]
  have missing : ¬ CatalogAvailable emptySnapshot pairCatalog := by decide
  simp [admitCheckedCatalog?, missing]

theorem combined_checks_reject_module_name_collision :
    elaborateCheckedCatalog? snapshot (quoteModules upstreamLimits [pairModule, pairModule]) =
      none := by
  apply checkedCatalog_rejects_catalog_failure
  simp only [elaborateCatalog?, elaborate_quoteModules, Option.bind_some]
  have collision : ¬ distinctModules upstreamLimits [pairModule, pairModule] := by decide
  simp [admitCatalog?, collision]

theorem fully_checked_mixed_layer_roundtrip :
    (checkedModuleCalculusLayer upstreamLimits).elaborate (snapshot, termLanguage)
        ((checkedModuleCalculusLayer upstreamLimits).quote
          (snapshot, termLanguage) (checkedPair, proofCalculus)) =
      some (checkedPair, proofCalculus) :=
  checkedModuleCalculus_roundtrip upstreamLimits snapshot termLanguage checkedPair proofCalculus

def checkedBase : CheckedCatalog snapshot := ⟨baseCatalog, by decide⟩
def checkedCombined : CheckedCatalog snapshot := ⟨combinedCatalog, by decide⟩

theorem fully_checked_compatible_assembly :
    mergeCheckedCatalog? snapshot checkedPair checkedBase = some checkedCombined := by decide

theorem fully_checked_conflict_rejected :
    mergeCheckedCatalog? snapshot checkedPair checkedPair = none := by decide

end Mettapedia.GSLT.LanguageDef.ModuleFormat.Controls
