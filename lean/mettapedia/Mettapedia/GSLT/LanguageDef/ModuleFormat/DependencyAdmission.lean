import Mettapedia.GSLT.LanguageDef.ModuleFormat.Exports

/-!
# Snapshot-dependent module coGSLT admission

The fibre over a registry snapshot contains only modules whose dependencies
are available in that snapshot. Changing the snapshot changes admission;
the envelope decoder and every export payload remain the same. Availability
means checked reference/commitment agreement, not cryptographic authentication
or export-language semantic admission.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition

abbrev AvailableModule {limits : Limits} (snapshot : Snapshot limits) :=
  { declaration : Module limits // DependenciesAvailable snapshot declaration }

def decodeAvailable? {limits : Limits} (snapshot : Snapshot limits) (value : Value) :
    Option (AvailableModule snapshot) := do
  let declaration ← decode? limits value
  if available : DependenciesAvailable snapshot declaration then
    some ⟨declaration, available⟩ else none

@[simp] theorem decodeAvailable_encode {limits : Limits} (snapshot : Snapshot limits)
    (declaration : AvailableModule snapshot) :
    decodeAvailable? snapshot (encodeRaw declaration.val.val) = some declaration := by
  simp [decodeAvailable?, declaration.property]

/-- Context admission retains every envelope field; its additional premise is
exactly dependency availability in the selected snapshot. -/
theorem decodeAvailable_some_iff {limits : Limits} (snapshot : Snapshot limits)
    (value : Value) (declaration : AvailableModule snapshot) :
    decodeAvailable? snapshot value = some declaration ↔
      decode? limits value = some declaration.val := by
  unfold decodeAvailable?
  cases decoded : decode? limits value with
  | none => simp
  | some parsed =>
      by_cases available : DependenciesAvailable snapshot parsed
      · simp [available]
        constructor
        · intro equal
          exact congrArg Subtype.val equal
        · intro equal
          exact Subtype.ext equal
      · simp [available]
        intro equal
        subst parsed
        exact available declaration.property

def elaborateAvailable? {limits : Limits} (snapshot : Snapshot limits)
    (document : Document) : Option (List (AvailableModule snapshot)) :=
  document.values.mapM (decodeAvailable? snapshot)

def quoteAvailable {limits : Limits} (snapshot : Snapshot limits)
    (declarations : List (AvailableModule snapshot)) : Document :=
  .bundle ((declarations.map fun declaration => encodeRaw declaration.val.val).map .declaration)

/-- Dependency-aware authoring reuses the declaration-document GSLT and its
composition equations. Both branches of an append use the same snapshot. -/
def availableSystem {limits : Limits} (snapshot : Snapshot limits) :
    GSLT.CompositionalElaboration (List (AvailableModule snapshot)) where
  authoring := ExactDeclarationCodec.documentCompositional Value
  elaboration := {
    elaborate := elaborateAvailable? snapshot
    quote := quoteAvailable snapshot
    elaborate_quote := by
      intro declarations
      unfold elaborateAvailable? quoteAvailable
      rw [DeclarationDocument.values_bundle_map]
      exact mapM_encode_decode (fun declaration => encodeRaw declaration.val.val)
        (decodeAvailable? snapshot) declarations
        (fun declaration _ => decodeAvailable_encode snapshot declaration)
    equation := by
      intro first second equivalent
      change first.values = second.values at equivalent
      unfold elaborateAvailable?
      rw [equivalent]
    rewrite := by
      intro first second impossible
      exact False.elim impossible }
  emptyPayload := []
  merge := fun first second => some (first ++ second)
  elaborate_empty := by
    change elaborateAvailable? snapshot (.bundle []) = some []
    simp [elaborateAvailable?, DeclarationDocument.values, DeclarationDocument.valuesList]
  elaborate_append := by
    intro first second
    change Document at first second
    change elaborateAvailable? snapshot (.bundle [first, second]) = _
    simp [elaborateAvailable?, DeclarationDocument.values, DeclarationDocument.valuesList]

/-- A genuinely indexed compositional layer: its admissible modules depend on
the base snapshot, while quotation retains their public module representation. -/
def availableLayer (limits : Limits) : CompositionalLayer (Snapshot limits) where
  Fiber := fun snapshot => List (AvailableModule snapshot)
  system := fun snapshot => availableSystem snapshot

/-- The stronger admitted fibre embeds in the ordinary envelope fibre without
changing decoded declarations or export specifications. -/
theorem decodeAvailable_forget {limits : Limits} (snapshot : Snapshot limits)
    (value : Value) (declaration : AvailableModule snapshot)
    (admitted : decodeAvailable? snapshot value = some declaration) :
    decode? limits value = some declaration.val :=
  (decodeAvailable_some_iff snapshot value declaration).mp admitted

/-- Decoded envelopes with unavailable dependencies cannot enter this fibre. -/
theorem decodeAvailable_rejects_unavailable {limits : Limits} (snapshot : Snapshot limits)
    (value : Value) (declaration : Module limits)
    (decoded : decode? limits value = some declaration)
    (unavailable : ¬ DependenciesAvailable snapshot declaration) :
    decodeAvailable? snapshot value = none := by
  simp [decodeAvailable?, decoded, unavailable]

/-- Dependency availability for a whole catalog, together with the catalog's
already checked unique module qualification names. -/
def CatalogAvailable {limits : Limits} (snapshot : Snapshot limits)
    (catalog : Catalog limits) : Prop :=
  ∀ declaration ∈ catalog.val, DependenciesAvailable snapshot declaration

instance {limits : Limits} (snapshot : Snapshot limits) (catalog : Catalog limits) :
    Decidable (CatalogAvailable snapshot catalog) := by
  unfold CatalogAvailable
  infer_instance

abbrev CheckedCatalog {limits : Limits} (snapshot : Snapshot limits) :=
  { catalog : Catalog limits // CatalogAvailable snapshot catalog }

def admitCheckedCatalog? {limits : Limits} (snapshot : Snapshot limits)
    (catalog : Catalog limits) : Option (CheckedCatalog snapshot) :=
  if available : CatalogAvailable snapshot catalog then some ⟨catalog, available⟩ else none

@[simp] theorem admitCheckedCatalog_val {limits : Limits} (snapshot : Snapshot limits)
    (catalog : CheckedCatalog snapshot) :
    admitCheckedCatalog? snapshot catalog.val = some catalog := by
  simp [admitCheckedCatalog?, catalog.property]

/-- One admission pipeline checks frame invariants, qualification uniqueness
and dependency availability, with no independently selectable bypass. -/
def elaborateCheckedCatalog? {limits : Limits} (snapshot : Snapshot limits)
    (document : Document) : Option (CheckedCatalog snapshot) :=
  (elaborateCatalog? limits document).bind (admitCheckedCatalog? snapshot)

/-- Exact dependency-aware elaboration of the existing catalog authoring GSLT. -/
def checkedCatalogElaboration {limits : Limits} (snapshot : Snapshot limits) :
    GSLT.ExactElaboration (catalogSystem limits).authoring.theory (CheckedCatalog snapshot) where
  elaborate := elaborateCheckedCatalog? snapshot
  quote := fun catalog => quoteModules limits catalog.val.val
  elaborate_quote := by
    intro catalog
    have quoted : elaborateCatalog? limits (quoteModules limits catalog.val.val) =
        some catalog.val := (catalogSystem limits).elaboration.elaborate_quote catalog.val
    simp [elaborateCheckedCatalog?, quoted]
  equation := by
    intro first second equivalent
    have congruent : elaborateCatalog? limits first = elaborateCatalog? limits second :=
      (catalogSystem limits).elaboration.equation equivalent
    simp only [elaborateCheckedCatalog?, congruent]
  rewrite := by
    intro first second impossible
    exact False.elim impossible

/-- Availability of an assembled catalog is equivalent to availability of
both components in the same snapshot, with no hidden new dependencies. -/
theorem catalogAvailable_merge_iff {limits : Limits} (snapshot : Snapshot limits)
    (first second merged : Catalog limits)
    (assembled : (catalogSystem limits).merge first second = some merged) :
    CatalogAvailable snapshot merged ↔
      CatalogAvailable snapshot first ∧ CatalogAvailable snapshot second := by
  have retained := catalog_merge_val limits first second merged assembled
  unfold CatalogAvailable
  rw [retained]
  constructor
  · intro available
    exact ⟨fun declaration member => available declaration (List.mem_append_left _ member),
      fun declaration member => available declaration (List.mem_append_right _ member)⟩
  · rintro ⟨left, right⟩ declaration member
    rcases List.mem_append.mp member with inLeft | inRight
    · exact left declaration inLeft
    · exact right declaration inRight

def mergeCheckedCatalog? {limits : Limits} (snapshot : Snapshot limits)
    (first second : CheckedCatalog snapshot) : Option (CheckedCatalog snapshot) :=
  ((catalogSystem limits).merge first.val second.val).bind (admitCheckedCatalog? snapshot)

/-- Dependency admission commutes with partial catalog assembly, including
namespace conflicts and unavailable dependencies on either side. -/
theorem admitCheckedCatalog_merge {limits : Limits} (snapshot : Snapshot limits)
    (first second : Catalog limits) :
    ((catalogSystem limits).merge first second).bind (admitCheckedCatalog? snapshot) =
      (admitCheckedCatalog? snapshot first).bind fun left =>
        (admitCheckedCatalog? snapshot second).bind fun right =>
          mergeCheckedCatalog? snapshot left right := by
  cases assembled : (catalogSystem limits).merge first second with
  | none =>
      by_cases left : CatalogAvailable snapshot first <;>
        by_cases right : CatalogAvailable snapshot second <;>
          simp [admitCheckedCatalog?, mergeCheckedCatalog?, left, right, assembled]
  | some merged =>
      have available := catalogAvailable_merge_iff snapshot first second merged assembled
      by_cases left : CatalogAvailable snapshot first <;>
        by_cases right : CatalogAvailable snapshot second <;>
          simp [admitCheckedCatalog?, mergeCheckedCatalog?, left, right, assembled, available] 

/-- The fully admitted catalog is itself a compositional coGSLT payload.
The partial monoid is again derived from authored equations, rather than an
independent merge selected after validation. -/
def checkedCatalogSystem {limits : Limits} (snapshot : Snapshot limits) :
    GSLT.CompositionalElaboration (CheckedCatalog snapshot) where
  authoring := (catalogSystem limits).authoring
  elaboration := checkedCatalogElaboration snapshot
  emptyPayload := ⟨(catalogSystem limits).emptyPayload, by
    simp [CatalogAvailable, catalogSystem]⟩
  merge := mergeCheckedCatalog? snapshot
  elaborate_empty := by
    have empty := (catalogSystem limits).elaborate_empty
    change elaborateCatalog? limits (catalogSystem limits).authoring.empty =
      some (catalogSystem limits).emptyPayload at empty
    change (elaborateCatalog? limits (catalogSystem limits).authoring.empty).bind
      (admitCheckedCatalog? snapshot) = _
    rw [empty]
    simp [admitCheckedCatalog?, CatalogAvailable, catalogSystem]
  elaborate_append := by
    intro first second
    change Document at first second
    have law : elaborateCatalog? limits (.bundle [first, second]) =
        (elaborateCatalog? limits first).bind fun left =>
          (elaborateCatalog? limits second).bind fun right =>
            (catalogSystem limits).merge left right :=
      (catalogSystem limits).elaborate_append first second
    change elaborateCheckedCatalog? snapshot (.bundle [first, second]) =
      (elaborateCheckedCatalog? snapshot first).bind fun left =>
        (elaborateCheckedCatalog? snapshot second).bind fun right =>
          mergeCheckedCatalog? snapshot left right
    unfold elaborateCheckedCatalog?
    rw [law]
    cases left : elaborateCatalog? limits first with
    | none => simp
    | some leftCatalog =>
        cases right : elaborateCatalog? limits second with
        | none => simp
        | some rightCatalog =>
            simpa only [left, right, Option.bind_some] using
              admitCheckedCatalog_merge snapshot leftCatalog rightCatalog

def checkedCatalogCompositionalLayer (limits : Limits) :
    CompositionalLayer (Snapshot limits) where
  Fiber := fun snapshot => CheckedCatalog snapshot
  system := checkedCatalogSystem

/-- The dependent coGSLT fibre with both catalog and snapshot admission,
obtained by forgetting only the additional compositional laws. -/
def checkedCatalogLayer (limits : Limits) : CoGSLTLayer (Snapshot limits) :=
  (checkedCatalogCompositionalLayer limits).toCoGSLTLayer

/-- Associativity preserves both kinds of admission and every rejection. -/
theorem checkedCatalog_assembly_assoc {limits : Limits} (snapshot : Snapshot limits)
    (first second third : CheckedCatalog snapshot) :
    (mergeCheckedCatalog? snapshot first second).bind
        (fun merged => mergeCheckedCatalog? snapshot merged third) =
      (mergeCheckedCatalog? snapshot second third).bind
        (fun merged => mergeCheckedCatalog? snapshot first merged) :=
  (checkedCatalogSystem snapshot).toPartialMonoid.op_assoc first second third

/-- A successful combined check retains the admitted catalog exactly,
including all namespaced export payloads. -/
theorem checkedCatalog_preserves_catalog {limits : Limits} (snapshot : Snapshot limits)
    (document : Document) (catalog : CheckedCatalog snapshot)
    (accepted : elaborateCheckedCatalog? snapshot document = some catalog) :
    elaborateCatalog? limits document = some catalog.val := by
  unfold elaborateCheckedCatalog? at accepted
  cases decoded : elaborateCatalog? limits document with
  | none => simp [decoded] at accepted
  | some original =>
      simp only [decoded, Option.bind_some] at accepted
      unfold admitCheckedCatalog? at accepted
      split at accepted
      · cases accepted
        rfl
      · contradiction

/-- Namespace rejection propagates through the combined coGSLT boundary. -/
theorem checkedCatalog_rejects_catalog_failure {limits : Limits} (snapshot : Snapshot limits)
    (document : Document) (rejected : elaborateCatalog? limits document = none) :
    elaborateCheckedCatalog? snapshot document = none := by
  simp [elaborateCheckedCatalog?, rejected]

/-- Checked modules and the existing calculus language compose over a common
context carrying both the registry snapshot and the term-language core. -/
def checkedModuleCalculusLayer (limits : Limits) :
    CompositionalLayer (Snapshot limits × Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) :=
  let modules : CompositionalLayer
      (Snapshot limits × Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) := {
    Fiber := fun context => CheckedCatalog context.1
    system := fun context => checkedCatalogSystem context.1 }
  let calculus : CompositionalLayer
      (Snapshot limits × Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) := {
    Fiber := fun context => calculusLayer.Fiber context.2
    system := fun context => calculusLayer.system context.2 }
  modules.product calculus

/-- Mixed quotation retains checked dependencies and qualification names as
well as all independently authored proof declarations. -/
theorem checkedModuleCalculus_roundtrip (limits : Limits)
    (snapshot : Snapshot limits) (language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef)
    (catalog : CheckedCatalog snapshot)
    (calculus : Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus) :
    (checkedModuleCalculusLayer limits).elaborate (snapshot, language)
      ((checkedModuleCalculusLayer limits).quote (snapshot, language) (catalog, calculus)) =
        some (catalog, calculus) :=
  (checkedModuleCalculusLayer limits).elaborate_quote (snapshot, language) (catalog, calculus)

end Mettapedia.GSLT.LanguageDef.ModuleFormat
