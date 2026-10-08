import Mettapedia.GSLT.LanguageDef.ModuleFormat.Authoring

/-!
# Compatible module-name assembly

A catalog uses declared module names as its local qualification policy.
Registry references remain a separate dependency-resolution identity. Catalog
assembly rejects repeated module names; it never silently overrides exports.
This policy is additional to the upstream single-envelope decoder.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension

def distinctModules (limits : Limits) (modules : List (Module limits)) : Prop :=
  (modules.map fun module => module.val.name).Nodup

instance (limits : Limits) (modules : List (Module limits)) :
    Decidable (distinctModules limits modules) := by
  unfold distinctModules
  infer_instance

abbrev Catalog (limits : Limits) :=
  { modules : List (Module limits) // distinctModules limits modules }

def admitCatalog? (limits : Limits) (modules : List (Module limits)) :
    Option (Catalog limits) :=
  if accepted : distinctModules limits modules then some ⟨modules, accepted⟩ else none

@[simp] theorem admitCatalog_val (limits : Limits) (catalog : Catalog limits) :
    admitCatalog? limits catalog.val = some catalog := by
  simp [admitCatalog?, catalog.property]

/-- Catalog admission preserves the complete ordered module list. -/
theorem admitCatalog_some_val (limits : Limits) (modules : List (Module limits))
    (catalog : Catalog limits) (admitted : admitCatalog? limits modules = some catalog) :
    catalog.val = modules := by
  unfold admitCatalog? at admitted
  split at admitted
  · cases admitted
    rfl
  · contradiction

/-- A conflict cannot be repaired by adding more modules to the catalog. -/
theorem distinct_append_iff (limits : Limits) (first second : List (Module limits)) :
    distinctModules limits (first ++ second) ↔
      distinctModules limits first ∧ distinctModules limits second ∧
        ∀ left ∈ first, ∀ right ∈ second, left.val.name ≠ right.val.name := by
  rw [distinctModules, List.map_append, List.nodup_append]
  constructor
  · rintro ⟨left, right, separate⟩
    exact ⟨left, right, fun firstMember firstIn secondMember secondIn =>
      separate firstMember.val.name (List.mem_map.mpr ⟨firstMember, firstIn, rfl⟩)
        secondMember.val.name (List.mem_map.mpr ⟨secondMember, secondIn, rfl⟩)⟩
  · rintro ⟨left, right, separate⟩
    refine ⟨left, right, ?_⟩
    intro firstName firstIn secondName secondIn
    rcases List.mem_map.mp firstIn with ⟨firstMember, firstMemberIn, rfl⟩
    rcases List.mem_map.mp secondIn with ⟨secondMember, secondMemberIn, rfl⟩
    exact separate firstMember firstMemberIn secondMember secondMemberIn

/-- Independent admission of both sides followed by merge agrees exactly
with admission of their concatenation, including all failure cases. -/
theorem admitCatalog_append (limits : Limits) (first second : List (Module limits)) :
    admitCatalog? limits (first ++ second) =
      (admitCatalog? limits first).bind fun left =>
        (admitCatalog? limits second).bind fun right =>
          admitCatalog? limits (left.val ++ right.val) := by
  by_cases left : distinctModules limits first
  · by_cases right : distinctModules limits second
    · simp [admitCatalog?, left, right]
    · have failed : ¬ distinctModules limits (first ++ second) := fun admitted =>
        right ((distinct_append_iff limits first second).mp admitted).2.1
      simp [admitCatalog?, right, failed]
  · have failed : ¬ distinctModules limits (first ++ second) := fun admitted =>
      left ((distinct_append_iff limits first second).mp admitted).1
    simp [admitCatalog?, left, failed]

def elaborateCatalog? (limits : Limits) (document : Document) : Option (Catalog limits) :=
  (elaborateDocument? limits document).bind (admitCatalog? limits)

/-- The catalog coGSLT derives its partial associative assembly from the same
bundle equations as plain module authoring. Failed overlap admission remains
visible in the elaborator and therefore in every staged consumer. -/
def catalogSystem (limits : Limits) : GSLT.CompositionalElaboration (Catalog limits) where
  authoring := ExactDeclarationCodec.documentCompositional Value
  elaboration := {
    elaborate := elaborateCatalog? limits
    quote := fun catalog => quoteModules limits catalog.val
    elaborate_quote := by
      intro catalog
      simp [elaborateCatalog?]
    equation := by
      intro first second equivalent
      change first.values = second.values at equivalent
      simp only [elaborateCatalog?, elaborateDocument?, equivalent]
    rewrite := by
      intro first second impossible
      exact False.elim impossible }
  emptyPayload := ⟨[], by simp [distinctModules]⟩
  merge := fun first second => admitCatalog? limits (first.val ++ second.val)
  elaborate_empty := by
    simp [elaborateCatalog?, elaborateDocument?, ExactDeclarationCodec.documentCompositional,
      DeclarationDocument.values, DeclarationDocument.valuesList, admitCatalog?, distinctModules]
  elaborate_append := by
    intro first second
    change Document at first second
    have law := elaborateDocument_append limits first second
    change elaborateCatalog? limits (.bundle [first, second]) =
      (elaborateCatalog? limits first).bind fun left =>
        (elaborateCatalog? limits second).bind fun right =>
          admitCatalog? limits (left.val ++ right.val)
    unfold elaborateCatalog?
    rw [law]
    cases left : elaborateDocument? limits first with
    | none => simp
    | some leftModules =>
        cases right : elaborateDocument? limits second with
        | none => simp
        | some rightModules =>
            simpa only [left, right, Option.bind_some] using admitCatalog_append limits leftModules rightModules

/-- The associativity theorem includes rejection: either bracketing fails,
or both return exactly the same catalog. -/
theorem catalog_assembly_assoc (limits : Limits) (first second third : Catalog limits) :
    ((catalogSystem limits).merge first second).bind
        (fun merged => (catalogSystem limits).merge merged third) =
      ((catalogSystem limits).merge second third).bind
        (fun merged => (catalogSystem limits).merge first merged) :=
  (catalogSystem limits).toPartialMonoid.op_assoc first second third

/-- Successful assembly retains both full module lists in their original order. -/
theorem catalog_merge_val (limits : Limits) (first second merged : Catalog limits)
    (assembled : (catalogSystem limits).merge first second = some merged) :
    merged.val = first.val ++ second.val :=
  admitCatalog_some_val limits (first.val ++ second.val) merged assembled

def catalogLayer (Base : Type) (limits : Limits) :
    Mettapedia.GSLT.LanguageDef.ExtensionComposition.CompositionalLayer Base where
  Fiber := fun _ => Catalog limits
  system := fun _ => catalogSystem limits

def Compatible (limits : Limits) (first second : Catalog limits) : Prop :=
  ∀ left ∈ first.val, ∀ right ∈ second.val, left.val.name ≠ right.val.name

theorem catalog_merge_isSome_iff (limits : Limits) (first second : Catalog limits) :
    ((catalogSystem limits).merge first second).isSome ↔ Compatible limits first second := by
  change (admitCatalog? limits (first.val ++ second.val)).isSome ↔ _
  simp only [admitCatalog?]
  split
  · rename_i accepted
    simp only [Option.isSome_some, true_iff]
    exact ((distinct_append_iff limits first.val second.val).mp accepted).2.2
  · rename_i rejected
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro compatible
    exact rejected ((distinct_append_iff limits first.val second.val).mpr
      ⟨first.property, second.property, compatible⟩)

end Mettapedia.GSLT.LanguageDef.ModuleFormat
