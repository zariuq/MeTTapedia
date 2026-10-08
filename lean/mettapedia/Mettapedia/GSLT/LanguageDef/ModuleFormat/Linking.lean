import Mettapedia.GSLT.LanguageDef.ModuleFormat.Catalog

/-!
# Dependency linking against an explicit registry snapshot

A commitment here is a retained byte string, not a proof of a cryptographic
hash or provenance. A snapshot is supplied by the host. Linking requires both
the parsed reference and the recorded commitment, and retains the matched
module declaration for every dependency in authored order. File references
do not grant filesystem access.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat

structure RegistryEntry (limits : Limits) where
  reference : ModuleRef
  commitment : List UInt8
  declaration : Module limits
  deriving Repr, DecidableEq

def Snapshot.Valid (limits : Limits) (entries : List (RegistryEntry limits)) : Prop :=
  (entries.map RegistryEntry.reference).Nodup ∧
    ∀ entry ∈ entries, entry.reference.valid ∧ entry.commitment.length = 32

instance (limits : Limits) (entries : List (RegistryEntry limits)) :
    Decidable (Snapshot.Valid limits entries) := by
  unfold Snapshot.Valid
  infer_instance

abbrev Snapshot (limits : Limits) :=
  { entries : List (RegistryEntry limits) // Snapshot.Valid limits entries }

/-- The resolution contract mentions membership and both identifiers,
independently of the executable search. -/
def Resolves {limits : Limits} (snapshot : Snapshot limits)
    (dependency : Dependency) (entry : RegistryEntry limits) : Prop :=
  entry ∈ snapshot.val ∧ entry.reference = dependency.reference ∧
    entry.commitment = dependency.commitment

def resolve? {limits : Limits} (snapshot : Snapshot limits)
    (dependency : Dependency) : Option (RegistryEntry limits) :=
  snapshot.val.find? fun entry =>
    decide (entry.reference = dependency.reference ∧ entry.commitment = dependency.commitment)

theorem resolve_sound {limits : Limits} (snapshot : Snapshot limits)
    (dependency : Dependency) (entry : RegistryEntry limits)
    (found : resolve? snapshot dependency = some entry) : Resolves snapshot dependency entry := by
  have member := List.mem_of_find?_eq_some found
  have matched := List.find?_some found
  exact ⟨member, of_decide_eq_true matched⟩

/-- Search succeeds exactly when the snapshot contains a matching dependency.
A changed commitment alone suffices to make a formerly available dependency
unavailable. No unrelated export or name can satisfy this contract. -/
theorem resolve_isSome_iff {limits : Limits} (snapshot : Snapshot limits)
    (dependency : Dependency) :
    (resolve? snapshot dependency).isSome ↔ ∃ entry, Resolves snapshot dependency entry := by
  simp [resolve?, Resolves]

/-- Successful monadic traversal has an independent positional specification. -/
theorem mapM_forall₂ {α β : Type} (decode : α → Option β) (inputs : List α)
    (outputs : List β) :
    inputs.mapM decode = some outputs ↔ List.Forall₂ (fun input output =>
      decode input = some output) inputs outputs := by
  induction inputs generalizing outputs with
  | nil => cases outputs <;> simp
  | cons input inputs ih =>
      cases head : decode input with
      | none => cases outputs <;> simp [List.mapM_cons, head]
      | some output =>
          cases outputs <;> cases tail : inputs.mapM decode <;>
            simp [List.mapM_cons, head, tail, ← ih]

/-- Successful traversal requires every individual decoder to succeed. -/
theorem mapM_isSome_iff {α β : Type} (decode : α → Option β) (inputs : List α) :
    (inputs.mapM decode).isSome ↔ ∀ input ∈ inputs, (decode input).isSome := by
  induction inputs with
  | nil => simp
  | cons input inputs ih =>
      cases head : decode input <;> cases tail : inputs.mapM decode <;>
        simp [List.mapM_cons, head, tail, ← ih]

/-- Every dependency is available in the same explicitly supplied snapshot. -/
def DependenciesAvailable {limits : Limits} (snapshot : Snapshot limits)
    (declaration : Module limits) : Prop :=
  ∀ dependency ∈ declaration.val.dependencies, ∃ entry ∈ snapshot.val,
    entry.reference = dependency.reference ∧ entry.commitment = dependency.commitment

instance {limits : Limits} (snapshot : Snapshot limits) (declaration : Module limits) :
    Decidable (DependenciesAvailable snapshot declaration) := by
  unfold DependenciesAvailable
  infer_instance

def linkDependencies? {limits : Limits} (snapshot : Snapshot limits)
    (declaration : Module limits) : Option (List (RegistryEntry limits)) :=
  declaration.val.dependencies.mapM (resolve? snapshot)

/-- Dependency linking is sound and complete for availability in the snapshot. -/
theorem linkDependencies_isSome_iff {limits : Limits} (snapshot : Snapshot limits)
    (declaration : Module limits) :
    (linkDependencies? snapshot declaration).isSome ↔ DependenciesAvailable snapshot declaration := by
  simp only [linkDependencies?, mapM_isSome_iff, resolve_isSome_iff,
    DependenciesAvailable, Resolves]

/-- Every linked dependency comes from the snapshot and matches both fields;
position and multiplicity are preserved by `Forall₂`. -/
theorem linkDependencies_sound {limits : Limits} (snapshot : Snapshot limits)
    (declaration : Module limits) (entries : List (RegistryEntry limits))
    (linked : linkDependencies? snapshot declaration = some entries) :
    List.Forall₂ (Resolves snapshot) declaration.val.dependencies entries := by
  have positional := (mapM_forall₂ (resolve? snapshot)
    declaration.val.dependencies entries).mp linked
  exact positional.imp (fun _ _ found => resolve_sound snapshot _ _ found)

/-- A linked module carries the declaration and its checked positional
resolution witness. It does not assert that export specifications implement
any language or that the host authenticated the snapshot. -/
structure LinkedModule {limits : Limits} (snapshot : Snapshot limits) where
  declaration : Module limits
  dependencies : List (RegistryEntry limits)
  resolved : List.Forall₂ (Resolves snapshot) declaration.val.dependencies dependencies

def linkModule? {limits : Limits} (snapshot : Snapshot limits)
    (declaration : Module limits) : Option (LinkedModule snapshot) :=
  match linked : linkDependencies? snapshot declaration with
  | none => none
  | some entries => some ⟨declaration, entries,
      linkDependencies_sound snapshot declaration entries linked⟩

/-- Dependency admission cannot alter the module or any exported payload. -/
theorem linkModule_preserves_declaration {limits : Limits} (snapshot : Snapshot limits)
    (declaration : Module limits) (linked : LinkedModule snapshot)
    (accepted : linkModule? snapshot declaration = some linked) :
    linked.declaration = declaration := by
  unfold linkModule? at accepted
  split at accepted
  · contradiction
  · cases accepted
    rfl

end Mettapedia.GSLT.LanguageDef.ModuleFormat
