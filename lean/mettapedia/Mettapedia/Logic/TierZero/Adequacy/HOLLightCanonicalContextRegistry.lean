import Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalLicenses
import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextLicensing
import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextActivation

/-!
# Source-admitted canonical context metadata

The actual private store's lookup/intern protocol preserves one row per key.
Logical eligibility is earned from original local admission and exactly the
selected source premises. Registering data alone does not make a context
available. Pure proof commands retain their existing context metadata.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalContextRegistry

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open HOLLightContextActivation (Entry)
open HOLLightContextLicensing
open HOLLightCanonicalLicenses (Key Store)

def Eligible (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) : Key → Prop
  | .inl context => Licensed initial policy (contexts context)
  | .inr (before, after) => Path policy (contexts before) (contexts after)

def LicensedStore (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (store : Store) : Prop :=
  ∀ index key, (index, key) ∈ store.rows → Eligible initial policy contexts key

theorem intern_preserves_licenses (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (store : Store) (prior : LicensedStore initial policy contexts store)
    (key : Key) (eligible : Eligible initial policy contexts key) :
    LicensedStore initial policy contexts (store.intern key).1 := by
  intro index other member
  cases known : store.lookup key with
  | some existing =>
      rw [(store.repeated_lookup_creates_no_row key existing known).1] at member
      exact prior index other member
  | none =>
      rw [(store.actual_fresh_row key known).1] at member
      rcases Finset.mem_insert.mp member with fresh | previous
      · have same : other = key := congrArg Prod.snd fresh
        exact same ▸ eligible
      · exact prior index other previous

def initialized (root : Nat) : Store := ((CanonicalMetadataStore.Store.empty (K := Key)).intern (.inl root)).1

theorem initialized_licensed (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (root : Nat) (rootContext : contexts root = initial) :
    LicensedStore initial policy contexts (initialized root) := by
  apply intern_preserves_licenses
  · intro index key member
    cases member
  · change Licensed initial policy (contexts root)
    rw [rootContext]
    exact initial_licensed initial policy

def record (store : Store) {contexts : Nat → TheoryContext} (entry : Entry contexts) : Store :=
  if entry.after = entry.before then store else
    (((store.intern (.inl entry.after)).1).intern (.inr (entry.before, entry.after))).1

theorem record_preserves_licenses (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (store : Store) (prior : LicensedStore initial policy contexts store)
    (entry : Entry contexts) (afterLicense : Licensed initial policy (contexts entry.after))
    (path : Path policy (contexts entry.before) (contexts entry.after)) :
    LicensedStore initial policy contexts (record store entry) := by
  unfold record
  split
  · exact prior
  · apply intern_preserves_licenses
    · exact intern_preserves_licenses initial policy contexts store prior (.inl entry.after) afterLicense
    · exact path

theorem record_retains_rows (store : Store) {contexts : Nat → TheoryContext} (entry : Entry contexts) :
    store.rows ⊆ (record store entry).rows := by
  unfold record
  split
  · exact Finset.Subset.refl _
  · exact Finset.Subset.trans (store.old_rows_retained (.inl entry.after))
      ((store.intern (.inl entry.after)).1.old_rows_retained (.inr (entry.before, entry.after)))

def admitCommand (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (store : Store) (entry : Entry contexts) (cache : Array Theorem) : Option (Store × Output) := do
  let _ ← store.lookup (.inl entry.before)
  let output ← entry.command.check policy (contexts entry.before) cache
  pure (record store entry, output)

/-- The canonical metadata mutation is licensed by the actual original local
check and selected independent premises; unused public cache rows are ignored. -/
theorem admitCommand_sound (initial : TheoryContext) (policy : AxiomPolicy) [DecidablePred policy]
    (contexts : Nat → TheoryContext) (store : Store) (prior : LicensedStore initial policy contexts store)
    (entry : Entry contexts) (cache : Array Theorem)
    (selected : ∀ index ∈ entry.command.parents, ∀ fact,
      cache[index]? = some fact → TheoryDerives policy (contexts entry.before) fact)
    {after : Store} {output : Output} (computed : admitCommand policy contexts store entry cache = some (after, output)) :
    after = record store entry ∧ LicensedStore initial policy contexts after ∧
      Licensed initial policy (contexts entry.after) ∧ output.context = contexts entry.after ∧
      ∀ fact ∈ output.theorems, TheoryDerives policy output.context fact := by
  cases beforeKnown : store.lookup (.inl entry.before) with
  | none => simp [admitCommand, beforeKnown] at computed
  | some index =>
      have beforeLicense : Licensed initial policy (contexts entry.before) :=
        prior index (.inl entry.before) ((store.represented index _).mpr beforeKnown)
      cases checked : entry.command.check policy (contexts entry.before) cache with
      | none => simp [admitCommand, beforeKnown, checked] at computed
      | some result =>
          have same : (record store entry, result) = (after, output) := by
            simpa [admitCommand, beforeKnown, checked] using computed
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
          have contextSame : result.context = contexts entry.after :=
            Option.some.inj ((HOLLightContextActivation.checked_target_context policy _ _ _ checked).symm.trans entry.routed)
          have licensed := checked_command_licenses_output initial policy beforeLicense entry.command cache checked selected
          have afterLicense : Licensed initial policy (contexts entry.after) := contextSame ▸ licensed.1
          have path : Path policy (contexts entry.before) (contexts entry.after) := contextSame ▸ licensed.2.1
          exact ⟨rfl, record_preserves_licenses initial policy contexts store prior entry afterLicense path,
            afterLicense, contextSame, licensed.2.2⟩

end Mettapedia.Logic.TierZero.Adequacy.HOLLightCanonicalContextRegistry
