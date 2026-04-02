import Mettapedia.Languages.MeTTa.HE.IncrementalTableSemantics
import Mettapedia.Languages.MeTTa.HE.BridgeMatrix

/-!
# CeTTa Runtime Contracts

Implementation-facing contracts that make the CeTTa runtime safe. Each contract
corresponds to a concrete C runtime invariant and can serve as a checklist for
safe refactoring.

## Contracts (all proved, 0 sorry)

### §1: Alpha-Canonicalization (`term_universe.c`, `term_canon.c`)
- Any injective variable renaming gives a safe canonicalization
- Canonical keys preserve match semantics (BEq, co-reference)
- Variant-equivalent queries share canonical keys → cache reuse is sound

### §2: Search Context Rollback (`search_machine.c`)
- Bindings builder with marks: save/rollback is stack-disciplined
- Rollback restores all prior bindings; new bindings after mark are discarded
- Scratch arena rollback is compatible with bindings rollback

### §3: Effect Classification (`runtime_effect_classes.json`)
- Pure operations: cache-safe, reorder-safe
- Space mutations: invalidate cache, preserve-order
- Import/oracle: avoid cache, external boundary
- Profile hierarchy gates which operations are available

### §4: Refactor Risk Map
Each theorem maps to a specific CeTTa refactor risk it reduces.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## §1: Alpha-Canonicalization Contracts

CeTTa's `term_universe_canonicalize_atom()` assigns ordinals to variables
in DFS order. We don't formalize the specific algorithm — we formalize the
PROPERTIES that make any such canonicalization safe for tabling and caching.

The key insight: canonicalization IS an injective VarRenaming applied via
`applyAtomTotal`. All safety properties follow from injectivity. -/

/-- A **canonicalization** is an injective variable renaming.
    CeTTa's `TermUniverseCanonMap` builds one by assigning fresh ordinals. -/
structure Canonicalization where
  ren : VarRenaming
  inj : ren.Injective

namespace Canonicalization

/-- Apply canonicalization to an atom. -/
def apply (c : Canonicalization) (a : Atom) : Atom :=
  applyAtomTotal c.ren a

/-- **Contract 1a**: Canonicalization preserves symbols.
    Risk: refactoring `term_universe_canonicalize_atom` to touch symbol atoms. -/
theorem preserves_symbols (c : Canonicalization) (s : String) :
    c.apply (.symbol s) = .symbol s := by
  unfold apply applyAtomTotal; rfl

/-- **Contract 1b**: Canonicalization preserves grounded values.
    Risk: refactoring canonicalization to touch grounded atoms. -/
theorem preserves_grounded (c : Canonicalization) (g : GroundedValue) :
    c.apply (.grounded g) = .grounded g := by
  unfold apply applyAtomTotal; rfl

/-- **Contract 1c**: Canonicalization distributes over expressions.
    Risk: breaking the recursive structure of canonicalization. -/
theorem distributes_expression (c : Canonicalization) (es : List Atom) :
    c.apply (.expression es) = .expression (es.map c.apply) := by
  simp only [apply]; unfold applyAtomTotal; rfl

/-- **Contract 1d**: Canonicalization is injective on atoms.
    Two different atoms cannot canonicalize to the same form.
    Risk: using a non-injective renaming (e.g., mapping all vars to one name). -/
theorem apply_injective (c : Canonicalization) :
    Function.Injective c.apply :=
  applyAtomTotal_injective c.ren c.inj

/-- **Contract 1e**: Canonicalization preserves BEq results.
    `(canon(a) == canon(b)) = (a == b)` for any atoms a, b.
    Risk: BEq check on canonical atoms disagreeing with original check. -/
theorem preserves_beq (c : Canonicalization) (a b : Atom) :
    (c.apply a == c.apply b) = (a == b) :=
  applyAtomTotal_beq_iff c.ren c.inj a b

/-- **Contract 1f**: Co-reference preservation (faithful encoding).
    Same variable name → same canonical name. Different → different.
    Risk: collapsing distinct variables during canonicalization. -/
theorem faithful_variables (c : Canonicalization) (v₁ v₂ : String) :
    v₁ = v₂ ↔ c.ren.rename v₁ = c.ren.rename v₂ :=
  VarRenaming.faithful_iff c.ren c.inj v₁ v₂

/-- **Contract 1g**: Variant-equivalent queries share canonical RHS atoms.
    If `q₂ = canon(q₁)` for some canonicalization, then tabled results are the same.
    Risk: variant-key cache returning wrong RHS after canonicalization change. -/
theorem variant_cache_safe (c : Canonicalization)
    (space : Space) (q : Atom) (fuel : Nat) :
    (queryEquations space q fuel).map Prod.fst =
    (queryEquations space (c.apply q) fuel).map Prod.fst := by
  have hvar : VariantEquiv q (c.apply q) := ⟨c.ren, c.inj, rfl⟩
  exact variant_queries_same_rhs space q (c.apply q) hvar fuel

end Canonicalization

/-! ## §2: Search Context Rollback Contracts

CeTTa's `SearchContext` uses mark/rollback for backtracking. The bindings
builder captures a mark (current length); rollback truncates back to it.

We model this as a list-based bindings builder with explicit marks. -/

/-- A **bindings builder mark**: captures the state at save time. -/
structure BindingsMark where
  savedLength : Nat

/-- A **bindings builder**: mutable accumulator with mark/rollback.
    Models CeTTa's `BindingsBuilder` from `search_machine.c`. -/
structure BindingsBuilder where
  entries : List (String × Atom)

namespace BindingsBuilder

def empty : BindingsBuilder := ⟨[]⟩

/-- Save the current state as a mark. -/
def save (bb : BindingsBuilder) : BindingsMark :=
  ⟨bb.entries.length⟩

/-- Add a binding. -/
def addBinding (bb : BindingsBuilder) (v : String) (a : Atom) : BindingsBuilder :=
  ⟨(v, a) :: bb.entries⟩

/-- Rollback to a saved mark. -/
def rollback (bb : BindingsBuilder) (mark : BindingsMark) : BindingsBuilder :=
  ⟨bb.entries.drop (bb.entries.length - mark.savedLength)⟩

/-- **Contract 2a**: Rollback after save with no intermediate changes is identity.
    Risk: save/rollback cycle corrupting bindings. -/
theorem rollback_save_noop (bb : BindingsBuilder) :
    bb.rollback (bb.save) = bb := by
  simp [rollback, save, Nat.sub_self]

/-- **Contract 2b**: Rollback discards bindings added after mark.
    Risk: rollback failing to undo recent bindings. -/
theorem rollback_discards_new (bb : BindingsBuilder) (v : String) (a : Atom) :
    (bb.addBinding v a).rollback (bb.save) = bb := by
  simp [rollback, save, addBinding]

/-- **Contract 2c**: Rollback preserves bindings from before the mark.
    Risk: rollback accidentally removing pre-existing bindings. -/
theorem rollback_preserves_old (bb : BindingsBuilder)
    (v₁ : String) (a₁ : Atom) (v₂ : String) (a₂ : Atom) :
    ((bb.addBinding v₁ a₁).addBinding v₂ a₂).rollback ((bb.addBinding v₁ a₁).save) =
    bb.addBinding v₁ a₁ := by
  simp [rollback, save, addBinding]

/-- **Contract 2d**: Multiple rollbacks to the same mark are idempotent.
    Risk: double-rollback causing corruption. -/
theorem rollback_idempotent (bb : BindingsBuilder) (mark : BindingsMark) :
    (bb.rollback mark).rollback mark = bb.rollback mark := by
  simp [rollback, List.length_drop]; omega

end BindingsBuilder

/-! ## §3: Effect Classification Contracts

CeTTa classifies operations by their effect class, which determines
caching and scheduling policies. This mirrors `runtime_effect_classes.json`. -/

/-- Effect classes from CeTTa's `runtime_effect_classes.json`. -/
inductive EffectClass where
  | pureValue       -- No side effects, deterministic
  | pureNondet      -- No side effects, nondeterministic (match results)
  | pureControl     -- No side effects, control flow (if, case)
  | spaceRead       -- Reads from space (get-atoms, match)
  | spaceWrite      -- Writes to space (add-atom, remove-atom)
  | stateEffect     -- Modifies state (bind!, new-state)
  | dynamicEval     -- Dynamic evaluation (eval on computed atom)
  | importEffect    -- Import/module loading
  deriving DecidableEq, Repr

/-- Memo policy derived from effect class. -/
inductive MemoPolicy where
  | stableCacheSafe    -- Safe to memoize across revisions
  | snapshotCacheOnly  -- Cache only for matching space revision
  | avoidRuntimeCache  -- Don't cache (effectful)
  deriving DecidableEq, Repr

/-- Scheduler policy derived from effect class. -/
inductive SchedulerPolicy where
  | reorderSafe      -- Can be reordered freely
  | preserveOrder    -- Must respect evaluation order
  | externalBoundary -- Import effects at system boundary
  deriving DecidableEq, Repr

/-- The effect→policy mapping from `runtime_effect_classes.json`. -/
def effectMemoPolicy : EffectClass → MemoPolicy
  | .pureValue => .stableCacheSafe
  | .pureNondet => .stableCacheSafe
  | .pureControl => .stableCacheSafe
  | .spaceRead => .snapshotCacheOnly
  | .spaceWrite => .snapshotCacheOnly
  | .stateEffect => .avoidRuntimeCache
  | .dynamicEval => .avoidRuntimeCache
  | .importEffect => .avoidRuntimeCache

def effectSchedulerPolicy : EffectClass → SchedulerPolicy
  | .pureValue => .reorderSafe
  | .pureNondet => .reorderSafe
  | .pureControl => .reorderSafe
  | .spaceRead => .preserveOrder
  | .spaceWrite => .preserveOrder
  | .stateEffect => .preserveOrder
  | .dynamicEval => .preserveOrder
  | .importEffect => .externalBoundary

/-- **Contract 3a**: Pure operations are always cache-safe.
    Risk: marking a pure operation as uncacheable (performance loss). -/
theorem pure_is_cache_safe :
    effectMemoPolicy .pureValue = .stableCacheSafe ∧
    effectMemoPolicy .pureNondet = .stableCacheSafe ∧
    effectMemoPolicy .pureControl = .stableCacheSafe :=
  ⟨rfl, rfl, rfl⟩

/-- **Contract 3b**: Pure operations are reorder-safe.
    Risk: unnecessarily serializing pure computations. -/
theorem pure_is_reorder_safe :
    effectSchedulerPolicy .pureValue = .reorderSafe ∧
    effectSchedulerPolicy .pureNondet = .reorderSafe ∧
    effectSchedulerPolicy .pureControl = .reorderSafe :=
  ⟨rfl, rfl, rfl⟩

/-- **Contract 3c**: Space writes require snapshot-only caching.
    Risk: caching space-write results across revisions (stale data). -/
theorem space_write_is_snapshot_only :
    effectMemoPolicy .spaceWrite = .snapshotCacheOnly :=
  rfl

/-- **Contract 3d**: Import effects avoid all caching.
    Risk: caching import side-effects (module loaded twice or not at all). -/
theorem import_avoids_cache :
    effectMemoPolicy .importEffect = .avoidRuntimeCache :=
  rfl

/-- **Contract 3e**: Import effects are external boundaries.
    Risk: reordering imports (module dependencies violated). -/
theorem import_is_external_boundary :
    effectSchedulerPolicy .importEffect = .externalBoundary :=
  rfl

/-- An operation is **eligible for aggressive lowering** iff it's cache-safe. -/
def isLoweringEligible (e : EffectClass) : Bool :=
  effectMemoPolicy e == .stableCacheSafe

/-- **Contract 3f**: Only pure operations are lowering-eligible.
    Risk: aggressively lowering effectful operations. -/
theorem lowering_eligible_iff_pure (e : EffectClass) :
    isLoweringEligible e = true ↔
    (e = .pureValue ∨ e = .pureNondet ∨ e = .pureControl) := by
  cases e <;> simp [isLoweringEligible, effectMemoPolicy]

/-! ## §4: Profile Hierarchy Contracts

CeTTa profiles gate which operations are available. -/

/-- CeTTa profile levels (from `session.h`). -/
inductive ProfileLevel where
  | heCompat     -- HE-compatible public surface
  | heExtended   -- HE-compatible + CeTTa extensions
  | hePrime      -- Extended + dependent telescope
  deriving DecidableEq, Repr

/-- Profile expressiveness ordering. -/
def ProfileLevel.rank : ProfileLevel → Nat
  | .heCompat => 0
  | .heExtended => 1
  | .hePrime => 2

/-- **Contract 4a**: Profile hierarchy is a total order.
    Risk: adding a profile that isn't comparable to existing ones. -/
theorem profile_total_order (p₁ p₂ : ProfileLevel) :
    p₁.rank ≤ p₂.rank ∨ p₂.rank ≤ p₁.rank := by
  omega

/-- A feature requires at minimum a given profile level. -/
def featureAvailable (required : ProfileLevel) (active : ProfileLevel) : Bool :=
  required.rank ≤ active.rank

/-- **Contract 4b**: HE-compat features are available in all profiles.
    Risk: breaking HE compatibility in extended profiles. -/
theorem he_compat_always_available (p : ProfileLevel) :
    featureAvailable .heCompat p = true := by
  cases p <;> simp [featureAvailable, ProfileLevel.rank]

/-- **Contract 4c**: HE-prime features require HE-prime profile.
    Risk: exposing dependent telescope in HE-compat mode. -/
theorem he_prime_requires_prime :
    featureAvailable .hePrime .heCompat = false ∧
    featureAvailable .hePrime .heExtended = false ∧
    featureAvailable .hePrime .hePrime = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## §5: Refactor Risk Map

Each contract reduces a specific refactor risk:

| Contract | C File | Risk Reduced |
|----------|--------|-------------|
| 1a: preserves_symbols | term_canon.c | Canon touching symbols |
| 1b: preserves_grounded | term_canon.c | Canon touching grounded |
| 1d: apply_injective | term_universe.c | Non-injective canon map |
| 1e: preserves_beq | term_canon.c | BEq mismatch after canon |
| 1f: faithful_variables | term_canon.c | Variable collapsing |
| 1g: variant_cache_safe | table_store.c | Wrong RHS from variant cache |
| 2a: rollback_save_noop | search_machine.c | Save/rollback cycle corruption |
| 2b: rollback_discards_new | search_machine.c | Rollback not undoing bindings |
| 2c: rollback_preserves_old | search_machine.c | Rollback removing too much |
| 2d: rollback_idempotent | search_machine.c | Double-rollback corruption |
| 3a: pure_is_cache_safe | eval.c | Pure op marked uncacheable |
| 3c: space_write_snapshot | table_store.c | Cross-revision stale cache |
| 3d: import_avoids_cache | eval.c | Caching import side-effects |
| 3f: lowering_eligible | mm2_lower.c | Lowering effectful ops |
| 4b: he_compat_available | session.c | Breaking HE compat |
| 4c: he_prime_requires | session.c | Leaking prime features |
-/

end Mettapedia.Languages.MeTTa.HE
