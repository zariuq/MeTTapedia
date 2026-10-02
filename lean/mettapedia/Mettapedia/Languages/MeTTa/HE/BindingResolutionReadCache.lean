import Mettapedia.Languages.MeTTa.HE.BindingResolutionReadSupport
import Mettapedia.Machines.ReadCertifiedGuard

/-!
# Certified reuse of the existing HE binding resolver

The governing authority consists of a logical owner and the ordered equality
relations. Assignment dependencies are validated individually, including absent
lookups. The key contains both the variable and the recursive fuel bound.

This instantiates the common supported-observer cache with the existing HE
`Bindings.resolveFull`, and with `Bindings.applyFull`, the application of
bindings to an atom that the HE evaluator performs. It neither introduces a new
binding store nor identifies this pure model with mutable C storage. A C adapter
must additionally establish ownership, frame identity, lifetime and complete
rollback observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.BindingResolutionReadCache

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines

universe u

/-- A logical owner labels an existing authoritative HE binding payload. -/
structure Context (Owner : Type u) where
  owner : Owner
  bindings : Bindings

abbrev Authority (Owner : Type u) := Owner × List (String × String)
abbrev Query := String × Nat

abbrev Entry (Owner : Type u) :=
  ReadCertifiedQueryReuse.Entry (Authority Owner) Query String (Option Atom) (Option Atom)

/-- Conservative read support suffices; no exact-trace encoding of the
resolver is required. The answer remains the actual public HE resolution. -/
def observer {Owner : Type u} :
    ReadCertifiedQueryReuse.Supported.Family (Context Owner) (Authority Owner)
      Query String (Option Atom) (Option Atom) where
  authority := fun state => (state.owner, state.bindings.equalities)
  memory := fun state => state.bindings.lookup
  observe := fun state query =>
    ⟨state.bindings.resolveFull query.1 query.2,
      BindingResolutionReadSupport.reads state.bindings query.1 query.2⟩
  certifies := by
    intro state query
    exact (ReadOnlyQuery.agrees_samples_iff _ _ _).mpr (fun _ _ => rfl)
  stable := by
    intro first second query authority reads
    exact BindingResolutionReadSupport.resolveFull_eq_of_reads
      (congrArg Prod.snd authority) query.1 query.2 reads

def Recorded {Owner : Type u} (entry : Entry Owner) : Prop :=
  ReadCertifiedQueryReuse.Supported.Recorded observer entry

/-- Population evaluates the resolver and records its computed support. -/
def populate {Owner : Type u} (state : Context Owner) (key : String) (fuel : Nat) :
    Entry Owner :=
  ReadCertifiedQueryReuse.Supported.populate observer state (key, fuel)

theorem populate_recorded {Owner : Type u} (state : Context Owner) (key : String) (fuel : Nat) :
    Recorded (populate state key fuel) :=
  ReadCertifiedQueryReuse.Supported.populate_recorded observer state (key, fuel)

/-- The counter counts fresh resolver evaluations, not validation or runtime
time. Zero denotes the branch that reuses an already certified answer. -/
def cached {Owner : Type u} [DecidableEq Owner]
    (state : Context Owner) (key : String) (fuel : Nat) (entry : Entry Owner) :
    Option Atom × Nat :=
  ReadCertifiedQueryReuse.Supported.reuse observer state (key, fuel) entry

/-- The cached algorithm agrees with fresh resolution, including cycle
rejection, open terms, correlated compounds and fuel exhaustion. -/
theorem cached_exact {Owner : Type u} [DecidableEq Owner]
    (state : Context Owner) (key : String) (fuel : Nat) (entry : Entry Owner)
    (history : Recorded entry) :
    (cached state key fuel entry).1 = state.bindings.resolveFull key fuel :=
  ReadCertifiedQueryReuse.Supported.reuse_exact observer state (key, fuel) entry history

theorem unchanged_reuses {Owner : Type u} [DecidableEq Owner]
    (state : Context Owner) (key : String) (fuel : Nat) :
    cached state key fuel (populate state key fuel) =
      (state.bindings.resolveFull key fuel, 0) :=
  ReadCertifiedQueryReuse.Supported.unchanged_reuses observer state (key, fuel)

/-- Equal owners, equal ordered equality authority and retained assignment
reads license the hit branch after unrelated updates or a restored checkpoint. -/
theorem retained_reads_reuse {Owner : Type u} [DecidableEq Owner]
    (first second : Context Owner) (key : String) (fuel : Nat)
    (owner : second.owner = first.owner)
    (equalities : second.bindings.equalities = first.bindings.equalities)
    (reads : ReadOnlyQuery.Agrees second.bindings.lookup
      (BindingResolutionReadSupport.reads first.bindings key fuel)) :
    cached second key fuel (populate first key fuel) =
      (first.bindings.resolveFull key fuel, 0) := by
  have accepted : ReadCertifiedQueryReuse.Supported.admissible observer second (key, fuel)
      (populate first key fuel) = true :=
    (ReadCertifiedQueryReuse.Supported.admissible_iff _ _ _ _).mpr
      ⟨(Prod.ext owner equalities).symm, rfl, reads⟩
  unfold cached ReadCertifiedQueryReuse.Supported.reuse
  rw [if_pos accepted]
  rfl

/-- Substituting certified HE resolution for a fresh pure resolution provider
preserves all ordered caller refinements and arbitrary consuming effects.
The source service must still establish that its provider is this resolver. -/
theorem cached_resolution_guard_exact {Owner Local World Result : Type}
    [DecidableEq Owner] (snapshot : Context Owner) (queryOf : Local → Query)
    (entry : Entry Owner) (history : Recorded entry)
    (materialize : Local → Option Atom → List Local)
    (body : ScopedCommit.Body Local World) (state : Local)
    (success : ScopedCommit.Success Local World Result)
    (failure saved : ScopedCommit.Failure World Result) (world : World) :
    ScopedCommit.eval (OrderedGuardPipeline.guard (fun caller =>
      materialize caller (cached snapshot (queryOf caller).1 (queryOf caller).2 entry).1) body)
        state success failure saved world =
    ScopedCommit.eval (OrderedGuardPipeline.guard (fun caller =>
      materialize caller (snapshot.bindings.resolveFull (queryOf caller).1 (queryOf caller).2)) body)
        state success failure saved world :=
  ReadCertifiedGuard.Supported.cached_guard_eval_exact observer snapshot queryOf
    entry history materialize body state success failure saved world

/-! ## Applying bindings to an atom

The query is an atom with its fuel, the answer is the applied atom, and the
certificate is the support of each variable occurrence. -/

abbrev ApplicationQuery := Atom × Nat

abbrev ApplicationEntry (Owner : Type u) :=
  ReadCertifiedQueryReuse.Entry (Authority Owner) ApplicationQuery String (Option Atom) Atom

/-- The supported observer of `Bindings.applyFull`. -/
def applicationObserver {Owner : Type u} :
    ReadCertifiedQueryReuse.Supported.Family (Context Owner) (Authority Owner)
      ApplicationQuery String (Option Atom) Atom where
  authority := fun state => (state.owner, state.bindings.equalities)
  memory := fun state => state.bindings.lookup
  observe := fun state query =>
    ⟨state.bindings.applyFull query.1 query.2,
      BindingResolutionReadSupport.applyReads state.bindings query.1 query.2⟩
  certifies := by
    intro state query
    exact (ReadOnlyQuery.agrees_samples_iff _ _ _).mpr (fun _ _ => rfl)
  stable := by
    intro first second query authority reads
    exact BindingResolutionReadSupport.applyFull_eq_of_reads
      (congrArg Prod.snd authority) query.1 query.2 reads

def populateApplication {Owner : Type u} (state : Context Owner) (atom : Atom) (fuel : Nat) :
    ApplicationEntry Owner :=
  ReadCertifiedQueryReuse.Supported.populate applicationObserver state (atom, fuel)

def cachedApplication {Owner : Type u} [DecidableEq Owner]
    (state : Context Owner) (atom : Atom) (fuel : Nat) (entry : ApplicationEntry Owner) :
    Atom × Nat :=
  ReadCertifiedQueryReuse.Supported.reuse applicationObserver state (atom, fuel) entry

/-- The cached application agrees with a fresh application of the current
bindings, including the variables a resolution leaves in place. -/
theorem cachedApplication_exact {Owner : Type u} [DecidableEq Owner]
    (state : Context Owner) (atom : Atom) (fuel : Nat) (entry : ApplicationEntry Owner)
    (history : ReadCertifiedQueryReuse.Supported.Recorded applicationObserver entry) :
    (cachedApplication state atom fuel entry).1 = state.bindings.applyFull atom fuel :=
  ReadCertifiedQueryReuse.Supported.reuse_exact applicationObserver state (atom, fuel) entry history

namespace Controls

open BindingResolutionReadSupport.Controls

def first : Context Nat := ⟨1, firstBranch⟩
def second : Context Nat := ⟨1, secondBranch⟩

/-- A restored alias and a rebound dependency cannot reuse the former answer. -/
theorem rollback_rebinding_recomputes :
    first.bindings.lookup "x" = second.bindings.lookup "x" ∧
      cached second "x" 6 (populate first "x" 6) = (some (.symbol "B"), 1) := by
  decide

theorem unrelated_update_reuses :
    cached ⟨1, firstBranch.assign "z" (.symbol "Other")⟩ "x" 6
      (populate first "x" 6) = (some (.symbol "A"), 0) := by
  decide

/-- An open assignment certificate retains the absence of its alias target. -/
theorem formerly_absent_dependency_recomputes :
    cached first "x" 6 (populate (⟨1, openAlias⟩ : Context Nat) "x" 6) =
      (some (.symbol "A"), 1) := by
  decide

/-- Assignment values may be unchanged while equality-class authority changes. -/
theorem changed_equalities_recompute :
    let initial : Context Nat := ⟨1, equalitySource⟩
    let changed : Context Nat := ⟨1, equalitySource.addEquality "z" "x"⟩
    cached changed "x" 6 (populate initial "x" 6) = (some (.symbol "B"), 1) := by
  decide

theorem changed_owner_recomputes :
    cached ⟨2, firstBranch⟩ "x" 6 (populate first "x" 6) = (some (.symbol "A"), 1) := by
  decide

/-- An exhausted computation cannot answer a query with a different budget. -/
theorem fuel_is_part_of_the_key :
    cached first "x" 6 (populate first "x" 0) = (some (.symbol "A"), 1) := by
  decide

/-- The full correlated compound is retained, not a single independent slot. -/
theorem compound_reuses_with_correlation :
    let state : Context Nat := ⟨1, compound⟩
    cached state "x" 6 (populate state "x" 6) =
      (some (.expression [.symbol "Pair", .symbol "A", .symbol "A"]), 0) := by
  decide

theorem cycle_rejection_reuses :
    let state : Context Nat := ⟨1, cyclic⟩
    cached state "x" 6 (populate state "x" 6) = (none, 0) := by
  decide

theorem application_reuses_after_unrelated_update :
    cachedApplication ⟨1, firstBranch.assign "z" (.symbol "Other")⟩ pairOfAlias 7
        (populateApplication first pairOfAlias 7) =
      (.expression [.symbol "Pair", .symbol "A", .var "w"], 0) := by
  decide

/-- Rebinding the target of an alias, or binding a variable the application
left in place, recomputes. -/
theorem application_recomputes_after_changed_dependency :
    cachedApplication second pairOfAlias 7 (populateApplication first pairOfAlias 7) =
        (.expression [.symbol "Pair", .symbol "B", .var "w"], 1) ∧
      cachedApplication ⟨1, firstBranch.assign "w" (.symbol "C")⟩ pairOfAlias 7
          (populateApplication first pairOfAlias 7) =
        (.expression [.symbol "Pair", .symbol "A", .symbol "C"], 1) := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.HE.BindingResolutionReadCache
