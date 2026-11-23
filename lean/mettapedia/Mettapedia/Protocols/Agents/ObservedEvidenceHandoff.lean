import Mettapedia.Protocols.Agents.EvidenceHandoff

/-!
# Partial source observations in an evidence handoff

Unavailable is an observation, not a version and not an unqueried cache entry.
The inner option records whether a version was established. The outer option
records whether the source has been observed in this render. A new render starts
with an empty cache; no theorem promotes an old observation to a current fact.

The claim's truth remains a separate hypothesis from matching its version.
Projection preserves the original list, including order and duplicates, even
when versions are unavailable. The cache law permits one coherent observation
per source within a render without requiring an atomic snapshot of all sources.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ObservedEvidenceHandoff

open EvidenceHandoff

variable {Source Version Content : Type}

structure Observation (Source Version Content : Type) where
  claim : Claim Source Version Content
  observed : Option Version

def project (claims : List (Claim Source Version Content))
    (observed : Source → Option Version) : List (Observation Source Version Content) :=
  claims.map fun c => ⟨c, observed c.source⟩

/-- No unavailable version loses a claim, and no equal-valued occurrence is deduplicated. -/
theorem project_preserves_claims (claims : List (Claim Source Version Content))
    (observed : Source → Option Version) :
    (project claims observed).map Observation.claim = claims := by
  simp [project, List.map_map, Function.comp_def]

def versionMatches [DecidableEq Version] (c : Claim Source Version Content)
    (observed : Option Version) : Bool :=
  decide (observed = some c.version)

theorem unavailable_never_matches [DecidableEq Version]
    (c : Claim Source Version Content) : versionMatches c none = false := by
  simp [versionMatches]

/-- A matching observation supports truth only with the original establishment
and the interpretation of the version that was actually observed. -/
theorem established_at_matching_version [DecidableEq Version]
    {den : Denotation Source Version Content} {c : Claim Source Version Content}
    (est : c.Established den) {v : Version} (h : versionMatches c (some v) = true) :
    c.property (den c.source v) := by
  have hv : v = c.version := by simpa [versionMatches] using h
  simpa [Claim.Established, hv] using est

abbrev Cache (Source Version : Type) := Source → Option (Option Version)

def emptyCache : Cache Source Version := fun _ => none

/-- One source observation. An observed failure is retained as `some none`. -/
def observe [DecidableEq Source] (read : Source → Option Version)
    (cache : Cache Source Version) (source : Source) :
    Option Version × Cache Source Version × Nat :=
  match cache source with
  | some known => (known, cache, 0)
  | none =>
    let value := read source
    (value, (fun key => if key = source then some value else cache key), 1)

/-- Observing the same source again uses exactly the retained result, even
if a later physical read would now give a different answer. -/
theorem observe_retains_result [DecidableEq Source]
    (read later : Source → Option Version) (cache : Cache Source Version) (source : Source) :
    let first := observe read cache source
    observe later first.2.1 source = (first.1, first.2.1, 0) := by
  cases h : cache source <;> simp [observe, h]

theorem unavailable_is_cached [DecidableEq Source] (source : Source)
    (read : Source → Option Version) (h : read source = none) :
    let first := observe read emptyCache source
    first.1 = none ∧ first.2.1 source = some none ∧ first.2.2 = 1 := by
  simp [observe, emptyCache, h]

/-- Releasing the cache at a render boundary permits genuine refresh. -/
theorem new_render_observes_change [DecidableEq Source] (source : Source)
    (read : Source → Option Version) (v : Version) (h : read source = some v) :
    (observe read emptyCache source).1 = some v := by
  simp [observe, emptyCache, h]

/-- Cached entries denote the source observations chosen for this render. -/
def Compatible (read : Source → Option Version) (cache : Cache Source Version) : Prop :=
  ∀ source value, cache source = some value → value = read source

theorem observe_agrees [DecidableEq Source] (read : Source → Option Version)
    (cache : Cache Source Version) (source : Source) (h : Compatible read cache) :
    (observe read cache source).1 = read source ∧
      Compatible read (observe read cache source).2.1 := by
  cases hc : cache source with
  | none =>
    simp only [observe, hc]
    refine ⟨trivial, ?_⟩
    intro key value hv
    by_cases hk : key = source
    · subst key
      simpa using hv.symm
    · exact h key value (by simpa [hk] using hv)
  | some value =>
    exact ⟨by simpa [observe, hc] using h source value hc,
      by simpa [observe, hc] using h⟩

/-- Ordered projection with an ephemeral source-observation map. -/
def run [DecidableEq Source] (read : Source → Option Version)
    (cache : Cache Source Version) : List (Claim Source Version Content) →
    List (Observation Source Version Content) × Cache Source Version × Nat
  | [] => ([], cache, 0)
  | c :: cs =>
    let first := observe read cache c.source
    let rest := run read first.2.1 cs
    (⟨c, first.1⟩ :: rest.1, rest.2.1, first.2.2 + rest.2.2)

/-- The cached operational pass agrees with indexed observation, including
unavailable versions, while preserving all original claim occurrences. -/
theorem run_agrees [DecidableEq Source] (read : Source → Option Version)
    (claims : List (Claim Source Version Content)) (cache : Cache Source Version)
    (h : Compatible read cache) :
    (run read cache claims).1 = project claims read := by
  induction claims generalizing cache with
  | nil => rfl
  | cons c cs ih =>
    have first := observe_agrees read cache c.source h
    have rest := ih _ first.2
    simp only [run, project, List.map_cons]
    rw [rest, first.1]
    rfl

theorem complete_projection_preserves_occurrences [DecidableEq Source]
    (read : Source → Option Version) (claims : List (Claim Source Version Content)) :
    (run read emptyCache claims).1.map Observation.claim = claims := by
  rw [run_agrees read claims emptyCache (by intro s v h; cases h)]
  exact project_preserves_claims claims read

end Mettapedia.Protocols.Agents.ObservedEvidenceHandoff
