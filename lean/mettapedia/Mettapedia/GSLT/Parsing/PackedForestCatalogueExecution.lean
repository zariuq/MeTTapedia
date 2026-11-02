import Mettapedia.GSLT.Parsing.PackedForestCatalogue

/-! Snapshot rounds of the existing selected-family extraction operation.
Only a checked fixed point is published as complete. A round budget alone
has no authority to discard later or cyclic unfoldings. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PackedForestCatalogue

open PackedForestSelection

universe u v
variable {Key : Type u} {Family : Type v} [DecidableEq Key]

abbrev Cache (Key : Type u) (Family : Type v) := List (Key × List (Derivation Family))

def lookup (cache : Cache Key Family) (key : Key) : List (Derivation Family) :=
  ((cache.find? fun entry => decide (entry.1 = key)).map Prod.snd).getD []

def snapshot (keys : List Key) (values : Key → List (Derivation Family)) : Cache Key Family :=
  keys.map fun key => (key, values key)

theorem lookup_snapshot (keys : List Key) (values : Key → List (Derivation Family)) (key : Key) :
    lookup (snapshot keys values) key = if key ∈ keys then values key else [] := by
  induction keys with
  | nil => simp [snapshot, lookup]
  | cons first rest ih =>
    by_cases same : first = key
    · subst first; simp [snapshot, lookup]
    · simp only [snapshot, List.map_cons, lookup, List.find?_cons, decide_eq_false same] at *
      simpa [same, Ne.symm same] using ih

def round (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (keys : List Key) (cache : Cache Key Family) : Cache Key Family :=
  snapshot keys (next families children allow (lookup cache))

theorem lookup_round (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (keys : List Key) (cache : Cache Key Family) (key : Key) :
    lookup (round families children allow keys cache) key =
      if key ∈ keys then next families children allow (lookup cache) key else [] :=
  lookup_snapshot _ _ _

theorem round_sound (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (keys : List Key) (cache : Cache Key Family) (sound : Sound families children allow (lookup cache)) :
    Sound families children allow (lookup (round families children allow keys cache)) := by
  intro key tree member
  rw [lookup_round] at member
  split at member
  · exact next_sound families children allow _ sound key tree member
  · simp at member

theorem fixed_complete (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (keys : List Key) (cache : Cache Key Family)
    (inventory : ∀ key, families key ≠ [] → key ∈ keys)
    (fixed : round families children allow keys cache = cache)
    {key : Key} {tree : Derivation Family} (source : Unfolds families children allow key tree) :
    tree ∈ lookup cache key := by
  apply closed_complete families children allow (lookup cache) _ source
  intro key tree member
  obtain ⟨family, present, _⟩ := (next_mem _ _ _ _ _ _).mp member
  have known := inventory key (by intro empty; simp [empty] at present)
  have equality := lookup_round families children allow keys cache key
  rw [fixed, if_pos known] at equality
  exact equality.symm ▸ member

variable [DecidableEq Family]

def finish? (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (keys : List Key) : Nat → Cache Key Family → Option (Cache Key Family)
  | 0, _ => none
  | rounds + 1, cache =>
    let updated := round families children allow keys cache
    if updated = cache then some cache else finish? families children allow keys rounds updated

theorem finish?_fixed (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (keys : List Key) (rounds : Nat) (cache output : Cache Key Family)
    (finished : finish? families children allow keys rounds cache = some output) :
    round families children allow keys output = output := by
  induction rounds generalizing cache with
  | zero => cases finished
  | succ rounds ih =>
    simp only [finish?] at finished
    split at finished
    · cases Option.some.inj finished; assumption
    · exact ih _ finished

theorem finish?_sound (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (keys : List Key) (rounds : Nat) (cache output : Cache Key Family)
    (sound : Sound families children allow (lookup cache))
    (finished : finish? families children allow keys rounds cache = some output) :
    Sound families children allow (lookup output) := by
  induction rounds generalizing cache with
  | zero => cases finished
  | succ rounds ih =>
    simp only [finish?] at finished
    split at finished
    · cases Option.some.inj finished; exact sound
    · exact ih _ (round_sound _ _ _ _ _ sound) finished

def catalogue? (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (keys : List Key) (rounds : Nat) : Option (Cache Key Family) :=
  finish? families children allow keys rounds []

theorem catalogue?_exact (families : Key → List Family) (children : Family → List Key) (allow : Family → Bool)
    (keys : List Key) (rounds : Nat) (output : Cache Key Family)
    (inventory : ∀ key, families key ≠ [] → key ∈ keys)
    (finished : catalogue? families children allow keys rounds = some output) (key : Key) (tree : Derivation Family) :
    tree ∈ lookup output key ↔ Unfolds families children allow key tree := by
  constructor
  · exact finish?_sound families children allow keys rounds [] output (by
      intro key tree member; simp [lookup] at member) finished key tree
  · exact fixed_complete families children allow keys output inventory
      (finish?_fixed families children allow keys rounds [] output finished)

end Mettapedia.GSLT.Parsing.PackedForestCatalogue
