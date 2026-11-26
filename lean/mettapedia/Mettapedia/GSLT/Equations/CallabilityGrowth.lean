import Mathlib.Logic.Relation
import Mathlib.Data.Set.Lattice

/-! # Closing an extended declaration without reopening settled keys

Rule heads seed reachability in a graph of admissible aliases. Appending
heads and extending the graph make the old closure reusable. More precisely,
a worklist starts at new heads outside the settled region and new edges
leaving that region. Once an old vertex has been settled, no search of its
old outgoing edges is needed. This is about the closure of a relation; an
implementation still needs to discover all new edges, including any new
consequences of compound congruence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.CallabilityGrowth

open Relation

variable {Head : Type*}

def close (step : Head → Head → Prop) (seeds : Set Head) : Set Head :=
  {x | ∃ y ∈ seeds, ReflTransGen step y x}

theorem seeds_le (step : Head → Head → Prop) (seeds : Set Head) :
    seeds ⊆ close step seeds :=
  fun _ member => ⟨_, member, .refl⟩

theorem step_closed {step : Head → Head → Prop} {seeds : Set Head} {a b : Head}
    (known : a ∈ close step seeds) (edge : step a b) : b ∈ close step seeds := by
  obtain ⟨start, head, path⟩ := known
  exact ⟨start, head, path.tail edge⟩

theorem close_mono {old fresh : Head → Head → Prop} (growth : old ≤ fresh)
    {first later : Set Head} (more : first ⊆ later) :
    close old first ⊆ close fresh later := by
  rintro x ⟨a, member, path⟩
  exact ⟨a, more member, ReflTransGen.mono growth a x path⟩

/-- The precise cache premise, even when the new relation is not a global
extension: every cached seed is still reachable, and the original seeds
remain available. Once this holds, closing longer paths adds no obligation
to rederive the cached prefix. -/
theorem resume_sound_and_complete (step : Head → Head → Prop)
    (original saved extra : Set Head) (retained : original ⊆ saved)
    (licensed : saved ⊆ close step (original ∪ extra)) :
    close step (saved ∪ extra) = close step (original ∪ extra) := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, origin, tail⟩
    have source : a ∈ close step (original ∪ extra) := by
      rcases origin with old | fresh
      · exact licensed old
      · exact seeds_le step _ (Or.inr fresh)
    obtain ⟨b, seed, front⟩ := source
    exact ⟨b, seed, front.trans tail⟩
  · exact close_mono (le_refl _) (fun _ h => h.imp_left (fun yes => retained yes))

/-- Keeping old heads does not license all cached discoveries after a
nonmonotone edit. The persisted seeds are reusable exactly when they are
still reachable in the new theory (possibly by different paths). -/
theorem resume_iff_current (step : Head → Head → Prop) (original saved extra : Set Head)
    (retained : original ⊆ saved) :
    close step (saved ∪ extra) = close step (original ∪ extra) ↔
      saved ⊆ close step (original ∪ extra) := by
  constructor
  · intro same h member
    rw [← same]
    exact seeds_le step _ (Or.inl member)
  · exact resume_sound_and_complete step original saved extra retained

/-- Append-only callability. `oldHeads ∪ newHeads` describes the heads
visible at the new cut; order is not used by this membership observation. -/
theorem resume_after_growth {old fresh : Head → Head → Prop} (growth : old ≤ fresh)
    (oldHeads newHeads : Set Head) :
    close fresh (close old oldHeads ∪ newHeads) = close fresh (oldHeads ∪ newHeads) :=
  resume_sound_and_complete fresh oldHeads (close old oldHeads) newHeads
    (seeds_le old oldHeads) (close_mono growth (fun _ h => Or.inl h))

def extend (old delta : Head → Head → Prop) (a b : Head) : Prop :=
  old a b ∨ delta a b

def restrictOutside (known : Set Head) (step : Head → Head → Prop) (a b : Head) : Prop :=
  step a b ∧ a ∉ known ∧ b ∉ known

/-- The boundary to start from: new seeds, and new edges leaving the
already reached region. Neither category needs to enqueue an old vertex. -/
def frontier (known extra : Set Head) (delta : Head → Head → Prop) : Set Head :=
  {b | b ∉ known ∧ (b ∈ extra ∨ ∃ a ∈ known, delta a b)}

private theorem outside_of_reached {known extra : Set Head} {old delta : Head → Head → Prop}
    {x : Head} (path : x ∈ close (restrictOutside known (extend old delta))
      (frontier known extra delta)) : x ∉ known := by
  obtain ⟨a, entered, reach⟩ := path
  induction reach with
  | refl => exact entered.1
  | tail _ edge _ => exact edge.2.2

/-- The exact incremental work region. A path may re-enter the old region,
but then its *last exit* is again one of the new boundary edges. This is why
walking only the induced outside graph loses no reachable key. -/
theorem frontier_exact (old delta : Head → Head → Prop) (known extra : Set Head)
    (settled : ∀ ⦃a b⦄, a ∈ known → old a b → b ∈ known) :
    close (extend old delta) (known ∪ extra) =
      known ∪ close (restrictOutside known (extend old delta)) (frontier known extra delta) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨a, first, path⟩
    induction path with
    | refl =>
      by_cases knownNow : a ∈ known
      · exact Or.inl knownNow
      · have fresh : a ∈ extra := first.resolve_left knownNow
        exact Or.inr ⟨a, ⟨knownNow, Or.inl fresh⟩, .refl⟩
    | @tail mid x _ edge ih =>
      by_cases hk : x ∈ known
      · exact Or.inl hk
      · rcases ih with before | outside
        · have fresh : delta mid x := edge.resolve_left (fun h => hk (settled before h))
          exact Or.inr ⟨x, ⟨hk, Or.inr ⟨mid, before, fresh⟩⟩, .refl⟩
        · have oldOutside := outside_of_reached outside
          exact Or.inr (step_closed outside ⟨edge, oldOutside, hk⟩)
  · intro x reachable
    rcases reachable with oldMember | ⟨a, start, path⟩
    · exact seeds_le _ _ (Or.inl oldMember)
    · have already : a ∈ close (extend old delta) (known ∪ extra) := by
        rcases start.2 with newHead | ⟨b, hb, edge⟩
        · exact seeds_le _ _ (Or.inr newHead)
        · exact ⟨b, Or.inl hb, .single (Or.inr edge)⟩
      obtain ⟨b, hb, initial⟩ := already
      exact ⟨b, hb, initial.trans (ReflTransGen.mono (fun _ _ h => h.1) a x path)⟩

theorem append_only_worklist (old delta : Head → Head → Prop) (base extra : Set Head) :
    close (extend old delta) (base ∪ extra) =
      close old base ∪
        close (restrictOutside (close old base) (extend old delta))
          (frontier (close old base) extra delta) := by
  rw [← resume_after_growth (fresh := extend old delta) (old := old)
    (fun _ _ edge => Or.inl edge) base extra]
  exact frontier_exact old delta _ extra (fun _ _ h e => step_closed h e)

/-- Declared equality edges are undirected even if presentation arrows
elsewhere choose a representative. -/
def undirected (edge : Head → Head → Prop) (a b : Head) : Prop :=
  edge a b ∨ edge b a

theorem undirected_closure (edge : Head → Head → Prop) (a b : Head) :
    ReflTransGen (undirected edge) a b ↔ EqvGen edge a b := by
  constructor
  · intro r
    induction r with
    | refl => exact .refl _
    | @tail x y _ last ih =>
      rcases last with same | back
      · exact .trans _ _ _ ih (.rel _ _ same)
      · exact .trans _ _ _ ih (.symm _ _ (.rel _ _ back))
  · intro r
    induction r with
    | rel x y same => exact .single (Or.inl same)
    | refl x => exact .refl
    | symm x y _ ih =>
      have flipped := ReflTransGen.swap y x ih
      exact ReflTransGen.mono (fun _ _ e => e.symm) y x flipped
    | trans x y z _ _ first last => exact first.trans last

theorem resume_alias_classes {old fresh : Head → Head → Prop} (growth : old ≤ fresh)
    (base extra : Set Head) :
    close (undirected fresh) (close (undirected old) base ∪ extra) =
      close (undirected fresh) (base ∪ extra) :=
  resume_after_growth (fun _ _ h => h.imp (growth _ _) (growth _ _)) base extra

def declaredCallability (equations : List (Head × Head)) (heads : List Head) : Set Head :=
  close (undirected (fun a b => (a, b) ∈ equations)) {x | x ∈ heads}

/-- Append-only presentation data supplies the monotonicity premises.
The observed predicate is callable membership, not rule multiplicity or
which visible rule body will be selected. -/
theorem declared_append (equations more : List (Head × Head)) (heads added : List Head) :
    close (undirected (fun a b => (a, b) ∈ equations ++ more))
      (declaredCallability equations heads ∪ {x | x ∈ added}) =
      declaredCallability (equations ++ more) (heads ++ added) := by
  have seeds : ({x | x ∈ heads} ∪ {x | x ∈ added} : Set Head) = {x | x ∈ heads ++ added} := by
    ext x
    exact List.mem_append.symm
  unfold declaredCallability
  rw [resume_alias_classes
    (old := fun a b => (a, b) ∈ equations)
    (fun _ _ e => List.mem_append_left _ e), seeds]

namespace Examples

private def pair (a b : Bool) : Prop := a = false ∧ b = true

private theorem empty_path {a b : Bool}
    (path : ReflTransGen (undirected (fun _ _ => False)) a b) : a = b := by
  induction path with
  | refl => rfl
  | tail _ e _ => exact False.elim (e.elim id id)

/-- Removing one alias can make an old callable key stale even though the
set of rule heads did not change. -/
theorem removal_invalidates_old_closure :
    true ∈ close (undirected pair) ({false} : Set Bool) ∧
    true ∉ close (undirected (fun _ _ : Bool => False)) ({false} : Set Bool) := by
  refine ⟨⟨false, rfl, .single (Or.inl ⟨rfl, rfl⟩)⟩, ?_⟩
  rintro ⟨a, seed, path⟩
  have atFirst : a = false := seed
  have atLast := empty_path path
  exact Bool.noConfusion (atFirst.symm.trans atLast)

/-- Appending an alias can create a callable key without adding any rule
head. Enqueuing new rule heads alone does not cover this change. -/
theorem alias_append_without_new_head :
    true ∈ frontier ({false} : Set Bool) ∅ (undirected pair) ∧
      true ∉ close (undirected pair) (∅ : Set Bool) := by
  constructor
  · exact ⟨by decide, Or.inr ⟨false, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  · rintro ⟨_, impossible, _⟩
    exact impossible

end Examples

end Mettapedia.GSLT.Equations.CallabilityGrowth
