import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.StaticFootprints
import Mettapedia.OSLF.Framework.DerivedModalities

/-!
# The commit system in logical form: modalities, separation, and the frame law

Operational semantics in logical form takes a reduction relation, presents it as a span
`E → X ← E` of steps, and derives the modalities from change of base: `◇φ` holds where some step
leads into `φ`, `□φ` where every step arriving comes from `φ`, and `◇ ⊣ □`. This module applies the
construction to the commits of a program over occurrence stores (`commitSpan`), so the modalities
below are the generic derived modalities of the framework, instantiated (`possibly`, `before`,
`possibly_galois`).

## What the generic construction gives, and what it does not

The adjunction `◇ ⊣ □` holds for every span and says nothing about commits; on its own it is
decorative here. What the commit system adds is **locality**: occurrence stores split as disjoint
unions, and a commit acts on the part it touches. That is the structure the generated separating
conjunction lacks when stores are read only modulo the equations of a bag: the equations give a
commutative monoid of configurations, not exclusive ownership and not a local transition relation.
Occurrence identities give both.

* **The separating conjunction** (`sep`): a store splits into two disjoint parts satisfying the two
  predicates. It is commutative and associative with the empty store as unit (`sep_comm`,
  `sep_assoc`, `sep_emp`).
* **The frame law** (`frame_law`): if a store part can step by a commit into `φ`, then beside any
  frame that avoids what the commit makes and the regions of its predicate queries, the whole store
  steps into `φ ⋆ frame`. In modal form, `(◇φ) ⋆ ψ ≤ ◇(φ ⋆ ψ)`. For positive commits only the
  freshness side condition remains (`frame_law_of_positive`).
* **Predicate queries break it** (`Controls.predicate_query_breaks_frame`): the absence of a lock
  holds on one part and fails on the whole once the frame holds a lock.
* **Disjoint concurrency with identity pools** (`parallel_law`): two parts, each owned by a process
  whose fresh identities come from its own pool, step independently, and the composite steps
  through both, in modal form `(◇φ ∧ owned U) ⋆ (◇ψ ∧ owned U') ≤ ◇◇(φ ⋆ ψ)`. Per-process pools are
  the allocator that the interleaved iteration theorems need; here they are what makes the frame
  law compose without freshness side conditions.
* **Compiled transforms are an instance** (`transform_possibly_eq`, `transform_frame_law`): the
  span whose steps are the commits a transform fires at a store has the same diamond as the commit
  span of everything the transform ever fires, because a fired commit is fired exactly where it is
  enabled (`fires_of_enabled`, from the footprint exactness of compilation). A transform without
  complete sources and without `every` therefore satisfies the frame law, a check on its text.
* **Exclusive separation under-approximates concurrency** (`Controls.readers_not_separable`): two
  readers of one token are independent and fire together, but the token cannot be split between
  them. Keeping is shared use, which an exclusive conjunction cannot express; independence (the
  exact commutation relation) is the finer judgement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.OSLF.Framework.DerivedModalities

universe u v uV uP

variable {O : Type u} [DecidableEq O] {R : Type v}

/-! ## The span of a program's commits -/

/-- **The reduction span of a program**, a predicate on commits: a step is a store with an enabled
commit of the program; it goes from the store to the store after firing. -/
def commitSpan (label : O → R) (Γ : Commit O R → Prop) : ReductionSpan (Finset O) where
  Edge := {p : Finset O × Commit O R // Γ p.2 ∧ Enabled label p.1 p.2}
  source e := e.1.1
  target e := fire e.1.1 e.1.2

/-- **Step-future**, the derived diamond of the span. -/
def possibly (label : O → R) (Γ : Commit O R → Prop) (φ : Finset O → Prop) : Finset O → Prop :=
  derivedDiamond (commitSpan label Γ) φ

/-- **Step-past**, the derived box of the span. -/
def before (label : O → R) (Γ : Commit O R → Prop) (φ : Finset O → Prop) : Finset O → Prop :=
  derivedBox (commitSpan label Γ) φ

/-- `◇ ⊣ □`, the framework's generic adjunction, at the commit span. -/
theorem possibly_galois (label : O → R) (Γ : Commit O R → Prop) :
    GaloisConnection (possibly label Γ) (before label Γ) :=
  derived_galois (commitSpan label Γ)

section General

variable {label : O → R}

theorem possibly_iff {Γ : Commit O R → Prop} {φ : Finset O → Prop} {S : Finset O} :
    possibly label Γ φ S ↔ ∃ c, Γ c ∧ Enabled label S c ∧ φ (fire S c) := by
  constructor
  · rintro ⟨⟨⟨S', c⟩, inΓ, enabled⟩, rfl, holds⟩
    exact ⟨c, inΓ, enabled, holds⟩
  · rintro ⟨c, inΓ, enabled, holds⟩
    exact ⟨⟨⟨S, c⟩, inΓ, enabled⟩, rfl, holds⟩

/-! ## The separating conjunction -/

/-- **The separating conjunction of store predicates**: the store is a disjoint union of a part
satisfying `φ` and a part satisfying `ψ`. -/
def sep (φ ψ : Finset O → Prop) (S : Finset O) : Prop :=
  ∃ A B, Disjoint A B ∧ A ∪ B = S ∧ φ A ∧ ψ B

/-- The empty store. -/
def emp (S : Finset O) : Prop := S = ∅

theorem sep_comm (φ ψ : Finset O → Prop) : sep φ ψ = sep ψ φ := by
  funext S
  apply propext
  constructor
  · rintro ⟨A, B, apart, rfl, hA, hB⟩
    exact ⟨B, A, apart.symm, Finset.union_comm _ _, hB, hA⟩
  · rintro ⟨A, B, apart, rfl, hA, hB⟩
    exact ⟨B, A, apart.symm, Finset.union_comm _ _, hB, hA⟩

theorem sep_assoc (φ ψ χ : Finset O → Prop) : sep (sep φ ψ) χ = sep φ (sep ψ χ) := by
  funext S
  apply propext
  constructor
  · rintro ⟨AB, C, apartABC, rfl, ⟨A, B, apartAB, rfl, hA, hB⟩, hC⟩
    rw [Finset.disjoint_union_left] at apartABC
    refine ⟨A, B ∪ C, Finset.disjoint_union_right.mpr ⟨apartAB, apartABC.1⟩,
      (Finset.union_assoc _ _ _).symm, hA, B, C, apartABC.2, rfl, hB, hC⟩
  · rintro ⟨A, BC, apartABC, rfl, hA, ⟨B, C, apartBC, rfl, hB, hC⟩⟩
    rw [Finset.disjoint_union_right] at apartABC
    refine ⟨A ∪ B, C, Finset.disjoint_union_left.mpr ⟨apartABC.2, apartBC⟩,
      Finset.union_assoc _ _ _, ⟨A, B, apartABC.1, rfl, hA, hB⟩, hC⟩

theorem sep_emp (φ : Finset O → Prop) : sep φ emp = φ := by
  funext S
  apply propext
  constructor
  · rintro ⟨A, B, -, rfl, hA, rfl⟩
    simpa using hA
  · intro hS
    exact ⟨S, ∅, Finset.disjoint_empty_right _, Finset.union_empty _, hS, rfl⟩

/-! ## The frame law -/

/-- Firing beside a frame: the result is the part's result beside the frame, and they stay apart
when the frame avoids what the commit makes. -/
theorem fire_beside_frame {A B : Finset O} {c : Commit O R} (enabled : Enabled label A c)
    (apart : Disjoint A B) (madeApart : Disjoint c.made B) :
    fire (A ∪ B) c = fire A c ∪ B ∧ Disjoint (fire A c) B := by
  refine ⟨fire_union_frame (Finset.disjoint_of_subset_left enabled.taken_subset apart), ?_⟩
  refine Finset.disjoint_left.mpr fun o inFire inB => ?_
  rcases mem_fire.mp inFire with ⟨inA, -⟩ | made
  · exact Finset.disjoint_left.mp apart inA inB
  · exact Finset.disjoint_left.mp madeApart made inB

/-- **The frame law.** When every commit of the program avoids, in what it makes and in the regions
of its predicate queries, every store satisfying the frame `ψ`, then `(◇φ) ⋆ ψ ≤ ◇(φ ⋆ ψ)`. -/
theorem frame_law {Γ : Commit O R → Prop} {φ ψ : Finset O → Prop}
    (madeApart : ∀ c, Γ c → ∀ B, ψ B → Disjoint c.made B)
    (outsideQueries : ∀ c, Γ c → ∀ B, ψ B → ∀ read ∈ c.queries, ∀ o ∈ B, read.region (label o) = false) :
    sep (possibly label Γ φ) ψ ≤ possibly label Γ (sep φ ψ) := by
  rintro S ⟨A, B, apart, rfl, stepA, hB⟩
  obtain ⟨c, inΓ, enabled, hφ⟩ := possibly_iff.mp stepA
  obtain ⟨fireEq, apartAfter⟩ := fire_beside_frame enabled apart (madeApart c inΓ B hB)
  refine possibly_iff.mpr ⟨c, inΓ, enabled.frame (madeApart c inΓ B hB) (outsideQueries c inΓ B hB), ?_⟩
  rw [fireEq]
  exact ⟨fire A c, B, apartAfter, rfl, hφ, hB⟩

/-- **The frame law for positive programs**: only freshness remains. -/
theorem frame_law_of_positive {Γ : Commit O R → Prop} {φ ψ : Finset O → Prop}
    (positive : ∀ c, Γ c → c.Positive) (madeApart : ∀ c, Γ c → ∀ B, ψ B → Disjoint c.made B) :
    sep (possibly label Γ φ) ψ ≤ possibly label Γ (sep φ ψ) :=
  frame_law madeApart fun c inΓ _ _ read member => by
    rw [show c.queries = [] from positive c inΓ] at member
    simp at member

/-! ## Disjoint concurrency with identity pools -/

/-- A store predicate whose stores lie in a pool of identities. -/
def owned (U : Finset O) (φ : Finset O → Prop) (S : Finset O) : Prop := φ S ∧ S ⊆ U

/-- **Disjoint concurrency.** Two programs whose commits are positive and make identities only from
their own pools, disjoint from each other: a store split into a part of the first pool that can
step into `φ` and a part of the second that can step into `ψ` steps through both into `φ ⋆ ψ`. -/
theorem parallel_law {Γ Δ : Commit O R → Prop} {φ ψ : Finset O → Prop} {U U' : Finset O}
    (pools : Disjoint U U') (positiveΓ : ∀ c, Γ c → c.Positive) (positiveΔ : ∀ d, Δ d → d.Positive)
    (poolΓ : ∀ c, Γ c → c.made ⊆ U) (poolΔ : ∀ d, Δ d → d.made ⊆ U') :
    sep (owned U (possibly label Γ φ)) (owned U' (possibly label Δ ψ)) ≤
      possibly label Γ (possibly label Δ (sep φ ψ)) := by
  rintro S ⟨A, B, apart, rfl, ⟨stepA, inU⟩, ⟨stepB, inU'⟩⟩
  obtain ⟨c, inΓ, enabledC, hφ⟩ := possibly_iff.mp stepA
  obtain ⟨d, inΔ, enabledD, hψ⟩ := possibly_iff.mp stepB
  have cApartB : Disjoint c.made B :=
    Finset.disjoint_of_subset_left (poolΓ c inΓ) (Finset.disjoint_of_subset_right inU' pools)
  obtain ⟨fireC, apartC⟩ := fire_beside_frame enabledC apart cApartB
  have fireCInU : fire A c ⊆ U := by
    intro o member
    rcases mem_fire.mp member with ⟨inA, -⟩ | made
    · exact inU inA
    · exact poolΓ c inΓ made
  have dApart : Disjoint d.made (fire A c) :=
    Finset.disjoint_of_subset_left (poolΔ d inΔ)
      (Finset.disjoint_of_subset_right fireCInU pools.symm)
  obtain ⟨fireD, apartD⟩ := fire_beside_frame enabledD apartC.symm dApart
  refine possibly_iff.mpr ⟨c, inΓ,
    enabledC.frame_of_positive (positiveΓ c inΓ) cApartB, ?_⟩
  rw [fireC, Finset.union_comm]
  refine possibly_iff.mpr ⟨d, inΔ, enabledD.frame_of_positive (positiveΔ d inΔ) dApart, ?_⟩
  rw [fireD]
  exact ⟨fire A c, fire B d, apartD.symm, Finset.union_comm _ _, hφ, hψ⟩

end General

/-! ## Compiled transforms -/

section Transforms

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {V : Type uV} {T : Type v} {P : Type uP} {L : TermLayer V T P} {m : Matcher V T P}
  {label : O → T}

/-- **A fired commit is fired wherever it is enabled.** -/
theorem fires_of_enabled (sound : Matcher.Sound L m) (monotone : Matcher.RegionMonotone m)
    {t : Transform V T P} {S S' : Finset O} {c : Commit O T} (fires : Fires L m label S t c)
    (enabled : Enabled label S' c) : Fires L m label S' t c := by
  obtain ⟨x, member, linear, commit⟩ := fires
  exact ⟨x, (enabled_iff_mem_rows sound monotone member linear commit enabled.fresh).mp enabled,
    linear, { commit with fresh := enabled.fresh }⟩

/-- **The reduction span of a compiled transform**: a step is a commit it fires at a store. -/
def transformSpan (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) (t : Transform V T P) :
    ReductionSpan (Finset O) where
  Edge := {p : Finset O × Commit O T // Fires L m label p.1 t p.2}
  source e := e.1.1
  target e := fire e.1.1 e.1.2

/-- The commits a transform fires at some store. -/
def FiredBy (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) (t : Transform V T P)
    (c : Commit O T) : Prop :=
  ∃ S, Fires L m label S t c

/-- **The transform's diamond is the commit span's diamond** of everything it fires. -/
theorem transform_possibly_eq (sound : Matcher.Sound L m) (monotone : Matcher.RegionMonotone m)
    (t : Transform V T P) :
    derivedDiamond (transformSpan L m label t) = possibly label (FiredBy L m label t) := by
  funext φ S
  apply propext
  constructor
  · rintro ⟨⟨⟨S', c⟩, fires⟩, rfl, holds⟩
    exact possibly_iff.mpr ⟨c, ⟨S', fires⟩, fires.enabled, holds⟩
  · intro step
    obtain ⟨c, ⟨S', fires⟩, enabled, holds⟩ := possibly_iff.mp step
    exact ⟨⟨⟨S, c⟩, fires_of_enabled sound monotone fires enabled⟩, rfl, holds⟩

/-- **The frame law for a transform without complete sources and `every`**, read off its text. -/
theorem transform_frame_law (sound : Matcher.Sound L m) (monotone : Matcher.RegionMonotone m)
    {t : Transform V T P} (shape : t.sources.queryFree = true) {φ ψ : Finset O → Prop}
    (madeApart : ∀ c, FiredBy L m label t c → ∀ B, ψ B → Disjoint c.made B) :
    sep (derivedDiamond (transformSpan L m label t) φ) ψ ≤
      derivedDiamond (transformSpan L m label t) (sep φ ψ) := by
  rw [transform_possibly_eq sound monotone]
  exact frame_law_of_positive (fun c ⟨_, fires⟩ => positive_of_noQueries shape fires) madeApart

end Transforms

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls

/-- Stores holding a lock. -/
def holdsLock (S : Finset ℕ) : Prop := 1 ∈ S

/-- **Predicate queries break the frame law**: the absence of a lock can fire on the token's part,
and the frame holds the lock; the whole store cannot fire it. -/
theorem predicate_query_breaks_frame :
    sep (possibly label (· = unlessLocked) (fun _ => True)) holdsLock ({0} ∪ {1}) ∧
      ¬ possibly label (· = unlessLocked) (fun _ => True) ({0} ∪ {1}) := by
  refine ⟨⟨{0}, {1}, by decide, rfl, possibly_iff.mpr ⟨unlessLocked, rfl, absence_holds_empty,
    trivial⟩, by simp [holdsLock]⟩, fun step => ?_⟩
  obtain ⟨c, rfl, enabled, -⟩ := possibly_iff.mp step
  exact absence_not_framed enabled

/-- The frame holding just the lock. -/
def justLock (S : Finset ℕ) : Prop := S = {1}

/-- **The frame law, positive control**: the reader of the token fires beside the lock. -/
theorem reader_frame :
    possibly label (· = reader) (sep (fun _ => True) justLock) ({0} ∪ {1}) :=
  frame_law_of_positive (Γ := (· = reader)) (φ := fun _ => True) (ψ := justLock)
    (fun c same => same ▸ rfl)
    (fun c same B lock => by subst same; unfold justLock at lock; subst lock; decide)
    ({0} ∪ {1}) ⟨{0}, {1}, by decide, rfl, possibly_iff.mpr ⟨reader, rfl, reader_enabled, trivial⟩, rfl⟩

/-- **Exclusive separation under-approximates concurrency**: two readers of one token are
independent, but the one-token store does not split into a part where each can fire. -/
theorem readers_not_separable :
    Independent label reader reader₂ ∧ Enabled label {0} reader ∧ Enabled label {0} reader₂ ∧
      ¬ sep (possibly label (· = reader) (fun _ => True))
        (possibly label (· = reader₂) (fun _ => True)) {0} := by
  refine ⟨readers_independent, reader_enabled, reader₂_enabled, ?_⟩
  rintro ⟨A, B, apart, cover, stepA, stepB⟩
  obtain ⟨c, rfl, enabledA, -⟩ := possibly_iff.mp stepA
  obtain ⟨d, rfl, enabledB, -⟩ := possibly_iff.mp stepB
  have inA : 0 ∈ A := enabledA.kept_subset (by simp [reader])
  have inB : 0 ∈ B := enabledB.kept_subset (by simp [reader₂])
  exact Finset.disjoint_left.mp apart inA inB

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
