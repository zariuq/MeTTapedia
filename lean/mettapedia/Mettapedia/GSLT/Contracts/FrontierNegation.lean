import Mettapedia.GSLT.Contracts.AbsenceFrontier
import Mettapedia.GSLT.Contracts.CoordinationFreedom

/-!
# Frontier absence is intuitionistic negation, certified

Read the states a program can reach as the worlds of a Kripke model ordered by
reachability.  A read of what is present now is **persistent**: once true, true
in every reachable state, provided the program only adds.  Persistent
statements are closed under conjunction, disjunction and existential
quantification (`Persistent.and`, `Persistent.or`, `Persistent.exists`), the
positive fragment of intuitionistic logic, and these are the reads a
presence-only program makes.

**Intuitionistic negation** `¬φ` holds in a state when `φ` fails in every state
reachable from it (`knot`).  It is persistent too (`knot_persistent`), and it is
the meaning of "absent in every possible future".  It quantifies over the
future, so it is not a read of the present.  Its finite evidence is an
**inductive invariant**: a set of states that contains the present state, is
closed under steps, and excludes `φ` (`knot_iff_invariant`).  The reachable
states are the least such set.

## In a self-modifying space

For the MM2 over-approximation of firing in
`Mettapedia.GSLT.Contracts.AbsenceFrontier`:

* **Frontier absence is exactly intuitionistic negation**
  (`knot_iff_absent_frontier`): a pattern is absent in every reachable state if
  and only if it is absent now and no pending executable may eventually
  produce it.  The new direction is that every potential producer can fire
  (`reaches_match_of_mayProduce`).  So a snapshot absence read is never
  contradicted later exactly at a frontier.
* **A frontier is sound for every refinement** (`refinement_sound`): if the
  actual semantics only takes steps of the over-approximation, absence at a
  frontier is absence in every actually reachable state.
* **and not complete for refinements** (`Controls.refinement_incomplete`): when
  a producer can never fire, the pattern is absent in every actually
  reachable state, though no frontier exists.  The frontier is a checkable
  certificate, not a decision procedure for actual reachability.

## Certified by ownership, revoked only by the owner

A module that owns a head certifies a frontier for every pattern over that
head by a check on its own atoms (`ownership_certifies_frontier`), provided the
space obeys the namespace discipline of
`Mettapedia.Languages.MeTTa.Seal.ClosedResolver`: an executable outputs only
atoms whose heads its own module owns or nobody owns.  The module's atoms must
form a set closed under the module-owned outputs of its executables and contain
no match (`FrozenAt`).

* **Atoms of other modules never revoke it** (`foreign_extension_certified`):
  adding atoms whose heads the module does not own keeps the certificate.
* **The owner revokes it by installing a producer**
  (`Controls.owner_revokes`): a new module executable that outputs a match makes
  a previously final absence false.  A verdict read under a certificate is
  valid for that certificate's rule set; changing the rule set starts a new
  epoch of the module.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.FrontierNegation

open Mettapedia.GSLT.Contracts.AbsenceFrontier

universe u v w x

/-! ## Kripke semantics over reachability -/

section Kripke

variable {S : Type u} (step : S → S → Prop)

/-- Reachability in zero or more steps. -/
abbrev Reaches : S → S → Prop := Relation.ReflTransGen step

/-- A statement is persistent when it survives every step. -/
def Persistent (φ : S → Prop) : Prop := ∀ s t, Reaches step s t → φ s → φ t

theorem Persistent.and {φ ψ : S → Prop} (hφ : Persistent step φ) (hψ : Persistent step ψ) :
    Persistent step fun s => φ s ∧ ψ s :=
  fun s t reaches holds => ⟨hφ s t reaches holds.1, hψ s t reaches holds.2⟩

theorem Persistent.or {φ ψ : S → Prop} (hφ : Persistent step φ) (hψ : Persistent step ψ) :
    Persistent step fun s => φ s ∨ ψ s :=
  fun s t reaches holds => holds.elim (fun h => Or.inl (hφ s t reaches h))
    (fun h => Or.inr (hψ s t reaches h))

theorem Persistent.exists {ι : Type v} {φ : ι → S → Prop} (hφ : ∀ i, Persistent step (φ i)) :
    Persistent step fun s => ∃ i, φ i s :=
  fun s t reaches ⟨i, holds⟩ => ⟨i, hφ i s t reaches holds⟩

/-- A statement survives every step if it survives one step. -/
theorem persistent_of_step {φ : S → Prop} (one : ∀ s t, step s t → φ s → φ t) : Persistent step φ := by
  intro s t reaches holds
  induction reaches with
  | refl => exact holds
  | tail _ last ih => exact one _ _ last ih

/-- **Presence reads are persistent**: under rules that only add, whatever is
present in a store stays present, so the reads of a presence-only program are
statements of the positive, persistent fragment. -/
theorem presence_persistent {α : Type v} [CompleteLattice α] {ι : Type w} {rules : ι → α → α}
    (inflationary : ∀ rule store, store ≤ rules rule store) (present : α) :
    Persistent (fun store next => ∃ rule, next = rules rule store) fun store => present ≤ store :=
  persistent_of_step _ fun _ _ ⟨rule, next⟩ holds => next ▸ holds.trans (inflationary rule _)

/-- **Intuitionistic negation**: false in every reachable state. -/
def knot (φ : S → Prop) (s : S) : Prop := ∀ t, Reaches step s t → ¬ φ t

/-- **Intuitionistic implication**. -/
def kimp (φ ψ : S → Prop) (s : S) : Prop := ∀ t, Reaches step s t → φ t → ψ t

theorem knot_persistent (φ : S → Prop) : Persistent step (knot step φ) :=
  fun _ _ first holds u second => holds u (first.trans second)

theorem kimp_persistent (φ ψ : S → Prop) : Persistent step (kimp step φ ψ) :=
  fun _ _ first holds u second => holds u (first.trans second)

/-- Intuitionistic negation implies classical negation now. -/
theorem knot_now {φ : S → Prop} {s : S} (holds : knot step φ s) : ¬ φ s :=
  holds s Relation.ReflTransGen.refl

/-- A step-closed set. -/
def Invariant (region : Set S) : Prop := ∀ s ∈ region, ∀ t, step s t → t ∈ region

/-- **Intuitionistic negation is certified by an inductive invariant.** -/
theorem knot_iff_invariant (φ : S → Prop) (s : S) :
    knot step φ s ↔ ∃ region : Set S, s ∈ region ∧ Invariant step region ∧ ∀ t ∈ region, ¬ φ t := by
  constructor
  · intro holds
    refine ⟨{t | Reaches step s t}, Relation.ReflTransGen.refl, ?_, fun t member => holds t member⟩
    intro t member u next
    exact Relation.ReflTransGen.tail member next
  · rintro ⟨region, member, invariant, excluded⟩ t reaches
    apply excluded
    induction reaches with
    | refl => exact member
    | tail _ last ih => exact invariant _ ih _ last

end Kripke

/-! ## In a self-modifying space -/

section Space

variable {Atom : Type u} {Pattern : Type v} (model : SpaceModel Atom Pattern)

/-- **Every potential producer can fire**: under the over-approximation, a pending
executable that may eventually produce a match reaches a state with one. -/
theorem reaches_match_of_mayProduce {pattern : Pattern} {exec : Atom}
    (produces : MayProduce model pattern exec) :
    ∀ space : Set Atom, exec ∈ space → model.isExec exec →
      ∃ later, Reaches (Step model) space later ∧ ∃ atom ∈ later, model.fits pattern atom := by
  induction produces with
  | @direct exec atom output matched =>
      intro space member isExec
      refine ⟨(space \ {exec}) ∪ model.outputs exec,
        Relation.ReflTransGen.single ⟨exec, member, isExec, le_rfl⟩, atom, Or.inr output, matched⟩
  | @indirect exec atom output atomExec _ ih =>
      intro space member isExec
      obtain ⟨later, reaches, found⟩ :=
        ih ((space \ {exec}) ∪ model.outputs exec) (Or.inr output) atomExec
      exact ⟨later, Relation.ReflTransGen.head ⟨exec, member, isExec, le_rfl⟩ reaches, found⟩

/-- **Frontier absence is exactly intuitionistic negation** of a match. -/
theorem knot_iff_absent_frontier (pattern : Pattern) (space : Set Atom) :
    knot (Step model) (fun later => ¬ Absent model pattern later) space ↔
      Absent model pattern space ∧ Frontier model pattern space := by
  constructor
  · intro holds
    have now : Absent model pattern space := not_not.1 (knot_now (Step model) holds)
    refine ⟨now, fun exec member isExec produces => ?_⟩
    obtain ⟨later, reaches, atom, inLater, matched⟩ :=
      reaches_match_of_mayProduce model produces space member isExec
    exact holds later reaches fun absent => absent atom inLater matched
  · rintro ⟨absent, frontier⟩ later reaches present
    exact present (absent_of_reaches model absent frontier reaches).1

/-- **A frontier is sound for every refinement** of the over-approximation. -/
theorem refinement_sound {actual : Set Atom → Set Atom → Prop}
    (refines : ∀ space next, actual space next → Step model space next) {pattern : Pattern}
    {space : Set Atom} (absent : Absent model pattern space) (frontier : Frontier model pattern space) :
    knot actual (fun later => ¬ Absent model pattern later) space := by
  intro later reaches present
  have overReaches : Reaches (Step model) space later :=
    Relation.ReflTransGen.mono (fun a b h => refines a b h) _ _ reaches
  exact present (absent_of_reaches model absent frontier overReaches).1

/-! ## Certified by ownership -/

section Ownership

variable {Head : Type w} {Module : Type x}

/-- **The namespace discipline**: an executable outputs only atoms whose heads
its own module owns or nobody owns. -/
def Disciplined (head : Atom → Head) (owner : Head → Option Module) : Prop :=
  ∀ exec, model.isExec exec → ∀ out ∈ model.outputs exec,
    owner (head out) = none ∨ owner (head out) = owner (head exec)

/-- The pattern matches only atoms over heads the module owns. -/
def OwnedPattern (head : Atom → Head) (owner : Head → Option Module) (module : Module)
    (pattern : Pattern) : Prop :=
  ∀ atom, model.fits pattern atom → owner (head atom) = some module

/-- **The module is frozen at a set of its atoms**: the set is closed under the
module-owned outputs of its executables and contains no match. -/
def FrozenAt (head : Atom → Head) (owner : Head → Option Module) (module : Module)
    (pattern : Pattern) (atoms : Set Atom) : Prop :=
  (∀ exec ∈ atoms, model.isExec exec → ∀ out ∈ model.outputs exec,
      owner (head out) = some module → out ∈ atoms) ∧
    ∀ atom ∈ atoms, ¬ model.fits pattern atom

/-- The region certified by ownership: atoms of other modules, and the module's
frozen atoms. -/
def ownedRegion (head : Atom → Head) (owner : Head → Option Module) (module : Module)
    (atoms : Set Atom) : Set Atom :=
  {atom | owner (head atom) ≠ some module} ∪ atoms

/-- **Ownership certifies a frontier.** -/
theorem ownership_certifies_frontier {head : Atom → Head} {owner : Head → Option Module}
    {module : Module} {pattern : Pattern} {atoms : Set Atom}
    (disciplined : Disciplined model head owner) (owned : OwnedPattern model head owner module pattern)
    (frozen : FrozenAt model head owner module pattern atoms) {space : Set Atom}
    (within : ∀ atom ∈ space, owner (head atom) = some module → atom ∈ atoms) :
    Absent model pattern space ∧ Frontier model pattern space := by
  rw [frontier_iff_closedRegion]
  refine ⟨ownedRegion head owner module atoms, ?_, ?_, ?_⟩
  · intro atom member
    by_cases mine : owner (head atom) = some module
    · exact Or.inr (within atom member mine)
    · exact Or.inl mine
  · intro exec inRegion isExec out output
    by_cases mine : owner (head out) = some module
    · rcases inRegion with foreign | frozenExec
      · rcases disciplined exec isExec out output with none | same
        · rw [none] at mine; exact absurd mine (by simp)
        · rw [same] at mine; exact absurd mine foreign
      · exact Or.inr (frozen.1 exec frozenExec isExec out output mine)
    · exact Or.inl mine
  · intro atom inRegion matched
    rcases inRegion with foreign | frozenAtom
    · exact foreign (owned atom matched)
    · exact frozen.2 atom frozenAtom matched

/-- **Atoms of other modules never revoke the certificate.** -/
theorem foreign_extension_certified {head : Atom → Head} {owner : Head → Option Module}
    {module : Module} {pattern : Pattern} {atoms : Set Atom}
    (disciplined : Disciplined model head owner) (owned : OwnedPattern model head owner module pattern)
    (frozen : FrozenAt model head owner module pattern atoms) {space extra : Set Atom}
    (within : ∀ atom ∈ space, owner (head atom) = some module → atom ∈ atoms)
    (foreign : ∀ atom ∈ extra, owner (head atom) ≠ some module) :
    Absent model pattern (space ∪ extra) ∧ Frontier model pattern (space ∪ extra) := by
  refine ownership_certifies_frontier model disciplined owned frozen ?_
  rintro atom (member | member) mine
  · exact within atom member mine
  · exact absurd mine (foreign atom member)

end Ownership

end Space

/-! ## Controls -/

namespace Controls

open Mettapedia.GSLT.Contracts.AbsenceFrontier.Controls

/-- No firing at all: a semantics in which the producer's guard never holds. -/
def neverFires : Set Item → Set Item → Prop := fun _ _ => False

/-- **A frontier is not complete for refinements**: if the producer never fires,
the target is absent in every actually reachable state, but no frontier exists. -/
theorem refinement_incomplete :
    knot neverFires (fun later => ¬ Absent items () later) {.producer, .fact} ∧
      ¬ Frontier items () {.producer, .fact} := by
  refine ⟨?_, snapshot_absence_flips.2.2⟩
  intro later reaches present
  cases reaches with
  | refl => exact present snapshot_absence_flips.1
  | tail _ last => exact last

/-- The heads of the control: one module owns the producer and the target. -/
def itemOwner : Item → Option Unit
  | .fact => none
  | _ => some ()

/-- **The owner revokes by installing a producer**: with the module frozen at no
atoms the inert space is certified, and the module's new producer makes the
absence false in a reachable state. -/
theorem owner_revokes :
    (Absent items () {.fact} ∧ Frontier items () {.fact}) ∧
      ∃ later, Reaches (Step items) {.producer, .fact} later ∧ ¬ Absent items () later := by
  refine ⟨?_, ⟨{.fact, .target}, Relation.ReflTransGen.single fire,
    snapshot_absence_flips.2.1⟩⟩
  refine ownership_certifies_frontier items (head := id) (owner := itemOwner) (module := ())
    (atoms := ∅) ?_ ?_ ⟨?_, ?_⟩ ?_
  · intro exec isExec out output
    simp only [items] at isExec output
    subst isExec
    simp only [if_true, Set.mem_singleton_iff] at output
    subst output
    right
    rfl
  · intro atom matched
    simp only [items] at matched
    subst matched
    rfl
  · intro exec member
    exact absurd member (Set.notMem_empty exec)
  · intro atom member
    exact absurd member (Set.notMem_empty atom)
  · intro atom member mine
    simp only [Set.mem_singleton_iff] at member
    subst member
    exact absurd mine (by simp [itemOwner])

end Controls

end Mettapedia.GSLT.Contracts.FrontierNegation
