import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeDeadEquivalence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeResidualExample
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceGeneric

/-!
# Agreement up to dead names is a bisimulation of the native step

## Programs that do not see dead names

A **live program** offers live firings under labels (`liveOffers`). It is **dead-name invariant**
(`DeadInvariant`) when, along every dead-name extension, it offers the carried firings, and every
firing it offers at the larger state is the carrying of one it offers at the smaller. Its firings
then mention only names that every inclusion reaches.

* **Agreement up to dead names is a bisimulation** (`bisimilar_of_deadEquiv`) of the generic step's
  labelled moves (`Race.Generic.Bisimilar`), for every dead-name invariant program. Agreeing states
  satisfy the same Hennessy–Milner formulas (`sat_iff_of_deadEquiv`).
* **The hypothesis is satisfied** (`closedOffers_invariant`): a program of closed firings, whose
  rules, outputs and query patterns mention no name of the state, is dead-name invariant. Closed
  firings still constrain the state's names through the rows they take and read.

## Controls

They are in `Step/NativeStepBisimControls`: a state and the same state with one extra dead name are
bisimilar although no renaming of names relates their frames; a state whose knowledge contradicts
itself on its one name is neither bisimilar to the first nor in agreement with it up to dead names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Mettapedia.GSLT.HennessyMilner (Formula)

namespace NativeDead

/-! ## The labelled step over live programs -/

section Bisimulation

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] {L : Type}

/-- The native firings a live program offers. -/
def liveOffers (program : L → (s : NativeState S O Γ sort) → LiveFiring s → Prop)
    (ℓ : L) (s : NativeState S O Γ sort) (g : NativeFiring s) : Prop :=
  ∃ f : LiveFiring s, program ℓ s f ∧ f.toNative = g

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **A program that does not see dead names**: along every dead-name extension it offers the
carried firings, and only those. -/
def DeadInvariant (program : L → (s : NativeState S O Γ sort) → LiveFiring s → Prop) : Prop :=
  ∀ ⦃s u : NativeState S O Γ sort⦄ (e : DeadExtension s u) (ℓ : L),
    (∀ f, program ℓ s f → program ℓ u (e.firing f)) ∧ ∀ g, program ℓ u g → ∃ f, program ℓ s f ∧ e.firing f = g

/-- One direction of the bisimulation: a move of `s` is matched by `t`. -/
theorem match_move {program : L → (s : NativeState S O Γ sort) → LiveFiring s → Prop}
    (invariant : DeadInvariant program) {s t u : NativeState S O Γ sort} (e : DeadExtension s u)
    (e' : DeadExtension t u) {ℓ : L} {s' : NativeState S O Γ sort}
    (moved : Race.Generic.Moves native.toStep (liveOffers program) s ℓ s') :
    ∃ t', Race.Generic.Moves native.toStep (liveOffers program) t ℓ t' ∧ DeadEquiv s' t' := by
  obtain ⟨g, admitted, ⟨f, offered, rfl⟩, rfl⟩ := moved
  obtain ⟨f', offered', same⟩ := (invariant e' ℓ).2 _ ((invariant e ℓ).1 f offered)
  obtain ⟨admits, results⟩ := DeadEquiv.step e e' same.symm
  exact ⟨_, ⟨f'.toNative, admits.mp admitted, ⟨f', offered', rfl⟩, rfl⟩, results admitted (admits.mp admitted)⟩

/-- **Agreement up to dead names is a bisimulation of the native step**, for every program that does
not see dead names. -/
theorem bisimilar_of_deadEquiv {program : L → (s : NativeState S O Γ sort) → LiveFiring s → Prop}
    (invariant : DeadInvariant program) {s t : NativeState S O Γ sort} (same : DeadEquiv s t) :
    Race.Generic.Bisimilar native.toStep (liveOffers program) s t := by
  refine ⟨DeadEquiv, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, same⟩
  · rintro s t ⟨u, ⟨e⟩, ⟨e'⟩⟩ ℓ s' moved
    exact match_move invariant e e' moved
  · rintro s t ⟨u, ⟨e⟩, ⟨e'⟩⟩ ℓ t' moved
    obtain ⟨s', moved', related⟩ := match_move invariant e' e moved
    exact ⟨s', moved', related.symm⟩

/-- **States that agree up to dead names satisfy the same Hennessy–Milner formulas.** -/
theorem sat_iff_of_deadEquiv {program : L → (s : NativeState S O Γ sort) → LiveFiring s → Prop}
    (invariant : DeadInvariant program) {s t : NativeState S O Γ sort} (same : DeadEquiv s t)
    (φ : Formula PEmpty.{1} L) :
    Race.Generic.Sat native.toStep (liveOffers program) φ s ↔ Race.Generic.Sat native.toStep (liveOffers program) φ t :=
  (Race.Generic.system native.toStep (liveOffers program)).logicallyEquivalent_of_bisimilar
    (bisimilar_of_deadEquiv invariant same) φ

/-- **Garbage-collecting dead helper names is sound**: a live firing's result is bisimilar to its
core, for every program that does not see dead names. -/
theorem result_bisimilar_core {program : L → (s : NativeState S O Γ sort) → LiveFiring s → Prop}
    (invariant : DeadInvariant program) {s : NativeState S O Γ sort} (f : LiveFiring s)
    (admitted : f.toNative.Realized) :
    Race.Generic.Bisimilar native.toStep (liveOffers program) (core f) (native.result f.toNative admitted) :=
  bisimilar_of_deadEquiv invariant (result_equiv_core f admitted)

end Bisimulation

/-! ## Closed programs do not see dead names -/

section Closed

variable {S : Signature} {O : Type} {Γ : Ctx S} {sort : S.Srt}

/-- No names. -/
def noNames : Empty → MetaArity S := fun impossible => nomatch impossible

/-- The assignment out of no names. -/
def fromNone {W : Type} (target : W → MetaArity S) : Assignment (noNames (S := S)) target :=
  fun impossible => nomatch impossible

theorem fromNone_unique {W W' : Type} {target : W → MetaArity S} {next : W' → MetaArity S}
    (later : Assignment target next) : Assignment.compose later (fromNone target) = fromNone next :=
  funext fun impossible => nomatch impossible

/-- **A closed firing**: its rule, outputs and query patterns mention no name. -/
structure ClosedFiring (S : Signature) (O : Type) (Γ : Ctx S) (sort : S.Srt) where
  rule : RuleInstance (Term (signature S (noNames (S := S))) Γ sort)
  selection : Selection O
  outputs : O → Term (signature S (noNames (S := S))) Γ sort
  patterns : List (Term (signature S (noNames (S := S))) Γ sort × Finset O)
  fuel : ℕ

namespace ClosedFiring

/-- A closed firing at a state. -/
def atState (k : ClosedFiring S O Γ sort) (s : NativeState S O Γ sort) : LiveFiring s where
  rule := k.rule.map (instantiate (fromNone _))
  selection := k.selection
  outputs o := instantiate (fromNone _) (k.outputs o)
  patterns := k.patterns.map fun pattern => (instantiate (fromNone _) pattern.1, pattern.2)
  fuel := k.fuel

/-- **Carrying a closed firing is the closed firing at the larger state.** -/
theorem firing_at {s u : NativeState S O Γ sort} (e : Inclusion s u) (k : ClosedFiring S O Γ sort) :
    e.firing (k.atState s) = k.atState u := by
  have rule : (k.rule.map (instantiate (fromNone _))).map (instantiate e.source) =
      k.rule.map (instantiate (fromNone _)) := by
    rw [OccurrenceRelabeling.rule_map_comp]
    exact congrArg (fun mapping => k.rule.map mapping) (funext fun term =>
      (Assignment.instantiate_compose _ _ term).symm.trans
        (congrArg (fun assignment => instantiate assignment term) (fromNone_unique e.source)))
  have outputs : (fun o => instantiate e.target (instantiate (fromNone _) (k.outputs o))) =
      fun o => instantiate (fromNone _) (k.outputs o) :=
    funext fun o => (Assignment.instantiate_compose _ _ _).symm.trans
      (congrArg (fun assignment => instantiate assignment (k.outputs o)) (fromNone_unique e.target))
  have patterns : (k.patterns.map fun pattern => (instantiate (fromNone _) pattern.1, pattern.2)).map
      (fun pattern => (instantiate e.target pattern.1, pattern.2)) =
      k.patterns.map fun pattern => (instantiate (fromNone _) pattern.1, pattern.2) := by
    rw [List.map_map]
    exact List.map_congr_left fun pattern _ => congrArg (fun term => (term, pattern.2))
      ((Assignment.instantiate_compose _ _ _).symm.trans
        (congrArg (fun assignment => instantiate assignment pattern.1) (fromNone_unique e.target)))
  unfold Inclusion.firing ClosedFiring.atState
  rw [rule, outputs, patterns]

end ClosedFiring

variable {L : Type}

/-- The live program of a family of closed firings. -/
def closedOffers (program : L → ClosedFiring S O Γ sort → Prop) (ℓ : L) (s : NativeState S O Γ sort)
    (f : LiveFiring s) : Prop :=
  ∃ k, program ℓ k ∧ f = k.atState s

/-- **Closed programs do not see dead names.** -/
theorem closedOffers_invariant [DecidableEq O] (program : L → ClosedFiring S O Γ sort → Prop) :
    DeadInvariant (closedOffers program) := by
  intro s u e ℓ
  refine ⟨?_, ?_⟩
  · rintro f ⟨k, offered, rfl⟩
    exact ⟨k, offered, ClosedFiring.firing_at e.toInclusion k⟩
  · rintro g ⟨k, offered, rfl⟩
    exact ⟨k.atState s, ⟨k, offered, rfl⟩, ClosedFiring.firing_at e.toInclusion k⟩

end Closed

end NativeDead

#print axioms NativeDead.bisimilar_of_deadEquiv
#print axioms NativeDead.sat_iff_of_deadEquiv
#print axioms NativeDead.result_bisimilar_core
#print axioms NativeDead.ClosedFiring.firing_at
#print axioms NativeDead.closedOffers_invariant

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
