import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Fold
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverOrbits
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverSightings

/-!
# Symmetry-quotiented folding of the one-frame instance

The escape-relative transport that renames occurrences (`renamingEscaping`) identifies escaped
states by a label-keeping renaming that carries one configuration to the other up to the solutions of
its knowledge, and the record to the other record. A canonical key for it is therefore a canonical form
of the configuration, the record and their relation together, under joint label-keeping renaming.

* **The key at a fixed record** (`renaming_key_iff`): two configurations with one record have equal
  canonical keys exactly when a label-keeping automorphism of the record carries one to the other up to
  the solutions of its knowledge. The relation keeps every label, every aliasing of occurrences, every
  overlap of sighted sets, the order inside recorded tuples, and the knowledge.
* **Folding is sound for supported probes** (`renaming_fold_observes`): configurations with equal keys
  at one record observe the same under every probe modulo the knowledge that the record supports.

## Controls (`FoldControls`)

Every occurrence is labelled `0`.

* **A sighted-set swap folds** (`sighting_swap_folds`): after sighting `{5, 6}`, holding `5` and
  holding `6` have one key.
* **A held reference blocks it** (`reference_blocks_fold`): after also holding a reference to `5`, they
  do not. A fold licensed before that disclosure is withdrawn after it.
* **Buckets are not canonical** (`overlap_blocks_fold`): the exchange of `5` and `6` fixes the bucket
  `{5, 6}` taken alone, yet after sighting the overlapping sets `{5, 6}` and `{6, 7}`, holding `5` and
  holding `6` do not have one key. Canonicalizing each recorded set separately would identify them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Transport Escaped Canonicalizer)
open Observation (Record ModuloProbe)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO

section Keys

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- **The key at a fixed record**: equal canonical keys are exactly a label-keeping automorphism of
the record carrying one configuration to the other up to the solutions of its knowledge. -/
theorem renaming_key_iff (c : Canonicalizer (renamingEscaping A label).classSetoid)
    (C D : Configuration T O) (r : Record O) :
    c.canon ⟨C, [], r⟩ = c.canon ⟨D, [], r⟩ ↔
      ∃ π : O ≃ O, (∀ o, label (π o) = label o) ∧ π ∈ Record.automorphisms r ∧
        SameUpTo A (renameConfiguration π C) D :=
  c.canon_eq_iff.trans (renaming_iso_iff_relative A label C D r)

variable {A label}

/-- **Folding is sound for every probe the record supports.** -/
theorem renaming_fold_observes (c : Canonicalizer (renamingEscaping A label).classSetoid)
    {C D : Configuration T O} {r : Record O} (keys : c.canon ⟨C, [], r⟩ = c.canon ⟨D, [], r⟩)
    {p : ModuloProbe A O} (supported : p.Supported r) : p.Observes label C ↔ p.Observes label D := by
  obtain ⟨π, keeps, aut, same⟩ := (renaming_key_iff A label c C D r).mp keys
  have modulo : Observation.RecordModuloEquivalent A label r C D := by
    refine ⟨π, aut, ⟨fun o σ _ => ?_, fun _ absent => absurd absent (Finset.notMem_empty _)⟩, same⟩
    show A.E (A.apply σ (label (π o))) (A.apply σ (label o))
    rw [keeps]
    exact A.equivalence.refl _
  exact modulo.recordEquivalent.observes supported

end Keys

/-! ## Controls -/

namespace FoldControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open EscapeControls (blank)
open Observation.Record (sighting reference)

/-- Holding occurrence `5`. -/
def holdsFive : Configuration (Term signature) ℕ := ⟨[], {5}⟩

/-- Holding occurrence `6`. -/
def holdsSix : Configuration (Term signature) ℕ := ⟨[], {6}⟩

theorem five_six_renamed : SameUpTo A (renameConfiguration (Equiv.swap 5 6) holdsFive) holdsSix :=
  ⟨fun _ => Iff.rfl, by decide⟩

theorem image_five {π : ℕ ≃ ℕ} (same : SameUpTo A (renameConfiguration π holdsFive) holdsSix) :
    π 5 = 6 := by
  have inside : π 5 ∈ holdsSix.present := by
    rw [← same.2]
    exact Finset.mem_map_of_mem _ (Finset.mem_singleton_self 5)
  simpa [holdsSix] using inside

/-- **A sighted-set swap folds.** -/
theorem sighting_swap_folds (c : Canonicalizer (renamingEscaping A blank).classSetoid) :
    c.canon ⟨holdsFive, [], [sighting {5, 6}]⟩ = c.canon ⟨holdsSix, [], [sighting {5, 6}]⟩ :=
  (renaming_key_iff A blank c _ _ _).mpr
    ⟨Equiv.swap 5 6, fun _ => rfl, Observation.RecordControls.sighting_swap.1, five_six_renamed⟩

/-- **A held reference blocks it**: after the later disclosure of a reference to `5`, the two states
no longer have one key. -/
theorem reference_blocks_fold (c : Canonicalizer (renamingEscaping A blank).classSetoid) :
    c.canon ⟨holdsFive, [], [sighting {5, 6}] ++ [reference 5]⟩ ≠
      c.canon ⟨holdsSix, [], [sighting {5, 6}] ++ [reference 5]⟩ := by
  intro keys
  obtain ⟨π, -, aut, same⟩ := (renaming_key_iff A blank c _ _ _).mp keys
  have held : Record.rename π (Record.references [5]) = Record.references [5] :=
    (Record.rename_append_eq_iff.mp aut).2
  have fixed : π 5 = 5 := Record.references_rename_eq_iff.mp held 5 (List.mem_singleton_self 5)
  rw [image_five same] at fixed
  exact absurd fixed (by decide)

/-- **Buckets are not canonical**: the exchange of `5` and `6` fixes the bucket `{5, 6}` alone, yet
after sighting the overlapping sets `{5, 6}` and `{6, 7}` the two states do not have one key. -/
theorem overlap_blocks_fold (c : Canonicalizer (renamingEscaping A blank).classSetoid) :
    Equiv.swap 5 6 ∈ Record.automorphisms [sighting ({5, 6} : Finset ℕ)] ∧
      c.canon ⟨holdsFive, [], [sighting {5, 6}, sighting {6, 7}]⟩ ≠
        c.canon ⟨holdsSix, [], [sighting {5, 6}, sighting {6, 7}]⟩ := by
  refine ⟨Observation.RecordControls.sighting_swap.1, fun keys => ?_⟩
  obtain ⟨π, -, aut, same⟩ := (renaming_key_iff A blank c _ _ _).mp keys
  have carried : Record.rename π [sighting {5, 6}, sighting {6, 7}] = [sighting {5, 6}, sighting {6, 7}] :=
    aut
  simp only [Record.rename, List.map_cons, List.map_nil, List.cons.injEq, and_true,
    Record.renameEntry_sighting] at carried
  have second : ({6, 7} : Finset ℕ).map π.toEmbedding = {6, 7} :=
    Finset.map_injective Record.single carried.2
  have moved := image_five same
  have six : (6 : ℕ) ∈ ({6, 7} : Finset ℕ).map π.toEmbedding := by
    rw [second]
    decide
  obtain ⟨a, member, image⟩ := Finset.mem_map.mp six
  have five : a = 5 := π.injective (image.trans moved.symm)
  subst five
  exact absurd member (by decide)

end FoldControls

#print axioms renaming_key_iff
#print axioms renaming_fold_observes
#print axioms FoldControls.five_six_renamed
#print axioms FoldControls.sighting_swap_folds
#print axioms FoldControls.reference_blocks_fold
#print axioms FoldControls.overlap_blocks_fold

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
