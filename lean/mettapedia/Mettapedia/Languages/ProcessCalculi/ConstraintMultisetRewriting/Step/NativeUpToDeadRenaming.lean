import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeUpToDeadInterface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeIdentity

/-!
# The renaming transport is a transport up to dead names

R81 renames the occurrences of native states and firings (`NativeState.rename`, `NativeFiring.rename`),
and proves admission and results are carried (`NativeFiring.realized_rename_iff`,
`native_result_rename`). The renamings are not the step's `Transport`, which also asks for residuals,
but they are a transport up to dead names over the whole native step, with no dead names at all.

* **The renaming transport** (`renamingTransport`): inclusions are renamings that carry one state to the
  other (`RenamingIncl`), seen by the interface as R81's isomorphisms of states (`renameStateIso`); a
  firing is carried to its renaming.
* **Its agreement is R81's renaming relation** (`same_iff_renamed`).
* **Equivariant programs are invariant** (`invariant_of_equivariant`), so **renamed states are
  bisimilar** (`renamed_bisimilar`): R81's `native_bisimilar_of_renamed`, as an instance of the
  interface's theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeUpToDeadRenaming

/-- **An inclusion along a renaming**: a renaming of occurrences that carries one state to the
other. -/
abbrev RenamingIncl (s u : NativeState S O Γ sort) : Type := {π : O ≃ O // s.rename π = u}

/-- The interface's view of a renaming: R81's isomorphism of states. -/
noncomputable def toIncl {s u : NativeState S O Γ sort} (e : RenamingIncl s u) :
    (native (S := S) (O := O) (Γ := Γ) (sort := sort)).StateIncl s u :=
  e.2 ▸ (renameStateIso e.1 s).toIncl

/-- **The renaming transport.** -/
noncomputable def renamingTransport :
    DeadTransport (native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep where
  Incl := RenamingIncl
  toStateIncl := toIncl
  refl s := ⟨Equiv.refl O, NativeState.rename_refl s⟩
  comp e e' := ⟨e.1.trans e'.1, by rw [← NativeState.rename_trans, e.2, e'.2]⟩
  amalgamate {t u v} e e' := by
    obtain ⟨π, rfl⟩ := e
    obtain ⟨ρ, rfl⟩ := e'
    refine ⟨t.rename ρ, ⟨⟨π.symm.trans ρ, ?_⟩⟩, ⟨⟨Equiv.refl O, NativeState.rename_refl _⟩⟩⟩
    rw [NativeState.rename_trans, ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]
  Carries e f g := HEq (f.rename e.1) g
  carries_comp {s u w e e' f g h} first second := by
    obtain ⟨π, rfl⟩ := e
    obtain ⟨ρ, rfl⟩ := e'
    have sameG := eq_of_heq first
    subst sameG
    have sameH := eq_of_heq second
    subst sameH
    exact (Sigma.mk.inj (NativeFiring.sigma_rename_trans π ρ s f)).2.symm
  selection_carries {s u e f g} carried := by
    obtain ⟨π, rfl⟩ := e
    have same := eq_of_heq carried
    subst same
    rfl
  admits_carries {s u e f g} carried := by
    obtain ⟨π, rfl⟩ := e
    have same := eq_of_heq carried
    subst same
    exact (NativeFiring.realized_rename_iff π f).symm
  result_carries {s u e f g} carried admitted admitted' := by
    obtain ⟨π, rfl⟩ := e
    have same := eq_of_heq carried
    subst same
    exact ⟨_, ⟨⟨π, (native_result_rename π f admitted admitted').symm⟩⟩,
      ⟨⟨Equiv.refl O, NativeState.rename_refl _⟩⟩⟩

/-- **The renaming transport's agreement is R81's renaming relation.** -/
theorem same_iff_renamed {s t : NativeState S O Γ sort} :
    (renamingTransport (S := S)).Same s t ↔ NativeRenamed s t := by
  constructor
  · rintro ⟨u, ⟨⟨π, first⟩⟩, ⟨⟨ρ, second⟩⟩⟩
    exact NativeRenamed.trans ⟨π, first⟩ (NativeRenamed.symm ⟨ρ, second⟩)
  · rintro ⟨π, renamed⟩
    exact ⟨t, ⟨⟨π, renamed⟩⟩, ⟨⟨Equiv.refl O, NativeState.rename_refl t⟩⟩⟩

variable {L : Type*}

/-- **Equivariant programs are invariant** for the renaming transport. -/
theorem invariant_of_equivariant {offers : L → (s : NativeState S O Γ sort) → NativeFiring s → Prop}
    (equivariant : NativeEquivariant offers) : (renamingTransport (S := S)).Invariant offers := by
  intro s u e ℓ
  obtain ⟨π, rfl⟩ := e
  refine ⟨fun f offered => ⟨f.rename π, HEq.rfl, (equivariant π ℓ s f).mpr offered⟩, fun g offered => ?_⟩
  refine ⟨NativeFiring.unrename π g, (equivariant π ℓ s _).mp ?_, heq_of_eq (NativeFiring.rename_unrename π g)⟩
  rw [NativeFiring.rename_unrename]
  exact offered

/-- **Renamed states are bisimilar**, for every equivariant program: R81's theorem as an instance of
the interface's theorem up to dead names. -/
theorem renamed_bisimilar {offers : L → (s : NativeState S O Γ sort) → NativeFiring s → Prop}
    (equivariant : NativeEquivariant offers) {s t : NativeState S O Γ sort} (renamed : NativeRenamed s t) :
    Race.Generic.Bisimilar native.toStep offers s t :=
  DeadTransport.bisimilar_of_same (invariant_of_equivariant equivariant) (same_iff_renamed.mpr renamed)

end NativeUpToDeadRenaming

#print axioms NativeUpToDeadRenaming.renamingTransport
#print axioms NativeUpToDeadRenaming.same_iff_renamed
#print axioms NativeUpToDeadRenaming.invariant_of_equivariant
#print axioms NativeUpToDeadRenaming.renamed_bisimilar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
