import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverFirstOrder

/-!
# Orbit and stabilizer: joint renaming and automorphisms of a record are one action

Renamings act on states (`IsAction`) and on records (`Observation.Record.rename`), hence diagonally
on a state paired with a record (`pairAct`). Two views of observers meet here:

* **Perspective-neutral**: observers' records are part of the state, and a renaming acts on both
  jointly (`Renamed (pairAct act) G`).
* **Perspective-relative**: one record is held fixed, and states are compared by the renamings that
  are automorphisms of it (`Renamed act (G ⊓ automorphisms r)`).

At a fixed record the joint relation is the relative one (`renamed_pair_iff`). Every pair whose record
lies in the orbit of `r` is jointly renamed to one with record exactly `r` (`renamed_slice`). So the
pairs over the orbit of `r`, up to joint renaming, are the states up to the stabilizer of `r`
(`orbitQuotientEquiv`): the two views are two faces of one action. For configurations and the
label-keeping renamings this is `AnnotatedRuns.configurationOrbitEquiv`.

For the escape-relative transport that renames occurrences (`AnnotatedRuns.renamingEscaping`), the
isomorphisms between escaped states with one record are the label-keeping automorphisms of the record
(`AnnotatedRuns.renaming_iso_iff_relative`), and an escaped state whose record is renamed is
isomorphic to its renamed-back state with the original record (`AnnotatedRuns.renaming_slice`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

universe uO uA

section Orbits

variable {O : Type uO} {α : Type uA} (act : (O ≃ O) → α → α)

/-- **An action of renamings.** -/
structure IsAction : Prop where
  refl : ∀ a, act (Equiv.refl O) a = a
  trans : ∀ (π ρ : O ≃ O) a, act (π.trans ρ) a = act ρ (act π a)

/-- **Renamed by a subgroup**: some renaming of `H` carries the first to the second. -/
def Renamed (H : Subgroup (Equiv.Perm O)) (a b : α) : Prop := ∃ π ∈ H, act π a = b

/-- **The diagonal action** on a state paired with a record. -/
def pairAct (π : O ≃ O) (p : α × Record O) : α × Record O := (act π p.1, Record.rename π p.2)

variable {act}

theorem IsAction.symm_act (h : IsAction act) (π : O ≃ O) (a : α) : act π.symm (act π a) = a := by
  rw [← h.trans, Equiv.self_trans_symm, h.refl]

theorem IsAction.act_symm (h : IsAction act) (π : O ≃ O) (a : α) : act π (act π.symm a) = a := by
  rw [← h.trans, Equiv.symm_trans_self, h.refl]

theorem IsAction.pair (h : IsAction act) : IsAction (pairAct act) :=
  ⟨fun p => by simp [pairAct, h.refl, Record.rename_refl],
    fun π ρ p => by simp [pairAct, h.trans, Record.rename_trans]⟩

/-- **Renaming by a subgroup is an equivalence.** -/
def renamedSetoid (h : IsAction act) (H : Subgroup (Equiv.Perm O)) : Setoid α where
  r := Renamed act H
  iseqv := ⟨fun a => ⟨1, H.one_mem, h.refl a⟩,
    fun ⟨π, mem, moved⟩ => ⟨π⁻¹, H.inv_mem mem, by rw [← moved]; exact h.symm_act π _⟩,
    fun ⟨π, mem, moved⟩ ⟨ρ, mem', moved'⟩ => ⟨ρ * π, H.mul_mem mem' mem, by
      show act (π.trans ρ) _ = _
      rw [h.trans, moved, moved']⟩⟩

variable (G : Subgroup (Equiv.Perm O))

/-- **At a fixed record, joint renaming is renaming by the record's automorphisms.** -/
theorem renamed_pair_iff {r : Record O} {a b : α} :
    Renamed (pairAct act) G (a, r) (b, r) ↔ Renamed act (G ⊓ Record.automorphisms r) a b := by
  constructor
  · rintro ⟨π, mem, moved⟩
    exact ⟨π, Subgroup.mem_inf.mpr ⟨mem, congrArg Prod.snd moved⟩, congrArg Prod.fst moved⟩
  · rintro ⟨π, mem, moved⟩
    obtain ⟨inG, aut⟩ := Subgroup.mem_inf.mp mem
    exact ⟨π, inG, Prod.ext moved aut⟩

/-- **Every pair over the orbit of a record meets the slice of that record.** -/
theorem renamed_slice (h : IsAction act) {ρ : O ≃ O} (mem : ρ ∈ G) (b : α) (r : Record O) :
    Renamed (pairAct act) G (act ρ.symm b, r) (b, Record.rename ρ r) :=
  ⟨ρ, mem, Prod.ext (h.act_symm ρ b) rfl⟩

/-- The pairs whose record lies in the orbit of `r`. -/
abbrev OrbitPairs (r : Record O) : Type _ := {p : α × Record O // ∃ ρ ∈ G, Record.rename ρ r = p.2}

variable {G}

/-- The pairs over the orbit of `r`, up to joint renaming. -/
def orbitSetoid (G : Subgroup (Equiv.Perm O)) (h : IsAction act) (r : Record O) :
    Setoid (OrbitPairs (α := α) G r) :=
  (renamedSetoid h.pair G).comap Subtype.val

/-- A renaming of `G` that carries `r` to a given record of its orbit. -/
noncomputable def OrbitPairs.witness {r : Record O} (p : OrbitPairs (α := α) G r) : O ≃ O :=
  Classical.choose p.2

theorem OrbitPairs.witness_mem {r : Record O} (p : OrbitPairs (α := α) G r) : p.witness ∈ G :=
  (Classical.choose_spec p.2).1

theorem OrbitPairs.witness_rename {r : Record O} (p : OrbitPairs (α := α) G r) :
    Record.rename p.witness r = p.1.2 :=
  (Classical.choose_spec p.2).2

/-- **Orbit and stabilizer**: the pairs over the orbit of `r`, up to joint renaming, are the states up
to the renamings of `G` that are automorphisms of `r`. -/
noncomputable def orbitQuotientEquiv (G : Subgroup (Equiv.Perm O)) (h : IsAction act) (r : Record O) :
    Quotient (orbitSetoid G h r) ≃ Quotient (renamedSetoid h (G ⊓ Record.automorphisms r)) where
  toFun := Quotient.lift (fun p => Quotient.mk _ (act p.witness.symm p.1.1)) fun p q related => by
    obtain ⟨π, mem, moved⟩ : Renamed (pairAct act) G p.1 q.1 := related
    have movedState : act π p.1.1 = q.1.1 := congrArg Prod.fst moved
    have movedRecord : Record.rename π p.1.2 = q.1.2 := congrArg Prod.snd moved
    apply Quotient.sound
    refine ⟨q.witness⁻¹ * π * p.witness, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact G.mul_mem (G.mul_mem (G.inv_mem q.witness_mem) mem) p.witness_mem
    · show Record.rename (p.witness.trans (π.trans q.witness.symm)) r = r
      rw [Record.rename_trans, Record.rename_trans, p.witness_rename, movedRecord,
        ← q.witness_rename, Record.rename_symm_rename]
    · show act (p.witness.trans (π.trans q.witness.symm)) (act p.witness.symm p.1.1) = act q.witness.symm q.1.1
      rw [h.trans, h.trans, h.act_symm, movedState]
  invFun := Quotient.lift (fun a => Quotient.mk _ ⟨(a, r), 1, G.one_mem, Record.rename_refl r⟩)
    fun a b related => Quotient.sound ((renamed_pair_iff G).mpr related)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      show Renamed (pairAct act) G (act p.witness.symm p.1.1, r) p.1
      have slice := renamed_slice G h p.witness_mem p.1.1 r
      rwa [p.witness_rename] at slice
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h a =>
      apply Quotient.sound
      let p : OrbitPairs (α := α) G r := ⟨(a, r), 1, G.one_mem, Record.rename_refl r⟩
      refine ⟨p.witness, Subgroup.mem_inf.mpr ⟨p.witness_mem, p.witness_rename⟩, ?_⟩
      exact h.act_symm p.witness a

end Orbits

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Transport Escaped)
open Observation (Record)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

omit [DecidableEq O] in
/-- **Renaming acts on configurations.** -/
theorem renameConfiguration_isAction : Observation.IsAction (renameConfiguration (T := T) (O := O)) :=
  ⟨Observation.renameConfiguration_refl, fun π ρ C => Observation.renameConfiguration_trans π ρ C⟩

/-- **The renamings that keep every label.** -/
def labelKeeping : Subgroup (Equiv.Perm O) where
  carrier := {π | ∀ o, label (π o) = label o}
  one_mem' _ := rfl
  mul_mem' {π ρ} kept kept' o := by
    show label (π (ρ o)) = label o
    rw [kept, kept']
  inv_mem' {π} kept o := by
    show label (π.symm o) = label o
    have back := kept (π.symm o)
    rw [Equiv.apply_symm_apply] at back
    exact back.symm

/-- **Orbit and stabilizer for configurations**: configurations paired with records over the orbit
of `r`, up to joint label-keeping renaming, are the configurations up to the label-keeping
automorphisms of `r`. -/
noncomputable def configurationOrbitEquiv (r : Record O) :
    Quotient (Observation.orbitSetoid (labelKeeping label) (renameConfiguration_isAction (T := T) (O := O)) r) ≃
      Quotient (Observation.renamedSetoid (renameConfiguration_isAction (T := T) (O := O))
        (labelKeeping label ⊓ Record.automorphisms r)) :=
  Observation.orbitQuotientEquiv (labelKeeping label) renameConfiguration_isAction r

/-- **The isomorphisms between escaped states with one record are its label-keeping automorphisms**
relating the configurations. -/
theorem renaming_iso_iff_relative (C D : Configuration T O) (r : Record O) :
    Nonempty ((renamingEscaping A label).Iso ⟨C, [], r⟩ ⟨D, [], r⟩) ↔
      ∃ π : O ≃ O, (∀ o, label (π o) = label o) ∧ π ∈ Record.automorphisms r ∧
        SameUpTo A (renameConfiguration π C) D := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i.base.rename, i.base.keeps, i.record, i.base.same⟩
  · rintro ⟨π, keeps, aut, same⟩
    exact ⟨⟨⟨π, keeps, same⟩, .nil, aut⟩⟩

/-- **An escaped state whose record is renamed is isomorphic to its renamed-back state with the
original record.** -/
def renaming_slice (C : Configuration T O) (r : Record O) {ρ : O ≃ O} (keeps : ∀ o, label (ρ o) = label o) :
    (renamingEscaping A label).Iso ⟨renameConfiguration ρ.symm C, [], r⟩ ⟨C, [], Record.rename ρ r⟩ :=
  ⟨⟨ρ, keeps, by
      rw [← Observation.renameConfiguration_trans, Equiv.symm_trans_self, Observation.renameConfiguration_refl]
      exact SameUpTo.refl A C⟩, .nil, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

#print axioms IsAction.pair
#print axioms renamedSetoid
#print axioms renamed_pair_iff
#print axioms renamed_slice
#print axioms orbitQuotientEquiv
#print axioms AnnotatedRuns.renameConfiguration_isAction
#print axioms AnnotatedRuns.configurationOrbitEquiv
#print axioms AnnotatedRuns.renaming_iso_iff_relative
#print axioms AnnotatedRuns.renaming_slice

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
