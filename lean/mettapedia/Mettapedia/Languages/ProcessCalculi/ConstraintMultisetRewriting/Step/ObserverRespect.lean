import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Observer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModuloFrames

/-!
# Respect: what an observer observes is invariant under the automorphisms of its record

An observer names identities only through what it recorded. A probe it can make is therefore one
that every automorphism of its record carries to itself: the probe is **supported** by the record.

* **Probes are equivariant** (`FrameProbe.rename`, `RowIsoModulo.observes_rename_iff`): along a row
  isomorphism modulo the knowledge, a probe observes at the first state what its renaming observes at
  the second. No identity needs to be fixed for this.
* **Respect** (`FrameProbe.observes_iff_of_aut`): along a row isomorphism whose renaming is an
  automorphism of a record, every probe the record supports observes the same at both states. The
  existing clause, that the renaming fixes every identity the probe names
  (`FrameProbe.observes_iff_modulo`), is the case of a record of references
  (`FrameProbe.supported_of_names`).
* **Which probe class matches the automorphisms of the record** (`FrameProbe.supported_references_iff`,
  `ModuloProbe.supported_references_iff`): for a record of references, over infinitely many
  identities, the probes it supports are exactly the probes that name only its references. So the
  full abstraction of pointwise equivalence (`pointwiseEquivalent_iff_observes`) is full abstraction
  for the probes such a record supports (`pointwiseEquivalent_iff_supported`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Observation (Record)

universe uO uT uH uOcc

section Frames

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
variable {X : Frames Tm Hom} {P : Obj} {O : Type uOcc}

namespace FrameProbe

/-- **Rename the identities a frame probe names.** -/
def rename (π : O ≃ O) : FrameProbe X P O → FrameProbe X P O
  | present reference => present (π reference)
  | test reference reader => test (π reference) reader
  | count reader number => count reader number
  | query reader seen => query reader (seen.map π.toEmbedding)
  | equal reference term => equal (π reference) term

theorem rename_symm_rename (π : O ≃ O) (p : FrameProbe X P O) : (p.rename π).rename π.symm = p := by
  cases p with
  | present reference => simp [rename]
  | test reference reader => simp [rename]
  | count reader number => rfl
  | query reader seen =>
      simp only [rename, Finset.map_map, ← Equiv.trans_toEmbedding, Equiv.self_trans_symm,
        Equiv.refl_toEmbedding, Finset.map_refl]
  | equal reference term => simp [rename]

/-- A probe whose named identities are fixed is its own renaming. -/
theorem rename_eq_self (p : FrameProbe X P O) {π : O ≃ O} (fixes : ∀ o ∈ p.names, π o = o) :
    p.rename π = p := by
  cases p with
  | present reference => simp only [rename, fixes reference (Finset.mem_singleton_self reference)]
  | test reference reader => simp only [rename, fixes reference (Finset.mem_singleton_self reference)]
  | count reader number => rfl
  | query reader seen =>
      show query reader (seen.map π.toEmbedding) = query reader seen
      rw [Observation.finset_map_eq_self (s := seen) π fixes]
  | equal reference term => simp only [rename, fixes reference (Finset.mem_singleton_self reference)]

/-- **A probe supported by a record**: every automorphism of the record carries it to itself. -/
def Supported (r : Record O) (p : FrameProbe X P O) : Prop :=
  ∀ π ∈ Record.automorphisms r, p.rename π = p

end FrameProbe

namespace RowIsoModulo

variable {E : Finset O}

/-- **Probes are equivariant**, in one direction: a probe observed at the first state, renamed, is
observed at the second. -/
theorem observes_rename {s t : RowState X P O} (i : RowIsoModulo E s t) {p : FrameProbe X P O}
    (observed : p.Observes s) : (p.rename i.rename).Observes t := by
  cases p with
  | present reference =>
      show i.rename reference ∈ t.present
      rw [← i.present]
      exact Finset.mem_map_of_mem _ observed
  | test reference reader =>
      intro b g solved
      have read := observed b (X.comp g i.frame.hom) (i.solution solved)
      have same := (reader b).respects (i.row_at solved reference)
      exact same.symm.trans read
  | count reader number =>
      intro b g solved
      rw [i.accepted_at (reader b) solved, Finset.card_map]
      exact observed b (X.comp g i.frame.hom) (i.solution solved)
  | query reader seen =>
      intro b g solved
      rw [i.accepted_at (reader b) solved, observed b (X.comp g i.frame.hom) (i.solution solved)]
  | equal reference term =>
      intro b g solved
      have held := observed b (X.comp g i.frame.hom) (i.solution solved)
      have rows := i.row_at solved reference
      exact (X.equivalence b).trans ((X.equivalence b).symm rows)
        ((X.equivalence b).trans held (i.names_at solved term))

/-- **Probes are equivariant**: a probe observes at the first state what its renaming observes at
the second. -/
theorem observes_rename_iff {s t : RowState X P O} (i : RowIsoModulo E s t) (p : FrameProbe X P O) :
    p.Observes s ↔ (p.rename i.rename).Observes t := by
  refine ⟨i.observes_rename, fun observed => ?_⟩
  have back := i.symm.observes_rename observed
  rwa [show i.symm.rename = i.rename.symm from rfl, FrameProbe.rename_symm_rename] at back

end RowIsoModulo

namespace FrameProbe

variable {E : Finset O}

/-- **Respect**: along a row isomorphism modulo the knowledge whose renaming is an automorphism of a
record, every probe the record supports observes the same at both states. -/
theorem observes_iff_of_aut {s t : RowState X P O} (i : RowIsoModulo E s t) {r : Record O}
    (aut : i.rename ∈ Record.automorphisms r) {p : FrameProbe X P O} (supported : p.Supported r) :
    p.Observes s ↔ p.Observes t := by
  rw [i.observes_rename_iff p, supported _ aut]

/-- **A record of references supports every probe that names only its references.** -/
theorem supported_of_names {l : List O} {p : FrameProbe X P O} (named : ∀ o ∈ p.names, o ∈ l) :
    p.Supported (Record.references l) := fun _ aut =>
  p.rename_eq_self fun o member => Record.references_rename_eq_iff.mp aut o (named o member)

/-- The exchange of an identity outside a list with a fresh one is an automorphism of the record of
its references. -/
theorem swap_mem_automorphisms {l : List O} [DecidableEq O] {a b : O} (outside : a ∉ l) (fresh : b ∉ l) :
    Equiv.swap a b ∈ Record.automorphisms (Record.references l) :=
  Record.references_rename_eq_iff.mpr fun _ member =>
    Equiv.swap_apply_of_ne_of_ne (fun same => outside (same ▸ member)) fun same => fresh (same ▸ member)

/-- **Over infinitely many identities, a record of references supports only the probes that name its
references.** -/
theorem names_of_supported [DecidableEq O] [Infinite O] {l : List O} {p : FrameProbe X P O}
    (supported : p.Supported (Record.references l)) : ∀ o ∈ p.names, o ∈ l := by
  have moved : ∀ a : O, a ∉ l → ∃ b : O, b ∉ l ∧ b ≠ a ∧ Equiv.swap a b ∈
      Record.automorphisms (Record.references l) := by
    intro a outside
    obtain ⟨b, fresh⟩ := Infinite.exists_notMem_finset (insert a l.toFinset)
    simp only [Finset.mem_insert, List.mem_toFinset, not_or] at fresh
    exact ⟨b, fresh.2, fresh.1, swap_mem_automorphisms outside fresh.2⟩
  have single : ∀ reference : O, (∀ π ∈ Record.automorphisms (Record.references l), π reference = reference) →
      reference ∈ l := by
    intro reference fixed
    by_contra outside
    obtain ⟨b, -, other, aut⟩ := moved reference outside
    have := fixed _ aut
    rw [Equiv.swap_apply_left] at this
    exact other this
  intro o member
  cases p with
  | present reference =>
      obtain rfl := Finset.mem_singleton.mp member
      exact single o fun π aut => present.inj (supported π aut)
  | test reference reader =>
      obtain rfl := Finset.mem_singleton.mp member
      exact single o fun π aut => (test.inj (supported π aut)).1
  | count reader number => simp [names] at member
  | query reader seen =>
      by_contra outside
      obtain ⟨b, fresh⟩ := Infinite.exists_notMem_finset (insert o (l.toFinset ∪ seen))
      simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, not_or] at fresh
      have kept : seen.map (Equiv.swap o b).toEmbedding = seen :=
        (query.inj (supported _ (swap_mem_automorphisms outside fresh.2.1))).2
      have there : Equiv.swap o b o ∈ seen.map (Equiv.swap o b).toEmbedding := Finset.mem_map_of_mem _ member
      rw [kept, Equiv.swap_apply_left] at there
      exact fresh.2.2 there
  | equal reference term =>
      obtain rfl := Finset.mem_singleton.mp member
      exact single o fun π aut => (equal.inj (supported π aut)).1

/-- **Which probes match the automorphisms of a record of references**: over infinitely many
identities, exactly the probes that name only its references. -/
theorem supported_references_iff [DecidableEq O] [Infinite O] {l : List O} {p : FrameProbe X P O} :
    p.Supported (Record.references l) ↔ ∀ o ∈ p.names, o ∈ l :=
  ⟨names_of_supported, supported_of_names⟩

/-- **The pointwise respect is the case of references.** -/
theorem observes_iff_of_references {s t : RowState X P O} (i : RowIsoModulo E s t) {l : List O}
    (fixes : ∀ o ∈ l, i.rename o = o) {p : FrameProbe X P O} (named : ∀ o ∈ p.names, o ∈ l) :
    p.Observes s ↔ p.Observes t :=
  observes_iff_of_aut i (Record.references_rename_eq_iff.mpr fixes) (supported_of_names named)

end FrameProbe

end Frames

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO}

namespace ModuloProbe

variable {A : SubstitutionAction T S}

/-- **Rename the identities a probe modulo the knowledge names.** -/
def rename (π : O ≃ O) : ModuloProbe A O → ModuloProbe A O
  | present reference => present (π reference)
  | check guard => check guard
  | ask region seen => ask region (seen.map π.toEmbedding)
  | tally region number => tally region number

/-- **A probe supported by a record**: every automorphism of the record carries it to itself. -/
def Supported (r : Record O) (p : ModuloProbe A O) : Prop :=
  ∀ π ∈ Record.automorphisms r, p.rename π = p

theorem rename_eq_self (p : ModuloProbe A O) {π : O ≃ O} (fixes : ∀ o ∈ p.names, π o = o) :
    p.rename π = p := by
  cases p with
  | present reference => simp only [rename, fixes reference (Finset.mem_singleton_self reference)]
  | check guard => rfl
  | ask region seen =>
      show ask region (seen.map π.toEmbedding) = ask region seen
      rw [finset_map_eq_self (s := seen) π fixes]
  | tally region number => rfl

theorem supported_of_names {l : List O} {p : ModuloProbe A O} (named : ∀ o ∈ p.names, o ∈ l) :
    p.Supported (Record.references l) := fun _ aut =>
  p.rename_eq_self fun o member => Record.references_rename_eq_iff.mp aut o (named o member)

/-- **Which probes modulo the knowledge match the automorphisms of a record of references**: over
infinitely many identities, exactly the probes that name only its references. -/
theorem supported_references_iff [DecidableEq O] [Infinite O] {l : List O} {p : ModuloProbe A O} :
    p.Supported (Record.references l) ↔ ∀ o ∈ p.names, o ∈ l := by
  refine ⟨fun supported o member => ?_, supported_of_names⟩
  by_contra outside
  cases p with
  | present reference =>
      obtain rfl := Finset.mem_singleton.mp member
      obtain ⟨b, fresh⟩ := Infinite.exists_notMem_finset (insert o l.toFinset)
      simp only [Finset.mem_insert, List.mem_toFinset, not_or] at fresh
      have moved : Equiv.swap o b o = o :=
        present.inj (supported _ (Interface.FrameProbe.swap_mem_automorphisms outside fresh.2))
      rw [Equiv.swap_apply_left] at moved
      exact fresh.1 moved
  | check guard => simp [names] at member
  | ask region seen =>
      obtain ⟨b, fresh⟩ := Infinite.exists_notMem_finset (insert o (l.toFinset ∪ seen))
      simp only [Finset.mem_insert, Finset.mem_union, List.mem_toFinset, not_or] at fresh
      have kept : seen.map (Equiv.swap o b).toEmbedding = seen :=
        (ask.inj (supported _ (Interface.FrameProbe.swap_mem_automorphisms outside fresh.2.1))).2
      have there : Equiv.swap o b o ∈ seen.map (Equiv.swap o b).toEmbedding := Finset.mem_map_of_mem _ member
      rw [kept, Equiv.swap_apply_left] at there
      exact fresh.2.2 there
  | tally region number => simp [names] at member

end ModuloProbe

/-- **Full abstraction for the probes a record of references supports**: over infinitely many
identities, two configurations are pointwise equivalent relative to the references exactly when
every probe the record supports observes the same at both. -/
theorem pointwiseEquivalent_iff_supported [DecidableEq O] [Infinite O] {A : SubstitutionAction T S}
    (label : O → T) (l : List O) (C D : Configuration T O) :
    PointwiseEquivalent A label l.toFinset C D ↔
      ∀ p : ModuloProbe A O, p.Supported (Record.references l) → (p.Observes label C ↔ p.Observes label D) := by
  rw [pointwiseEquivalent_iff_observes]
  refine forall_congr' fun p => imp_congr_left ?_
  rw [ModuloProbe.supported_references_iff]
  exact ⟨fun named o member => List.mem_toFinset.mp (named member),
    fun named o member => List.mem_toFinset.mpr (named o member)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

#print axioms FrameProbe.rename_symm_rename
#print axioms RowIsoModulo.observes_rename
#print axioms RowIsoModulo.observes_rename_iff
#print axioms FrameProbe.observes_iff_of_aut
#print axioms FrameProbe.supported_of_names
#print axioms FrameProbe.names_of_supported
#print axioms FrameProbe.supported_references_iff
#print axioms FrameProbe.observes_iff_of_references
#print axioms Observation.ModuloProbe.supported_references_iff
#print axioms Observation.pointwiseEquivalent_iff_supported

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
