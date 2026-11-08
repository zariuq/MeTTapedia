import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CongruenceClients
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverSightings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverChoices

/-!
# Equivalence relative to an observer's record: firings and composition

Relative to a record (`Observation.Record`), configurations are compared by the automorphisms of the
record that keep labels up to the knowledge (`RecordModuloEquivalent`). An automorphism need not fix
the identities the record mentions, only carry the record to itself. Two consequences, each with a
counterexample, separate the record level from the level of held references.

## Supported automorphisms

* **The witness can be chosen to move only what it must** (`RecordModuloEquivalent.supported`): an
  automorphism that relates two configurations can be replaced by one that agrees with it on the
  identities the record mentions and fixes every identity outside the two configurations and the
  record. It is glued (`piecewiseRenaming`) from the old automorphism on the record's identities
  (`Record.support_rename`, `Record.rename_congr`) and a renaming supported on the rest.

## Disjoint parallel composition

* **True** (`RecordModuloEquivalent.tensor_disjoint`): for a context disjoint from both
  configurations and from the identities the record mentions, the composites are equivalent relative
  to the record together with references to the context's occurrences.
* **Counterexample** (`RecordCongruenceControls.record_overlap_control`): when the record relates a context
  occurrence to the state, composition breaks the equivalence. The record `{[5, 7], [6, 8]}` relates
  `{5}` to `{6}` by the automorphism `(5 6)(7 8)`; with `{7}` beside them, no automorphism carries
  `{5, 7}` to `{6, 7}`.

## Semantic firings

A firing extends the record by what it sighted and took (`choiceRecord`, the record of
`AnnotatedRuns.choiceEscape`), and the record moves with the firing (`choiceRecord_rename`). Joint
ends compare states with records by one renaming that carries one record to the other
(`JointRecordModuloEquivalent`, a groupoid; at one record it is `RecordModuloEquivalent`,
`jointRecordModuloEquivalent_iff`).

* **True** (`RecordModuloEquivalent.firing`, `RecordModuloEquivalent.counterpart`): an admitted
  semantic firing that does not remake an identity the record mentions has a counterpart, renamed
  along an automorphism, and the joint ends are equivalent; with a fresh supply of the made labels no
  other hypothesis is needed.
* **Counterexample** (`RecordCongruenceControls.remake_control`): a firing that remakes a remembered identity
  has no counterpart with equivalent joint ends, even with a fresh supply of its label. The
  automorphism relating the states moves the remembered identity to one of another label, so the
  counterpart cannot remake its image. This is the record-level form of the runtime's freshness
  contract (`ReuseFree`).

For records of references the automorphisms fix every mentioned identity, and both restrictions
disappear (`Observation.ModuloEquivalent.tensor_disjoint`, `Observation.ModuloEquivalent.client_counterpart`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)
open MeTTaCalculus.OccurrenceCommits (regionOf)
open Semantic

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO}

/-! ## Gluing renamings -/

section Piecewise

variable [DecidableEq O]

/-- **A renaming glued from two**: `π` on a set `s` that `π` carries to itself, and `σ`, which fixes
every identity of `s`, elsewhere. -/
def piecewiseRenaming (s : Finset O) (π σ : O ≃ O) (keeps : ∀ o, o ∈ s ↔ π o ∈ s)
    (fixes : ∀ o ∈ s, σ o = o) : O ≃ O where
  toFun o := if o ∈ s then π o else σ o
  invFun o := if o ∈ s then π.symm o else σ.symm o
  left_inv o := by
    by_cases inS : o ∈ s
    · have image : π o ∈ s := (keeps o).mp inS
      simp only [if_pos inS, if_pos image, Equiv.symm_apply_apply]
    · have image : σ o ∉ s := fun inS' => by
        have back : σ o = o := σ.injective (fixes (σ o) inS')
        rw [back] at inS'
        exact inS inS'
      simp only [if_neg inS, if_neg image, Equiv.symm_apply_apply]
  right_inv o := by
    by_cases inS : o ∈ s
    · have image : π.symm o ∈ s := (keeps (π.symm o)).mpr (by rwa [Equiv.apply_symm_apply])
      simp only [if_pos inS, if_pos image, Equiv.apply_symm_apply]
    · have image : σ.symm o ∉ s := fun inS' => by
        have fixed := fixes (σ.symm o) inS'
        rw [Equiv.apply_symm_apply] at fixed
        rw [← fixed] at inS'
        exact inS inS'
      simp only [if_neg inS, if_neg image, Equiv.apply_symm_apply]

variable {s : Finset O} {π σ : O ≃ O} {keeps : ∀ o, o ∈ s ↔ π o ∈ s} {fixes : ∀ o ∈ s, σ o = o}

theorem piecewiseRenaming_of_mem {o : O} (inS : o ∈ s) : piecewiseRenaming s π σ keeps fixes o = π o := by
  show (if o ∈ s then π o else σ o) = π o
  exact if_pos inS

theorem piecewiseRenaming_of_not_mem {o : O} (outS : o ∉ s) :
    piecewiseRenaming s π σ keeps fixes o = σ o := by
  show (if o ∈ s then π o else σ o) = σ o
  exact if_neg outS

end Piecewise

/-! ## The identities a renamed record mentions -/

section Support

variable [DecidableEq O]

/-- **Renaming a record depends only on the identities it mentions.** -/
theorem Record.rename_congr {π π' : O ≃ O} {r : Record O}
    (agree : ∀ o ∈ Record.support r, π o = π' o) : Record.rename π r = Record.rename π' r := by
  refine List.map_congr_left fun e inR => ?_
  ext l'
  simp only [Record.renameEntry, Finset.mem_map]
  constructor
  · rintro ⟨l, inE, rfl⟩
    refine ⟨l, inE, ?_⟩
    show l.map π' = l.map π
    exact List.map_congr_left fun o inL => (agree o (Record.mem_support.mpr ⟨e, inR, l, inE, inL⟩)).symm
  · rintro ⟨l, inE, rfl⟩
    refine ⟨l, inE, ?_⟩
    show l.map π = l.map π'
    exact List.map_congr_left fun o inL => agree o (Record.mem_support.mpr ⟨e, inR, l, inE, inL⟩)

end Support

/-! ## Supported automorphisms -/

section Supported

variable {A : SubstitutionAction T S} {label : O → T} {r : Record O}

/-- **A supported witness**: two configurations equivalent relative to a record are related by an
automorphism of the record that fixes every identity outside the two configurations and the
record. -/
theorem RecordModuloEquivalent.supported [DecidableEq O] {C D : Configuration T O}
    (h : RecordModuloEquivalent A label r C D) :
    ∃ π ∈ Record.automorphisms r, RenamingUpTo (entailedSetoid A C.equations) label ∅ π ∧
      SameUpTo A (renameConfiguration π C) D ∧
      ∀ o, o ∉ C.present → o ∉ D.present → o ∉ Record.support r → π o = o := by
  obtain ⟨π, aut, k, same⟩ := h
  have onto : C.present.map π.toEmbedding = D.present := same.2
  have fixedS : (Record.support r).map π.toEmbedding = Record.support r := by
    rw [← Record.support_rename, Record.mem_automorphisms.mp aut]
  have keepsS : ∀ o, o ∈ Record.support r ↔ π o ∈ Record.support r := by
    intro o
    have moved : π.toEmbedding o ∈ (Record.support r).map π.toEmbedding ↔ o ∈ Record.support r :=
      Finset.mem_map' π.toEmbedding
    rw [fixedS] at moved
    exact moved.symm
  have ontoRest : (C.present \ Record.support r).map π.toEmbedding = D.present \ Record.support r := by
    rw [Finset.map_sdiff, onto, fixedS]
  obtain ⟨σ, kσ, ontoσ, supportσ⟩ := exists_supported_renamingUpTo _ label ∅
    (fun o member => absurd member (Finset.notMem_empty o))
    ((exists_renamingUpTo_iff _ label ∅ _ _).mp ⟨π, k, ontoRest⟩).2
  have fixesS : ∀ o ∈ Record.support r, σ o = o := fun o inS =>
    supportσ o (fun member => (Finset.mem_sdiff.mp member).2 inS)
      (fun member => (Finset.mem_sdiff.mp member).2 inS)
  obtain ⟨π', onS, offS⟩ : ∃ π' : O ≃ O, (∀ o ∈ Record.support r, π' o = π o) ∧
      ∀ o, o ∉ Record.support r → π' o = σ o :=
    ⟨piecewiseRenaming (Record.support r) π σ keepsS fixesS, fun _ inS => piecewiseRenaming_of_mem inS,
      fun _ outS => piecewiseRenaming_of_not_mem outS⟩
  refine ⟨π', Record.mem_automorphisms.mpr ((Record.rename_congr onS).trans
    (Record.mem_automorphisms.mp aut)), ⟨fun o => ?_, fun o member => absurd member (Finset.notMem_empty o)⟩,
    ⟨same.1, ?_⟩, ?_⟩
  · by_cases inS : o ∈ Record.support r
    · rw [onS o inS]
      exact k.keeps o
    · rw [offS o inS]
      exact kσ.keeps o
  · show C.present.map π'.toEmbedding = D.present
    ext o
    rw [Finset.mem_map]
    constructor
    · rintro ⟨c, inC, rfl⟩
      show π' c ∈ D.present
      by_cases inS : c ∈ Record.support r
      · rw [onS c inS, ← onto]
        exact Finset.mem_map_of_mem _ inC
      · rw [offS c inS]
        have rest : σ c ∈ D.present \ Record.support r := by
          rw [← ontoσ]
          exact Finset.mem_map_of_mem _ (Finset.mem_sdiff.mpr ⟨inC, inS⟩)
        exact (Finset.mem_sdiff.mp rest).1
    · intro inD
      by_cases inS : o ∈ Record.support r
      · rw [← onto] at inD
        obtain ⟨c, inC, rfl⟩ := Finset.mem_map.mp inD
        refine ⟨c, inC, ?_⟩
        show π' c = π c
        exact onS c ((keepsS c).mpr inS)
      · have rest : o ∈ (C.present \ Record.support r).map σ.toEmbedding := by
          rw [ontoσ]
          exact Finset.mem_sdiff.mpr ⟨inD, inS⟩
        obtain ⟨c, inRest, rfl⟩ := Finset.mem_map.mp rest
        refine ⟨c, (Finset.mem_sdiff.mp inRest).1, ?_⟩
        show π' c = σ c
        exact offS c (Finset.mem_sdiff.mp inRest).2
  · intro o outC outD outS
    rw [offS o outS]
    exact supportσ o (fun member => outC (Finset.mem_sdiff.mp member).1)
      (fun member => outD (Finset.mem_sdiff.mp member).1)

/-- **Disjoint composition relative to a record**: for a context disjoint from both configurations and
from the identities the record mentions, the composites are equivalent relative to the record with
references to the context's occurrences. -/
theorem RecordModuloEquivalent.tensor_disjoint [DecidableEq O] {C D : Configuration T O}
    (h : RecordModuloEquivalent A label r C D) (F : Configuration T O)
    (apartC : Disjoint C.present F.present) (apartD : Disjoint D.present F.present)
    (apartR : Disjoint (Record.support r) F.present) :
    RecordModuloEquivalent A label (r ++ Record.references F.present.toList)
      (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) := by
  obtain ⟨π, aut, k, same, outside⟩ := h.supported
  have fixesF : ∀ o ∈ F.present, π o = o := fun o inF =>
    outside o (Finset.disjoint_right.mp apartC inF) (Finset.disjoint_right.mp apartD inF)
      (Finset.disjoint_right.mp apartR inF)
  have referencesFixed : Record.rename π (Record.references F.present.toList) =
      Record.references F.present.toList :=
    Record.rename_eq_self_of_fixes fun o member => by
      rw [Record.support_references, List.mem_toFinset] at member
      exact fixesF o (Finset.mem_toList.mp member)
  have onto : C.present.map π.toEmbedding = D.present := same.2
  refine ⟨π, ?_, k.weaken (entailedSetoid_mono (A.append_refines C.equations F.equations)), ?_, ?_⟩
  · show Record.rename π (r ++ Record.references F.present.toList) = r ++ Record.references F.present.toList
    rw [Record.rename_append, Record.mem_automorphisms.mp aut, referencesFixed]
  · intro σ
    show A.Models σ (C.equations ++ F.equations) ↔ A.Models σ (D.equations ++ F.equations)
    rw [A.models_append, A.models_append]
    exact and_congr (same.1 σ) Iff.rfl
  · show (C.present ∪ F.present).map π.toEmbedding = D.present ∪ F.present
    rw [Finset.map_union, onto, finset_map_eq_self π fixesF]

end Supported

/-! ## Firings -/

section Firings

/-- **The record a firing leaves**: the sets its queries sighted and the occurrences it took, as held
references; the record of `AnnotatedRuns.choiceEscape`. -/
def choiceRecord (f : Firing T S O) : Record O :=
  querySightings f.queries ++ Record.references f.selection.taken

theorem choiceRecord_rename (π : O ≃ O) (f : Firing T S O) :
    choiceRecord (f.rename π) = Record.rename π (choiceRecord f) := by
  show querySightings (f.queries.map (renameQuery π)) ++ Record.references (f.selection.taken.map π) =
    Record.rename π (querySightings f.queries ++ Record.references f.selection.taken)
  rw [querySightings_rename, Record.rename_append, Record.references_rename]

/-- **The record a firing leaves is what the choice escape records for it.** -/
theorem choiceRecord_eq_records [DecidableEq O] (A : SubstitutionAction T S) (label : O → T)
    {C : Configuration T O} (f : Firing T S O) :
    (AnnotatedRuns.choiceEscape A label).records (s := C) f = choiceRecord f :=
  rfl

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Joint ends relative to records**: one renaming carries the first record to the second, keeps
labels up to the first knowledge, and carries the first state to the second up to its solutions. -/
def JointRecordModuloEquivalent (x y : Configuration T O × Record O) : Prop :=
  ∃ π : O ≃ O, Record.rename π x.2 = y.2 ∧ RenamingUpTo (entailedSetoid A x.1.equations) label ∅ π ∧
    SameUpTo A (renameConfiguration π x.1) y.1

variable {A label}

/-- **At one record, joint equivalence is equivalence relative to the record.** -/
theorem jointRecordModuloEquivalent_iff (r : Record O) (C D : Configuration T O) :
    JointRecordModuloEquivalent A label (C, r) (D, r) ↔ RecordModuloEquivalent A label r C D :=
  ⟨fun ⟨π, aut, k, same⟩ => ⟨π, aut, k, same⟩, fun ⟨π, aut, k, same⟩ => ⟨π, aut, k, same⟩⟩

theorem JointRecordModuloEquivalent.trans {x y z : Configuration T O × Record O}
    (h : JointRecordModuloEquivalent A label x y) (k : JointRecordModuloEquivalent A label y z) :
    JointRecordModuloEquivalent A label x z := by
  obtain ⟨π, carriedπ, kπ, same⟩ := h
  obtain ⟨ρ, carriedρ, kρ, same'⟩ := k
  have equivalent : A.Equivalent x.1.equations y.1.equations := same.1
  rw [← entailedSetoid_congr equivalent] at kρ
  refine ⟨π.trans ρ, ?_, kπ.trans kρ, ?_⟩
  · rw [Record.rename_trans, carriedπ, carriedρ]
  · rw [renameConfiguration_trans]
    exact GuardFreeProcessOrders.SameUpTo.trans A (sameUpTo_rename A ρ same) same'

variable {r : Record O}

/-- **Semantic firings that remake no remembered identity preserve equivalence relative to the
record**, when their made identities also avoid the other state. -/
theorem RecordModuloEquivalent.firing [DecidableEq O] {C D : Configuration T O}
    (h : RecordModuloEquivalent A label r C D) {f : Firing T S O} (valid : f.Valid A label C)
    (reads : IsSemantic A f)
    (avoids : ∀ m ∈ f.selection.made, m ∉ D.present ∧ m ∉ Record.support r) :
    ∃ π : O ≃ O, (f.rename π).Valid A label D ∧
      JointRecordModuloEquivalent A label (f.result label C, r ++ choiceRecord f)
        ((f.rename π).result label D, r ++ choiceRecord (f.rename π)) := by
  obtain ⟨π, aut, k, same, outside⟩ := h.supported
  obtain ⟨admits, kResult, sameResult⟩ := modulo_step_witness k same
    (fun m member => outside m (made_fresh valid member) (avoids m member).1 (avoids m member).2) reads
  refine ⟨π, admits.mpr valid, π, ?_, kResult, sameResult⟩
  show Record.rename π (r ++ choiceRecord f) = r ++ choiceRecord (f.rename π)
  rw [Record.rename_append, Record.mem_automorphisms.mp aut, choiceRecord_rename]

/-- **With a fresh supply of the made labels, semantic firings that remake no remembered identity
preserve equivalence relative to the record.** -/
theorem RecordModuloEquivalent.counterpart [DecidableEq O] {C D : Configuration T O}
    (h : RecordModuloEquivalent A label r C D) {f : Firing T S O} (valid : f.Valid A label C)
    (reads : IsSemantic A f) (unremembered : ∀ m ∈ f.selection.made, m ∉ Record.support r)
    (supply : ∀ m ∈ f.selection.made, ∀ G : Finset O, ∃ o, o ∉ G ∧ label o = label m) :
    ∃ τ : O ≃ O, (f.rename τ).Valid A label D ∧
      JointRecordModuloEquivalent A label (f.result label C, r ++ choiceRecord f)
        ((f.rename τ).result label D, r ++ choiceRecord (f.rename τ)) := by
  classical
  let M := f.selection.made.toFinset.filter (· ∈ D.present)
  let F := C.present ∪ D.present ∪ Record.support r ∪ f.names
  have inF_C : ∀ {o}, o ∈ C.present → o ∈ F := fun inC =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ inC))
  have inF_D : ∀ {o}, o ∈ D.present → o ∈ F := fun inD =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ inD))
  have inF_R : ∀ {o}, o ∈ Record.support r → o ∈ F := fun inR =>
    Finset.mem_union_left _ (Finset.mem_union_right _ inR)
  have madeNamed : ∀ {o}, o ∈ f.selection.made → o ∈ f.names := fun made => by
    simp [Firing.names, made]
  have madeOfM : ∀ {o}, o ∈ M → o ∈ f.selection.made := fun inM =>
    List.mem_toFinset.mp (Finset.mem_filter.mp inM).1
  have sub : M ⊆ F := fun o inM => inF_D (Finset.mem_filter.mp inM).2
  obtain ⟨ρ, keeps, moved, fixed⟩ := exists_fresh_relabelling M F sub
    fun m inM => supply m (madeOfM inM)
  have freshC : ∀ {m}, m ∈ f.selection.made → m ∉ C.present := fun made => made_fresh valid made
  have fixC : ∀ o ∈ C.present, ρ o = o := fun o inC =>
    fixed o (inF_C inC) fun inM => freshC (madeOfM inM) inC
  have fixR : ∀ o ∈ Record.support r, ρ o = o := fun o inR =>
    fixed o (inF_R inR) fun inM => unremembered o (madeOfM inM) inR
  have stays : renameConfiguration ρ C = C := by
    show (⟨C.equations, C.present.map ρ.toEmbedding⟩ : Configuration T O) = C
    rw [finset_map_eq_self ρ fixC]
  have gValid : (f.rename ρ).Valid A label C := by
    have moved := (Firing.valid_rename A keeps f C).mpr valid
    rwa [stays] at moved
  have gResult : (f.rename ρ).result label C = renameConfiguration ρ (f.result label C) := by
    have moved := Firing.result_rename keeps f C
    rwa [stays] at moved
  have gAvoids : ∀ m ∈ (f.rename ρ).selection.made, m ∉ D.present ∧ m ∉ Record.support r := by
    intro m member
    change m ∈ f.selection.made.map ρ at member
    obtain ⟨m₀, made₀, rfl⟩ := List.mem_map.mp member
    by_cases inD : m₀ ∈ D.present
    · have out := moved m₀ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr made₀, inD⟩)
      exact ⟨fun inD' => out (inF_D inD'), fun inR => out (inF_R inR)⟩
    · have same : ρ m₀ = m₀ := fixed m₀
        (Finset.mem_union_right _ (madeNamed made₀)) fun inM => inD (Finset.mem_filter.mp inM).2
      rw [same]
      exact ⟨inD, unremembered m₀ made₀⟩
  have privateStep : JointRecordModuloEquivalent A label (f.result label C, r ++ choiceRecord f)
      ((f.rename ρ).result label C, r ++ choiceRecord (f.rename ρ)) := by
    refine ⟨ρ, ?_, ⟨fun o => ?_, fun o member => absurd member (Finset.notMem_empty o)⟩, ?_⟩
    · show Record.rename ρ (r ++ choiceRecord f) = r ++ choiceRecord (f.rename ρ)
      rw [Record.rename_append, Record.rename_eq_self_of_fixes fixR, ← choiceRecord_rename]
    · show (entailedSetoid A (f.result label C).equations) (label (ρ o)) (label o)
      rw [keeps o]
    · show SameUpTo A (renameConfiguration ρ (f.result label C)) ((f.rename ρ).result label C)
      rw [gResult]
      exact GuardFreeProcessOrders.SameUpTo.refl A _
  obtain ⟨π, admitted, joint⟩ := h.firing gValid (isSemantic_rename ρ reads) gAvoids
  refine ⟨ρ.trans π, ?_, ?_⟩
  · rw [Firing.rename_trans]
    exact admitted
  · rw [Firing.rename_trans]
    exact privateStep.trans joint

end Firings

/-! ## Controls -/

namespace RecordCongruenceControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (zeros)
open ModuloControls (Tm X Y X_ne_Y knowsXY zeros_solves entailed_XY)

/-! ### A context occurrence that the record relates to the state -/

/-- One relation of two pairs. -/
def pairs : Record ℕ := [{[5, 7], [6, 8]}]

/-- The exchange of the pairs. -/
def pairSwap : ℕ ≃ ℕ := (Equiv.swap 5 6).trans (Equiv.swap 7 8)

section Overlap

variable (act : SubstitutionAction T S) (τ : T)

/-- `{5}` and `{6}`, all labels `τ`, are equivalent relative to the record of pairs. -/
theorem pairs_equivalent :
    RecordModuloEquivalent act (fun _ : ℕ => τ) pairs ⟨[], {5}⟩ ⟨[], {6}⟩ := by
  refine ⟨pairSwap, ?_, ⟨fun _ => (entailedSetoid act []).refl' τ,
    fun o member => absurd member (Finset.notMem_empty o)⟩, fun _ => Iff.rfl, ?_⟩
  · show Record.rename pairSwap pairs = pairs
    decide
  · show ({5} : Finset ℕ).map pairSwap.toEmbedding = {6}
    decide

/-- **A context occurrence related to the state by the record breaks composition**: `{7}` is disjoint
from `{5}` and `{6}`, the record mentions it, and the composites are not equivalent. -/
theorem record_overlap_control :
    RecordModuloEquivalent act (fun _ : ℕ => τ) pairs ⟨[], {5}⟩ ⟨[], {6}⟩ ∧
      Disjoint ({5} : Finset ℕ) {7} ∧ Disjoint ({6} : Finset ℕ) {7} ∧ 7 ∈ Record.support pairs ∧
      ¬ RecordModuloEquivalent act (fun _ : ℕ => τ) pairs
        (AnnotatedRuns.tensor ⟨[], {5}⟩ ⟨[], {7}⟩) (AnnotatedRuns.tensor ⟨[], {6}⟩ ⟨[], {7}⟩) := by
  refine ⟨pairs_equivalent act τ, by decide, by decide, by decide, ?_⟩
  rintro ⟨π, aut, -, same⟩
  have carried : Record.rename π pairs = pairs := aut
  have entry : Record.renameEntry π {[5, 7], [6, 8]} = {[5, 7], [6, 8]} := (List.cons.inj carried).1
  have image : [π 5, π 7] ∈ ({[5, 7], [6, 8]} : Finset (List ℕ)) := by
    rw [← entry]
    exact Finset.mem_map_of_mem (Record.tupleEmbedding π)
      (show [5, 7] ∈ ({[5, 7], [6, 8]} : Finset (List ℕ)) by decide)
  have present : (({5} : Finset ℕ) ∪ {7}).map π.toEmbedding = {6} ∪ {7} := same.2
  have at5 : π.toEmbedding 5 ∈ (({5} : Finset ℕ) ∪ {7}).map π.toEmbedding :=
    Finset.mem_map_of_mem _ (by decide)
  have at7 : π.toEmbedding 7 ∈ (({5} : Finset ℕ) ∪ {7}).map π.toEmbedding :=
    Finset.mem_map_of_mem _ (by decide)
  rw [present] at at5 at7
  simp only [Finset.mem_union, Finset.mem_singleton, Equiv.coe_toEmbedding] at at5 at7
  rcases Finset.mem_insert.mp image with first | second
  · have five : π 5 = 5 := (List.cons.inj first).1
    omega
  · have seven : π 7 = 8 := (List.cons.inj (List.cons.inj (Finset.mem_singleton.mp second)).2).1
    omega

end Overlap

/-! ### A firing that remakes a remembered identity -/

/-- Labels: `21` and `23` carry `Y`, every other identity `X`. -/
def recLabel (o : ℕ) : Tm := if o = 21 ∨ o = 23 then Y else X

/-- The record that relates `20` to `22` and `21` to `23`. -/
def twins : Record ℕ := [{[20, 22], [21, 23]}]

def twinC : Configuration Tm ℕ := ⟨knowsXY, {22}⟩
def twinD : Configuration Tm ℕ := ⟨knowsXY, {23}⟩

/-- The rule that makes one row labelled `X`. -/
def makeXRule : RuleInstance Tm := ⟨[], [], [], [], [X]⟩

/-- Make the row `o`. -/
def makeAt (o : ℕ) : Firing Tm (Subst signature) ℕ := ⟨makeXRule, [], ⟨[], [], [o]⟩⟩

theorem recLabel_entailed (o : ℕ) : (entailedSetoid A knowsXY) (recLabel o) X := by
  unfold recLabel
  split_ifs
  · exact (entailedSetoid A knowsXY).symm' entailed_XY
  · exact (entailedSetoid A knowsXY).refl' X

theorem recLabel_ne_21 {o : ℕ} (labelled : recLabel o = X) : o ≠ 21 := by
  rintro rfl
  exact X_ne_Y (by simpa [recLabel] using labelled.symm)

/-- **`{22}` and `{23}` are equivalent relative to the twin record**, by the exchange of the twins. -/
theorem twins_equivalent : RecordModuloEquivalent A recLabel twins twinC twinD := by
  refine ⟨(Equiv.swap 20 21).trans (Equiv.swap 22 23), ?_,
    ⟨fun o => (entailedSetoid A knowsXY).trans' (recLabel_entailed _)
      ((entailedSetoid A knowsXY).symm' (recLabel_entailed o)),
      fun o member => absurd member (Finset.notMem_empty o)⟩, fun _ => Iff.rfl, ?_⟩
  · show Record.rename ((Equiv.swap 20 21).trans (Equiv.swap 22 23)) twins = twins
    decide
  · show ({22} : Finset ℕ).map ((Equiv.swap 20 21).trans (Equiv.swap 22 23)).toEmbedding = {23}
    decide

theorem makeAt_valid {o : ℕ} (labelled : recLabel o = X) (fresh : o ≠ 22) :
    (makeAt o).Valid A recLabel twinC := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton o, rfl, rfl, by simp [makeAt, makeXRule, labelled],
    ⟨by simp [makeAt, Selection.commit], by simp [makeAt, Selection.commit],
      by simp [makeAt, Selection.commit], by simp [makeAt, Selection.commit, twinC, fresh],
      by simp [makeAt, Selection.commit]⟩, ⟨zeros, ?_⟩, by simp [makeAt, makeXRule]⟩,
    by simp [makeAt]⟩
  intro e member
  have known : e ∈ knowsXY := by
    simpa [Selection.problem, Selection.equations, makeAt, makeXRule, twinC] using member
  exact zeros_solves e known

theorem recLabel_supply (G : Finset ℕ) : ∃ o, o ∉ G ∧ recLabel o = X := by
  obtain ⟨o, out⟩ := Infinite.exists_notMem_finset (insert 21 (insert 23 G))
  refine ⟨o, fun inG => out (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem inG)), ?_⟩
  have not21 : o ≠ 21 := fun same => out (by rw [same]; exact Finset.mem_insert_self _ _)
  have not23 : o ≠ 23 := fun same =>
    out (Finset.mem_insert_of_mem (by rw [same]; exact Finset.mem_insert_self _ _))
  simp [recLabel, not21, not23]

/-- **A firing that remakes a remembered identity has no counterpart with equivalent joint ends.**
Making `20`, which the record relates to `22`, is admitted at `{22}`, semantic, and its label is
plentiful; every firing of its rule admitted at `{23}` leaves joint ends not equivalent to its own. -/
theorem remake_control :
    RecordModuloEquivalent A recLabel twins twinC twinD ∧ (makeAt 20).Valid A recLabel twinC ∧
      IsSemantic A (makeAt 20) ∧ 20 ∈ Record.support twins ∧
      (∀ G : Finset ℕ, ∃ o, o ∉ G ∧ recLabel o = recLabel 20) ∧
      ∀ g : Firing Tm (Subst signature) ℕ, g.rule = makeXRule → g.Valid A recLabel twinD →
        ¬ JointRecordModuloEquivalent A recLabel
          ((makeAt 20).result recLabel twinC, twins ++ choiceRecord (makeAt 20))
          (g.result recLabel twinD, twins ++ choiceRecord g) := by
  have label20 : recLabel 20 = X := by simp [recLabel]
  refine ⟨twins_equivalent, makeAt_valid label20 (by decide), isSemantic_of_queries_nil rfl,
    by decide, fun G => by rw [label20]; exact recLabel_supply G, fun g rule valid joint => ?_⟩
  obtain ⟨τ, carried, -, same⟩ := joint
  have takes := valid.firing.take_length
  rw [rule] at takes
  have noTake : g.selection.taken = [] := List.eq_nil_of_length_eq_zero takes.symm
  have outputs := valid.firing.outputs
  rw [rule] at outputs
  obtain ⟨n, single⟩ : ∃ n, g.selection.made = [n] := by
    rcases madeEq : g.selection.made with _ | ⟨n, _ | ⟨n', rest⟩⟩
    · rw [madeEq] at outputs
      exact absurd outputs (by simp [makeXRule])
    · exact ⟨n, rfl⟩
    · rw [madeEq] at outputs
      exact absurd outputs (by simp [makeXRule])
  rw [single] at outputs
  have labelN : recLabel n = X := List.singleton_inj.mp outputs
  have entry : Record.renameEntry τ {[20, 22], [21, 23]} = {[20, 22], [21, 23]} :=
    (List.cons.inj carried).1
  have image : [τ 20, τ 22] ∈ ({[20, 22], [21, 23]} : Finset (List ℕ)) := by
    rw [← entry]
    exact Finset.mem_map_of_mem (Record.tupleEmbedding τ)
      (show [20, 22] ∈ ({[20, 22], [21, 23]} : Finset (List ℕ)) by decide)
  have present : (MeTTaCalculus.OccurrenceCommits.fire ({22} : Finset ℕ)
      ((makeAt 20).selection.commit (T := Tm))).map τ.toEmbedding =
      MeTTaCalculus.OccurrenceCommits.fire ({23} : Finset ℕ) (g.selection.commit (T := Tm)) := same.2
  have at20 : τ.toEmbedding 20 ∈ (MeTTaCalculus.OccurrenceCommits.fire ({22} : Finset ℕ)
      ((makeAt 20).selection.commit (T := Tm))).map τ.toEmbedding :=
    Finset.mem_map_of_mem _ (by simp [MeTTaCalculus.OccurrenceCommits.fire, makeAt, Selection.commit])
  have at22 : τ.toEmbedding 22 ∈ (MeTTaCalculus.OccurrenceCommits.fire ({22} : Finset ℕ)
      ((makeAt 20).selection.commit (T := Tm))).map τ.toEmbedding :=
    Finset.mem_map_of_mem _ (by simp [MeTTaCalculus.OccurrenceCommits.fire, makeAt, Selection.commit])
  rw [present] at at20 at22
  simp [MeTTaCalculus.OccurrenceCommits.fire, Selection.commit, noTake, single] at at20 at22
  rcases Finset.mem_insert.mp image with first | second
  · have fixed20 : τ 20 = 20 := (List.cons.inj first).1
    have fixed22 : τ 22 = 22 := (List.cons.inj (List.cons.inj first).2).1
    omega
  · have moved20 : τ 20 = 21 := (List.cons.inj (Finset.mem_singleton.mp second)).1
    exact recLabel_ne_21 labelN (by omega)

end RecordCongruenceControls

#print axioms piecewiseRenaming
#print axioms Record.rename_congr
#print axioms RecordModuloEquivalent.supported
#print axioms RecordModuloEquivalent.tensor_disjoint
#print axioms choiceRecord_rename
#print axioms choiceRecord_eq_records
#print axioms jointRecordModuloEquivalent_iff
#print axioms JointRecordModuloEquivalent.trans
#print axioms RecordModuloEquivalent.firing
#print axioms RecordModuloEquivalent.counterpart
#print axioms RecordCongruenceControls.pairs_equivalent
#print axioms RecordCongruenceControls.record_overlap_control
#print axioms RecordCongruenceControls.twins_equivalent
#print axioms RecordCongruenceControls.makeAt_valid
#print axioms RecordCongruenceControls.remake_control

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
