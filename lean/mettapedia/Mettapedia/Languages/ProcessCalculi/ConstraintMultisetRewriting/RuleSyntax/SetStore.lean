import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AskTiming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Renaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder

/-!
# Idempotent store updates and occurrence firings

Remove selected source memberships, transport the surviving rows, and union
the produced rows. Transport can identify distinct rows, so removal must
precede transport. The result law is proved against the existing occurrence
firing, not used as the definition of the finite-set update.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore

open Interface (Frames)
open JointFirings
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe u v w uO uT uH uE uOcc

section Update

variable {T : Type u} {U : Type v} [DecidableEq T] [DecidableEq U]

def update (transport : T → U) (rows taken : Finset T) (made : Finset U) : Finset U :=
  (rows \ taken).image transport ∪ made

theorem mem_update {transport : T → U} {rows taken : Finset T} {made : Finset U} {value : U} :
    value ∈ update transport rows taken made ↔
      (∃ old ∈ rows, old ∉ taken ∧ transport old = value) ∨ value ∈ made := by
  simp only [update, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff]
  aesop

theorem update_no_take (transport : T → U) (rows : Finset T) (made : Finset U) :
    update transport rows ∅ made = rows.image transport ∪ made := by
  simp [update]

theorem update_known (rows made : Finset T) (known : made ⊆ rows) :
    update id rows ∅ made = rows := by
  simpa [update] using Finset.union_eq_left.mpr known

theorem update_duplicate_made (transport : T → U) (rows taken : Finset T)
    (made : Finset U) (value : U) :
    update transport rows taken (insert value (insert value made)) =
      update transport rows taken (insert value made) := by simp

theorem update_insertions_commute (rows first second : Finset T) :
    update id (update id rows ∅ first) ∅ second =
      update id (update id rows ∅ second) ∅ first := by
  simp [update, Finset.union_left_comm, Finset.union_comm]

end Update

section Zip

variable {O : Type u} {T : Type v}

theorem zip_left {made : List O} {rows : List T} (lengths : made.length = rows.length)
    {o : O} (member : o ∈ made) : ∃ t, (o, t) ∈ made.zip rows := by
  induction made generalizing rows with
  | nil => cases member
  | cons head rest ih =>
    cases rows with
    | nil => simp at lengths
    | cons value later =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨value, List.mem_cons_self⟩
      · obtain ⟨t, inside⟩ := ih (Nat.succ.inj lengths) member
        exact ⟨t, List.mem_cons_of_mem _ inside⟩

theorem zip_right {made : List O} {rows : List T} (lengths : made.length = rows.length)
    {t : T} (member : t ∈ rows) : ∃ o, (o, t) ∈ made.zip rows := by
  induction rows generalizing made with
  | nil => cases member
  | cons value later ih =>
    cases made with
    | nil => simp at lengths
    | cons head rest =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨head, List.mem_cons_self⟩
      · obtain ⟨o, inside⟩ := ih (Nat.succ.inj lengths) member
        exact ⟨o, List.mem_cons_of_mem _ inside⟩

end Zip

section Relabel

variable {Obj : Type w} {Tm : Obj → Type v} {a : Obj} {O : Type u}
  [DecidableEq O] [DecidableEq (Tm a)]

theorem image_relabel_made (old : O → Tm a) (made : List O) (rows : List (Tm a))
    (nodup : made.Nodup) (lengths : made.length = rows.length) :
    made.toFinset.image (relabel old made rows) = rows.toFinset := by
  ext t
  simp only [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨o, inside, rfl⟩
    obtain ⟨value, member⟩ := zip_left lengths inside
    rw [Firing.relabel_zip old made rows nodup lengths (o, value) member]
    exact (List.of_mem_zip member).2
  · intro inside
    obtain ⟨o, member⟩ := zip_right lengths inside
    exact ⟨o, (List.of_mem_zip member).1,
      Firing.relabel_zip old made rows nodup lengths (o, t) member⟩

/-- Independent finite-set update versus occurrence allocation and relabelling. -/
theorem image_fire (old : O → Tm a) (present taken : Finset O) (made : List O) (rows : List (Tm a))
    (nodup : made.Nodup) (lengths : made.length = rows.length)
    (fresh : Disjoint made.toFinset present) :
    ((present \ taken) ∪ made.toFinset).image (relabel old made rows) =
      (present \ taken).image old ∪ rows.toFinset := by
  rw [Finset.image_union, image_relabel_made old made rows nodup lengths]
  congr 1
  apply Finset.image_congr
  intro o member
  exact Firing.relabel_of_not_mem old made rows fun inside =>
    Finset.disjoint_left.mp fresh (List.mem_toFinset.mpr inside) (Finset.mem_sdiff.mp member).1

end Relabel

section Observe

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] [∀ a, DecidableEq (Tm a)]

noncomputable def support {a : Obj} (s : State Tm O) (σ : Hom s.frame a) :
    Finset (Tm a) := s.present.image fun o => X.act σ (s.label o)

omit [DecidableEq O] in
theorem support_rename {a : Obj} (s : State Tm O)
    (σ : Hom s.frame a) (π : Equiv.Perm O) :
    support X (Equivalence.renameState π s) σ = support X s σ := by
  classical
  simp only [support, Equivalence.renameState]
  ext value
  simp only [Finset.mem_image, Finset.mem_map_equiv]
  constructor
  · rintro ⟨o, inside, value⟩
    exact ⟨π.symm o, inside, value⟩
  · rintro ⟨o, inside, value⟩
    exact ⟨π o, by simpa using inside, by simpa using value⟩

variable {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

omit [DecidableEq O] [∀ a, DecidableEq (Tm a)] in
theorem bag_produce_length (s : State Tm O) (f : Bag O E P s.frame) (fits : f.Fits X s) :
    f.selection.made.length = (f.produce X).length := by
  simp only [Bag.selection, Bag.produce, List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro m inside
  simp only [Firing.opened, RuleInstance.map, List.length_map]
  exact (fits.2.2.2 m inside).2.2.1.symm

/-- Keep the actual solver's assignment global: aliases between rows survive transport. -/
theorem support_result {a : Obj} (s : State Tm O)
    (f : Bag O E P s.frame) (admitted : f.Admits X s) (σ : Hom (E.target f.ext) a) :
    support X (f.result X s) σ =
      (s.present \ f.selection.taken.toFinset).image
          (fun o => X.act σ (X.act (E.weaken f.ext) (s.label o))) ∪
        (f.produce X).toFinset.image (X.act σ) := by
  classical
  have raw := image_fire (fun o => X.act (E.weaken f.ext) (s.label o)) s.present f.selection.taken.toFinset
    f.selection.made (f.produce X) admitted.1.2.2.1 (bag_produce_length X s f admitted.1)
    admitted.2.1.fresh
  have mapped := congrArg (Finset.image (X.act σ)) raw
  simpa only [support, Bag.result, fire, Selection.commit, Finset.image_union,
    Finset.image_image, Function.comp_def] using mapped

/-- On a duplicate-free source, selection is removal of memberships before transport. -/
theorem support_result_set_update {a : Obj} (s : State Tm O)
    (f : Bag O E P s.frame) (admitted : f.Admits X s)
    (distinct : Set.InjOn s.label (s.present : Set O)) (σ : Hom (E.target f.ext) a) :
    support X (f.result X s) σ =
      update (fun value => X.act σ (X.act (E.weaken f.ext) value))
        (s.present.image s.label) (f.selection.taken.toFinset.image s.label)
        ((f.produce X).toFinset.image (X.act σ)) := by
  classical
  rw [support_result X s f admitted σ]
  unfold update
  have subset : f.selection.taken.toFinset ⊆ s.present := admitted.2.1.taken_subset
  rw [← Finset.image_sdiff_of_injOn distinct subset, Finset.image_image]
  rfl

end Observe

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore
