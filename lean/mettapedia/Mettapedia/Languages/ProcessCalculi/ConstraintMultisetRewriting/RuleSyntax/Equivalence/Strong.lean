import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Renaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Modulo

/-!
# The congruence is closed under contexts with the same identities

A candidate lets the right side choose fresh identities for the rows a context adds. With Law 1 and
Law 2 that choice is immaterial:

* **Restoring identities** (`exists_perm_restore`): when the identities `ids` and their renaming
  `π ids` are both absent from `W`, some permutation fixes `W` pointwise and sends each `π o` back to
  `o`; it is a product of transpositions.
* **Rows with the same identities** (`Congruent.addRows_same`): congruent systems with the same rows
  added at the same identities, absent from both, are congruent. The proof renames the right side's
  rows back (Law 1) and forgets the labels of absent identities (Law 2).
* **Every context with the same identities** (`Congruent.basic_same`, `Congruent.applyAll_same`), and
  hence **soundness for contextual equivalence** in its plain form (`congruent_contextual`): under every
  composite context applying to both, congruent systems reach the same barbs.

These hold for every barb family invariant under renaming of identities and under equivalence modulo
the knowledge; the may-barbs are (`congruent_contextual_mayBarb`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

open Interface (Frames)

universe uO uT uH uE uOcc uB

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

section Permutations

variable {O : Type uOcc} [DecidableEq O]

/-- **Restoring identities**: when `ids` and its renaming are absent from `W`, a permutation fixes `W`
and sends each renamed identity back. -/
theorem exists_perm_restore (π : Equiv.Perm O) (W : Finset O) (ids : Finset O) :
    Disjoint ids W → Disjoint (ids.map π.toEmbedding) W →
      ∃ ρ : Equiv.Perm O, (∀ o ∈ ids, ρ (π o) = o) ∧ ∀ o ∈ W, ρ o = o := by
  induction ids using Finset.induction_on with
  | empty =>
      intro _ _
      exact ⟨1, fun o inside => absurd inside (Finset.notMem_empty o), fun _ _ => rfl⟩
  | @insert a rest notMem ih =>
      intro apart apartMap
      have aOut : a ∉ W := Finset.disjoint_left.mp apart (Finset.mem_insert_self a rest)
      have restApart : Disjoint rest W :=
        Finset.disjoint_of_subset_left (Finset.subset_insert a rest) apart
      have imageOut : π a ∉ W := Finset.disjoint_left.mp apartMap
        (Finset.mem_map_of_mem _ (Finset.mem_insert_self a rest))
      have restMapApart : Disjoint (rest.map π.toEmbedding) W :=
        Finset.disjoint_of_subset_left (Finset.map_subset_map.mpr (Finset.subset_insert a rest))
          apartMap
      obtain ⟨ρ₀, back, fixes⟩ := ih restApart restMapApart
      refine ⟨Equiv.swap a (ρ₀ (π a)) * ρ₀, fun o inside => ?_, fun w inside => ?_⟩
      · rw [Equiv.Perm.mul_apply]
        rcases Finset.mem_insert.mp inside with rfl | later
        · exact Equiv.swap_apply_right _ _
        · rw [back o later]
          apply Equiv.swap_apply_of_ne_of_ne
          · exact fun same => notMem (same ▸ later)
          · intro same
            have images : ρ₀ (π o) = ρ₀ (π a) := (back o later).trans same
            have equal : o = a := π.injective (ρ₀.injective images)
            exact notMem (equal ▸ later)
      · rw [Equiv.Perm.mul_apply, fixes w inside]
        apply Equiv.swap_apply_of_ne_of_ne
        · exact fun same => aOut (same ▸ inside)
        · intro same
          have images : ρ₀ w = ρ₀ (π a) := (fixes w inside).trans same
          exact imageOut (ρ₀.injective images ▸ inside)

end Permutations

section Strong

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {B : Type uB} {obs : B → State Tm O → Prop}

/-- **The same rows at two sets of fresh identities**: adding them at `ids` or at the renamed `π ids`,
both absent from the state, gives congruent systems. -/
theorem rows_rename_congruent
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (modulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    (P : Program Tm) (s : State Tm O) (ids : Finset O) (label : O → Tm s.frame) (π : Equiv.Perm O)
    (apart : Disjoint ids s.present) (apart' : Disjoint (ids.map π.toEmbedding) s.present) :
    Congruent X O E obs ⟨P, addRows s (ids.map π.toEmbedding) (fun o => label (π.symm o))⟩
      ⟨P, addRows s ids label⟩ := by
  obtain ⟨ρ, back, fixes⟩ := exists_perm_restore π s.present ids apart apart'
  let moved : State Tm O := addRows s (ids.map π.toEmbedding) (fun o => label (π.symm o))
  let target : State Tm O := addRows s ids label
  have backSymm : ∀ o ∈ ids, ρ.symm o = π o := fun o inside => by
    rw [Equiv.symm_apply_eq]
    exact (back o inside).symm
  have fixesSymm : ∀ o ∈ s.present, ρ.symm o = o := fun o inside => by
    rw [Equiv.symm_apply_eq]
    exact (fixes o inside).symm
  have present : (renameState ρ moved).present = target.present := by
    show (s.present ∪ ids.map π.toEmbedding).map ρ.toEmbedding = s.present ∪ ids
    ext o
    rw [Finset.mem_map_equiv, Finset.mem_union, Finset.mem_union, Finset.mem_map_equiv]
    constructor
    · rintro (old | new)
      · have same : ρ (ρ.symm o) = ρ.symm o := fixes _ old
        rw [Equiv.apply_symm_apply] at same
        left
        rw [same]
        exact old
      · have restored := back _ new
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at restored
        right
        rw [restored]
        exact new
    · rintro (old | new)
      · rw [fixesSymm o old]
        exact Or.inl old
      · rw [backSymm o new, Equiv.symm_apply_apply]
        exact Or.inr new
  have agree : ∀ o ∈ target.present, (renameState ρ moved).label o = target.label o := by
    intro o inside
    show (if ρ.symm o ∈ ids.map π.toEmbedding then label (π.symm (ρ.symm o))
        else s.label (ρ.symm o)) = (if o ∈ ids then label o else s.label o)
    by_cases new : o ∈ ids
    · have moved' : π o ∈ ids.map π.toEmbedding := Finset.mem_map_equiv.mpr (by simpa using new)
      rw [backSymm o new, if_pos moved', if_pos new, Equiv.symm_apply_apply]
    · have old : o ∈ s.present := by
        rcases Finset.mem_union.mp inside with old | inIds
        · exact old
        · exact absurd inIds new
      have notMoved : o ∉ ids.map π.toEmbedding := fun inside' =>
        Finset.disjoint_left.mp apart' inside' old
      rw [fixesSymm o old, if_neg notMoved, if_neg new]
  have renamed : Congruent X O E obs ⟨P, moved⟩ ⟨P, renameState ρ moved⟩ :=
    rename_congruent invariantRename ρ ⟨P, moved⟩
  have forgotten : Congruent X O E obs ⟨P, target⟩ ⟨P, renameState ρ moved⟩ := by
    have equal : (⟨target.frame, target.knowledge, target.present, (renameState ρ moved).label⟩ :
        State Tm O) =
        ⟨target.frame, target.knowledge, (renameState ρ moved).present, (renameState ρ moved).label⟩ := by
      rw [present]
    have base := offPresent_congruent (E := E) modulo P target (renameState ρ moved).label agree
    rw [equal] at base
    exact base
  exact renamed.trans forgotten.symm

/-- **Rows with the same identities.** -/
theorem Congruent.addRows_same
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (modulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    {S T : System Tm O} (related : Congruent X O E obs S T) (ids : Finset O)
    (label : (a : Obj) → O → Tm a) (applyS : Disjoint ids S.state.present)
    (applyT : Disjoint ids T.state.present) :
    Congruent X O E obs ⟨S.program, Equivalence.addRows S.state ids (label S.state.frame)⟩
      ⟨T.program, Equivalence.addRows T.state ids (label T.state.frame)⟩ := by
  obtain ⟨π, applyT', related'⟩ := related.addRows ids label applyS
  exact related'.trans (rows_rename_congruent invariantRename modulo T.program T.state ids
    (label T.state.frame) π applyT applyT')

/-- **Every basic context with the same identities.** -/
theorem Congruent.basic_same
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (modulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    {S T : System Tm O} (related : Congruent X O E obs S T) (c : Basic Tm O E)
    (applyS : c.Applies S) (applyT : c.Applies T) :
    Congruent X O E obs (c.apply X S) (c.apply X T) := by
  cases c with
  | rows ids label => exact related.addRows_same invariantRename modulo ids label applyS applyT
  | rules added => exact related.addRules added
  | tell equations => exact related.tell equations
  | extend extension => exact related.extend extension

/-- **Every composite context with the same identities.** -/
theorem Congruent.applyAll_same
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (modulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    {C : List (Basic Tm O E)} :
    ∀ {S T : System Tm O}, Congruent X O E obs S T → AppliesAll X C S → AppliesAll X C T →
      Congruent X O E obs (applyAll X C S) (applyAll X C T) := by
  induction C with
  | nil => exact fun related _ _ => related
  | cons c C ih =>
      intro S T related appliesS appliesT
      cases appliesS with
      | cons firstS restS =>
          cases appliesT with
          | cons firstT restT =>
              exact ih (related.basic_same invariantRename modulo c firstS firstT) restS restT

/-- **The congruence is sound for contextual equivalence.** -/
theorem congruent_contextual
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (modulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    {S T : System Tm O} (related : Congruent X O E obs S T) :
    ContextuallyEquivalent X O E obs S T := by
  intro C appliesS appliesT β
  have related' := related.applyAll_same invariantRename modulo appliesS appliesT
  exact ⟨related'.converges, related'.symm.converges⟩

/-- **For the chosen barbs.** -/
theorem congruent_contextual_mayBarb {S T : System Tm O}
    (related : Congruent X O E (MayBarb X) S T) : ContextuallyEquivalent X O E (MayBarb X) S T :=
  congruent_contextual (fun π p s => mayBarb_renameState X π p s)
    (fun related p => mayBarb_modulo related p) related

end Strong

#print axioms exists_perm_restore
#print axioms rows_rename_congruent
#print axioms Congruent.addRows_same
#print axioms Congruent.basic_same
#print axioms Congruent.applyAll_same
#print axioms congruent_contextual
#print axioms congruent_contextual_mayBarb

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
