import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Strong

/-!
# The congruence is the largest relation closed under contexts with the same identities

The standard definition of reduction-closed barbed congruence closes a relation under every context
that applies to both systems, the same context at both sides (`CandidateSame`, `CongruentSame`). The
definition used in `Congruence` lets the right side choose the identities of added rows afresh,
which makes transitivity immediate for every identity type.

* **The two agree with infinitely many identities** (`congruent_iff_congruentSame`). One direction
  holds for every identity type (`congruentSame_of_congruent`, from `Congruent.basic_same`). For the
  other, a same-identity candidate is closed under contexts up to the congruence: a context that applies
  to the left system is renamed for the middle systems, moved away from both of them
  (`exists_perm_avoid`), applied with the same identities there, and the renamings of its rows are
  congruent (`rename_apply_congruent`).
* For finitely many identities the equality is not claimed: a middle system may hold every identity a
  context could use.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

open Interface (Frames)

universe uO uT uH uE uOcc uB

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

section Permutations

variable {O : Type uOcc} [DecidableEq O]

/-- **Moving identities away**: with infinitely many identities, some permutation sends a finite set
outside any other finite set. -/
theorem exists_perm_avoid [Infinite O] (A : Finset O) (ids : Finset O) :
    ∃ ρ : Equiv.Perm O, Disjoint (ids.map ρ.toEmbedding) A := by
  induction ids using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | @insert a rest notMem ih =>
      obtain ⟨ρ₀, apart⟩ := ih
      obtain ⟨z, fresh⟩ := Infinite.exists_notMem_finset (A ∪ rest.map ρ₀.toEmbedding ∪ {ρ₀ a})
      have zOut : z ∉ A := fun h => fresh (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have zNotRest : z ∉ rest.map ρ₀.toEmbedding := fun h =>
        fresh (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      refine ⟨Equiv.swap (ρ₀ a) z * ρ₀, ?_⟩
      rw [Finset.disjoint_left]
      intro x inside inA
      obtain ⟨y, member, rfl⟩ := Finset.mem_map.mp inside
      rcases Finset.mem_insert.mp member with same | later
      · rw [same] at inA
        have moved : (Equiv.swap (ρ₀ a) z * ρ₀) a = z := by
          rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        exact zOut (moved ▸ inA)
      · have different : ρ₀ y ≠ ρ₀ a := fun h => notMem (ρ₀.injective h ▸ later)
        have notZ : ρ₀ y ≠ z := fun h => zNotRest (h ▸ Finset.mem_map_of_mem _ later)
        have kept : (Equiv.swap (ρ₀ a) z * ρ₀) y = ρ₀ y := by
          rw [Equiv.Perm.mul_apply]
          exact Equiv.swap_apply_of_ne_of_ne different notZ
        have inA' : ρ₀ y ∈ A := kept ▸ inA
        exact Finset.disjoint_left.mp apart (Finset.mem_map_of_mem _ later) inA'

end Permutations

section Same

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)
  {B : Type uB} (obs : B → State Tm O → Prop)

/-- **A candidate with the same identities**: a barbed bisimulation closed under every basic context
that applies to both systems. -/
structure CandidateSame (R : System Tm O → System Tm O → Prop) : Prop
    extends Bisimulation X O E obs R where
  context : ∀ {S T : System Tm O}, R S T → ∀ c : Basic Tm O E, c.Applies S → c.Applies T →
    R (c.apply X S) (c.apply X T)

/-- **Reduction-closed barbed congruence with the same identities.** -/
def CongruentSame (S T : System Tm O) : Prop := ∃ R, CandidateSame X O E obs R ∧ R S T

end Same

section Theory

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {B : Type uB} {obs : B → State Tm O → Prop}

/-- **The congruence is a same-identity candidate.** -/
theorem congruentSame_of_congruent
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (invariantModulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    {S T : System Tm O} (related : Congruent X O E obs S T) : CongruentSame X O E obs S T :=
  ⟨Congruent X O E obs, ⟨candidate_congruent.toBisimulation,
    fun related c applyS applyT => related.basic_same invariantRename invariantModulo c applyS applyT⟩,
    related⟩

/-- **A context and its renaming**, both applying to a system, give congruent systems. -/
theorem rename_apply_congruent
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (invariantModulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    (c : Basic Tm O E) (ρ : Equiv.Perm O) (S : System Tm O) (applies : c.Applies S)
    (applies' : (c.rename ρ).Applies S) :
    Congruent X O E obs (c.apply X S) ((c.rename ρ).apply X S) := by
  cases c with
  | rows ids label =>
      exact (rows_rename_congruent invariantRename invariantModulo S.program S.state ids
        (label S.state.frame) ρ applies applies').symm
  | rules added => exact Congruent.refl _
  | tell equations => exact Congruent.refl _
  | extend extension => exact Congruent.refl _

/-- **With infinitely many identities, a same-identity candidate relates only congruent systems.** -/
theorem congruent_of_congruentSame [Infinite O]
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (invariantModulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    {S T : System Tm O} (related : CongruentSame X O E obs S T) : Congruent X O E obs S T := by
  obtain ⟨R, candidate, related⟩ := related
  let R' : System Tm O → System Tm O → Prop := fun S T =>
    ∃ S₀ T₀, Congruent X O E obs S S₀ ∧ R S₀ T₀ ∧ Congruent X O E obs T₀ T
  have candidate' : Candidate X O E obs R' := {
    symm := fun ⟨S₀, T₀, left, r, right⟩ => ⟨T₀, S₀, right.symm, candidate.symm r, left.symm⟩
    barbs := fun ⟨_, _, left, r, right⟩ β holds =>
      candidate_congruent.barbs right β (candidate.barbs r β (candidate_congruent.barbs left β holds))
    reduces := fun ⟨_, _, left, r, right⟩ _ moved => by
      obtain ⟨S₀', moved₀, left'⟩ := candidate_congruent.reduces left moved
      obtain ⟨T₀', movedT₀, r'⟩ := candidate.reduces r moved₀
      obtain ⟨T', movedT, right'⟩ := candidate_congruent.reduces right movedT₀
      exact ⟨T', movedT, S₀', T₀', left', r', right'⟩
    context := fun {_ _} ⟨S₀, T₀, left, r, right⟩ c applies => by
      obtain ⟨π₁, applies₀, left'⟩ := candidate_congruent.context left c applies
      obtain ⟨ρ, apart⟩ := exists_perm_avoid (S₀.state.present ∪ T₀.state.present) (c.rename π₁).ids
      have appliesS₀ : ((c.rename π₁).rename ρ).Applies S₀ := by
        unfold Basic.Applies
        rw [Basic.ids_rename]
        exact Finset.disjoint_of_subset_right Finset.subset_union_left apart
      have appliesT₀ : ((c.rename π₁).rename ρ).Applies T₀ := by
        unfold Basic.Applies
        rw [Basic.ids_rename]
        exact Finset.disjoint_of_subset_right Finset.subset_union_right apart
      have moved₀ := rename_apply_congruent invariantRename invariantModulo (c.rename π₁) ρ S₀
        applies₀ appliesS₀
      have r' := candidate.context r ((c.rename π₁).rename ρ) appliesS₀ appliesT₀
      obtain ⟨π₃, appliesT, right'⟩ := candidate_congruent.context right ((c.rename π₁).rename ρ)
        appliesT₀
      rw [Basic.rename_rename] at moved₀
      rw [Basic.rename_rename] at r'
      rw [Basic.rename_rename, Basic.rename_rename] at appliesT
      rw [Basic.rename_rename, Basic.rename_rename] at right'
      exact ⟨π₃ * (ρ * π₁), appliesT, _, _, left'.trans moved₀, r', right'⟩ }
  exact candidate'.le_congruent ⟨S, T, Congruent.refl S, related, Congruent.refl T⟩

/-- **With infinitely many identities, the congruence is the standard one.** -/
theorem congruent_iff_congruentSame [Infinite O]
    (invariantRename : ∀ (π : Equiv.Perm O) β s, obs β (renameState π s) ↔ obs β s)
    (invariantModulo : ∀ {s t : State Tm O}, Modulo X s t → ∀ β, obs β s → obs β t)
    {S T : System Tm O} : Congruent X O E obs S T ↔ CongruentSame X O E obs S T :=
  ⟨congruentSame_of_congruent invariantRename invariantModulo,
    congruent_of_congruentSame invariantRename invariantModulo⟩

/-- **For the chosen barbs.** -/
theorem congruent_iff_congruentSame_mayBarb [Infinite O] {S T : System Tm O} :
    Congruent X O E (MayBarb X) S T ↔ CongruentSame X O E (MayBarb X) S T :=
  congruent_iff_congruentSame (fun π p s => mayBarb_renameState X π p s)
    (fun related p => mayBarb_modulo related p)

end Theory

#print axioms exists_perm_avoid
#print axioms congruentSame_of_congruent
#print axioms rename_apply_congruent
#print axioms congruent_of_congruentSame
#print axioms congruent_iff_congruentSame
#print axioms congruent_iff_congruentSame_mayBarb

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
