import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsStages
import Mathlib.Data.Fintype.Basic

/-!
# Finite presentations of positive consequence stages

The executable finite-set operation is compared to the set-valued immediate
consequence operator. A finite presentation must cover the actual instances;
enumerating only some enabled rules is not silently complete. The adapter is
useful for controls and for licensed finite kernel configurations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds

universe u v w
variable {G : Type u} {I : Type v} {J : Type w} [DecidableEq G]

def finiteImmediate [Fintype I] (rules : I → SetStoreClosure.Instance G) (rows : Finset G) : Finset G :=
  rows ∪ Finset.univ.biUnion (fun i => if (rules i).read ⊆ rows then (rules i).made else ∅)

theorem coe_finiteImmediate [Fintype I] (rules : I → SetStoreClosure.Instance G) (rows : Finset G) :
    (finiteImmediate rules rows : Set G) = immediate rules (rows : Set G) := by
  ext value
  simp only [finiteImmediate, Finset.mem_coe, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_univ, true_and, immediate, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (old | ⟨i, member⟩)
    · exact Or.inl old
    · by_cases enabled : (rules i).read ⊆ rows
      · exact Or.inr ⟨i, enabled, by simpa only [if_pos enabled] using member⟩
      · simp only [if_neg enabled, Finset.notMem_empty] at member
  · rintro (old | ⟨i, enabled, made⟩)
    · exact Or.inl old
    · have fits : (rules i).read ⊆ rows := enabled
      refine Or.inr ⟨i, ?_⟩
      rw [if_pos fits]
      exact made

def finiteStage [Fintype I] (rules : I → SetStoreClosure.Instance G) (seed : Finset G) : Nat → Finset G
  | 0 => seed
  | n + 1 => finiteImmediate rules (finiteStage rules seed n)

theorem coe_finiteStage [Fintype I] (rules : I → SetStoreClosure.Instance G) (seed : Finset G) (n : Nat) :
    (finiteStage rules seed n : Set G) = stage rules (seed : Set G) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finiteStage, coe_finiteImmediate, ih, stage_succ]

omit [DecidableEq G] in
theorem immediate_eq_of_instance_cover (rules : I → SetStoreClosure.Instance G)
    (presented : J → SetStoreClosure.Instance G)
    (covers : ∀ i, ∃ j, rules i = presented j)
    (sound : ∀ j, ∃ i, presented j = rules i) (rows : Set G) :
    immediate rules rows = immediate presented rows := by
  ext value
  constructor
  · rintro (old | ⟨i, enabled, made⟩)
    · exact Or.inl old
    · obtain ⟨j, same⟩ := covers i
      rw [same] at enabled made
      exact Or.inr ⟨j, enabled, made⟩
  · rintro (old | ⟨j, enabled, made⟩)
    · exact Or.inl old
    · obtain ⟨i, same⟩ := sound j
      rw [same] at enabled made
      exact Or.inr ⟨i, enabled, made⟩

omit [DecidableEq G] in
theorem stage_eq_of_instance_cover (rules : I → SetStoreClosure.Instance G)
    (presented : J → SetStoreClosure.Instance G)
    (covers : ∀ i, ∃ j, rules i = presented j)
    (sound : ∀ j, ∃ i, presented j = rules i) (seed : Set G) (n : Nat) :
    stage rules seed n = stage presented seed n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stage_succ, stage_succ, ih, immediate_eq_of_instance_cover rules presented covers sound]

#print axioms coe_finiteImmediate
#print axioms coe_finiteStage
#print axioms immediate_eq_of_instance_cover
#print axioms stage_eq_of_instance_cover

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds
