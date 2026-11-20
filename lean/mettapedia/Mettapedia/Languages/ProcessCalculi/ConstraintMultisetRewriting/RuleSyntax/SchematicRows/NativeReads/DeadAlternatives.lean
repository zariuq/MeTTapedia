import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Observation

/-!
# Removing proved-unsolvable alternatives preserves actual source execution

Dead branches cannot take a source step. The result is a simulation in both
directions with the same world effects and step count, plus the existing
answer/refusal/waiting observation. It is not equality of raw branch storage
or a licence to call unfinished solver work unsatisfiable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.DeadAlternatives

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  {D : Discipline S Γ star} {P : Program κ Γ star D.Ty} {supply : Nat → Term S Γ star}

def extend (config : Config κ Γ star D.Ty) (dead : Multiset (Branch κ Γ star D.Ty)) : Config κ Γ star D.Ty :=
  ⟨config.world, config.branches + dead⟩

def Dead (branches : Multiset (Branch κ Γ star D.Ty)) : Prop :=
  ∀ branch ∈ branches, ¬ Solvable branch.store

theorem observation (config : Config κ Γ star D.Ty) (dead : Multiset (Branch κ Γ star D.Ty))
    (refuted : Dead dead) : Observation.observe (extend config dead) = Observation.observe config :=
  Observation.observe_add_dead config dead refuted

theorem lift_step {before after : Config κ Γ star D.Ty}
    (step : SourceLanguage.Step D P supply before after) (dead : Multiset (Branch κ Γ star D.Ty)) :
    SourceLanguage.Step D P supply (extend before dead) (extend after dead) := step.frame dead

theorem project_step (before : Config κ Γ star D.Ty) (dead : Multiset (Branch κ Γ star D.Ty))
    (refuted : Dead dead) {fullAfter : Config κ Γ star D.Ty}
    (step : SourceLanguage.Step D P supply (extend before dead) fullAfter) :
    ∃ after, SourceLanguage.Step D P supply before after ∧ fullAfter = extend after dead := by
  classical
  generalize origin : extend before dead = fullBefore at step
  cases step with
  | move world next branch rest outputs alive moved =>
      have worlds : before.world = world := congrArg Config.world origin
      have branches : before.branches + dead = branch ::ₘ rest := congrArg Config.branches origin
      have member : branch ∈ before.branches + dead := by
        rw [branches]
        exact Multiset.mem_cons_self ..
      have kept : branch ∈ before.branches := by
        rcases Multiset.mem_add.mp member with kept | discarded
        · exact kept
        · exact False.elim (refuted branch discarded alive)
      have remainder : rest = before.branches.erase branch + dead := by
        have erased := congrArg (fun rows => rows.erase branch) branches
        simpa only [Multiset.erase_add_left_pos dead kept, Multiset.erase_cons_head] using erased.symm
      let after : Config κ Γ star D.Ty := ⟨next, outputs + before.branches.erase branch⟩
      refine ⟨after, ?_, ?_⟩
      · rcases before with ⟨originalWorld, originalBranches⟩
        simp only at worlds kept
        subst originalWorld
        exact SourceLanguage.Step.of_eq (Multiset.cons_erase kept).symm rfl alive moved
      · simp only [after, extend, remainder, add_assoc]

theorem project_run (before : Config κ Γ star D.Ty) (dead : Multiset (Branch κ Γ star D.Ty))
    (refuted : Dead dead) {fullAfter : Config κ Γ star D.Ty}
    (run : SourceLanguage.Runs D P supply (extend before dead) fullAfter) :
    ∃ after, SourceLanguage.Runs D P supply before after ∧ fullAfter = extend after dead := by
  generalize origin : extend before dead = fullBefore at run
  induction run generalizing before with
  | refl => exact ⟨before, .refl, origin.symm⟩
  | tail previous step ih =>
      obtain ⟨middle, earlier, same⟩ := ih before origin
      rw [same] at step
      obtain ⟨after, later, final⟩ := project_step middle dead refuted step
      exact ⟨after, earlier.tail later, final⟩

theorem quiescent_iff (config : Config κ Γ star D.Ty) (dead : Multiset (Branch κ Γ star D.Ty))
    (refuted : Dead dead) :
    (extend config dead).Quiescent P supply ↔ config.Quiescent P supply := by
  constructor
  · intro stopped branch member alive world outputs moved
    exact stopped branch (Multiset.mem_add.mpr (Or.inl member)) alive world outputs moved
  · intro stopped branch member alive world outputs moved
    rcases Multiset.mem_add.mp member with kept | removed
    · exact stopped branch kept alive world outputs moved
    · exact refuted branch removed alive

#print axioms project_step
#print axioms project_run
#print axioms observation
#print axioms quiescent_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.DeadAlternatives
