import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.ContextualIndex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.DeadAlternatives

/-!
# Indexed matching refines the actual binding-aware query move

Filtering removes only proved-unsolvable alternatives. The reference move
still constructs its complete branch bag; the indexed result differs by a
dead extension. The existing observer and the actual subsequent source steps
therefore agree, including future effects, waiting and answer multiplicity.
Raw branch-allocation counts and solver work are deliberately not identified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.QueryProjection

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty} {supply : Nat → Term S Γ star}
  [DecidableEq (S.Op star)]

def branchAt (scope : Nat) (store : List (Constraint κ Γ star)) (pattern : Data κ Γ star)
    (body : Comp κ Γ star D.Ty) (frames : List (SourceLanguage.Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty)) (row : SourceLanguage.Row κ Γ star) : Branch κ Γ star D.Ty :=
  ⟨store ++ rowUse scope row pattern, .eval body, frames, pending⟩

def indexed (world : World κ Γ star) (store : List (Constraint κ Γ star))
    (address : Term S Γ star) (pattern : Data κ Γ star)
    (body : Comp κ Γ star D.Ty) (frames : List (SourceLanguage.Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty)) : Config κ Γ star D.Ty :=
  ⟨world.fresh, ((world.spaces address).filter (fun row => ContextualIndex.permits pattern row.atom = true)).map
    (branchAt world.scope store pattern body frames pending)⟩

def discarded (world : World κ Γ star) (store : List (Constraint κ Γ star))
    (address : Term S Γ star) (pattern : Data κ Γ star)
    (body : Comp κ Γ star D.Ty) (frames : List (SourceLanguage.Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty)) : Multiset (Branch κ Γ star D.Ty) :=
  ((world.spaces address).filter (fun row => ¬ ContextualIndex.permits pattern row.atom = true)).map
    (branchAt world.scope store pattern body frames pending)

theorem discarded_dead (world : World κ Γ star) (store : List (Constraint κ Γ star))
    (address : Term S Γ star) (pattern : Data κ Γ star)
    (body : Comp κ Γ star D.Ty) (frames : List (SourceLanguage.Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty)) :
    DeadAlternatives.Dead (discarded world store address pattern body frames pending) := by
  intro branch member
  obtain ⟨row, selected, rfl⟩ := Multiset.mem_map.mp member
  have rejected := (Multiset.mem_filter.mp selected).2
  have no : ContextualIndex.permits pattern row.atom = false := Bool.eq_false_iff.mpr rejected
  exact ContextualIndex.rejected_problem_unsolvable world.scope store pattern row no

theorem partition (world : World κ Γ star) (store : List (Constraint κ Γ star))
    (address : Term S Γ star) (pattern : Data κ Γ star)
    (body : Comp κ Γ star D.Ty) (frames : List (SourceLanguage.Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty)) :
    (world.spaces address).map (branchAt world.scope store pattern body frames pending) =
      (indexed world store address pattern body frames pending).branches +
        discarded world store address pattern body frames pending := by
  simp only [indexed, discarded]
  rw [← Multiset.map_add, Multiset.filter_add_not]

theorem actual_move (world : World κ Γ star) (store : List (Constraint κ Γ star))
    (space pattern : Data κ Γ star) (address : Term S Γ star)
    (body : Comp κ Γ star D.Ty) (frames : List (SourceLanguage.Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty))
    (addressed : Determines store space address) :
    Move D P supply world ⟨store, .eval (.query space pattern body), frames, pending⟩ world.fresh
      ((indexed world store address pattern body frames pending).branches +
        discarded world store address pattern body frames pending) := by
  rw [← partition]
  exact .query world store space pattern body frames pending address addressed

theorem projected_future_run (world : World κ Γ star) (store : List (Constraint κ Γ star))
    (address : Term S Γ star) (pattern : Data κ Γ star)
    (body : Comp κ Γ star D.Ty) (frames : List (SourceLanguage.Frame κ Γ star D.Ty))
    (pending : List (Data κ Γ star × Comp κ Γ star D.Ty))
    {fullAfter : Config κ Γ star D.Ty}
    (run : SourceLanguage.Runs D P supply
      ⟨world.fresh, (world.spaces address).map (branchAt world.scope store pattern body frames pending)⟩ fullAfter) :
    ∃ after, SourceLanguage.Runs D P supply (indexed world store address pattern body frames pending) after ∧
      fullAfter.world = after.world ∧ Observation.observe fullAfter = Observation.observe after := by
  have source : (⟨world.fresh,
      (world.spaces address).map (branchAt world.scope store pattern body frames pending)⟩ : Config κ Γ star D.Ty) =
      DeadAlternatives.extend (indexed world store address pattern body frames pending)
        (discarded world store address pattern body frames pending) := by
    exact congrArg (Config.mk world.fresh) (partition world store address pattern body frames pending)
  rw [source] at run
  have dead := discarded_dead world store address pattern body frames pending
  obtain ⟨after, steps, same⟩ := DeadAlternatives.project_run _ _ dead run
  refine ⟨after, steps, ?_, ?_⟩
  · have worlds := congrArg (fun config : Config κ Γ star D.Ty => config.world) same
    exact worlds
  · rw [same]
    exact DeadAlternatives.observation after _ dead

#print axioms discarded_dead
#print axioms actual_move
#print axioms projected_future_run

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.QueryProjection
