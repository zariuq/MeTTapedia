import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedInventory

/-!
# Real selected firings compose under the original resource contract

The ordered condition says that the first event does not destroy an input
of the second or claim its fresh output. It permits a read followed by a
take; its reverse need not hold. Symmetric independence is exactly the
existing occurrence-commit discipline, with read aliases retained in lists.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion ContextualScopeSupport
open ContextualSelectedNormalization ContextualExecutionCommutationNames
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  [DecidableEq O] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
  {Γ : Ctx S} {sort : S.Srt} {before : Endpoint locals O Γ sort}

namespace Interaction

def CanFollow (first second : Interaction before) : Prop :=
  ¬ Clash (second.selection.commit (T := Unit)) first.selection.commit ∧
    ¬ Spoils (fun _ : O => ()) first.selection.commit second.selection.commit

def Independent (first second : Interaction before) : Prop :=
  MeTTaCalculus.OccurrenceCommits.Independent (fun _ : O => ()) first.selection.commit second.selection.commit

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem Independent.orders {first second : Interaction before} (apart : first.Independent second) :
    first.CanFollow second ∧ second.CanFollow first :=
  ⟨⟨fun clash => apart.1 clash.symm, apart.2.1⟩, ⟨apart.1, apart.2.2⟩⟩

omit [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem independent_iff_disjoint (first second : Interaction before) :
    first.Independent second ↔
      Disjoint first.taken.toFinset second.taken.toFinset ∧
      Disjoint first.made.toFinset second.made.toFinset ∧
      Disjoint first.taken.toFinset second.read.toFinset ∧
      Disjoint second.taken.toFinset first.read.toFinset := by
  simp [Independent, MeTTaCalculus.OccurrenceCommits.Independent, Clash, Spoils, WritesInto,
    Selection.commit, selection, and_assoc]

def after (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (survives : first.CanFollow second) : Interaction (first.target prior incoming) := by
  have resource := (enabled_fire_iff second.physical first.physical).mpr survives
  refine
    { made := second.made
      distinct := second.distinct
      fresh := ?_
      value := fun occurrence => instantiate (ContextualStoredRows.liftCaptures locals (intoCapture locals before.declarations))
        (second.value occurrence)
      covered := ?_
      taken := second.taken
      read := second.read
      take_distinct := second.take_distinct
      take_available := ?_
      read_available := ?_
      take_read_apart := second.take_read_apart
      label := second.label
      template := ?_ }
  · rw [first.target_world prior incoming]
    exact resource.fresh
  · intro occurrence member
    exact (covered_instantiate_of_respects _ _ _ _
      (respects_liftCaptures locals before.scopes (first.target prior incoming).scopes
        (intoCapture locals before.declarations) (first.captures_keep_scopes prior incoming))
      (second.covered occurrence member)).mono (first.target_retains_ledger prior incoming)
  · rw [first.target_world prior incoming]
    exact resource.taken_subset
  · rw [first.target_world prior incoming]
    exact resource.kept_subset
  · intro occurrence selected
    have present : occurrence ∈ before.inventory.configuration.present := by
      rcases List.mem_append.mp selected with taken | read
      · exact second.take_available (by simpa using taken)
      · exact second.read_available (by simpa using read)
    have notMade : occurrence ∉ first.made := by
      intro member
      exact Finset.disjoint_left.mp first.fresh (by simpa using member) present
    rw [first.target_rows prior incoming, if_neg notMade, ContextualStoredRows.asTemplate_map,
      second.template occurrence selected]
    exact Rigid.instantiate_include _ _

def twoTarget (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (survives : first.CanFollow second) : Endpoint locals O Γ sort :=
  (first.after second prior incoming survives).target (first.terms prior) (first.target_equations prior incoming)

def twoPath (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (survives : first.CanFollow second) : Quiver.Path before (first.twoTarget second prior incoming survives) :=
  (Quiver.Hom.toPath (first.firing prior incoming)).comp
    (Quiver.Hom.toPath ((first.after second prior incoming survives).firing (first.terms prior)
      (first.target_equations prior incoming)))

theorem actual_selected_path (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (survives : first.CanFollow second) :
    ContextualExecution.selections (first.twoPath second prior incoming survives) = [first.selection, second.selection] ∧
      ContextualExecution.fuels (first.twoPath second prior incoming survives) = [1, 1] := by
  constructor <;> rfl

theorem actual_both_orders (first second : Interaction before) (prior : List (Term S Γ sort))
    (incoming : before.inventory.configuration.equations = diagonals before.declarations prior)
    (apart : first.Independent second) :
    Nonempty (Quiver.Path before (first.twoTarget second prior incoming apart.orders.1)) ∧
      Nonempty (Quiver.Path before (second.twoTarget first prior incoming apart.orders.2)) :=
  ⟨⟨first.twoPath second prior incoming apart.orders.1⟩, ⟨second.twoPath first prior incoming apart.orders.2⟩⟩

end Interaction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectedExecution
