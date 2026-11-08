import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRegression
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleMetadata
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationRenaming

/-!
# Guard cuts represented by a different conditional row inventory

The information problem and checks stay at their original cut. Only the
row representation and physical names change. Conditional matching plus
an injective inventory image preserves equality, absence and exact counts.
The construction and proof are independent of the source clause kind.
An entry cut records such a representation over allocation names together
with the prefix resource delta that produced it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Cut

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalGuards

variable {S : Signature} {O Physical Shared Private Next : Type}
    [DecidableEq O] [DecidableEq Physical]
    {captures : Shared → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}

def represent (cut : Cut captures O Γ sort) (locals : Private → MetaArity S)
    (rows : Physical → Row locals captures Γ sort) (world : Finset Physical) : Cut captures Physical Γ sort :=
  ⟨Private, locals, cut.problem, rows, world, cut.checks⟩

omit [DecidableEq O] in
theorem represent_iff (cut : Cut captures O Γ sort) (locals : Private → MetaArity S)
    (rows : Physical → Row locals captures Γ sort) (world : Finset Physical)
    (name : O → Physical) (injective : Function.Injective name) (inventory : world = cut.world.image name)
    (agree : ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment captures future)
      (pattern : Term (signature S future) Γ sort) (occurrence : O), occurrence ∈ cut.world →
        (Matches cut.locals captures candidate pattern (cut.rows occurrence) ↔
          Matches locals captures candidate pattern (rows (name occurrence)))) :
    (cut.represent locals rows world).Holds ↔ cut.Holds := by
  simp only [Holds, represent]
  apply forall_congr'
  intro check
  apply forall_congr'
  intro _member
  constructor <;> intro asked Future future candidate model
  · have compared := ContextualGuardRegression.holds_image_of_matches cut.locals locals name injective candidate
      cut.rows rows cut.world (fun pattern occurrence inside => agree Future future candidate
        (instantiate candidate pattern) occurrence inside) check
    rw [← inventory] at compared
    exact compared.mp (asked Future future candidate model)
  · have compared := ContextualGuardRegression.holds_image_of_matches cut.locals locals name injective candidate
      cut.rows rows cut.world (fun pattern occurrence inside => agree Future future candidate
        (instantiate candidate pattern) occurrence inside) check
    rw [← inventory] at compared
    exact compared.mpr (asked Future future candidate model)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Cut

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows

variable {S : Signature} {O V Later : Type}
    {declaration : V → MetaArity S} {later : Later → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

structure EntryCut (declaration : V → MetaArity S) (O : Type) (context : Ctx S) (sort : S.Srt) : Type 1 where
  view : Cut declaration (OccurrenceAllocationRenaming.Name O) context sort
  taken : Finset (OccurrenceAllocationRenaming.Name O)
  made : Finset (OccurrenceAllocationRenaming.Name O)

def EntryCut.map (change : Assignment declaration later) (cut : EntryCut declaration O Γ sort) : EntryCut later O Γ sort :=
  ⟨cut.view.map change, cut.taken, cut.made⟩

def EntryCut.Holds (cut : EntryCut declaration O Γ sort) : Prop := cut.view.Holds

theorem EntryCut.extension_iff (cut : EntryCut declaration O Γ sort)
    (extension : ContextualGuardMatching.Extension declaration) :
    (cut.map extension.assignment).Holds ↔ cut.Holds := cut.view.extension_iff extension

theorem EntryCut.comparison_map (entry : EntryCut declaration O Γ sort) (source : Cut declaration O Γ sort)
    (extension : ContextualGuardMatching.Extension declaration)
    (compared : entry.view.problem = source.problem ∧ entry.view.checks = source.checks ∧
      (entry.Holds ↔ source.Holds)) :
    (entry.map extension.assignment).view.problem = (source.map extension.assignment).problem ∧
      (entry.map extension.assignment).view.checks = (source.map extension.assignment).checks ∧
      ((entry.map extension.assignment).Holds ↔ (source.map extension.assignment).Holds) := by
  refine ⟨congrArg (ContextualResidual.mapProblem extension.assignment) compared.1,
    congrArg (List.map (Check.map (instantiate extension.assignment))) compared.2.1, ?_⟩
  exact ((entry.extension_iff extension).trans compared.2.2).trans (source.extension_iff extension).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules
