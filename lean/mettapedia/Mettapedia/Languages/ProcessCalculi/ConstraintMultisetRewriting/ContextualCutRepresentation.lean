import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRegression
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleMetadata

/-!
# Guard cuts represented by a different conditional row inventory

The information problem and checks stay at their original cut. Only the
row representation and physical names change. Conditional matching plus
an injective inventory image preserves equality, absence and exact counts.
The construction and proof are independent of the source clause kind.
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
