import Mettapedia.TypeTheory.ContextualLocalUniversesDecoding
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum

/-!
# Local presentation and substitution controls

Two different parameter spaces describe the same genuinely varying family.
Decoding retains its supplied section and actual contextual pairing. A
nonidentity substitution changes the name and the section readout. Erasing
that name changes the fibre and loses the original contextual type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualLocalUniversesControls

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualLocalUniverses

abbrev model := familiesCwfWithTerminal.{0}
abbrev core := model.toCwf

def sizes (point : Bool) : Nat := if point then 2 else 1

def first : LocalType core Bool := ⟨Bool, (fun point => Fin (sizes point)), id⟩

def second : LocalType core Bool :=
  ⟨Bool × Bool, (fun point => Fin (sizes point.1)), (fun point => (point, false))⟩

theorem decoded_families_agree : first.decoded = second.decoded := rfl

/-- Presentation data is not identified merely because its decoded family
agrees. The two finite parameter spaces have different cardinalities. -/
theorem presentations_differ : first ≠ second := by
  intro same
  have spaces : Bool = (Bool × Bool) := congrArg LocalType.parameters same
  have cards := congrArg Nat.card spaces
  norm_num [Nat.card_eq_fintype_card] at cards

def suppliedSection : Term core Bool first := by
  change ∀ point : Bool, Fin (sizes point)
  intro point
  cases point with
  | false => exact ⟨0, by decide⟩
  | true => exact ⟨1, by decide⟩

theorem section_true : (suppliedSection true).val = 1 := rfl
theorem section_false : (suppliedSection false).val = 0 := rfl

theorem decode_section : (familyDecoder core).mapTerm suppliedSection = suppliedSection :=
  familyDecoder_term core suppliedSection

def exchange : core.Sub Bool Bool := Bool.not

theorem reindexed_name_true : (first.reindex exchange).name true = false := rfl
theorem reindexed_name_false : (first.reindex exchange).name false = true := rfl

theorem reindex_preserves_parameter_family :
    (first.reindex exchange).parameters = first.parameters ∧
      HEq (first.reindex exchange).family first.family := ⟨rfl, HEq.rfl⟩

theorem substituted_section_true : (substituteTerm suppliedSection exchange true).val = 0 := rfl
theorem substituted_section_false : (substituteTerm suppliedSection exchange false).val = 1 := rfl

/-- The comprehension witness is the actually supplied changing section. -/
def extendedPoint : core.Sub Bool (extension Bool first) :=
  pairing (core.idS Bool) first
    (cast (congrArg (Term core Bool) first.reindex_id.symm) suppliedSection)

theorem pairing_reads_supplied_section (point : Bool) :
    (extendedPoint point).2 = suppliedSection point := rfl

theorem pairing_projects_to_supplied_base :
    core.compS (projection first) extendedPoint = core.idS Bool :=
  projection_pairing _ _ _

def erasedName : LocalType core Bool :=
  ⟨first.parameters, first.family, (fun _ => false)⟩

/-- The forgotten name changes the true fibre from two values to one. -/
theorem erased_name_changes_type : erasedName.decoded ≠ first.decoded := by
  intro same
  have fibres := congrFun same true
  have cards := congrArg Nat.card fibres
  change Nat.card (Fin 1) = Nat.card (Fin 2) at cards
  norm_num [Nat.card_eq_fintype_card] at cards

end Mettapedia.TypeTheory.ContextualLocalUniversesControls
