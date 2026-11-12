import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceFootprints
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceControls

/-! # Shared reads, asymmetric consumption and freshness controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.FootprintControls

open MeTTaCalculus.OccurrenceCommits (Enabled fire)

def reader : Selection Nat := ⟨[], [0], []⟩
def taker : Selection Nat := ⟨[0], [], [1]⟩
def maker : Selection Nat := ⟨[], [], [1]⟩

abbrev Active (selection : Selection Nat) (store : Finset Nat) :=
  Enabled (fun _ : Nat => ()) store (selection.commit (T := Unit))

theorem read_read_sharing :
    Active reader {0} ∧ Active reader ({0} ∪ {0}) ∧
      fire ({0} ∪ {0}) (reader.commit (T := Unit)) =
        fire {0} (reader.commit (T := Unit)) ∪ {0} := by decide

theorem taking_shared_cell_changes_context :
    Active taker {0} ∧ Active taker ({0} ∪ {0}) ∧
      fire ({0} ∪ {0}) (taker.commit (T := Unit)) ≠
        fire {0} (taker.commit (T := Unit)) ∪ {0} := by decide

theorem context_freshness_is_needed :
    Active maker {0} ∧ ¬Active maker ({0} ∪ {1}) := by decide

theorem read_take_order_is_asymmetric :
    Active reader {0} ∧ Active taker (fire {0} (reader.commit (T := Unit))) ∧
      Active taker {0} ∧ ¬Active reader (fire {0} (taker.commit (T := Unit))) := by decide

theorem native_shared_read_prepares :
    Enabled (fun _ : Nat => ()) (Controls.singleCell.present 0 ∪ {0})
      ((Controls.singleCell.selection (s := 0) ()).commit (T := Unit)) := by
  apply (EffectCore.prepared_context_enabled_iff Controls.singleCell ()
    (Controls.singleCell_prepares 0) {0}).mpr
  simp [Controls.singleCell]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Coexistence.FootprintControls
