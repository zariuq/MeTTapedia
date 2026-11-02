import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochPlanWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlSearchWireExecution

/-! O0 provider epochs share the emitted canonical commitment data.
Closed snapshots require no free-name footprint; constructor names and
declared laws depend only on the unchanged language.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochStandard

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

def names (prepared : Prepared) : List String := StandardWire.planTable (plan prepared) []
def standard (prepared : Prepared) : Term := StandardWire.commitTerm (plan prepared) .canonical (names prepared)

theorem epoch_declared (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot) :
    Complete.Footprint.Declared (epochPlan prepared table) [] := by
  intro name type found
  cases found

theorem epoch_table (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot) :
    StandardWire.TableFor (epochPlan prepared table) (names prepared) := by
  have declared : ∀ name type, (plan prepared).snapshot.free name = some type → name ∈ ([] : List String) := by
    intro name type found
    cases found
  exact StandardWire.planTable_for (epochPlan prepared table) (epoch_declared prepared table)

theorem epoch_standard (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot) :
    StandardWire.commitTerm (epochPlan prepared table) .canonical (names prepared) = standard prepared := rfl

theorem epoch_free_table (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot) :
    (epochPlan prepared table).snapshot.free.entriesOn [] = [] := rfl

theorem request_commit_ready (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot) (source : Pattern)
    (checked : Complete.Classes.Checked (epochPlan prepared table) [] (.base "MlConfig") source) :
    CompleteExecution.CommitReady .canonical (names prepared) source :=
  CompleteExecution.commitReady_of_checked (epochPlan prepared table) (epoch_table prepared table) checked

#print axioms epoch_table
#print axioms epoch_standard
#print axioms request_commit_ready

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEpochStandard
