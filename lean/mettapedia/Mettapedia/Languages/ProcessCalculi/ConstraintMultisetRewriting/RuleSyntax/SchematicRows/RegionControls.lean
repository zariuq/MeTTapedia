import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Regions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.QuantifierControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketQueryControls

/-!
# A schematic region cannot be replaced by one equivalence class

At one fixed caller model the schematic datum admits both five and six. The
shared datum admits five but not six. The existing equivalence-rectangle law
therefore rules out every encoding with one value per pattern and per row,
irrespective of the encoded carrier or its chosen equivalence relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.RegionControls

open Mettapedia.Logic.LP
open QuantifierControls

universe uV

theorem no_equivalence_pattern_membership {V : Type uV} (E : V → V → Prop) (laws : Equivalence E)
    (encodePattern : Term RuleSyntax.Controls.atoms → V)
    (encodeRow : Row Tm PUnit.unit → V)
    (faithful : ∀ pattern row, E (encodePattern pattern) (encodeRow row) ↔
      Row.ReadsAt X (b := PUnit.unit) (point 5) pattern row) : False := by
  have firstFirst := (faithful (c 5) schematic).mpr (schematic_reads _ _)
  have firstSecond := (faithful (c 5) shared).mpr shared_reads_first
  have secondFirst := (faithful (c 6) schematic).mpr (schematic_reads _ _)
  exact shared_refuses_second ((faithful (c 6) shared).mp
    (Interface.Bridges.Concurrency.NativePacketQueryControls.Schema.equivalence_rectangle
      E laws firstFirst firstSecond secondFirst))

theorem regions_preserve_the_overlap :
    Regions.membership X (c 5) (b := PUnit.unit) (point 5) schematic = true ∧
      Regions.membership X (c 6) (b := PUnit.unit) (point 5) schematic = true ∧
      Regions.membership X (c 5) (b := PUnit.unit) (point 5) shared = true ∧
      ¬ Regions.membership X (c 6) (b := PUnit.unit) (point 5) shared = true := by
  refine ⟨(Regions.membership_iff X _ _ _).mpr (schematic_reads _ _),
    (Regions.membership_iff X _ _ _).mpr (schematic_reads _ _),
    (Regions.membership_iff X _ _ _).mpr shared_reads_first, ?_⟩
  intro accepted
  exact shared_refuses_second ((Regions.membership_iff X _ _ _).mp accepted)

#print axioms no_equivalence_pattern_membership
#print axioms regions_preserve_the_overlap

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.RegionControls
