import Mettapedia.GSLT.Parsing.ClassAwareChartDemandExecution

/-! Independent whole-input coverage of an exactly decoded native forest.
None means unfinished chart construction; false means the supplied forest
does not pass the representation or coverage checks. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareChartCoverage

open ClassAwarePackedForest ClassAwareGroundedChart ClassAwareChartClosure
open ClassAwareNativeForestContract ClassAwareNativeForestIdentityWire
open ClassAwareNativeForestIdentityInventory ClassAwareNativeForestFamilyWitness
open ClassAwareNativeForestFamilyCompleteness ClassAwareNativeForestQualification
open ClassAwareNativeForestParserCompleteness ClassAwareParserPackCorrespondence ParserProfileSemantics

def coverage? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (backend : Forest) (rounds : Nat) : Option Bool :=
  (ClassAwareChartDemand.reference? profile plan input rounds).map fun reference => validateForestCovers reference backend

theorem coverage?_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {backend : Forest} {rounds : Nat}
    (accepted : coverage? profile plan input backend rounds = some true) :
    RootParserComplete backend profile plan input := by
  obtain ⟨reference, finished, covered⟩ := Option.map_eq_some_iff.mp accepted
  exact rootParserComplete_of_covers (validateForestCovers_sound covered) (ClassAwareChartDemand.reference?_complete finished)

def validate? (snapshot : Snapshot) (view : ForestView)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (rounds : Nat) : Option Bool := do
  match snapshot.resolveInventory? plan with
  | none => some false
  | some inventory =>
    if validateExactFamilyRepresentation view inventory profile plan then
      coverage? profile plan view.codepoints (decodedForestData view inventory profile) rounds
    else some false

theorem validate?_sound {snapshot : Snapshot} {view : ForestView}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan} {rounds : Nat}
    (accepted : validate? snapshot view profile plan rounds = some true) :
    ∃ inventory : Inventory, snapshot.resolveInventory? plan = some inventory ∧
      ∃ inputs : RootedFamilyDecodingInputs view inventory profile plan,
        ParserCompleteRepresentation view inventory profile plan
          (decodedForest inputs.families (enumerateFamilyWitnesses view)) := by
  unfold validate? at accepted
  cases resolved : snapshot.resolveInventory? plan with
  | none => simp [resolved] at accepted
  | some inventory =>
    simp only [resolved] at accepted
    split at accepted
    · rename_i valid
      obtain ⟨inputs, represents⟩ := validateExactFamilyRepresentation_sound valid
      have complete := coverage?_complete accepted
      rw [← decodedForest_eq_data inputs.families] at complete
      exact ⟨inventory, rfl, inputs, ⟨represents, complete⟩⟩
    · cases accepted

end Mettapedia.GSLT.Parsing.ClassAwareChartCoverage
