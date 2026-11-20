import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericShapes

/-!
# Actual generic admission agrees across the read expansion

Direct admission derives both staged admissions. Conversely, the actual staged
freshness and retained-image laws derive direct freshness, and the final model
supplies direct solvability. Temporary allocation and access to the consumer
code are explicit licences; they are not made into language defaults.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings

open Interface (Frames)
open RuleOccurrences HeldReadGenericSources

universe uO uT uH uE uOcc uR
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {E : Extensions.{uO, uH, uE} Hom}
  (X : Frames Tm Hom) (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
  (closures : R → Closure Tm ordinary.frame) (selected : R) (extension : E.Ext ordinary.frame)
  (ruleOpening datumOpening : Hom (closures selected).schema.locals (E.target extension))
  [DecidableEq O] [DecidableEq R] (temporary output : O)

theorem direct_admission_data
    (admitted : (direct ordinary rows closures selected extension ruleOpening datumOpening output).Admits X) :
    (direct ordinary rows closures selected extension ruleOpening datumOpening output).Fresh X ∧
      (closures selected).WellFormed ∧ selected ∈ rows ∧ output ∉ ordinary.present ∧
      X.Solvable ((direct ordinary rows closures selected extension ruleOpening datumOpening output).information X) := by
  obtain ⟨shapes, enabled, solved, _⟩ := admitted
  obtain ⟨fresh, _, _, _, _, _, _, selectedWellFormed, _⟩ := shapes
  have wellFormed := selectedWellFormed
    ⟨Row.schematic (closures selected), RowUse.schematic (closures selected) datumOpening⟩
    (List.mem_singleton_self _)
  have present : Sum.inr selected ∈ (mixed ordinary rows closures).present :=
    enabled.kept_subset (List.mem_toFinset.mpr (List.mem_singleton_self _))
  have outputFresh : output ∉ ordinary.present := by
    intro old
    exact Finset.disjoint_left.mp enabled.fresh
      (List.mem_toFinset.mpr (List.mem_singleton_self _))
      ((ordinary_present ordinary rows closures output).mpr old)
  exact ⟨fresh, wellFormed, (schematic_present ordinary rows closures selected).mp present, outputFresh, solved⟩

theorem stages_of_direct_admitted (ambient : Set (HeldReadEncoding.Code Tm))
    (available : Sum.inr (consumeRule (closures selected).schema) ∈ ambient)
    (temporaryFresh : temporary ∉ ordinary.present) (different : temporary ≠ output)
    (admitted : (direct ordinary rows closures selected extension ruleOpening datumOpening output).Admits X) :
    (datum ordinary rows closures selected extension datumOpening temporary).Admits X ambient ∧
      (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Admits X ambient := by
  obtain ⟨fresh, wellFormed, present, outputFresh, target, point, solved⟩ :=
    direct_admission_data X ordinary rows closures selected extension ruleOpening datumOpening output admitted
  obtain ⟨datumFresh, consumerFresh⟩ := staged_fresh_of_direct X ordinary rows closures selected extension
    ruleOpening datumOpening temporary output ambient present fresh
  have whole : X.Models (a := E.target extension) (b := target) point
      (datumInformation ordinary closures selected extension datumOpening X ++
        [(X.act ruleOpening (closures selected).schema.value,
          X.act datumOpening (closures selected).schema.value)]) :=
    (direct_information ordinary rows closures selected extension ruleOpening datumOpening X output) ▸ solved
  have base : X.Models point (datumInformation ordinary closures selected extension datumOpening X) :=
    ((Frames.models_append (X := X) point _ _).mp whole).1
  have datumSolved : X.Models point
      ((datum ordinary rows closures selected extension datumOpening temporary).information X) :=
    (datum_information ordinary rows closures selected extension datumOpening X temporary).symm ▸ base
  have consumerSolved : X.Models point
      ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).information X) :=
    (information_eq X ordinary rows closures selected extension ruleOpening datumOpening temporary output).symm ▸ solved
  constructor
  · refine ⟨datum_shapes X ordinary rows closures selected extension datumOpening temporary ambient present datumFresh wellFormed,
      datum_enabled ordinary rows closures selected extension datumOpening temporary temporaryFresh,
      ⟨target, point, datumSolved⟩, ?_⟩
    intro later assignment _
    exact datum_holds X ordinary rows closures selected extension datumOpening temporary assignment
  · refine ⟨consumer_shapes X ordinary rows closures selected extension ruleOpening datumOpening temporary output ambient available consumerFresh,
      consumer_enabled X ordinary rows closures selected extension ruleOpening datumOpening temporary output outputFresh different,
      ⟨target, point, consumerSolved⟩, ?_⟩
    intro later assignment _
    exact consumer_holds X ordinary rows closures selected extension ruleOpening datumOpening temporary output assignment

theorem direct_of_stages_admitted (ambient : Set (HeldReadEncoding.Code Tm))
    (datumAdmitted : (datum ordinary rows closures selected extension datumOpening temporary).Admits X ambient)
    (consumerAdmitted : (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Admits X ambient) :
    (direct ordinary rows closures selected extension ruleOpening datumOpening output).Admits X := by
  have temporaryFresh : temporary ∉ ordinary.present := by
    intro old
    exact Finset.disjoint_left.mp datumAdmitted.2.1.fresh
      (List.mem_toFinset.mpr (List.mem_singleton_self _)) old
  have wellFormed : (closures selected).WellFormed := datumAdmitted.1.2.2.arguments
  have present : selected ∈ rows := datumAdmitted.1.2.2.available
  have outputFresh : output ∉ ordinary.present := by
    intro old
    exact Finset.disjoint_left.mp consumerAdmitted.2.1.fresh
      (List.mem_toFinset.mpr (List.mem_singleton_self _))
      ((datum_present X ordinary rows closures selected extension datumOpening temporary).symm ▸
        Finset.mem_union_left _ old)
  have fresh := direct_fresh_of_stages X ordinary rows closures selected extension ruleOpening datumOpening
    temporary output temporaryFresh wellFormed datumAdmitted.1.1 consumerAdmitted.1.1
  obtain ⟨target, point, solved⟩ := consumerAdmitted.2.2.1
  have directSolved : X.Models point
      ((direct ordinary rows closures selected extension ruleOpening datumOpening output).information X) :=
    (information_eq X ordinary rows closures selected extension ruleOpening datumOpening temporary output) ▸ solved
  refine ⟨direct_shapes X ordinary rows closures selected extension ruleOpening datumOpening output fresh wellFormed,
    direct_enabled ordinary rows closures selected extension ruleOpening datumOpening output present outputFresh,
    ⟨target, point, directSolved⟩, ?_⟩
  intro later assignment _
  exact direct_holds X ordinary rows closures selected extension ruleOpening datumOpening output assignment

theorem admission_iff (ambient : Set (HeldReadEncoding.Code Tm))
    (available : Sum.inr (consumeRule (closures selected).schema) ∈ ambient)
    (temporaryFresh : temporary ∉ ordinary.present) (different : temporary ≠ output) :
    (direct ordinary rows closures selected extension ruleOpening datumOpening output).Admits X ↔
      (datum ordinary rows closures selected extension datumOpening temporary).Admits X ambient ∧
        (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Admits X ambient :=
  ⟨stages_of_direct_admitted X ordinary rows closures selected extension ruleOpening datumOpening temporary output
      ambient available temporaryFresh different,
    fun stages => direct_of_stages_admitted X ordinary rows closures selected extension ruleOpening datumOpening
      temporary output ambient stages.1 stages.2⟩

#print axioms direct_admission_data
#print axioms stages_of_direct_admitted
#print axioms direct_of_stages_admitted
#print axioms admission_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings
