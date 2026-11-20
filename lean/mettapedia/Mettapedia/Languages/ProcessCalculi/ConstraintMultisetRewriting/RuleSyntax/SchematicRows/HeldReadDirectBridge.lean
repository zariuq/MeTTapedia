import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadEncoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDirectModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadProtocol

/-!
# Direct and held executions have the same projected read results

The direct candidate is a real schematic-row firing constructed independently
of the held protocol. Their observable result-model families agree over the
whole original source interface. The resource comparison uses the ordinary/
held partition, not payload deduplication. This is an isolated fixed-occurrence
comparison; neither arbitrary interleavings nor raw histories are quotiented.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDirectBridge

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationMachine (RowTerms Store X E sourceBound)
open RuleOccurrences

universe uOcc
variable {O : Type uOcc} [DecidableEq O]

abbrev HostCode := HeldReadEncoding.Code RowTerms
abbrev host (s : Store O) (filler : Tm) := HeldReadEncoding.encode s filler
abbrev codeBook : Codes RowTerms HostCode Unit := HeldReadEncoding.codes
def reader : HostCode := .inr HeldCopyConsumer.readerRule
def ambient : Set HostCode := {reader}

def directResults (s : Store O) (caller : Subst rowSig) (selected made : O) : Set Tm :=
  {value | ∃ _admitted : (HeldReadDirect.candidate (sourceBound s) s selected made).Admits X,
    ∃ point : Subst rowSig,
      X.Models (a := s.frame) (b := PUnit.unit) point
        ((HeldReadDirect.candidate (sourceBound s) s selected made).result X).knowledge ∧
      (∀ term, s.scope.Mentions term → point.applyTerm term = caller.applyTerm term) ∧
      (((HeldReadDirect.candidate (sourceBound s) s selected made).result X).label made).ReadsAt X
        (b := PUnit.unit) point value}

def heldResults (s : Store O) (filler : Tm) (caller : Subst rowSig)
    (selected temporary made : O) : Set Tm :=
  {value | ∃ (materialized : (HeldReadMaterializer.materializer codeBook (host s filler) selected temporary).Admits X ambient)
    (consumed : (HeldCopyConsumer.consumer codeBook
      ((HeldReadMaterializer.materializer codeBook (host s filler) selected temporary).result X)
      reader temporary made).Admits X ambient) (point : Subst rowSig),
    X.Models (a := s.frame) (b := PUnit.unit) point
      (HeldReadProtocol.execution codeBook ambient (host s filler) selected temporary made
        reader materialized consumed).last.knowledge ∧
    (∀ term, s.scope.Mentions term → point.applyTerm term = caller.applyTerm term) ∧
    point.applyTerm
      ((HeldReadProtocol.execution codeBook ambient (host s filler) selected temporary made
        reader materialized consumed).last.label made) = value}

theorem direct_iff_reading (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge)
    (selected made : O) (present : selected ∈ s.present) (fresh : made ∉ s.present) (value : Tm) :
    value ∈ directResults s caller selected made ↔
      (s.label selected).ReadsAt X (b := PUnit.unit) caller value :=
  (HeldReadDirect.reading_iff_actual_result s caller known selected made present fresh value).symm

theorem held_iff_reading (s : Store O) (filler : Tm) (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge)
    (selected temporary made : O) (datum : Closure RowTerms s.frame)
    (labelled : s.label selected = .schematic datum) (wellFormed : datum.WellFormed)
    (present : selected ∈ s.present) (temporaryFresh : temporary ∉ s.present)
    (madeFresh : made ∉ s.present) (different : made ≠ temporary) (value : Tm) :
    value ∈ heldResults s filler caller selected temporary made ↔
      datum.ReadsAt X (b := PUnit.unit) caller value := by
  have arguments := HeldReadEncoding.schema_arguments s filler selected datum labelled
  have declared := HeldReadEncoding.schema_unfold s filler selected datum labelled
  have heldPresent := HeldReadEncoding.schematic_available s filler selected datum labelled present
  have persistent := HeldReadEncoding.schema_persistent s filler selected
  have lengths : datum.schema.params.length = ((host s filler).held selected).args.length := by
    rw [arguments]
    exact wellFormed
  have tempNotPresent : temporary ∉ (host s filler).present := fun inside =>
    temporaryFresh ((HeldReadEncoding.present_iff s filler temporary).mp inside).1
  have madeNotPresent : made ∉ (host s filler).present := fun inside =>
    madeFresh ((HeldReadEncoding.present_iff s filler made).mp inside).1
  have law := HeldReadProtocol.reading_iff_execution codeBook ambient (host s filler)
    selected temporary made reader datum.schema declared rfl (Set.mem_singleton reader)
    heldPresent persistent lengths tempNotPresent madeNotPresent different caller known value
  have sameClosure :
      (⟨datum.schema, ((host s filler).held selected).args⟩ : Closure RowTerms s.frame) = datum := by
    rw [arguments]
  constructor
  · rintro ⟨materialized, consumed, point, solved, agrees, output⟩
    have reading := law.mpr ⟨materialized, consumed, point, solved,
      fun term mentioned => agrees term ((HeldReadEncoding.scope_mentions_iff s filler term).mp mentioned), output⟩
    rwa [sameClosure] at reading
  · intro reading
    have represented :
        (⟨datum.schema, ((host s filler).held selected).args⟩ : Closure RowTerms s.frame).ReadsAt X
          (b := PUnit.unit) caller value := by
      rw [sameClosure]
      exact reading
    obtain ⟨materialized, consumed, point, solved, agrees, output⟩ := law.mp represented
    exact ⟨materialized, consumed, point, solved,
      fun term mentioned => agrees term ((HeldReadEncoding.scope_mentions_iff s filler term).mpr mentioned), output⟩

theorem results_equal (s : Store O) (filler : Tm) (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge)
    (selected temporary made : O) (datum : Closure RowTerms s.frame)
    (labelled : s.label selected = .schematic datum) (wellFormed : datum.WellFormed)
    (present : selected ∈ s.present) (temporaryFresh : temporary ∉ s.present)
    (madeFresh : made ∉ s.present) (different : made ≠ temporary) :
    directResults s caller selected made = heldResults s filler caller selected temporary made := by
  ext value
  have direct := direct_iff_reading s caller known selected made present madeFresh value
  have held := held_iff_reading s filler caller known selected temporary made datum labelled
    wellFormed present temporaryFresh madeFresh different value
  rw [labelled] at direct
  exact direct.trans held.symm

theorem held_final_resources (s : Store O) (filler : Tm) (selected temporary made : O)
    (temporaryFresh : temporary ∉ s.present)
    (materialized : (HeldReadMaterializer.materializer codeBook (host s filler) selected temporary).Admits X ambient)
    (consumed : (HeldCopyConsumer.consumer codeBook
      ((HeldReadMaterializer.materializer codeBook (host s filler) selected temporary).result X)
      reader temporary made).Admits X ambient) :
    (HeldReadProtocol.execution codeBook ambient (host s filler) selected temporary made
      reader materialized consumed).last.present ∪
        (HeldReadProtocol.execution codeBook ambient (host s filler) selected temporary made
          reader materialized consumed).last.rules = s.present ∪ {made} := by
  have tempNotPresent : temporary ∉ (host s filler).present := fun inside =>
    temporaryFresh ((HeldReadEncoding.present_iff s filler temporary).mp inside).1
  rw [HeldReadProtocol.final_present _ _ _ _ _ _ _ _ _ tempNotPresent,
    HeldReadProtocol.final_rules _ _ _ _ _ _ _ _ _ (HeldReadEncoding.schema_persistent s filler selected)]
  calc
    ((host s filler).present ∪ {made}) ∪ (host s filler).rules =
        ((host s filler).present ∪ (host s filler).rules) ∪ {made} := by
      ext occurrence
      simp only [Finset.mem_union, Finset.mem_singleton]
      tauto
    _ = s.present ∪ {made} := congrArg (fun resources => resources ∪ {made})
      (HeldReadEncoding.resource_partition s filler).1

#print axioms results_equal
#print axioms held_final_resources

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDirectBridge
