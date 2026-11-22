import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericExtensions

/-!
# The generic read expansion is an actual two-firing dependent run

The datum uses the original extension branch. Its consumer uses the explicit
internal identity branch. Every final model and output reading agrees with
the independently constructed direct candidate. The run keeps source schema
identities, removes its temporary, and still has two chronological events.

This is an isolated protocol law. Private access and protected contextual
composition are separate from freshness and endpoint agreement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings

open Interface (Frames)
open RuleOccurrences HeldReadGenericSources
open HeldReadExtensionSum

universe uO uT uH uE uOcc uR
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {E : Extensions.{uO, uH, uE} Hom}
  (X : Frames Tm Hom) [DecidableEq O] [DecidableEq R]

abbrev protocolMachine (ambient : Set (HeldReadEncoding.Code Tm)) :=
  (rstep X O R (withIdentity X E) HeldReadEncoding.codes ambient).toStep

variable (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
  (closures : R → Closure Tm ordinary.frame) (selected : R) (extension : E.Ext ordinary.frame)
  (ruleOpening datumOpening : Hom (closures selected).schema.locals (E.target extension))
  (temporary output : O) (ambient : Set (HeldReadEncoding.Code Tm))

noncomputable def execution
    (datumAdmitted : (datum ordinary rows closures selected extension datumOpening temporary).Admits X ambient)
    (consumerAdmitted : (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Admits X ambient) :
    (protocolMachine (E := E) (O := O) (R := R) X ambient).Run (hosted ordinary rows closures) :=
  .cons (liftHeld X E (datum ordinary rows closures selected extension datumOpening temporary))
    ((liftHeld_admission_iff X E ambient _).mpr datumAdmitted)
    (.cons (liftInternal X E
      (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output))
      ((liftInternal_admission_iff X E ambient _).mpr consumerAdmitted) (.nil _))

theorem execution_last
    (datumAdmitted : (datum ordinary rows closures selected extension datumOpening temporary).Admits X ambient)
    (consumerAdmitted : (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Admits X ambient) :
    (execution X ordinary rows closures selected extension ruleOpening datumOpening temporary output ambient datumAdmitted consumerAdmitted).last =
      (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X := rfl

theorem execution_length
    (datumAdmitted : (datum ordinary rows closures selected extension datumOpening temporary).Admits X ambient)
    (consumerAdmitted : (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Admits X ambient) :
    (execution X ordinary rows closures selected extension ruleOpening datumOpening temporary output ambient datumAdmitted consumerAdmitted).word.length = 2 := rfl

theorem execution_models_iff
    (datumAdmitted : (datum ordinary rows closures selected extension datumOpening temporary).Admits X ambient)
    (consumerAdmitted : (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Admits X ambient)
    {b : Obj} (point : Hom (E.target extension) b) :
    X.Models point
        (execution X ordinary rows closures selected extension ruleOpening datumOpening temporary output ambient datumAdmitted consumerAdmitted).last.knowledge ↔
      X.Models point ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).knowledge :=
  result_models_iff X ordinary rows closures selected extension ruleOpening datumOpening temporary output point

theorem execution_output_iff
    (datumAdmitted : (datum ordinary rows closures selected extension datumOpening temporary).Admits X ambient)
    (consumerAdmitted : (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Admits X ambient)
    {b : Obj} (point : Hom (E.target extension) b) (value : Tm b) :
    (((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).label (.inl output)).ReadsAt X point value ↔
      X.E (X.act point
        ((execution X ordinary rows closures selected extension ruleOpening datumOpening temporary output ambient datumAdmitted consumerAdmitted).last.label output)) value :=
  output_reading_iff X ordinary rows closures selected extension ruleOpening datumOpening temporary output point value

theorem execution_preserves_source_action
    (datumAdmitted : (datum ordinary rows closures selected extension datumOpening temporary).Admits X ambient)
    (consumerAdmitted : (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).Admits X ambient)
    (term : Tm ordinary.frame) :
    X.act (execution X ordinary rows closures selected extension ruleOpening datumOpening temporary output ambient datumAdmitted consumerAdmitted).toLast term =
      X.act (E.weaken extension) term := by
  change X.act
    (X.comp (X.comp (X.id (E.target extension)) (X.comp (X.id (E.target extension)) (X.id (E.target extension))))
      (X.comp (X.id (E.target extension)) (E.weaken extension))) term = _
  simp only [X.act_comp, X.act_id]

theorem execution_of_direct
    (available : Sum.inr (consumeRule (closures selected).schema) ∈ ambient)
    (temporaryFresh : temporary ∉ ordinary.present) (different : temporary ≠ output)
    (admitted : (direct ordinary rows closures selected extension ruleOpening datumOpening output).Admits X) :
    ∃ run : (protocolMachine (E := E) (O := O) (R := R) X ambient).Run (hosted ordinary rows closures),
      run.word.length = 2 ∧
      run.last = (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X ∧
      run.last.present = ordinary.present ∪ {output} ∧ run.last.rules = rows ∧ temporary ∉ run.last.present := by
  obtain ⟨first, second⟩ := stages_of_direct_admitted X ordinary rows closures selected extension
    ruleOpening datumOpening temporary output ambient available temporaryFresh different admitted
  refine ⟨execution X ordinary rows closures selected extension ruleOpening datumOpening temporary output ambient first second,
    rfl, rfl, ?_, ?_, ?_⟩
  · exact consumer_present X ordinary rows closures selected extension ruleOpening datumOpening temporary output temporaryFresh
  · exact consumer_rules X ordinary rows closures selected extension ruleOpening datumOpening temporary output
  · exact private_absent X ordinary rows closures selected extension ruleOpening datumOpening temporary output different

#print axioms execution_length
#print axioms execution_models_iff
#print axioms execution_output_iff
#print axioms execution_preserves_source_action
#print axioms execution_of_direct

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings
