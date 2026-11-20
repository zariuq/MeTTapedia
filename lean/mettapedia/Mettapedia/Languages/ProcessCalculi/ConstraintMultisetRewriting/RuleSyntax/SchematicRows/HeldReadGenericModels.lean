import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFresh

/-!
# Actual direct and two-stage results carry the same information

The materialized label and the consumer's matching equation are computed from
their real result fields. The final information is exactly the direct read's
information, and both output readings agree at each common model. No solver,
value-variable object or adequacy assumption is introduced.
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

theorem datum_label :
    ((datum ordinary rows closures selected extension datumOpening temporary).result X).label temporary =
      X.act datumOpening (closures selected).schema.value :=
  Materialization.result_label_single X
    (datum ordinary rows closures selected extension datumOpening temporary)
    temporary (closures selected).schema.value rfl rfl

theorem consumer_information :
    (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).information X =
      datumInformation ordinary closures selected extension datumOpening X ++
        [(X.act ruleOpening (closures selected).schema.value,
          X.act datumOpening (closures selected).schema.value)] := by
  let sourceInformation : EquationStore (Tm (E.target extension)) :=
    (datum ordinary rows closures selected extension datumOpening temporary).information X
  let materializedValue : Tm (E.target extension) :=
    ((datum ordinary rows closures selected extension datumOpening temporary).result X).label temporary
  have normalize (knowledge : EquationStore (Tm (E.target extension))) (value : Tm (E.target extension)) :
      (((X.applyStore (X.id (E.target extension)) knowledge ++
          [(X.act ruleOpening (closures selected).schema.value, X.act (X.id (E.target extension)) value)]) ++
          []) ++ []) ++ [] = knowledge ++ [(X.act ruleOpening (closures selected).schema.value, value)] := by
    simp only [Frames.applyStore_id, X.act_id, List.append_nil]
  have actual :
      (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).information X =
        sourceInformation ++ [(X.act ruleOpening (closures selected).schema.value, materializedValue)] :=
    normalize sourceInformation materializedValue
  have known : sourceInformation = datumInformation ordinary closures selected extension datumOpening X :=
    datum_information ordinary rows closures selected extension datumOpening X temporary
  have labelled : materializedValue = X.act datumOpening (closures selected).schema.value :=
    datum_label X ordinary rows closures selected extension datumOpening temporary
  exact actual.trans (congrArg₂
    (fun knowledge value => knowledge ++ [(X.act ruleOpening (closures selected).schema.value, value)]) known labelled)

theorem information_eq :
    (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).information X =
      (direct ordinary rows closures selected extension ruleOpening datumOpening output).information X := by
  rw [consumer_information, direct_information]

theorem result_models_iff {b : Obj} (point : Hom (E.target extension) b) :
    X.Models point
        ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).knowledge ↔
      X.Models point
        ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).knowledge := by
  change X.Models point
      ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).information X) ↔
    X.Models point ((direct ordinary rows closures selected extension ruleOpening datumOpening output).information X)
  rw [information_eq]

theorem direct_output_label :
    ((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).label (.inl output) =
      Row.shared (X.act ruleOpening (closures selected).schema.value) := by
  change RuleSyntax.relabel (Tm := fun a => Row Tm a)
    ((direct ordinary rows closures selected extension ruleOpening datumOpening output).row X)
    [.inl output] [Row.shared (X.act ruleOpening (closures selected).schema.value)] (.inl output) = _
  exact if_pos rfl

theorem consumer_output_label :
    ((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).label output =
      X.act ruleOpening (closures selected).schema.value :=
  Materialization.result_label_single X
    (consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output)
    output (closures selected).schema.value rfl rfl

theorem output_reading_iff {b : Obj} (point : Hom (E.target extension) b) (value : Tm b) :
    (((direct ordinary rows closures selected extension ruleOpening datumOpening output).result X).label
      (.inl output)).ReadsAt X point value ↔
      X.E (X.act point
        (((consumer ordinary rows closures selected extension ruleOpening datumOpening X temporary output).result X).label output)) value := by
  rw [direct_output_label, consumer_output_label]
  rfl

#print axioms information_eq
#print axioms result_models_iff
#print axioms output_reading_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericFirings
