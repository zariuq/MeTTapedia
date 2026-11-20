import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceResults

/-!
# The arbitrary mixed-source correspondence has an actual held execution

The original direct candidate is independent of the common encoding. Its
admission constructs an admitted two-firing run on the actual encoded source;
the returned decoder agrees on the whole live view and never merges two live
resource identities. This does not identify the raw one- and two-event words.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceAdapter

open Interface (Frames)
open RuleOccurrences HeldReadEncoding

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  (source : SchematicRows.State Tm O) (selected output : O) (extension : E.Ext source.frame)
  (ruleOpening datumOpening : Hom (closure (source.label selected)).schema.locals (E.target extension))
  (schematic : sharedTag (source.label selected) = false) (filler : Tm source.frame) (X : Frames Tm Hom)
  (temporary : O) (ambient : Set (HeldReadEncoding.Code Tm))

theorem actual_execution_of_original
    (available : Sum.inr (HeldReadGenericFirings.consumeRule (closure (source.label selected)).schema) ∈ ambient)
    (temporaryFresh : temporary ∉ (encode source filler).present) (different : temporary ≠ output)
    (admitted : (direct source selected output extension ruleOpening datumOpening schematic).Admits X) :
    ∃ run : (HeldReadGenericFirings.protocolMachine (E := E) (O := O) (R := O) X ambient).Run (encode source filler),
      run.word.length = 2 ∧
      run.last = nativeFinal source selected output extension ruleOpening datumOpening filler X temporary ∧
      LiveObservations.observe (decodeResult source selected output extension ruleOpening datumOpening filler X temporary) =
        LiveObservations.observe ((direct source selected output extension ruleOpening datumOpening schematic).result X) ∧
      Disjoint run.last.present run.last.rules := by
  have input := (original_admits_iff source selected output extension ruleOpening datumOpening schematic X).mp admitted
  have outputFresh : output ∉ source.present := input.2.2.2.1
  have commonAdmitted := (admission_iff source selected output extension ruleOpening datumOpening schematic filler X outputFresh).mp admitted
  obtain ⟨first, second⟩ := HeldReadGenericFirings.stages_of_direct_admitted X
    (encode source filler).toState (encode source filler).rules (fun o => closure (source.label o))
    selected extension ruleOpening datumOpening temporary output ambient available temporaryFresh different commonAdmitted
  let run := HeldReadGenericFirings.execution X (encode source filler).toState (encode source filler).rules
    (fun o => closure (source.label o)) selected extension ruleOpening datumOpening temporary output ambient first second
  refine ⟨run, rfl, rfl,
    decode_view_eq source selected output extension ruleOpening datumOpening schematic filler X temporary temporaryFresh, ?_⟩
  exact returned_components_disjoint source selected output extension ruleOpening datumOpening filler X temporary temporaryFresh outputFresh

#print axioms actual_execution_of_original

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceAdapter
