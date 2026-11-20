import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadProtected

/-!
# Original mixed-source reads instantiate the protected plan family

The same allocation function is used for the original request and its actual
held execution. Original admission derives the protected plan; its primitive
run returns the canonical decoded live view of that independent original read.
No abstract protocol realizer or endpoint-adequacy hypothesis is supplied.
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
  (ambient : Set (HeldReadEncoding.Code Tm))
  (allocate : (ordinary : RuleSyntax.State Tm O) → O → O)

noncomputable def protectedPlan
    (available : Sum.inr (HeldReadGenericFirings.consumeRule (closure (source.label selected)).schema) ∈ ambient)
    (temporaryFresh : allocate (encode source filler).toState output ∉ (encode source filler).present)
    (different : allocate (encode source filler).toState output ≠ output)
    (admitted : (direct source selected output extension ruleOpening datumOpening schematic).Admits X) :
    HeldReadProtected.Plan X E ambient allocate (encode source filler) := by
  have original := (original_admits_iff source selected output extension ruleOpening datumOpening schematic X).mp admitted
  have common := (admission_iff source selected output extension ruleOpening datumOpening schematic filler X original.2.2.2.1).mp admitted
  exact .read (encode source filler).toState (encode source filler).rules (fun o => closure (source.label o))
    selected extension ruleOpening datumOpening output available temporaryFresh different common

theorem protectedPlan_returns_original
    (available : Sum.inr (HeldReadGenericFirings.consumeRule (closure (source.label selected)).schema) ∈ ambient)
    (temporaryFresh : allocate (encode source filler).toState output ∉ (encode source filler).present)
    (different : allocate (encode source filler).toState output ≠ output)
    (admitted : (direct source selected output extension ruleOpening datumOpening schematic).Admits X) :
    ∃ plan : HeldReadProtected.Plan X E ambient allocate (encode source filler),
      (HeldReadProtected.realize X E ambient allocate plan).run.word.length = 2 ∧
      (HeldReadProtected.realize X E ambient allocate plan).finishState =
        nativeFinal source selected output extension ruleOpening datumOpening filler X
          (allocate (encode source filler).toState output) ∧
      LiveObservations.observe
        (decodeResult source selected output extension ruleOpening datumOpening filler X
          (allocate (encode source filler).toState output)) =
        LiveObservations.observe ((direct source selected output extension ruleOpening datumOpening schematic).result X) := by
  let plan := protectedPlan source selected output extension ruleOpening datumOpening schematic filler X ambient
    allocate available temporaryFresh different admitted
  refine ⟨plan, rfl, rfl, ?_⟩
  exact decode_view_eq source selected output extension ruleOpening datumOpening schematic filler X
    (allocate (encode source filler).toState output) temporaryFresh

#print axioms protectedPlan
#print axioms protectedPlan_returns_original

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceAdapter
