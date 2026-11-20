import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericProtocol
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.LiveObservations

/-!
# Returning to the original mixed occurrence namespace

The ordinary and held components partition the original source. A globally
fresh public output preserves their disjointness at return. Decoding keeps
every original live identity and schema, hides the consumed temporary, and
agrees with the independently constructed original direct result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceAdapter

open Interface (Frames)
open RuleOccurrences HeldReadEncoding

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}
  (source : SchematicRows.State Tm O) (selected output : O) (extension : E.Ext source.frame)
  (ruleOpening datumOpening : Hom (closure (source.label selected)).schema.locals (E.target extension))
  (schematic : sharedTag (source.label selected) = false) (filler : Tm source.frame) (X : Frames Tm Hom)
  [DecidableEq O] (temporary : O)

def nativeFinal :=
  (HeldReadGenericFirings.consumer (encode source filler).toState (encode source filler).rules
    (fun o => closure (source.label o)) selected extension ruleOpening datumOpening X temporary output).result X

def decodeResult : SchematicRows.State Tm O where
  frame := E.target extension
  knowledge := (nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).knowledge
  present := (nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).present ∪
    (nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).rules
  label o := if o = output then .shared ((nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).label o)
    else match source.label o with
      | .shared _ => .shared ((nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).label o)
      | .schematic row => .schematic ⟨row.schema,
          ((nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).held o).args⟩

theorem original_present :
    ((direct source selected output extension ruleOpening datumOpening schematic).result X).present =
      source.present ∪ {output} := by
  simp [SchematicRows.Firing.result, direct, Selection.commit, MeTTaCalculus.OccurrenceCommits.fire]

theorem original_output_label :
    ((direct source selected output extension ruleOpening datumOpening schematic).result X).label output =
      Row.shared (X.act ruleOpening (closure (source.label selected)).schema.value) := by
  exact if_pos rfl

theorem original_label_other (o : O) (different : o ≠ output) :
    ((direct source selected output extension ruleOpening datumOpening schematic).result X).label o =
      (source.label o).act X (E.weaken extension) := by
  exact if_neg different

theorem decode_knowledge :
    (decodeResult source selected output extension ruleOpening datumOpening filler X temporary).knowledge =
      ((direct source selected output extension ruleOpening datumOpening schematic).result X).knowledge :=
  (HeldReadGenericFirings.information_eq X (encode source filler).toState (encode source filler).rules
    (fun o => closure (source.label o)) selected extension ruleOpening datumOpening temporary output).trans
      (information_eq source selected output extension ruleOpening datumOpening schematic filler X).symm

theorem decode_present (temporaryFresh : temporary ∉ (encode source filler).present) :
    (decodeResult source selected output extension ruleOpening datumOpening filler X temporary).present =
      ((direct source selected output extension ruleOpening datumOpening schematic).result X).present := by
  have ordinary := HeldReadGenericFirings.consumer_present X (encode source filler).toState
    (encode source filler).rules (fun o => closure (source.label o)) selected extension ruleOpening datumOpening
    temporary output temporaryFresh
  have held := HeldReadGenericFirings.consumer_rules X (encode source filler).toState
    (encode source filler).rules (fun o => closure (source.label o)) selected extension ruleOpening datumOpening temporary output
  change _ ∪ _ = _
  unfold nativeFinal
  rw [ordinary, held, original_present]
  have partition := (resource_partition source filler).1
  calc ((encode source filler).present ∪ {output}) ∪ (encode source filler).rules =
        ((encode source filler).present ∪ (encode source filler).rules) ∪ {output} := by
          ext o
          simp only [Finset.mem_union, Finset.mem_singleton]
          tauto
    _ = source.present ∪ {output} := congrArg (fun rows => rows ∪ {output}) partition

theorem returned_components_disjoint (temporaryFresh : temporary ∉ (encode source filler).present)
    (outputFresh : output ∉ source.present) :
    Disjoint (nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).present
      (nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).rules := by
  have ordinary := HeldReadGenericFirings.consumer_present X (encode source filler).toState
    (encode source filler).rules (fun o => closure (source.label o)) selected extension ruleOpening datumOpening
    temporary output temporaryFresh
  have held := HeldReadGenericFirings.consumer_rules X (encode source filler).toState
    (encode source filler).rules (fun o => closure (source.label o)) selected extension ruleOpening datumOpening temporary output
  unfold nativeFinal
  rw [ordinary, held]
  apply Finset.disjoint_left.mpr
  intro o present schemaPresent
  rcases Finset.mem_union.mp present with old | made
  · exact Finset.disjoint_left.mp (resource_partition source filler).2 old schemaPresent
  · have same := Finset.mem_singleton.mp made
    subst o
    exact outputFresh ((rules_iff source filler output).mp schemaPresent).1

theorem decode_live_labels (temporaryFresh : temporary ∉ (encode source filler).present)
    (o : O) (present : o ∈ ((direct source selected output extension ruleOpening datumOpening schematic).result X).present) :
    (decodeResult source selected output extension ruleOpening datumOpening filler X temporary).label o =
      ((direct source selected output extension ruleOpening datumOpening schematic).result X).label o := by
  by_cases same : o = output
  · subst o
    have decoded :
        (decodeResult source selected output extension ruleOpening datumOpening filler X temporary).label output =
          Row.shared ((nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).label output) :=
      if_pos rfl
    have actual := HeldReadGenericFirings.consumer_output_label X (encode source filler).toState
      (encode source filler).rules (fun o => closure (source.label o)) selected extension ruleOpening datumOpening temporary output
    exact decoded.trans ((congrArg (Row.shared (Tm := Tm)) actual).trans
      (original_output_label source selected output extension ruleOpening datumOpening schematic X).symm)
  · have old : o ∈ source.present := by
      rw [original_present, Finset.mem_union, Finset.mem_singleton] at present
      exact present.resolve_right same
    cases row : source.label o with
    | shared value =>
      have ordinaryPresent : o ∈ (encode source filler).present :=
        (present_iff source filler o).mpr ⟨old, by rw [row]; rfl⟩
      have notTemporary : o ≠ temporary := fun equality => temporaryFresh (equality ▸ ordinaryPresent)
      have actual := HeldReadGenericFirings.consumer_label_other X (encode source filler).toState
        (encode source filler).rules (fun o => closure (source.label o)) selected extension ruleOpening datumOpening
        temporary output o same notTemporary
      have valueEq := actual.trans
        (congrArg (X.act (E.weaken extension)) (label_shared source filler o value row))
      have decoded : (decodeResult source selected output extension ruleOpening datumOpening filler X temporary).label o =
          (Row.shared ((nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).label o) :
            Row Tm (E.target extension)) := by
        simp only [decodeResult, if_neg same, row]
      have sourceAct : (source.label o).act X (E.weaken extension) =
          Row.shared (X.act (E.weaken extension) value) := by rw [row]; rfl
      exact decoded.trans ((congrArg (Row.shared (Tm := Tm) (a := E.target extension)) valueEq).trans
        (sourceAct.symm.trans
          (original_label_other source selected output extension ruleOpening datumOpening schematic X o same).symm))
    | schematic datumRow =>
      have args :
          ((nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).held o).args =
            (closure (source.label o)).args.map (X.act (E.weaken extension)) :=
        congrArg (fun held : Held Tm (HeldReadEncoding.Code Tm) Unit (E.target extension) => held.args)
          (HeldReadGenericFirings.consumer_held X (encode source filler).toState (encode source filler).rules
            (fun o => closure (source.label o)) selected extension ruleOpening datumOpening temporary output o)
      have originalClosure : closure (source.label o) = datumRow := by rw [row]; rfl
      have finalArgs := args.trans
        (congrArg (fun datum : Closure Tm source.frame => datum.args.map (X.act (E.weaken extension))) originalClosure)
      have closureLabels := congrArg (fun arguments : List (Tm (E.target extension)) =>
        (Row.schematic (⟨datumRow.schema, arguments⟩ : Closure Tm (E.target extension)))) finalArgs
      have decoded : (decodeResult source selected output extension ruleOpening datumOpening filler X temporary).label o =
          Row.schematic (⟨datumRow.schema,
            ((nativeFinal source selected output extension ruleOpening datumOpening filler X temporary).held o).args⟩ :
              Closure Tm (E.target extension)) := by
        simp only [decodeResult, if_neg same, row]
      have sourceAct : (source.label o).act X (E.weaken extension) =
          Row.schematic (datumRow.act X (E.weaken extension)) := by rw [row]; rfl
      exact decoded.trans (closureLabels.trans
        (sourceAct.symm.trans
          (original_label_other source selected output extension ruleOpening datumOpening schematic X o same).symm))

theorem decode_view_eq (temporaryFresh : temporary ∉ (encode source filler).present) :
    LiveObservations.observe (decodeResult source selected output extension ruleOpening datumOpening filler X temporary) =
      LiveObservations.observe ((direct source selected output extension ruleOpening datumOpening schematic).result X) := by
  exact (LiveObservations.observe_eq (E.target extension)
    ((direct source selected output extension ruleOpening datumOpening schematic).result X).knowledge
    (decodeResult source selected output extension ruleOpening datumOpening filler X temporary).knowledge
    ((direct source selected output extension ruleOpening datumOpening schematic).result X).present
    (decodeResult source selected output extension ruleOpening datumOpening filler X temporary).present
    ((direct source selected output extension ruleOpening datumOpening schematic).result X).label
    (decodeResult source selected output extension ruleOpening datumOpening filler X temporary).label
    (decode_knowledge source selected output extension ruleOpening datumOpening schematic filler X temporary).symm
    (decode_present source selected output extension ruleOpening datumOpening schematic filler X temporary temporaryFresh).symm
    (fun o present =>
      (decode_live_labels source selected output extension ruleOpening datumOpening schematic filler X temporary temporaryFresh o present).symm)).symm

#print axioms decode_knowledge
#print axioms decode_present
#print axioms returned_components_disjoint
#print axioms decode_live_labels
#print axioms decode_view_eq

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceAdapter
