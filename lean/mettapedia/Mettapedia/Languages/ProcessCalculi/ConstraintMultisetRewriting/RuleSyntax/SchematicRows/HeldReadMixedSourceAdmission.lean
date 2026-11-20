import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceAdapter

/-!
# The arbitrary mixed-source read and its common representation admit together

The original occurrence namespace is preserved: the output must be fresh from
all original rows, not merely from the ordinary component of the encoding.
With that resource licence the actual information, freshness, well-formedness
and admission judgments agree. No behavior-only or solved-value quotient is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceAdapter

open Interface (Frames)
open HeldReadEncoding HeldReadGenericFirings

universe uO uT uH uE uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}
  (source : SchematicRows.State Tm O) (selected output : O) (extension : E.Ext source.frame)
  (ruleOpening datumOpening : Hom (closure (source.label selected)).schema.locals (E.target extension))
  (schematic : sharedTag (source.label selected) = false) (filler : Tm source.frame) (X : Frames Tm Hom)

theorem information_eq :
    (direct source selected output extension ruleOpening datumOpening schematic).information X =
      (commonDirect source selected output extension ruleOpening datumOpening filler).information X := by
  simp only [SchematicRows.Firing.information, SchematicRows.Firing.readValues,
    direct_uses, direct_readUses]
  rfl

variable [DecidableEq O]

theorem original_admits_iff :
    (direct source selected output extension ruleOpening datumOpening schematic).Admits X ↔
      (direct source selected output extension ruleOpening datumOpening schematic).Fresh X ∧
        (closure (source.label selected)).WellFormed ∧ selected ∈ source.present ∧ output ∉ source.present ∧
        X.Solvable ((direct source selected output extension ruleOpening datumOpening schematic).information X) := by
  constructor
  · rintro ⟨shapes, enabled, solved, _⟩
    obtain ⟨fresh, _, _, _, _, _, _, wellFormed, _⟩ := shapes
    have rowWellFormed := wellFormed
      ⟨.schematic (closure (source.label selected)), RowUse.schematic (closure (source.label selected)) datumOpening⟩
      ((direct_uses source selected output extension ruleOpening datumOpening schematic).symm ▸ List.mem_singleton_self _)
    refine ⟨fresh, rowWellFormed, ?_, ?_, solved⟩
    · exact enabled.kept_subset (List.mem_toFinset.mpr (List.mem_singleton_self _))
    · intro old
      exact Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr (List.mem_singleton_self _)) old
  · rintro ⟨fresh, wellFormed, present, outputFresh, solved⟩
    refine ⟨?_, ?_, solved, ?_⟩
    · refine ⟨fresh, List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · intro packed member
        rw [direct_uses] at member
        obtain rfl := List.mem_singleton.mp member
        exact wellFormed
      · intro row member
        cases member
    · apply RuleOccurrences.enabled_of
      · intro occurrence member
        cases member
      · intro occurrence member
        have same := List.mem_singleton.mp member
        subst occurrence
        exact present
      · intro occurrence member
        cases member
      · intro occurrence member
        have same := List.mem_singleton.mp member
        subst occurrence
        exact outputFresh
    · intro target point _
      constructor
      · intro check member
        cases member
      · intro query member
        cases member

theorem admission_iff (outputFresh : output ∉ source.present) :
    (direct source selected output extension ruleOpening datumOpening schematic).Admits X ↔
      (commonDirect source selected output extension ruleOpening datumOpening filler).Admits X := by
  have ordinaryFresh : output ∉ (encode source filler).present := by
    intro member
    exact outputFresh ((HeldReadEncoding.present_iff source filler output).mp member).1
  constructor
  · intro admitted
    obtain ⟨fresh, wellFormed, present, _, target, point, solved⟩ :=
      (original_admits_iff source selected output extension ruleOpening datumOpening schematic X).mp admitted
    have commonFresh := (fresh_iff source selected output extension ruleOpening datumOpening schematic filler X).mp fresh
    have heldPresent : selected ∈ (encode source filler).rules :=
      (HeldReadEncoding.rules_iff source filler selected).mpr ⟨present, schematic⟩
    have commonSolved : X.Models point
        ((commonDirect source selected output extension ruleOpening datumOpening filler).information X) :=
      (information_eq source selected output extension ruleOpening datumOpening schematic filler X) ▸ solved
    refine ⟨direct_shapes X (encode source filler).toState (encode source filler).rules
        (fun o => closure (source.label o)) selected extension ruleOpening datumOpening output commonFresh wellFormed,
      direct_enabled (encode source filler).toState (encode source filler).rules
        (fun o => closure (source.label o)) selected extension ruleOpening datumOpening output heldPresent ordinaryFresh,
      ⟨target, point, commonSolved⟩, ?_⟩
    intro target point _
    exact direct_holds X (encode source filler).toState (encode source filler).rules
      (fun o => closure (source.label o)) selected extension ruleOpening datumOpening output point
  · intro admitted
    obtain ⟨fresh, wellFormed, present, _, target, point, solved⟩ :=
      direct_admission_data X (encode source filler).toState (encode source filler).rules
        (fun o => closure (source.label o)) selected extension ruleOpening datumOpening output admitted
    apply (original_admits_iff source selected output extension ruleOpening datumOpening schematic X).mpr
    refine ⟨(fresh_iff source selected output extension ruleOpening datumOpening schematic filler X).mpr fresh,
      wellFormed, ((HeldReadEncoding.rules_iff source filler selected).mp present).1, outputFresh,
      target, point, ?_⟩
    exact (information_eq source selected output extension ruleOpening datumOpening schematic filler X).symm ▸ solved

#print axioms information_eq
#print axioms original_admits_iff
#print axioms admission_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceAdapter
