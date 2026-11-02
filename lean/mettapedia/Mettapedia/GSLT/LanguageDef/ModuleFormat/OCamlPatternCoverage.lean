import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternReadback

/-! Source matches construct finite, noncolliding captures for the existing
compiled pattern. Wildcards consume fresh slots but publish no bindings.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

abbrev PatternCaptures := List (Nat × OCaml.Value)

def slotName (index : Nat) : String := "ml:" ++ ("pattern:" ++ toString index)
def captureBindings (captures : PatternCaptures) : Bindings :=
  captures.map fun entry => (slotName entry.1, value entry.2)
def captureAt : PatternCaptures → Nat → Option OCaml.Value
  | [], _ => none
  | (slot, actual) :: rest, index => if slot = index then some actual else captureAt rest index

theorem slotName_injective : Function.Injective slotName := by
  intro first second same
  simp only [slotName, String.append_right_inj] at same
  exact Nat.repr_injective same

theorem apply_capture_hole (captures : PatternCaptures) (index : Nat) :
    applyBindings (captureBindings captures) (hole ("pattern:" ++ toString index)) =
      match captureAt captures index with
      | some actual => value actual
      | none => hole ("pattern:" ++ toString index) := by
  induction captures with
  | nil => simp [captureBindings, captureAt, hole, applyBindings]
  | cons entry rest ih =>
      rcases entry with ⟨other, actual⟩
      by_cases same : other = index
      · subst other
        simp [captureBindings, captureAt, hole, slotName, applyBindings]
      · have different : slotName other ≠ slotName index := fun equal => same (slotName_injective equal)
        change applyBindings ((slotName other, value actual) :: captureBindings rest)
          (.fvar (slotName index)) = _
        rw [applyBindings]
        have no : (slotName other == slotName index) = false := beq_eq_false_iff_ne.mpr different
        simp only [List.find?_cons, no]
        simpa only [captureAt, same, if_false, hole, slotName, applyBindings] using ih

theorem captureAt_append (first second : PatternCaptures) (index : Nat) :
    captureAt (first ++ second) index = (captureAt first index).or (captureAt second index) := by
  induction first with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨other, actual⟩
      by_cases same : other = index <;> simp [captureAt, same, ih]

def CapturesWithin (captures : PatternCaptures) (start finish : Nat) : Prop :=
  ∀ entry ∈ captures, start ≤ entry.1 ∧ entry.1 < finish

theorem captureAt_none_of_outside {captures : PatternCaptures} {start finish index : Nat}
    (within : CapturesWithin captures start finish) (outside : index < start ∨ finish ≤ index) :
    captureAt captures index = none := by
  induction captures with
  | nil => rfl
  | cons entry rest ih =>
      have bounds := within entry List.mem_cons_self
      have different : entry.1 ≠ index := by omega
      simpa [captureAt, different] using
        ih (fun item member => within item (List.mem_cons_of_mem entry member))

theorem capture_append_left {first second : PatternCaptures} {start middle finish index : Nat}
    (within : CapturesWithin second middle finish) (inRange : start ≤ index ∧ index < middle) :
    captureAt (first ++ second) index = captureAt first index := by
  rw [captureAt_append, captureAt_none_of_outside within (Or.inl inRange.2)]
  cases captureAt first index <;> rfl

theorem capture_append_right {first second : PatternCaptures} {start middle finish index : Nat}
    (within : CapturesWithin first start middle) (inRange : middle ≤ index ∧ index < finish) :
    captureAt (first ++ second) index = captureAt second index := by
  rw [captureAt_append, captureAt_none_of_outside within (Or.inr inRange.1)]
  rfl

theorem pattern_capture_agreement (pattern : OCaml.MatchPattern) :
    ∀ (start : Nat) (first second : PatternCaptures),
      start ≤ patternAfter pattern start ∧
      ((∀ index, start ≤ index → index < patternAfter pattern start →
          captureAt first index = captureAt second index) →
        applyBindings (captureBindings first) (patternAt pattern start).term =
          applyBindings (captureBindings second) (patternAt pattern start).term) := by
  refine OCaml.MatchPattern.rec
    (motive_1 := fun pattern => ∀ (start : Nat) (first second : PatternCaptures),
      start ≤ patternAfter pattern start ∧
      ((∀ index, start ≤ index → index < patternAfter pattern start →
          captureAt first index = captureAt second index) →
        applyBindings (captureBindings first) (patternAt pattern start).term =
          applyBindings (captureBindings second) (patternAt pattern start).term))
    (motive_2 := fun patterns => ∀ (start : Nat) (first second : PatternCaptures),
      start ≤ fieldsAfter patterns start ∧
      ((∀ index, start ≤ index → index < fieldsAfter patterns start →
          captureAt first index = captureAt second index) →
        (fieldsAt patterns start).1.map (applyBindings (captureBindings first)) =
          (fieldsAt patterns start).1.map (applyBindings (captureBindings second))))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pattern
  · intro start first second
    refine ⟨by change start ≤ start + 1; omega, ?_⟩
    intro same
    simp only [patternAt_bind, apply_capture_hole, same start (by omega) (by change start < start + 1; omega)]
  · intro start first second
    refine ⟨by change start ≤ start + 1; omega, ?_⟩
    intro same
    simp only [patternAt_wildcard, apply_capture_hole, same start (by omega) (by change start < start + 1; omega)]
  · intro datum start first second
    exact ⟨Nat.le_refl _, by simp only [patternAt_literal, apply_literal, implies_true]⟩
  · intro patterns ih start first second
    obtain ⟨bounds, transfer⟩ := ih start first second
    refine ⟨bounds, ?_⟩
    intro same
    have fieldsSame := transfer same
    simpa only [patternAt_tuple, apply_node, List.map_cons, List.map_nil, values, apply_linked] using
      congrArg (fun items => node "MlTuple" [values items]) fieldsSame
  · intro head tail headIH tailIH start first second
    obtain ⟨headBounds, headTransfer⟩ := headIH start first second
    obtain ⟨tailBounds, tailTransfer⟩ := tailIH (patternAfter head start) first second
    change start ≤ patternAfter tail (patternAfter head start) ∧ _
    refine ⟨Nat.le_trans headBounds tailBounds, ?_⟩
    intro same
    have firstSame := headTransfer (fun index lo hi => same index lo (Nat.lt_of_lt_of_le hi tailBounds))
    have restSame := tailTransfer (fun index lo hi => same index (Nat.le_trans headBounds lo) hi)
    simp only [patternAt_cons, apply_node, List.map_cons, List.map_nil, firstSame, restSame]
  · intro typeId constructor patterns ih start first second
    obtain ⟨bounds, transfer⟩ := ih start first second
    refine ⟨bounds, ?_⟩
    intro same
    have fieldsSame := transfer same
    simp only [patternAt_variant, apply_node, List.map_cons, List.map_nil, apply_tag, values, apply_linked]
    rw [fieldsSame]
  · intro start first second
    exact ⟨Nat.le_refl _, fun _ => rfl⟩
  · intro head rest headIH restIH start first second
    obtain ⟨headBounds, headTransfer⟩ := headIH start first second
    obtain ⟨tailBounds, tailTransfer⟩ := restIH (patternAfter head start) first second
    change start ≤ fieldsAfter rest (patternAfter head start) ∧ _
    refine ⟨Nat.le_trans headBounds tailBounds, ?_⟩
    intro same
    have firstSame := headTransfer (fun index lo hi => same index lo (Nat.lt_of_lt_of_le hi tailBounds))
    have restSame := tailTransfer (fun index lo hi => same index (Nat.le_trans headBounds lo) hi)
    simp only [fieldsAt_cons, List.map_cons, firstSame, restSame]

theorem fields_capture_agreement (patterns : List OCaml.MatchPattern) (start : Nat)
    (first second : PatternCaptures)
    (same : ∀ index, start ≤ index → index < fieldsAfter patterns start →
      captureAt first index = captureAt second index) :
    (fieldsAt patterns start).1.map (applyBindings (captureBindings first)) =
      (fieldsAt patterns start).1.map (applyBindings (captureBindings second)) := by
  have whole := (pattern_capture_agreement (.tuple patterns) start first second).2 same
  simp only [patternAt_tuple, apply_node, List.map_cons, List.map_nil, values, apply_linked] at whole
  exact values_injective (List.cons.inj (Pattern.apply.inj whole).2).1

theorem capturesWithin_append {first second : PatternCaptures} {start middle finish : Nat}
    (firstWithin : CapturesWithin first start middle) (secondWithin : CapturesWithin second middle finish)
    (firstBounds : start ≤ middle) (secondBounds : middle ≤ finish) :
    CapturesWithin (first ++ second) start finish := by
  intro entry member
  rcases List.mem_append.mp member with here | later
  · have bounds := firstWithin entry here
    exact ⟨bounds.1, Nat.lt_of_lt_of_le bounds.2 secondBounds⟩
  · have bounds := secondWithin entry later
    exact ⟨Nat.le_trans firstBounds bounds.1, bounds.2⟩

theorem pattern_instance_construct (pattern : OCaml.MatchPattern) :
    ∀ (start : Nat) (actual : OCaml.Value) (boundValues : List OCaml.Value),
      OCaml.matchPattern pattern actual = some boundValues →
      ∃ captures : PatternCaptures, CapturesWithin captures start (patternAfter pattern start) ∧
        applyBindings (captureBindings captures) (patternAt pattern start).term = value actual := by
  refine OCaml.MatchPattern.rec
    (motive_1 := fun pattern => ∀ (start : Nat) (actual : OCaml.Value) (boundValues : List OCaml.Value),
      OCaml.matchPattern pattern actual = some boundValues →
      ∃ captures : PatternCaptures, CapturesWithin captures start (patternAfter pattern start) ∧
        applyBindings (captureBindings captures) (patternAt pattern start).term = value actual)
    (motive_2 := fun patterns => ∀ (start : Nat) (actuals boundValues : List OCaml.Value),
      OCaml.matchFields patterns actuals = some boundValues →
      ∃ captures : PatternCaptures, CapturesWithin captures start (fieldsAfter patterns start) ∧
        (fieldsAt patterns start).1.map (applyBindings (captureBindings captures)) = actuals.map value)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pattern
  · intro start actual _ _
    refine ⟨[(start, actual)], ?_, ?_⟩
    · intro entry member
      have equal : entry = (start, actual) := List.mem_singleton.mp member
      subst entry
      change start ≤ start ∧ start < start + 1
      omega
    · simp only [patternAt_bind, apply_capture_hole, captureAt, if_true]
  · intro start actual _ _
    refine ⟨[(start, actual)], ?_, ?_⟩
    · intro entry member
      have equal : entry = (start, actual) := List.mem_singleton.mp member
      subst entry
      change start ≤ start ∧ start < start + 1
      omega
    · simp only [patternAt_wildcard, apply_capture_hole, captureAt, if_true]
  · intro datum start actual _ matched
    cases actual with
    | literal other =>
        by_cases same : datum = other
        · subst other
          exact ⟨[], by simp [CapturesWithin], by simp only [patternAt_literal, apply_literal, value]⟩
        · simp [OCaml.matchPattern, same] at matched
    | tuple | cons | variant | closure => simp [OCaml.matchPattern] at matched
  · intro patterns ih start actual boundValues matched
    cases actual with
    | tuple actuals =>
        obtain ⟨captures, within, realized⟩ := ih start actuals boundValues matched
        refine ⟨captures, within, ?_⟩
        simp only [patternAt_tuple, apply_node, List.map_cons, List.map_nil, values, apply_linked, realized]
        exact congrArg (fun items => node "MlTuple" [items]) (valueList_as_values actuals).symm
    | literal | cons | variant | closure => simp [OCaml.matchPattern] at matched
  · intro head tail headIH tailIH start actual boundValues matched
    cases actual with
    | cons first rest =>
        cases headMatch : OCaml.matchPattern head first with
        | none => simp [OCaml.matchPattern, headMatch] at matched
        | some firstBindings =>
            cases tailMatch : OCaml.matchPattern tail rest with
            | none => simp [OCaml.matchPattern, headMatch, tailMatch] at matched
            | some restBindings =>
                obtain ⟨firstCaptures, firstWithin, firstRealized⟩ := headIH start first firstBindings headMatch
                obtain ⟨restCaptures, restWithin, restRealized⟩ :=
                  tailIH (patternAfter head start) rest restBindings tailMatch
                have headBounds := (pattern_capture_agreement head start [] []).1
                have tailBounds := (pattern_capture_agreement tail (patternAfter head start) [] []).1
                have firstTransfer := (pattern_capture_agreement head start
                  (firstCaptures ++ restCaptures) firstCaptures).2
                  (fun index lo hi => capture_append_left restWithin ⟨lo, hi⟩)
                have restTransfer := (pattern_capture_agreement tail (patternAfter head start)
                  (firstCaptures ++ restCaptures) restCaptures).2
                  (fun index lo hi => capture_append_right firstWithin ⟨lo, hi⟩)
                refine ⟨firstCaptures ++ restCaptures,
                  capturesWithin_append firstWithin restWithin headBounds tailBounds, ?_⟩
                simp only [patternAt_cons, apply_node, List.map_cons, List.map_nil,
                  firstTransfer, restTransfer, firstRealized, restRealized, value]
    | literal | tuple | variant | closure => simp [OCaml.matchPattern] at matched
  · intro typeId constructor patterns ih start actual boundValues matched
    cases actual with
    | variant actualType actualConstructor actuals =>
        by_cases same : typeId = actualType ∧ constructor = actualConstructor
        · obtain ⟨rfl, rfl⟩ := same
          have fieldsMatch : OCaml.matchFields patterns actuals = some boundValues := by
            simpa [OCaml.matchPattern] using matched
          obtain ⟨captures, within, realized⟩ := ih start actuals boundValues fieldsMatch
          refine ⟨captures, within, ?_⟩
          simp only [patternAt_variant, apply_node, List.map_cons, List.map_nil, apply_tag,
            values, apply_linked, realized]
          exact congrArg (fun items => node "MlVariant" [tag typeId constructor, items])
            (valueList_as_values actuals).symm
        · simp [OCaml.matchPattern, same] at matched
    | literal | tuple | cons | closure => simp [OCaml.matchPattern] at matched
  · intro start actuals _ matched
    cases actuals with
    | nil => exact ⟨[], by simp [CapturesWithin], rfl⟩
    | cons _ _ => cases matched
  · intro head tail headIH tailIH start actuals boundValues matched
    cases actuals with
    | nil => cases matched
    | cons first rest =>
        cases headMatch : OCaml.matchPattern head first with
        | none => simp [OCaml.matchFields, headMatch] at matched
        | some firstBindings =>
            cases tailMatch : OCaml.matchFields tail rest with
            | none => simp [OCaml.matchFields, headMatch, tailMatch] at matched
            | some restBindings =>
                obtain ⟨firstCaptures, firstWithin, firstRealized⟩ := headIH start first firstBindings headMatch
                obtain ⟨restCaptures, restWithin, restRealized⟩ :=
                  tailIH (patternAfter head start) rest restBindings tailMatch
                have headBounds := (pattern_capture_agreement head start [] []).1
                have tailBounds := (pattern_capture_agreement (.tuple tail) (patternAfter head start) [] []).1
                have firstTransfer := (pattern_capture_agreement head start
                  (firstCaptures ++ restCaptures) firstCaptures).2
                  (fun index lo hi => capture_append_left restWithin ⟨lo, hi⟩)
                have restTransfer := fields_capture_agreement tail (patternAfter head start)
                  (firstCaptures ++ restCaptures) restCaptures
                  (fun index lo hi => capture_append_right firstWithin ⟨lo, hi⟩)
                refine ⟨firstCaptures ++ restCaptures,
                  capturesWithin_append firstWithin restWithin headBounds tailBounds, ?_⟩
                simp only [fieldsAt_cons, List.map_cons, firstTransfer, restTransfer,
                  firstRealized, restRealized]

theorem pattern_instance_complete (pattern : OCaml.MatchPattern) (start : Nat) (actual : OCaml.Value)
    (boundValues : List OCaml.Value) (matched : OCaml.matchPattern pattern actual = some boundValues) :
    ∃ captures : PatternCaptures, CapturesWithin captures start (patternAfter pattern start) ∧
      applyBindings (captureBindings captures) (patternAt pattern start).term = value actual ∧
      (patternAt pattern start).bindings.map (applyBindings (captureBindings captures)) = boundValues.map value := by
  obtain ⟨captures, within, instanceSame⟩ := pattern_instance_construct pattern start actual boundValues matched
  obtain ⟨readBindings, sourceMatch, output⟩ := pattern_instance_readback pattern start actual
    (captureBindings captures) instanceSame
  have same : readBindings = boundValues := Option.some.inj (sourceMatch.symm.trans matched)
  exact ⟨captures, within, instanceSame, same ▸ output⟩

theorem pattern_instance_iff (pattern : OCaml.MatchPattern) (start : Nat) (actual : OCaml.Value) :
    (∃ assignment : Bindings, applyBindings assignment (patternAt pattern start).term = value actual) ↔
      ∃ boundValues, OCaml.matchPattern pattern actual = some boundValues := by
  constructor
  · rintro ⟨assignment, instanceSame⟩
    obtain ⟨boundValues, matched, _⟩ := pattern_instance_readback pattern start actual assignment instanceSame
    exact ⟨boundValues, matched⟩
  · rintro ⟨boundValues, matched⟩
    obtain ⟨captures, _, instanceSame⟩ := pattern_instance_construct pattern start actual boundValues matched
    exact ⟨captureBindings captures, instanceSame⟩

theorem pattern_failure_iff (pattern : OCaml.MatchPattern) (start : Nat) (actual : OCaml.Value) :
    OCaml.matchPattern pattern actual = none ↔
      ¬ ∃ assignment : Bindings, applyBindings assignment (patternAt pattern start).term = value actual := by
  rw [pattern_instance_iff]
  cases OCaml.matchPattern pattern actual <;> simp

#print axioms pattern_instance_complete
#print axioms pattern_instance_iff
#print axioms pattern_failure_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
