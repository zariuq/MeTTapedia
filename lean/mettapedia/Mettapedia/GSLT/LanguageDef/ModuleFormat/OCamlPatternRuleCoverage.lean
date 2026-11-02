import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternShapes

/-! Successful source matches extend to ordinary instances of both emitted
pattern-rule forms, including their actual control and environment fields.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

theorem pattern_slot_agreement (pattern : OCaml.MatchPattern) :
    ∀ (start : Nat) (first second : Bindings),
      (∀ index, start ≤ index → index < patternAfter pattern start →
        applyBindings first (hole ("pattern:" ++ toString index)) =
          applyBindings second (hole ("pattern:" ++ toString index))) →
      applyBindings first (patternAt pattern start).term =
        applyBindings second (patternAt pattern start).term := by
  refine OCaml.MatchPattern.rec
    (motive_1 := fun pattern => ∀ (start : Nat) (first second : Bindings),
      (∀ index, start ≤ index → index < patternAfter pattern start →
        applyBindings first (hole ("pattern:" ++ toString index)) =
          applyBindings second (hole ("pattern:" ++ toString index))) →
      applyBindings first (patternAt pattern start).term = applyBindings second (patternAt pattern start).term)
    (motive_2 := fun patterns => ∀ (start : Nat) (first second : Bindings),
      (∀ index, start ≤ index → index < fieldsAfter patterns start →
        applyBindings first (hole ("pattern:" ++ toString index)) =
          applyBindings second (hole ("pattern:" ++ toString index))) →
      (fieldsAt patterns start).1.map (applyBindings first) =
        (fieldsAt patterns start).1.map (applyBindings second))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pattern
  · intro start first second same
    exact same start (by omega) (by change start < start + 1; omega)
  · intro start first second same
    exact same start (by omega) (by change start < start + 1; omega)
  · intro datum start first second _
    simp only [patternAt_literal, apply_literal]
  · intro fields ih start first second same
    have fieldsSame := ih start first second same
    simp only [patternAt_tuple, apply_node, List.map_cons, List.map_nil, values, apply_linked]
    rw [fieldsSame]
  · intro head tail headIH tailIH start first second same
    have headBounds := (pattern_capture_agreement head start [] []).1
    have tailBounds := (pattern_capture_agreement tail (patternAfter head start) [] []).1
    have firstSame := headIH start first second
      (fun index lo hi => same index lo (Nat.lt_of_lt_of_le hi tailBounds))
    have restSame := tailIH (patternAfter head start) first second
      (fun index lo hi => same index (Nat.le_trans headBounds lo) hi)
    simp only [patternAt_cons, apply_node, List.map_cons, List.map_nil, firstSame, restSame]
  · intro typeId constructor fields ih start first second same
    have fieldsSame := ih start first second same
    simp only [patternAt_variant, apply_node, List.map_cons, List.map_nil, apply_tag, values, apply_linked]
    rw [fieldsSame]
  · intro start first second _
    rfl
  · intro head rest headIH restIH start first second same
    have headBounds := (pattern_capture_agreement head start [] []).1
    have tailBounds := (pattern_capture_agreement (.tuple rest) (patternAfter head start) [] []).1
    have firstSame := headIH start first second
      (fun index lo hi => same index lo (Nat.lt_of_lt_of_le hi tailBounds))
    have restSame := restIH (patternAfter head start) first second
      (fun index lo hi => same index (Nat.le_trans headBounds lo) hi)
    simp only [fieldsAt_cons, List.map_cons, firstSame, restSame]

def patternRequestBindings (captures : PatternCaptures) (body captured continuation later : Pattern) : Bindings :=
  [("ml:body", body), ("ml:environment", captured), ("ml:continuation", continuation), ("ml:later", later)] ++
    captureBindings captures

theorem request_pattern_hole (captures : PatternCaptures) (body captured continuation later : Pattern) (index : Nat) :
    applyBindings (patternRequestBindings captures body captured continuation later) (hole ("pattern:" ++ toString index)) =
      applyBindings (captureBindings captures) (hole ("pattern:" ++ toString index)) := by
  have bodyDifferent : "ml:body" ≠ slotName index := by
    intro same
    have byte := congrArg (fun text : String => text.toByteArray.data[3]?) same
    simp only [slotName, String.toByteArray_append, ByteArray.data_append] at byte
    change some (98 : UInt8) =
      (#[109, 108, 58] ++ (#[112, 97, 116, 116, 101, 114, 110, 58] ++ (toString index).toByteArray.data))[3]? at byte
    simp at byte
  have environmentDifferent : "ml:environment" ≠ slotName index := by
    intro same
    have byte := congrArg (fun text : String => text.toByteArray.data[3]?) same
    simp only [slotName, String.toByteArray_append, ByteArray.data_append] at byte
    change some (101 : UInt8) =
      (#[109, 108, 58] ++ (#[112, 97, 116, 116, 101, 114, 110, 58] ++ (toString index).toByteArray.data))[3]? at byte
    simp at byte
  have continuationDifferent : "ml:continuation" ≠ slotName index := by
    intro same
    have byte := congrArg (fun text : String => text.toByteArray.data[3]?) same
    simp only [slotName, String.toByteArray_append, ByteArray.data_append] at byte
    change some (99 : UInt8) =
      (#[109, 108, 58] ++ (#[112, 97, 116, 116, 101, 114, 110, 58] ++ (toString index).toByteArray.data))[3]? at byte
    simp at byte
  have laterDifferent : "ml:later" ≠ slotName index := by
    intro same
    have byte := congrArg (fun text : String => text.toByteArray.data[3]?) same
    simp only [slotName, String.toByteArray_append, ByteArray.data_append] at byte
    change some (108 : UInt8) =
      (#[109, 108, 58] ++ (#[112, 97, 116, 116, 101, 114, 110, 58] ++ (toString index).toByteArray.data))[3]? at byte
    simp at byte
  have bodyNo : ("ml:body" == slotName index) = false := beq_eq_false_iff_ne.mpr bodyDifferent
  have environmentNo : ("ml:environment" == slotName index) = false := beq_eq_false_iff_ne.mpr environmentDifferent
  have continuationNo : ("ml:continuation" == slotName index) = false := beq_eq_false_iff_ne.mpr continuationDifferent
  have laterNo : ("ml:later" == slotName index) = false := beq_eq_false_iff_ne.mpr laterDifferent
  change applyBindings _ (.fvar (slotName index)) = applyBindings _ (.fvar (slotName index))
  simp only [patternRequestBindings, applyBindings, List.cons_append, List.nil_append, List.find?_cons,
    bodyNo, environmentNo, continuationNo, laterNo]

theorem request_control_fields (captures : PatternCaptures) (body captured continuation later : Pattern) :
    applyBindings (patternRequestBindings captures body captured continuation later) (hole "body") = body ∧
    applyBindings (patternRequestBindings captures body captured continuation later) (hole "environment") = captured ∧
    applyBindings (patternRequestBindings captures body captured continuation later) (hole "continuation") = continuation ∧
    applyBindings (patternRequestBindings captures body captured continuation later) (hole "later") = later := by
  simp [patternRequestBindings, hole, applyBindings]

theorem match_one_rule_complete (pattern : OCaml.MatchPattern) (index : Nat) (actual : OCaml.Value)
    (boundValues : List OCaml.Value) (body : OCaml.Code) (captured : OCaml.Environment) (continuation : Pattern)
    (matched : OCaml.matchPattern pattern actual = some boundValues) :
    ∃ assignment : Bindings,
      applyBindings assignment ((patternRules index pattern)[0]'(by simp [patternRules])).left =
        node "MlMatchOne" [patternId index, value actual, code body, environment captured, continuation] ∧
      applyBindings assignment ((patternRules index pattern)[0]'(by simp [patternRules])).right =
        node "MlEvaluate" [code body, environment (OCaml.extend captured boundValues), continuation] := by
  obtain ⟨captures, _, instanceSame⟩ := pattern_instance_construct pattern 0 actual boundValues matched
  let assignment := patternRequestBindings captures (code body) (environment captured) continuation (node "MlClauseNil")
  have slotsSame := pattern_slot_agreement pattern 0 assignment (captureBindings captures)
    (fun slot _ _ => request_pattern_hole captures _ _ _ _ slot)
  have controls := request_control_fields captures (code body) (environment captured) continuation (node "MlClauseNil")
  change applyBindings assignment (hole "body") = code body ∧
    applyBindings assignment (hole "environment") = environment captured ∧
    applyBindings assignment (hole "continuation") = continuation ∧
    applyBindings assignment (hole "later") = node "MlClauseNil" at controls
  have input : applyBindings assignment ((patternRules index pattern)[0]'(by simp [patternRules])).left =
      node "MlMatchOne" [patternId index, value actual, code body, environment captured, continuation] := by
    change applyBindings assignment (node "MlMatchOne"
      [patternId index, (patternAt pattern 0).term, hole "body", hole "environment", hole "continuation"]) = _
    simp only [apply_node, List.map_cons, List.map_nil, apply_patternId, slotsSame, instanceSame,
      controls.1, controls.2.1, controls.2.2.1]
  obtain ⟨readBindings, readMatch, output⟩ := match_one_rule_readback pattern index actual body captured continuation assignment input
  have same : readBindings = boundValues := Option.some.inj (readMatch.symm.trans matched)
  exact ⟨assignment, input, same ▸ output⟩

theorem try_clause_rule_complete (pattern : OCaml.MatchPattern) (index : Nat) (actual : OCaml.Value)
    (boundValues : List OCaml.Value) (body : OCaml.Code) (later : Pattern) (captured : OCaml.Environment)
    (continuation : Pattern) (matched : OCaml.matchPattern pattern actual = some boundValues) :
    ∃ assignment : Bindings,
      applyBindings assignment ((patternRules index pattern)[1]'(by simp [patternRules])).left =
        node "MlTryClause" [patternId index, value actual, code body, later, environment captured, continuation] ∧
      applyBindings assignment ((patternRules index pattern)[1]'(by simp [patternRules])).right =
        node "MlEvaluate" [code body, environment (OCaml.extend captured boundValues), continuation] := by
  obtain ⟨captures, _, instanceSame⟩ := pattern_instance_construct pattern 0 actual boundValues matched
  let assignment := patternRequestBindings captures (code body) (environment captured) continuation later
  have slotsSame := pattern_slot_agreement pattern 0 assignment (captureBindings captures)
    (fun slot _ _ => request_pattern_hole captures _ _ _ _ slot)
  have controls := request_control_fields captures (code body) (environment captured) continuation later
  change applyBindings assignment (hole "body") = code body ∧
    applyBindings assignment (hole "environment") = environment captured ∧
    applyBindings assignment (hole "continuation") = continuation ∧
    applyBindings assignment (hole "later") = later at controls
  have input : applyBindings assignment ((patternRules index pattern)[1]'(by simp [patternRules])).left =
      node "MlTryClause" [patternId index, value actual, code body, later, environment captured, continuation] := by
    change applyBindings assignment (node "MlTryClause"
      [patternId index, (patternAt pattern 0).term, hole "body", hole "later", hole "environment", hole "continuation"]) = _
    simp only [apply_node, List.map_cons, List.map_nil, apply_patternId, slotsSame, instanceSame,
      controls.1, controls.2.1, controls.2.2.1, controls.2.2.2]
  obtain ⟨readBindings, readMatch, output⟩ := try_clause_rule_readback pattern index actual body later captured continuation assignment input
  have same : readBindings = boundValues := Option.some.inj (readMatch.symm.trans matched)
  exact ⟨assignment, input, same ▸ output⟩

theorem match_one_rule_iff (pattern : OCaml.MatchPattern) (index : Nat) (actual : OCaml.Value)
    (body : OCaml.Code) (captured : OCaml.Environment) (continuation target : Pattern) :
    (∃ assignment : Bindings,
      applyBindings assignment ((patternRules index pattern)[0]'(by simp [patternRules])).left =
        node "MlMatchOne" [patternId index, value actual, code body, environment captured, continuation] ∧
      applyBindings assignment ((patternRules index pattern)[0]'(by simp [patternRules])).right = target) ↔
    ∃ boundValues, OCaml.matchPattern pattern actual = some boundValues ∧
      target = node "MlEvaluate" [code body, environment (OCaml.extend captured boundValues), continuation] := by
  constructor
  · rintro ⟨assignment, input, output⟩
    obtain ⟨boundValues, matched, result⟩ :=
      match_one_rule_readback pattern index actual body captured continuation assignment input
    exact ⟨boundValues, matched, output.symm.trans result⟩
  · rintro ⟨boundValues, matched, rfl⟩
    exact match_one_rule_complete pattern index actual boundValues body captured continuation matched

theorem try_clause_rule_iff (pattern : OCaml.MatchPattern) (index : Nat) (actual : OCaml.Value)
    (body : OCaml.Code) (later : Pattern) (captured : OCaml.Environment) (continuation target : Pattern) :
    (∃ assignment : Bindings,
      applyBindings assignment ((patternRules index pattern)[1]'(by simp [patternRules])).left =
        node "MlTryClause" [patternId index, value actual, code body, later, environment captured, continuation] ∧
      applyBindings assignment ((patternRules index pattern)[1]'(by simp [patternRules])).right = target) ↔
    ∃ boundValues, OCaml.matchPattern pattern actual = some boundValues ∧
      target = node "MlEvaluate" [code body, environment (OCaml.extend captured boundValues), continuation] := by
  constructor
  · rintro ⟨assignment, input, output⟩
    obtain ⟨boundValues, matched, result⟩ :=
      try_clause_rule_readback pattern index actual body later captured continuation assignment input
    exact ⟨boundValues, matched, output.symm.trans result⟩
  · rintro ⟨boundValues, matched, rfl⟩
    exact try_clause_rule_complete pattern index actual boundValues body later captured continuation matched

#print axioms match_one_rule_complete
#print axioms try_clause_rule_complete
#print axioms match_one_rule_iff
#print axioms try_clause_rule_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
