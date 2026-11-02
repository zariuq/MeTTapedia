import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlInstructionCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlValueReading

/-! Indexed environment lookup preserves the source position and value.
The actual compiled prefix remains an ordinary constructor pattern, with
one fresh skip capture for each preceding environment entry.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

def skipName (index : Nat) : String := "ml:" ++ ("skip:" ++ toString index)
def skipBindings (items : List OCaml.Value) : Bindings := items.zipIdx.map fun (actual, index) => (skipName index, value actual)

theorem skipName_injective : Function.Injective skipName := by
  intro first second same
  simp only [skipName, String.append_right_inj] at same
  exact Nat.repr_injective same

theorem skip_bindings_lookup (items : List OCaml.Value) (index : Nat) (actual : OCaml.Value)
    (found : items[index]? = some actual) : (skipBindings items).lookup (skipName index) = some (value actual) := by
  have member : (skipName index, value actual) ∈ skipBindings items :=
    List.mem_map.mpr ⟨(actual, index), List.mk_mem_zipIdx_iff_getElem?.mpr found, rfl⟩
  have allSame : ∀ entry ∈ skipBindings items, entry.1 = skipName index → entry.2 = value actual := by
    intro entry present same
    obtain ⟨⟨other, slot⟩, indexed, rfl⟩ := List.mem_map.mp present
    have slotSame := skipName_injective same
    subst slot
    have sourceSame := Option.some.inj ((List.mk_mem_zipIdx_iff_getElem?.mp indexed).symm.trans found)
    exact congrArg value sourceSame
  unfold Bindings.lookup
  cases selected : (skipBindings items).find? (fun entry => entry.1 == skipName index) with
  | none =>
      have fails := List.find?_eq_none.mp selected _ member
      exact False.elim (fails (by simp))
  | some entry =>
      have present := List.mem_of_find?_eq_some selected
      have nameSame := beq_iff_eq.mp (List.find?_some (p := fun entry : String × Pattern => entry.1 == skipName index) selected)
      simp only [Option.map_some]
      exact congrArg some (allSame entry present nameSame)

def variableBindings (before : List OCaml.Value) (actual : OCaml.Value) (after : List OCaml.Value) (rest : Pattern) : Bindings :=
  [("ml:variable", value actual), ("ml:tail", environment after), ("ml:continuation", rest)] ++ skipBindings before

theorem variable_skip_lookup (before : List OCaml.Value) (actual : OCaml.Value) (after : List OCaml.Value) (rest : Pattern)
    (index : Nat) (item : OCaml.Value) (found : before[index]? = some item) :
    applyBindings (variableBindings before actual after rest) (hole ("skip:" ++ toString index)) = value item := by
  have different (name : String) (head : name.toByteArray.data[3]? ≠ some (115 : UInt8)) : name ≠ skipName index := by
    intro same
    apply head
    rw [same]
    simp only [skipName, String.toByteArray_append, ByteArray.data_append]
    change (#[109, 108, 58] ++ (#[115, 107, 105, 112, 58] ++ (toString index).toByteArray.data))[3]? = _
    simp
  have noVariable := beq_eq_false_iff_ne.mpr (different "ml:variable" (by decide))
  have noTail := beq_eq_false_iff_ne.mpr (different "ml:tail" (by decide))
  have noRest := beq_eq_false_iff_ne.mpr (different "ml:continuation" (by decide))
  have read := skip_bindings_lookup before index item found
  change applyBindings _ (.fvar (skipName index)) = _
  rw [GeneralFirstOrderProjection.apply_variable]
  simp only [variableBindings, Bindings.lookup, List.cons_append, List.nil_append, List.find?_cons,
    noVariable, noTail, noRest]
  change ((skipBindings before).lookup (skipName index)).getD _ = _
  rw [read]
  rfl

theorem environment_prefix (before : List OCaml.Value) (actual : OCaml.Value) (after : List OCaml.Value) :
    environment (before ++ actual :: after) =
      extend (before.map value).reverse (node "MlEnvironmentCons" [value actual, environment after]) := by
  rw [environment_append]
  simp only [extend, List.foldl_reverse, List.foldr_map]
  rfl

theorem variable_prefix_instance (before : List OCaml.Value) (actual : OCaml.Value) (after : List OCaml.Value) (rest : Pattern) :
    applyBindings (variableBindings before actual after rest)
      (extend (((List.range before.length).map fun skip => hole ("skip:" ++ toString skip)).reverse)
        (node "MlEnvironmentCons" [hole "variable", hole "tail"])) = environment (before ++ actual :: after) := by
  rw [apply_extend, environment_prefix]
  have mapped : (((List.range before.length).map fun skip => hole ("skip:" ++ toString skip)).reverse).map
      (applyBindings (variableBindings before actual after rest)) = (before.map value).reverse := by
    rw [List.map_reverse, List.map_map]
    apply congrArg List.reverse
    apply List.ext_getElem?
    intro index
    by_cases inside : index < before.length
    · have sourceAt := List.getElem?_eq_getElem inside
      simp only [List.getElem?_map, List.getElem?_range, inside, sourceAt, Option.map_some, Function.comp_apply]
      exact congrArg some (variable_skip_lookup before actual after rest index before[index] sourceAt)
    · simp [inside]
  rw [mapped]
  congr 1
  simp [apply_node, variableBindings, hole, applyBindings]

#print axioms variable_prefix_instance

theorem environment_lookup_split (items : List OCaml.Value) (index : Nat) (actual : OCaml.Value)
    (found : items[index]? = some actual) :
    items = items.take index ++ actual :: items.drop (index + 1) ∧ (items.take index).length = index := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have same := (List.getElem?_eq_some_iff.mp found).2
  constructor
  · conv_lhs => rw [← List.take_append_drop index items]
    rw [List.drop_eq_getElem_cons inside, same]
  · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt inside)]

theorem variable_instruction_instance (pool : List OCaml.MatchPattern) (reference index : Nat)
    (items : OCaml.Environment) (actual : OCaml.Value) (rest : Pattern) (row : RewriteRule)
    (found : items[index]? = some actual)
    (formed : compileInstruction? pool reference (.variable index) = some row) :
    ∃ assignment, applyBindings assignment row.left = node "MlEvaluate" [code reference, environment items, rest] ∧
      applyBindings assignment row.right = node "MlReturn" [value actual, rest] := by
  obtain ⟨split, length⟩ := environment_lookup_split items index actual found
  let assignment := variableBindings (items.take index) actual (items.drop (index + 1)) rest
  have prefixInstance := variable_prefix_instance (items.take index) actual (items.drop (index + 1)) rest
  rw [length, ← split] at prefixInstance
  refine ⟨assignment, ?_, ?_⟩
  · simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
    cases formed
    simp only [rule, apply_node, List.map_cons, List.map_nil, apply_code]
    rw [show applyBindings assignment (extend (((List.range index).map fun skip => hole ("skip:" ++ toString skip)).reverse)
        (node "MlEnvironmentCons" [hole "variable", hole "tail"])) = environment items from prefixInstance]
    simp [assignment, variableBindings, hole, applyBindings]
  · simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
    cases formed
    simp [assignment, variableBindings, rule, apply_node, hole, applyBindings]

theorem variable_plan_step {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {row : GeneralExecutionAdmission.RulePlan} {ordinal : Nat}
    {program : OCaml.Program} {reference index : Nat} {items : OCaml.Environment} {actual : OCaml.Value}
    {rest : OCaml.Continuation} {encodedRest : Pattern}
    (position : (GeneralExecutionAdmission.compile snapshot permissions).rules[ordinal]? = some row)
    (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames)
    (declared : program.instruction? reference = some (.variable index))
    (found : items[index]? = some actual)
    (formed : compileInstruction? (patterns program) reference (.variable index) = some row.authored)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    OCaml.machineStep program (.evaluate reference items rest) = .ok (some (.returned actual rest)) ∧
      ∃ trace captured, GeneralPremise.RootFiring
        (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)) [] (.base "MlConfig")
        (node "MlEvaluate" [code reference, environment items, encodedRest]) ordinal trace captured captured []
        (node "MlReturn" [value actual, encodedRest]) := by
  refine ⟨?_, ?_⟩
  · simp only [OCaml.machineStep, OCaml.evaluateInstruction, declared, found, Except.map]
    rfl
  · obtain ⟨assignment, input, output⟩ := variable_instruction_instance (patterns program) reference index items actual encodedRest row.authored found formed
    apply instruction_plan_coverage (pool := patterns program) (sourceState := .evaluate reference items rest)
      (targetState := .returned actual rest) position terms types formed
    · simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    · simp only [state?, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    · exact input
    · exact output

#print axioms variable_instruction_instance
#print axioms variable_plan_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
