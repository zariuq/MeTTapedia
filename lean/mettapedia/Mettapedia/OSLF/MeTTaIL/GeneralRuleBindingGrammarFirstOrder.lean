import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProjectionTotality

/-! Binder-free grammar traversal preserves the ambient binder context.
Consequently either omitted-binding inference route gives nullary captures
for a premise-free binder-free rule, including explicit occurrence rows. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

open Syntax Match RuleBinding

private theorem member_binderFree {patterns : List Pattern} {pattern : Pattern}
    (free : binderFreeList patterns = true) (member : pattern ∈ patterns) : binderFree pattern = true := by
  induction patterns with
  | nil => cases member
  | cons first rest ih =>
    have parts := Bool.and_eq_true_iff.mp free
    rcases List.mem_cons.mp member with rfl | later
    · exact parts.1
    · exact ih parts.2 later

theorem contextAt?_binderFree (language : LanguageDef) (context : List (String × TypeExpr))
    (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern) (address : List Nat)
    (localBound : List TypeExpr) (result : TypeExpr)
    (free : binderFree pattern = true)
    (read : contextAt? language context bound expected pattern address = some (localBound, result)) :
    localBound = bound := by
  induction address generalizing expected pattern with
  | nil =>
    cases pattern <;> simp [contextAt?] at read
    exact read.1.symm
  | cons index rest ih =>
    cases pattern with
    | fvar name => simp [contextAt?] at read
    | bvar index => simp [contextAt?] at read
    | lambda name body => simp [binderFree] at free
    | multiLambda arity names body => simp [binderFree] at free
    | subst body replacement => simp [binderFree] at free
    | apply label arguments =>
      simp only [contextAt?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
      obtain ⟨declaration, _, _, _, _, _, parameter, _, argument, atArgument, _, _, argumentType, _, read⟩ := read
      exact ih argumentType argument
        (member_binderFree free (List.mem_of_getElem? atArgument)) read
    | collection kind elements tail =>
      simp only [contextAt?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
      obtain ⟨elementType, _, read⟩ := read
      split at read
      · simp only [Option.bind_eq_some_iff] at read
        obtain ⟨element, atElement, read⟩ := read
        exact ih elementType element (member_binderFree free (List.mem_of_getElem? atElement)) read
      · split at read
        · exact (congrArg Prod.fst (Option.some.inj read)).symm
        · contradiction

private theorem traverse_property {α β : Type} (compile : α → Option β) (property : β → Prop)
    (inputs : List α) (outputs : List β)
    (each : ∀ input ∈ inputs, ∀ output, compile input = some output → property output)
    (compiled : inputs.mapM compile = some outputs) : ∀ output ∈ outputs, property output := by
  induction inputs generalizing outputs with
  | nil =>
    have empty : outputs = [] := by simpa using compiled.symm
    subst outputs
    simp
  | cons input rest ih =>
    rw [List.mapM_cons] at compiled
    cases first : compile input with
    | none => simp [first] at compiled
    | some output =>
      cases tail : rest.mapM compile with
      | none => simp [first, tail] at compiled
      | some results =>
        have same : output :: results = outputs := by simpa [first, tail] using compiled
        subst outputs
        intro value member
        rcases List.mem_cons.mp member with rfl | later
        · exact each input List.mem_cons_self value first
        · exact ih results (fun child present => each child (List.mem_cons_of_mem input present)) tail value later

theorem inspect_binderFree (language : LanguageDef) (context : List (String × TypeExpr))
    (site : RulePatternSite) (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern)
    (rows : List Occurrence) (free : binderFree pattern = true)
    (read : inspect language context site bound expected pattern = some rows) :
    ∀ row ∈ rows, row.bound = bound := by
  apply traverse_property _ (fun row : Occurrence => row.bound = bound) _ rows _ read
  intro address _ row read
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at read
  obtain ⟨⟨localBound, result⟩, found, same⟩ := read
  change some (Occurrence.mk address localBound result) = some row at same
  cases Option.some.inj same
  exact contextAt?_binderFree language context bound expected pattern address.path localBound result free found

theorem specification_zero (context : List (String × TypeExpr)) (rows : List Occurrence)
    (empty : ∀ row ∈ rows, row.bound = []) :
    GeneralPremise.checkZeroDependencies (specification context rows) = true := by
  apply List.all_eq_true.mpr
  intro entry member
  obtain ⟨declared, _, rfl⟩ := List.mem_map.mp member
  change ((rows.find? fun row => row.name == declared.1).map Occurrence.bound |>.getD []).isEmpty = true
  cases found : rows.find? (fun row => row.name == declared.1) with
  | none => rfl
  | some row =>
    have noBinders := empty row (List.mem_of_find?_eq_some found)
    simp [noBinders]

theorem infer_binderFree_zero (language : LanguageDef) (rule : RewriteRule) (result : Inference)
    (left : binderFree rule.left = true) (right : binderFree rule.right = true)
    (premises : rule.premises = []) (inferred : infer? language rule = some result) :
    GeneralPremise.checkZeroDependencies result.spec = true := by
  simp only [infer?, Option.bind_eq_bind, Option.bind_eq_some_iff] at inferred
  obtain ⟨expected, _, leftRows, leftRead, rightRows, rightRead, premiseRows, premisesRead, inferred⟩ := inferred
  rw [premises] at premisesRead
  change some [] = some premiseRows at premisesRead
  cases Option.some.inj premisesRead
  split at inferred
  · cases Option.some.inj inferred
    apply specification_zero
    intro row member
    rcases List.mem_append.mp (by simpa using member) with fromLeft | fromRight
    · exact inspect_binderFree language rule.typeContext .left [] expected rule.left leftRows left leftRead row fromLeft
    · exact inspect_binderFree language rule.typeContext .right [] expected rule.right rightRows right rightRead row fromRight
  · contradiction

example (language : LanguageDef) :
    contextAt? language [] [] (.base "Proc") (.fvar "P") [] = some ([], .base "Proc") := by
  simp [contextAt?]

example (language : LanguageDef) :
    contextAt? language [] [] (.arrow (.base "Name") (.base "Proc"))
      (.lambda "x" (.fvar "P")) [0] ≠ some ([], .base "Proc") := by
  simp [contextAt?]

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingGrammar

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference

open Syntax Match RuleBinding

theorem compile_binderFree_zero (language : LanguageDef) (rule : RewriteRule) (binding : BindingPlan)
    (omitted : rule.bindings = none) (left : binderFree rule.left = true) (right : binderFree rule.right = true)
    (premises : rule.premises = []) (compiled : compile? language rule = some binding) :
    GeneralPremise.checkZeroDependencies binding.spec = true := by
  rcases compile_origin compiled with authored | root | grammar
  · rw [omitted] at authored
    cases authored.2
  · rw [root.2.2.1]
    simp [GeneralPremise.checkZeroDependencies, inferredSpec]
  · obtain ⟨_, result, inferred, _, spec⟩ := grammar
    rw [spec]
    exact GeneralRuleBindingGrammar.infer_binderFree_zero language rule result left right premises inferred

#print axioms compile_binderFree_zero

end Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
