import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternRuleReadback
import Mettapedia.OSLF.MeTTaIL.GeneralVectorBindingAdmission

/-! Compiled OCaml patterns use only ordinary constructors, metavariables
and fixed vectors, so the shared scoped root readout applies to their rules.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

theorem node_vector (label : String) (arguments : List Pattern)
    (children : ∀ item ∈ arguments, VectorFirstOrder item) : VectorFirstOrder (node label arguments) :=
  .constructor label arguments children

theorem digits_vector (number : Nat) : VectorFirstOrder (digits number) := by
  apply VectorFirstOrder.vector
  intro item member
  obtain ⟨digit, _, rfl⟩ := List.mem_map.mp member
  exact .constructor _ [] (by simp)

theorem code_vector (number : Nat) : VectorFirstOrder (code number) := by
  apply node_vector
  simpa only [List.mem_singleton, forall_eq] using digits_vector number

theorem tag_vector (typeId constructor : Nat) : VectorFirstOrder (tag typeId constructor) := by
  apply node_vector
  intro item member
  rcases List.mem_cons.mp member with rfl | member
  · exact digits_vector typeId
  · have same := List.mem_singleton.mp member
    exact same ▸ digits_vector constructor

theorem linked_vector (cons nil : String) (items : List Pattern)
    (children : ∀ item ∈ items, VectorFirstOrder item) : VectorFirstOrder (linked cons nil items) := by
  induction items with
  | nil => exact .constructor nil [] (by simp)
  | cons first rest ih =>
      apply node_vector
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact children _ List.mem_cons_self
      · have same := List.mem_singleton.mp member
        subst item
        exact ih (fun child present => children child (List.mem_cons_of_mem _ present))

theorem literal_vector (datum : OCaml.Literal) : VectorFirstOrder (literal datum) := by
  cases datum with
  | integer number =>
      apply node_vector
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact .constructor _ [] (by simp)
      · have same := List.mem_singleton.mp member
        exact same ▸ digits_vector number.natAbs
  | boolean choice => exact .constructor _ [] (by simp)
  | unit => exact .constructor _ [] (by simp)
  | nil => exact .constructor _ [] (by simp)
  | string bytes =>
      apply node_vector
      intro item member
      have same := List.mem_singleton.mp member
      subst item
      apply VectorFirstOrder.vector
      intro byte member
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      apply node_vector
      intro nibble present
      rcases List.mem_cons.mp present with rfl | present
      · exact .constructor _ [] (by simp)
      · have same := List.mem_singleton.mp present
        subst nibble
        exact .constructor _ [] (by simp)

theorem pattern_vector (pattern : OCaml.MatchPattern) : ∀ start,
    VectorFirstOrder (patternAt pattern start).term ∧
      ∀ item ∈ (patternAt pattern start).bindings, VectorFirstOrder item := by
  refine OCaml.MatchPattern.rec
    (motive_1 := fun pattern => ∀ start, VectorFirstOrder (patternAt pattern start).term ∧
      ∀ item ∈ (patternAt pattern start).bindings, VectorFirstOrder item)
    (motive_2 := fun patterns => ∀ start,
      (∀ item ∈ (fieldsAt patterns start).1, VectorFirstOrder item) ∧
      (∀ item ∈ (fieldsAt patterns start).2, VectorFirstOrder item))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pattern
  · intro start
    exact ⟨.metavariable _, by simp only [patternAt_bind, List.mem_singleton]; rintro item rfl; exact .metavariable _⟩
  · intro start
    exact ⟨.metavariable _, by simp only [patternAt_wildcard, List.not_mem_nil, false_implies, implies_true]⟩
  · intro datum start
    exact ⟨literal_vector datum, by simp only [patternAt_literal, List.not_mem_nil, false_implies, implies_true]⟩
  · intro fields ih start
    obtain ⟨inputs, outputs⟩ := ih start
    refine ⟨?_, outputs⟩
    apply node_vector
    intro item member
    have same := List.mem_singleton.mp member
    exact same ▸ linked_vector _ _ _ inputs
  · intro head tail headIH tailIH start
    obtain ⟨headShape, headOutputs⟩ := headIH start
    obtain ⟨tailShape, tailOutputs⟩ := tailIH (patternAfter head start)
    refine ⟨?_, ?_⟩
    · apply node_vector
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact headShape
      · have same := List.mem_singleton.mp member
        exact same ▸ tailShape
    · intro item member
      rcases List.mem_append.mp member with first | rest
      · exact headOutputs item first
      · exact tailOutputs item rest
  · intro typeId constructor fields ih start
    obtain ⟨inputs, outputs⟩ := ih start
    refine ⟨?_, outputs⟩
    apply node_vector
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact tag_vector typeId constructor
    · have same := List.mem_singleton.mp member
      exact same ▸ linked_vector _ _ _ inputs
  · intro start
    exact ⟨by simp [fieldsAt_nil], by simp [fieldsAt_nil]⟩
  · intro first rest firstIH restIH start
    obtain ⟨input, output⟩ := firstIH start
    obtain ⟨inputs, outputs⟩ := restIH (patternAfter first start)
    constructor
    · intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact input
      · exact inputs item member
    · intro item member
      rcases List.mem_append.mp member with here | later
      · exact output item here
      · exact outputs item later

theorem extend_vector (bindings : List Pattern) (captured : Pattern)
    (children : ∀ item ∈ bindings, VectorFirstOrder item) (tail : VectorFirstOrder captured) :
    VectorFirstOrder (extend bindings captured) := by
  induction bindings generalizing captured with
  | nil => exact tail
  | cons first rest ih =>
      apply ih _ (fun item member => children item (List.mem_cons_of_mem first member))
      apply node_vector
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact children _ List.mem_cons_self
      · have same := List.mem_singleton.mp member
        exact same ▸ tail

theorem pattern_rule_shapes (pattern : OCaml.MatchPattern) (index : Nat) (row : RewriteRule)
    (member : row ∈ patternRules index pattern) :
    VectorFirstOrder row.left ∧ VectorFirstOrder row.right ∧ row.premises = [] := by
  have termShape := (pattern_vector pattern 0).1
  have bindingsShape := (pattern_vector pattern 0).2
  have idShape : VectorFirstOrder (patternId index) := by
    apply node_vector
    intro item present
    have same := List.mem_singleton.mp present
    exact same ▸ digits_vector index
  simp only [patternRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals
    refine ⟨?_, ?_, rfl⟩
    · apply node_vector
      intro item present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      repeat' first | rcases present with present | present
      all_goals first | exact idShape | exact termShape | exact .metavariable _
    · apply node_vector
      intro item present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl
      · exact .metavariable _
      · exact extend_vector _ _ bindingsShape (.metavariable _)
      · exact .metavariable _

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
