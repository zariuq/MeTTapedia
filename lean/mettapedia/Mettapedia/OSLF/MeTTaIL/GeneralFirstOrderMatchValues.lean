import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderTyping

/-! Captures of a first-order match against a first-order subject remain
first-order. A successful merge introduces no value outside its two input
binding maps. This is independent of any language's term codec. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match MatchSpec

mutual
theorem matched_values_firstOrder {schema target : Pattern} {bindings : Bindings}
    (shape : FirstOrder schema) (subject : FirstOrder target) (matched : MatchRel schema target bindings) :
    ∀ entry ∈ bindings, FirstOrder entry.2 := by
  cases shape with
  | metavariable name =>
      cases matched
      intro entry member
      cases List.mem_singleton.mp member
      exact subject
  | constructor label schemas shapes =>
      cases matched with
      | apply arguments _ =>
          cases subject with
          | constructor _ _ subjects => exact matched_arguments_values_firstOrder shapes subjects arguments
termination_by sizeOf schema

theorem matched_arguments_values_firstOrder {schemas targets : List Pattern} {bindings : Bindings}
    (shapes : ∀ schema ∈ schemas, FirstOrder schema)
    (subjects : ∀ target ∈ targets, FirstOrder target) (matched : MatchArgsRel schemas targets bindings) :
    ∀ entry ∈ bindings, FirstOrder entry.2 := by
  cases schemas with
  | nil =>
      cases matched
      intro entry member
      cases member
  | cons schema schemas =>
      cases matched with
      | cons first rest merged =>
          have head := matched_values_firstOrder (shapes schema (by simp)) (subjects _ (by simp)) first
          have tail := matched_arguments_values_firstOrder
            (fun child member => shapes child (List.mem_cons_of_mem _ member))
            (fun child member => subjects child (List.mem_cons_of_mem _ member)) rest
          intro entry member
          exact (List.mem_append.mp (merge_members merged member)).elim (head entry) (tail entry)
termination_by sizeOf schemas
end

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
