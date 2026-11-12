import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanFormationDepth

/-!
# Source children visited by the output-plan compiler

Binding rows remain flat: their patterns and values use the parent's child
allowance. The omitted conditional branch contributes the existing empty
producer, whose compilation is a leaf. These are structural bounds, unrelated
to evaluator fuel or to termination of a source producer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def rowTerms : List Atom → List Atom
  | [] => []
  | first :: rest =>
      match LambdaStaging.rowParts first with
      | none => rowTerms rest
      | some (pattern,value) => pattern :: value :: rowTerms rest

theorem rowTerm_member (rows : List Atom) (row pattern value : Atom)
    (present : row ∈ rows) (parsed : LambdaStaging.rowParts row = some (pattern,value)) :
    pattern ∈ rowTerms rows ∧ value ∈ rowTerms rows := by
  induction rows with
  | nil => cases present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | later
      · simp [rowTerms,parsed]
      · have both := ih later
        cases parts : LambdaStaging.rowParts first with
        | none => simpa only [rowTerms,parts] using both
        | some pair =>
            rcases pair with ⟨left,right⟩
            simpa only [rowTerms,parts] using
              And.intro (List.mem_cons_of_mem left (List.mem_cons_of_mem right both.1))
                (List.mem_cons_of_mem left (List.mem_cons_of_mem right both.2))

theorem term_depth_bounded (items : List Atom) (term : Atom) (present : term ∈ items) :
    LambdaStaging.depthOf term ≤ LambdaStaging.depthOf.list items := by
  induction items with
  | nil => cases present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact Nat.le_max_left _ _
      · exact (ih later).trans (Nat.le_max_right _ _)

theorem source_child_smaller (items : List Atom) (term : Atom) (present : term ∈ items) :
    LambdaStaging.depthOf term < LambdaStaging.depthOf (.expression items) := by
  have bound := term_depth_bounded items term present
  simp only [LambdaStaging.depthOf]
  omega

theorem row_terms_smaller (rows : List Atom) (term : Atom) (present : term ∈ rowTerms rows) :
    LambdaStaging.depthOf term < LambdaStaging.depthOf (.expression rows) := by
  induction rows with
  | nil => cases present
  | cons first rest ih =>
      cases parts : LambdaStaging.rowParts first with
      | none =>
          have later : term ∈ rowTerms rest := by simpa only [rowTerms,parts] using present
          have small := ih later
          have outer : LambdaStaging.depthOf (.expression rest) ≤
              LambdaStaging.depthOf (.expression (first :: rest)) := by
            simp only [LambdaStaging.depthOf,LambdaStaging.depthOf.list]
            omega
          exact small.trans_le outer
      | some pair =>
          rcases pair with ⟨pattern,value⟩
          have shape := LambdaStaging.rowParts_shape parts
          simp only [rowTerms,parts,List.mem_cons] at present
          rcases present with rfl | rfl | later
          · exact (source_child_smaller [term,value] term (by simp)).trans
              (shape ▸ source_child_smaller (first :: rest) first List.mem_cons_self)
          · exact (source_child_smaller [pattern,term] term (by simp)).trans
              (shape ▸ source_child_smaller (first :: rest) first List.mem_cons_self)
          · have small := ih later
            have outer : LambdaStaging.depthOf (.expression rest) ≤
                LambdaStaging.depthOf (.expression (first :: rest)) := by
              simp only [LambdaStaging.depthOf,LambdaStaging.depthOf.list]
              omega
            exact small.trans_le outer

theorem parsed_case_member {rows : List Atom} {cases : SpaceSemantics.Cases}
    (parsed : Eval.readCases rows = some cases) :
    ∀ row ∈ cases, row.2 ∈ rowTerms rows := by
  induction rows generalizing cases with
  | nil =>
      simp only [Eval.readCases,Option.some.injEq] at parsed
      subst cases
      simp
  | cons first rest ih =>
      cases first with
      | var | symbol | grounded => cases parsed
      | expression fields =>
          cases fields with
          | nil => cases parsed
          | cons pattern extra =>
              cases extra with
              | nil => cases parsed
              | cons body tail =>
                  cases tail with
                  | cons => cases parsed
                  | nil =>
                      cases following : Eval.readCases rest with
                      | none => simp only [Eval.readCases,following] at parsed; cases parsed
                      | some parsedRest =>
                          simp only [Eval.readCases,following] at parsed
                          change some ((pattern,body) :: parsedRest) = some cases at parsed
                          have same := Option.some.inj parsed
                          subst cases
                          intro row present
                          rcases List.mem_cons.mp present with rfl | later
                          · exact (rowTerm_member _ _ _ _ List.mem_cons_self rfl).2
                          · have inside := ih following row later
                            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inside)

def Shape.children : Shape → List Atom
  | .value _ | .quoted _ | .empty | .unsupported => []
  | .binding pattern initializer body => [pattern,initializer,body]
  | .bindings rows body => body :: rowTerms rows
  | .alternatives values => values
  | .collection body | .first body => [body]
  | .condition test yes no => [test,yes,no]
  | .selection key rows => key :: rowTerms rows
  | .query location _ body => [location,body]
  | .application _ arguments | .groundedApplication _ arguments => arguments
  | .listApplication head arguments => .expression head :: arguments

theorem classified_child_bound (expression child : Atom)
    (present : child ∈ (classify expression).children) :
    LambdaStaging.depthOf child < LambdaStaging.depthOf expression ∨ child = call "empty" [] := by
  unfold classify at present
  split at present
  · simp only [Shape.children,List.not_mem_nil] at present
  · simp only [Shape.children,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl <;> exact .inl (source_child_smaller _ _ (by simp))
  · simp only [Shape.children,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl <;> exact .inl (source_child_smaller _ _ (by simp))
  · simp only [Shape.children,List.mem_cons] at present
    rcases present with rfl | row
    · exact .inl (source_child_smaller _ _ (by simp))
    · exact .inl ((row_terms_smaller _ _ row).trans (source_child_smaller _ _ (by simp)))
  · simp only [Shape.children] at present
    exact .inl ((source_child_smaller _ _ present).trans (source_child_smaller _ _ (by simp)))
  · simp only [Shape.children,List.mem_singleton] at present
    subst child
    exact .inl (source_child_smaller _ _ (by simp))
  · simp only [Shape.children,List.mem_singleton] at present
    subst child
    exact .inl (source_child_smaller _ _ (by simp))
  · simp only [Shape.children,List.not_mem_nil] at present
  · simp only [Shape.children,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl <;> exact .inl (source_child_smaller _ _ (by simp))
  · simp only [Shape.children,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl | rfl
    · exact .inl (source_child_smaller _ _ (by simp))
    · exact .inl (source_child_smaller _ _ (by simp))
    · exact .inr rfl
  · simp only [Shape.children,List.mem_cons] at present
    rcases present with rfl | row
    · exact .inl (source_child_smaller _ _ (by simp))
    · exact .inl ((row_terms_smaller _ _ row).trans (source_child_smaller _ _ (by simp)))
  · simp only [Shape.children,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl <;> exact .inl (source_child_smaller _ _ (by simp))
  · simp only [Shape.children,List.not_mem_nil] at present
  · split at present
    · simp only [Shape.children,List.not_mem_nil] at present
    · exact .inl (source_child_smaller _ _ (List.mem_cons_of_mem _ present))
  · simp only [Shape.children,List.not_mem_nil] at present
  · exact .inl (source_child_smaller _ _ (List.mem_cons_of_mem _ present))
  · simp only [Shape.children,List.mem_cons] at present
    rcases present with rfl | argument
    · exact .inl (source_child_smaller _ _ List.mem_cons_self)
    · exact .inl (source_child_smaller _ _ (List.mem_cons_of_mem _ argument))
  · simp only [Shape.children,List.not_mem_nil] at present
  · simp only [Shape.children,List.not_mem_nil] at present

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
