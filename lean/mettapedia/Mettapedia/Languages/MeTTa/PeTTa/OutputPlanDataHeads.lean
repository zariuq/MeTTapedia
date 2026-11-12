import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanCompiler

/-!
# Static data terms for the source plain-list-head case

The grammar excludes calls and control forms and leaves variable leaves
uninterpreted. A variable in head position needs runtime dispatch instead.
These rules justify the compiler's static region; they do not define the
source language or complete the general data-term evaluation relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive DataTree (context : Context) : Atom → Prop where
  | var (name : String) : DataTree context (.var name)
  | symbol (name : String) : DataTree context (.symbol name)
  | grounded (value : OSLFCore.GroundedValue) : DataTree context (.grounded value)
  | empty : DataTree context (.expression [])
  | constructor (head : String) (rest : List Atom)
      (notCallable : context.callable head = false) (notControl : controlHead head = false)
      (children : ∀ item ∈ rest, DataTree context item) : DataTree context (.expression (.symbol head :: rest))
  | listHead (head rest : List Atom) (first : DataTree context (.expression head))
      (children : ∀ item ∈ rest, DataTree context item) : DataTree context (.expression (.expression head :: rest))
  | scalarHead (head : OSLFCore.GroundedValue) (rest : List Atom)
      (children : ∀ item ∈ rest, DataTree context item) : DataTree context (.expression (.grounded head :: rest))

theorem staticDataList_iff (context : Context) (items : List Atom) :
    staticDataList context items = true ↔ ∀ item ∈ items, staticData context item = true := by
  induction items with
  | nil => simp [staticDataList]
  | cons first rest ih => simp only [staticDataList,Bool.and_eq_true,ih,List.mem_cons,forall_eq_or_imp]

theorem DataTree.computed {context : Context} {term : Atom} (tree : DataTree context term) :
    staticData context term = true := by
  induction tree with
  | var | symbol | grounded | empty => rfl
  | constructor head rest notCallable notControl children ih =>
      simp only [staticData,notCallable,notControl,Bool.not_false,Bool.true_and]
      exact (staticDataList_iff context rest).mpr ih
  | listHead head rest first children firstIH restIH =>
      simp only [staticData,firstIH,Bool.true_and]
      exact (staticDataList_iff context rest).mpr restIH
  | scalarHead head rest children ih => exact (staticDataList_iff context rest).mpr ih

theorem staticData_source (context : Context) : ∀ term : Atom,
    staticData context term = true → DataTree context term
  | .var name => by intro _; exact .var name
  | .symbol name => by intro _; exact .symbol name
  | .grounded value => by intro _; exact .grounded value
  | .expression [] => by intro _; exact .empty
  | .expression (.symbol head :: rest) => by
      intro normal
      simp only [staticData,Bool.and_eq_true,Bool.not_eq_true'] at normal
      exact .constructor head rest normal.1.1 normal.1.2 (list rest normal.2)
  | .expression (.expression head :: rest) => by
      intro normal
      have parts : staticData context (.expression head) = true ∧ staticDataList context rest = true := by
        simpa only [staticData,Bool.and_eq_true] using normal
      exact .listHead head rest (staticData_source context (.expression head) parts.1) (list rest parts.2)
  | .expression (.grounded head :: rest) => by
      intro normal
      exact .scalarHead head rest (list rest normal)
  | .expression (.var _ :: _) => by intro normal; cases normal
where
  list : ∀ items : List Atom,
      staticDataList context items = true → ∀ item ∈ items, DataTree context item
    | [] => by intro _ item present; cases present
    | first :: rest => by
        intro normal item present
        have parts : staticData context first = true ∧ staticDataList context rest = true := by
          simpa only [staticDataList,Bool.and_eq_true] using normal
        have firstTree := staticData_source context first parts.1
        have restTrees := list rest parts.2
        rcases List.mem_cons.mp present with rfl | later
        · exact firstTree
        · exact restTrees item later

theorem staticData_iff_source (context : Context) (term : Atom) :
    staticData context term = true ↔ DataTree context term :=
  ⟨staticData_source context term,DataTree.computed⟩

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
