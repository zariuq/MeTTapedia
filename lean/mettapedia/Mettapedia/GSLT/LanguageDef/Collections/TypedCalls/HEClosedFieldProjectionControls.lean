import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEClosedFieldProjection

/-! # Closed field projection: shared variables, exact capture, and refusals -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEClosedFieldProjection.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open ShapeTyping StaticEvidence InferredTypeSets
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation
open Spec.Bindings.ScopeObservation

def listOf {V : Type} (element : Ty V) : Ty V := .app [.sym "List", element]
def pairOf {V : Type} (left right : Ty V) : Ty V := .app [.sym "Pair", left, right]

theorem open_field_closes_from_the_range :
    inferClosedField (listOf (.var "a")) (listOf (.sym "Number")) (.var "a") =
      some (.sym "Number") := by cbv

theorem open_recursive_field_closes_from_the_range :
    inferClosedField (listOf (.var "a")) (listOf (.sym "Number")) (listOf (.var "a")) =
      some (listOf (.sym "Number")) := by cbv

theorem unmentioned_field_variable_is_not_invented :
    inferClosedField (listOf (.var "a")) (listOf (.sym "Number")) (.var "other") = none := by cbv

theorem shared_range_variables_cannot_choose_two_types :
    inferClosedField (pairOf (.var "a") (.var "a")) (pairOf (.sym "Number") (.sym "String"))
      (.var "a") = none := by cbv

/-- The static result continues to hold under every runtime valuation;
unmentioned variables may be assigned arbitrarily. -/
theorem all_refinements_keep_the_element (assignment : String → Ty Empty)
    (agrees : (listOf (.var "a")).bind assignment = listOf (.sym "Number")) :
    assignment "a" = .sym "Number" :=
  inferred_field_fixed (listOf (.var "a")) (.var "a") (listOf (.sym "Number")) (.sym "Number")
    open_field_closes_from_the_range assignment agrees

theorem cons_tail_inferred (first second : Int) (rest : List Int) :
    StaticAt (stamp ShapeTyping.Controls.decls (ShapeTyping.Controls.numList (second :: rest)))
      (listOf (.sym "Number")) := by
  apply inferred_constructor_field ShapeTyping.Controls.decls "Cons" ShapeTyping.Controls.consRow
    [.var "x", listOf (.var "x")] (listOf (.var "x")) (listOf (.var "x"))
    (listOf (.sym "Number")) (listOf (.sym "Number"))
    (by decide) [.grounded (.int first), ShapeTyping.Controls.numList (second :: rest)] 1
    (ShapeTyping.Controls.numList (second :: rest)) rfl rfl
    (by intro value; rfl) (by cbv)
  have typed := ShapeTyping.Controls.list_stamp first (second :: rest)
  change Typable (stamp ShapeTyping.Controls.decls (ShapeTyping.Controls.numList (first :: second :: rest))) _
  rw [typed]
  exact ⟨{ShapeTyping.Controls.glist (ShapeTyping.Controls.gc "Number")}, by simp, rfl⟩

def markedTail : Entry.Value := .expression .held
  [.symbol "Cons", .grounded (.int 7), .symbol "Nil"]

theorem source_capture_retains_the_ready_field (policy readingPolicy : Policy) :
    let after := HEFreshSyntaxBinding.bindFrame policy Frame.empty "tail" markedTail
      (by simp [Frame.empty, specBindingVars, Bindings.empty])
      (by simp [markedTail, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList])
    Entry.Value.UnifyListRel policy.rebuilding Frame.empty.environment
      [.symbol "Cons", .grounded (.int 5), markedTail]
      [.symbol "Cons", .grounded (.int 5), .var "tail"] after.environment ∧
      after.read readingPolicy (.var "tail") = markedTail := by
  refine ⟨?_, HEFreshSyntaxBinding.bound_read policy Frame.empty "tail" markedTail _
    (by simp [markedTail, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]) readingPolicy⟩
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Entry.Value.erase, Entry.Value.ofAtom] using source_field_capture policy Frame.empty "tail" markedTail
    (by simp [Frame.empty, specBindingVars, Bindings.empty])
    (by simp [markedTail, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList])
    [.symbol "Cons", .grounded (.int 5)] []

theorem erasing_before_capture_loses_the_mark : Entry.Value.ofAtom markedTail.erase ≠ markedTail := by
  simp [markedTail, Entry.Value.ofAtom, Entry.Value.erase]

/-- Positive nominal metadata alone cannot license field extraction: the
same real source argument checker rejects the shared Number/String row. -/
theorem nominal_parent_annotation_does_not_check_its_fields :
    getAnnotatedTypes HEShownBuildCounterexample.selfAnnotatedSource HEShownBuildCounterexample.built =
      [HEShownBuildCounterexample.range] ∧
    NativeTypeViews.sourceArgs HEConstructorDeclarationGuard.Controls.sourceOps HEConstructorDeclarationGuard.Controls.sourceReads
      [.var "t", .var "t"] [.grounded (.int 1), .grounded (.string "wrong-field")]
      Atom.var = none := by cbv

/-- Independently checking each field would lose the same-row constraint.
The real ordered loop refuses even though each separate check succeeds. -/
theorem independent_fields_are_not_a_shared_constructor_check :
    (NativeTypeViews.sourceArgs HEConstructorDeclarationGuard.Controls.sourceOps HEConstructorDeclarationGuard.Controls.sourceReads
      [.var "t"] [.grounded (.int 1)] Atom.var).isSome = true ∧
    (NativeTypeViews.sourceArgs HEConstructorDeclarationGuard.Controls.sourceOps HEConstructorDeclarationGuard.Controls.sourceReads
      [.var "t"] [.grounded (.string "wrong-field")] Atom.var).isSome = true ∧
    NativeTypeViews.sourceArgs HEConstructorDeclarationGuard.Controls.sourceOps HEConstructorDeclarationGuard.Controls.sourceReads
      [.var "t", .var "t"] [.grounded (.int 1), .grounded (.string "wrong-field")]
      Atom.var = none := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEClosedFieldProjection.Controls
