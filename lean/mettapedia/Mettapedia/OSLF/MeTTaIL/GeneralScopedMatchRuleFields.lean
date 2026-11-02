import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch

/-! Scoped matches use the operational rule fields at their occurrence
addresses. With the binding specification fixed, changing other owner
metadata preserves the matching judgment. Static typing is a separate check.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch

open Syntax RuleBinding ScopedRuleMatching

private theorem site_fields {first second : RewriteRule}
    (left : first.left = second.left) (right : first.right = second.right)
    (premises : first.premises = second.premises) (site : RulePatternSite) :
    sitePattern? first site = sitePattern? second site := by
  cases site <;> simp only [sitePattern?, left, right, premises]

private theorem arguments_fields {first second : RewriteRule}
    (left : first.left = second.left) (right : first.right = second.right)
    (premises : first.premises = second.premises) (spec : RuleBindingSpec)
    (name : String) (site : RulePatternSite) (path : List Nat) :
    arguments? first spec name site path = arguments? second spec name site path := by
  have occurrence : ∀ row, occurrenceDeclared first row = occurrenceDeclared second row := by
    intro row
    simp only [occurrenceDeclared, site_fields left right premises]
  simp only [arguments?, occurrence]

private theorem capture_fields {first second : RewriteRule}
    (left : first.left = second.left) (right : first.right = second.right)
    (premises : first.premises = second.premises) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (initial : Assignment) (name : String) (target : Pattern) :
    capture? first spec ambient depth site path initial name target =
      capture? second spec ambient depth site path initial name target := by
  simp only [capture?, arguments_fields left right premises]

private theorem rest_fields {first second : RewriteRule}
    (left : first.left = second.left) (right : first.right = second.right)
    (premises : first.premises = second.premises) (spec : RuleBindingSpec)
    (ambient depth : Nat) (site : RulePatternSite) (path : List Nat)
    (initial : Assignment) (name : String) (kind : CollType) (targets : List Pattern) :
    captureRest? first spec ambient depth site path initial name kind targets =
      captureRest? second spec ambient depth site path initial name kind targets := by
  simp only [captureRest?, capture_fields left right premises]

mutual
  theorem Matches.rule_fields {first second : RewriteRule}
      (left : first.left = second.left) (right : first.right = second.right)
      (premises : first.premises = second.premises)
      {spec : RuleBindingSpec} {ambient depth : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : Assignment} {schema target : Pattern}
      (matched : Matches first spec ambient site path depth initial schema target final) :
      Matches second spec ambient site path depth initial schema target final := by
    cases matched with
    | capture stored => exact .capture ((capture_fields left right premises _ _ _ _ _ _ _ _).symm.trans stored)
    | bound => exact .bound
    | constructor arguments => exact .constructor (arguments.rule_fields left right premises)
    | binder body => exact .binder (body.rule_fields left right premises)
    | binders body => exact .binders (body.rule_fields left right premises)
    | substitution body replacement => exact .substitution (body.rule_fields left right premises) (replacement.rule_fields left right premises)
    | bag nonvector bag => exact .bag nonvector (bag.rule_fields left right premises)
    | vector arguments => exact .vector (arguments.rule_fields left right premises)
    | vectorRest arguments stored =>
      exact .vectorRest (arguments.rule_fields left right premises)
        ((rest_fields left right premises _ _ _ _ _ _ _ _ _).symm.trans stored)
  termination_by sizeOf schema

  theorem Arguments.rule_fields {first second : RewriteRule}
      (left : first.left = second.left) (right : first.right = second.right)
      (premises : first.premises = second.premises)
      {spec : RuleBindingSpec} {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : Assignment} {schemas targets : List Pattern}
      (matched : Arguments first spec ambient site path depth initial index schemas targets final) :
      Arguments second spec ambient site path depth initial index schemas targets final := by
    cases matched with
    | nil => exact .nil
    | cons head tail => exact .cons (head.rule_fields left right premises) (tail.rule_fields left right premises)
  termination_by sizeOf schemas

  theorem Bag.rule_fields {first second : RewriteRule}
      (left : first.left = second.left) (right : first.right = second.right)
      (premises : first.premises = second.premises)
      {spec : RuleBindingSpec} {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
      {initial final : Assignment} {schemas targets : List Pattern} {rest : Option String} {kind : CollType}
      (matched : Bag first spec ambient site path depth initial index schemas rest kind targets final) :
      Bag second spec ambient site path depth initial index schemas rest kind targets final := by
    cases matched with
    | nil => exact .nil
    | rest stored =>
      exact .rest ((rest_fields left right premises _ _ _ _ _ _ _ _ _).symm.trans stored)
    | cons selected within head tail =>
      exact .cons selected within (head.rule_fields left right premises) (tail.rule_fields left right premises)
  termination_by sizeOf schemas
end

#print axioms Matches.rule_fields

namespace RuleFieldsControls

private def spec : RuleBindingSpec := {dependencies := [("X", [])]}
private def schemaRule : RewriteRule := {
  name := "metadata-control"
  typeContext := [("X", .base "Term")]
  left := .fvar "X"
  right := .fvar "X"
  premises := [] }
private def value : Pattern := .apply "Value" []

#guard (capture? schemaRule spec 0 0 .left [] [] "X" value).isSome
#guard (capture? {schemaRule with bindings := some spec} spec 0 0 .left [] [] "X" value).isSome
#guard (capture? {schemaRule with left := .fvar "Y"} spec 0 0 .left [] [] "X" value).isNone

end RuleFieldsControls

end Mettapedia.OSLF.MeTTaIL.GeneralScopedMatch
