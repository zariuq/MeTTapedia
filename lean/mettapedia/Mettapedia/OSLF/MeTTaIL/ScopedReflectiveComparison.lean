import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

/-!
# Source-selected comparison of captured name bodies

The existing reflection profile selects the matching presentation. Only a
uniquely declared metavariable whose result type is that presentation's name
sort receives canonical comparison. All other variables retain literal
comparison, including generated signature and funding variables.

This adapter computes an observation; it neither normalizes stored captures
nor traverses an input term. The scoped matcher must separately retain exact
dependency and ambient contexts and keep the first captured raw value.
Compatibility with general occurrence substitutions is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedReflectiveComparison

open Syntax Reflection ReflectiveSubstitution ReflectiveCanonical

/-- Compare only declared name results canonically; missing or ambiguous
declarations retain the ordinary literal check. -/
def bodyComparison (profile : ReflectionProfile) (rule : RewriteRule)
    (name : String) (left right : Pattern) : Bool :=
  match matchingPresentationForRule? profile rule with
  | none => left == right
  | some declaration =>
      match rule.typeContext.filter (fun entry => entry.1 == name) with
      | [(_, type)] =>
          if type == .base declaration.nameSort then
            canonicalEquivalent declaration left right
          else left == right
      | _ => left == right

theorem bodyComparison_unselected (profile : ReflectionProfile) (rule : RewriteRule)
    (unselected : matchingPresentationForRule? profile rule = none)
    (name : String) (left right : Pattern) :
    bodyComparison profile rule name left right = (left == right) := by
  simp only [bodyComparison, unselected]

/-- Result-sort selection is read from the actual unique context row. -/
theorem bodyComparison_selected_name (profile : ReflectionProfile) (rule : RewriteRule)
    (declaration : ReflectivePresentationDecl) (name : String)
    (selected : matchingPresentationForRule? profile rule = some declaration)
    (declared : rule.typeContext.filter (fun entry => entry.1 == name) =
      [(name, .base declaration.nameSort)]) (left right : Pattern) :
    bodyComparison profile rule name left right =
      canonicalEquivalent declaration left right := by
  simp only [bodyComparison, selected, declared, beq_self_eq_true, if_true]

theorem bodyComparison_selected_name_iff (profile : ReflectionProfile) (rule : RewriteRule)
    (declaration : ReflectivePresentationDecl) (name : String)
    (selected : matchingPresentationForRule? profile rule = some declaration)
    (declared : rule.typeContext.filter (fun entry => entry.1 == name) =
      [(name, .base declaration.nameSort)]) (left right : Pattern) :
    bodyComparison profile rule name left right = true ↔
      canonicalize declaration left = canonicalize declaration right := by
  rw [bodyComparison_selected_name profile rule declaration name selected declared]
  exact canonicalEquivalent_eq_true_iff

theorem bodyComparison_other_sort (profile : ReflectionProfile) (rule : RewriteRule)
    (declaration : ReflectivePresentationDecl) (name : String) (type : TypeExpr)
    (selected : matchingPresentationForRule? profile rule = some declaration)
    (declared : rule.typeContext.filter (fun entry => entry.1 == name) = [(name, type)])
    (different : type ≠ .base declaration.nameSort) (left right : Pattern) :
    bodyComparison profile rule name left right = (left == right) := by
  simp [bodyComparison, selected, declared, different]

theorem bodyComparison_missing (profile : ReflectionProfile) (rule : RewriteRule)
    (name : String)
    (missing : rule.typeContext.filter (fun entry => entry.1 == name) = [])
    (left right : Pattern) :
    bodyComparison profile rule name left right = (left == right) := by
  cases chosen : matchingPresentationForRule? profile rule <;>
    simp only [bodyComparison, chosen, missing]

/-- Even duplicate equal declarations do not authorize canonical matching. -/
theorem bodyComparison_ambiguous (profile : ReflectionProfile) (rule : RewriteRule)
    (name : String) (first second : String × TypeExpr) (rest : List (String × TypeExpr))
    (ambiguous : rule.typeContext.filter (fun entry => entry.1 == name) =
      first :: second :: rest) (left right : Pattern) :
    bodyComparison profile rule name left right = (left == right) := by
  cases chosen : matchingPresentationForRule? profile rule <;>
    simp only [bodyComparison, chosen, ambiguous]

/-- Canonical comparison extends literal acceptance without changing values. -/
@[simp] theorem bodyComparison_refl (profile : ReflectionProfile) (rule : RewriteRule)
    (name : String) (body : Pattern) :
    bodyComparison profile rule name body body = true := by
  unfold bodyComparison
  split
  · exact beq_self_eq_true body
  · split
    · split <;> simp [canonicalEquivalent]
    · exact beq_self_eq_true body

theorem bodyComparison_of_eq (profile : ReflectionProfile) (rule : RewriteRule)
    (name : String) {left right : Pattern} (same : left = right) :
    bodyComparison profile rule name left right = true := by
  subst right
  exact bodyComparison_refl profile rule name left

end Mettapedia.OSLF.MeTTaIL.ScopedReflectiveComparison
