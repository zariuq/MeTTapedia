import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeAnnotationPolicy
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypePolicyAgreement

/-!
# Current application typing through the actual scoped read driver

The historical and current policies are instances of the same driver. These
controls execute actual declaration reads, signature matching and subtype
closure. They distinguish internal prefix-overlap removal from deduplicating
derived occurrences and from the structural constructor question.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCurrentReader

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeCallGraph NativeTypeSourcePorts

def external : RetainedTypePayloads.ExternalView := fun tag key => .grounded (.custom tag key)
def historicalOps := TypeScopeMatcher.ops external id (fun _ => [])
def currentOps := TypeScopeMatcher.currentOps external id (fun _ => [])

def number : Atom := .grounded (.int 1)
def badValue : Atom := .grounded (.string "bad")
def box (value : Atom) : Atom := .expression [.symbol "Box", value]
def twice : Atom := .expression [.symbol "Twice", number]
def agreed : Atom := .expression [.symbol "Agreed", number]

def declaration (subject type_ : Atom) : Atom := .expression [.symbol ":", subject, type_]
def arrow (formal range : Atom) : Atom := .expression [.symbol "->", formal, range]

def source : Source where
  rows := [declaration (.symbol "Box") (arrow (.symbol "Number") (.symbol "Actual")),
    declaration (box number) (.symbol "Claimed"), declaration (box badValue) (.symbol "Claimed"),
    declaration (.symbol "Twice") (arrow (.symbol "Number") (.symbol "Actual")),
    declaration (.symbol "Twice") (arrow (.symbol "Atom") (.symbol "Actual")),
    declaration twice (.symbol "Claimed"),
    declaration (.symbol "Agreed") (arrow (.symbol "Number") (.symbol "Actual")),
    declaration (.symbol "Agreed") (arrow (.symbol "Atom") (.symbol "Actual")),
    declaration agreed (.symbol "Actual"),
    .expression [.symbol ":<", .symbol "Claimed", .symbol "Parent"]]
  intrinsicRows := []
  rename := fun _ _ name => name
  subtypeBudget := 4
  subtypeFresh := "super"
  alpha := (· == ·)

def result (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (direct : Bool)
    (value : Atom) : Option Reply :=
  (NativeTypeScopedReads.evaluate ops source external 4 (.infer direct value) ⟨[], 0⟩).1

theorem annotation_closure_precedes_derived_answers :
    result currentOps true (box number) =
      some (.types [.symbol "Claimed", .symbol "Parent", .symbol "Actual"]) := by cbv

theorem historical_override_omits_the_arrow_answer :
    result historicalOps true (box number) = some (.types [.symbol "Claimed", .symbol "Parent"]) := by cbv

theorem different_arrows_keep_duplicate_derived_answers :
    result currentOps true twice =
      some (.types [.symbol "Claimed", .symbol "Parent", .symbol "Actual", .symbol "Actual"]) := by cbv

theorem prefix_overlap_drops_only_covered_derivations :
    result currentOps true agreed = some (.types [.symbol "Actual"]) ∧
    result currentOps false agreed = some (.types [.symbol "Actual", .symbol "Actual"]) := by cbv

theorem bad_fields_keep_nominal_information_but_fail_structural_question :
    result currentOps true (box badValue) = some (.types [.symbol "Claimed", .symbol "Parent"]) ∧
    result currentOps false (box badValue) = some (.types []) := by cbv

theorem current_reader_does_not_publish_unfinished_annotation_closure :
    (NativeTypeScopedReads.evaluate currentOps { source with subtypeBudget := 0 } external 4
      (.infer true (box number)) ⟨[], 0⟩).1 = none := by cbv

theorem structural_reader_does_not_request_unused_annotation_closure :
    (NativeTypeScopedReads.evaluate currentOps { source with subtypeBudget := 0 } external 4
      (.infer false (box number)) ⟨[], 0⟩).1 = some (.types [.symbol "Actual"]) := by cbv

theorem annotated_source_is_outside_policy_agreement :
    ¬ NativeTypePolicyAgreement.NoExpressionRows source.rows := by
  intro absent
  exact absent [.symbol "Box", number] (.symbol "Claimed") (by simp [source, declaration, box])

def resourceSource : Source := { source with
  rows := [declaration (.symbol "Box") (arrow (.symbol "Number") (.symbol "Actual")),
    declaration (box number) (.grounded (.custom "TypeCell" "cell"))] }

def resourceWorld (type_ : Atom) : RetainedTypePayloads.ExternalView := fun _ _ => type_

theorem resource_annotation_changes_current_reader :
    (NativeTypeScopedReads.evaluate
      (TypeScopeMatcher.currentOps (resourceWorld (.symbol "Actual")) id (fun _ => []))
      resourceSource (resourceWorld (.symbol "Actual")) 4 (.infer true (box number)) ⟨[], 0⟩).1 =
      some (.types [.symbol "Actual"]) ∧
    (NativeTypeScopedReads.evaluate
      (TypeScopeMatcher.currentOps (resourceWorld (.symbol "Other")) id (fun _ => []))
      resourceSource (resourceWorld (.symbol "Other")) 4 (.infer true (box number)) ⟨[], 0⟩).1 =
      some (.types [.symbol "Other", .symbol "Actual"]) := by cbv

theorem resource_source_fails_admission : ¬ NativeTypeSourcePorts.Safe resourceSource := by
  unfold NativeTypeSourcePorts.Safe
  decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCurrentReader
