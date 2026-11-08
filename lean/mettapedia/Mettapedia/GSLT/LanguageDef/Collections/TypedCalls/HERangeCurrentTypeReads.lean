import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypePolicyAgreement
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeTypeReadApplications

/-!
# Current annotation policy for the authored range source

The existing range packet has no expression-subject declarations. Its
occurrence-scoped reads therefore migrate to the corrected annotation policy
without changing answers or private allocation. The theorem applies at every
depth, including unfinished recursive reads, and to all three inquiry roles.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeCurrentTypeReads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeCallGraph
open HERangeTypeReadPrimitives (source)
open RetainedTypePayloads (ExternalView)
open TypeReadSupply (Supply)

theorem policy_agreement (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (policy : NativeTypeViews.AnnotationPolicy Atom) (world : ExternalView)
    (depth : Nat) (call : Call) (supply : Supply) :
    NativeTypeScopedReads.evaluate { ops with annotationPolicy := policy } source world depth call supply =
      NativeTypeScopedReads.evaluate ops source world depth call supply :=
  NativeTypePolicyAgreement.evaluate_policy ops policy source world
    (HERangeTypeReadPrimitives.no_expression_annotations world) depth call supply

theorem current_reader_agrees (world : ExternalView) (normalize : Atom → Atom)
    (subtypes : List Atom → List Atom) (depth : Nat) (call : Call) (supply : Supply) :
    NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps world normalize subtypes)
        source world depth call supply =
      NativeTypeScopedReads.evaluate (TypeScopeMatcher.ops world normalize subtypes)
        source world depth call supply := policy_agreement _ _ world depth call supply

theorem comparison_type (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : NativeTypeViews.AnnotationPolicy Atom) (depth : Nat) (supply : Supply) (left right : Int) :
    (NativeTypeScopedReads.evaluate
      { HERangeTypeReadApplications.ops world active primitive unobservedClosure with annotationPolicy := policy }
      source world (depth + 2)
      (.infer true (.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)])) supply).1 =
      some (.types [.symbol "Bool"]) := by
  rw [policy_agreement]
  exact HERangeTypeReadApplications.comparison_type world active primitive unobservedClosure depth supply left right

theorem shallow_comparison_still_declines (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (policy : NativeTypeViews.AnnotationPolicy Atom) (world : ExternalView)
    (supply : Supply) (left right : Int) :
    (NativeTypeScopedReads.evaluate { ops with annotationPolicy := policy } source world 1
      (.infer true (.expression [.symbol ">=", .grounded (.int left), .grounded (.int right)])) supply).1 = none := by
  rw [policy_agreement]
  exact HERangeTypeReadApplications.comparison_shallow_declines ops world supply left right

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeCurrentTypeReads
