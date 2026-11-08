import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSupplyVariants

/-! # Actual annotation reads earn independent ordered signature instances -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
open NativeTypeCallGraph NativeTypeSourcePorts
open TypeReadSupply (Supply remember)
open RetainedTypePayloads (ExternalView)

theorem annotation_variants (source : Source) (world : ExternalView) (supply : Supply)
    (subject : Atom) (types : List Atom)
    (returned : (primitive source world supply (.annotations subject)).1 = some (.types types)) :
    ArgumentAlphaVariantsRel (remember supply [subject]).used
      (rawDeclarations source world subject) types := by
  have same := NativeTypeDemand.ViewReply.types.inj (Option.some.inj returned)
  rw [← same]
  exact TypeReadSupply.freshList_variants _ _

theorem annotation_avoids (source : Source) (world : ExternalView) (supply : Supply)
    (subject : Atom) (types : List Atom)
    (returned : (primitive source world supply (.annotations subject)).1 = some (.types types))
    (name : String) (occurs : name ∈ atomListVariables types) : name ∉ supply.used := by
  have same := NativeTypeDemand.ViewReply.types.inj (Option.some.inj returned)
  rw [← same] at occurs
  intro old
  exact TypeReadSupply.freshList_avoids _ _ _ occurs (TypeReadSupply.remember_old supply [subject] old)

/-- The subject can be the same in both reads. Any intervening recursive
work, including incomplete work, retains the first instance's allocated names. -/
theorem read_occurrences_are_apart (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (world : ExternalView) (supply : Supply) (firstSubject laterSubject : Atom)
    (firstTypes laterTypes : List Atom)
    (first : (primitive source world supply (.annotations firstSubject)).1 = some (.types firstTypes))
    (depth : Nat) (intervening : Call)
    (later : (primitive source world
      (evaluate ops source world depth intervening (primitive source world supply (.annotations firstSubject)).2).2
      (.annotations laterSubject)).1 = some (.types laterTypes))
    (name : String) (earlier : name ∈ atomListVariables firstTypes) :
    name ∉ atomListVariables laterTypes := by
  intro next
  apply annotation_avoids source world _ laterSubject laterTypes later name next
  apply evaluate_remembers
  exact primitive_retains_reply source world supply (.annotations firstSubject) firstTypes first earlier

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads
