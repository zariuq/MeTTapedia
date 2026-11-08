import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveDriver
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeSourcePorts
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReads
import Mettapedia.Machines.QueryState

/-!
# Occurrence-scoped primitive and recursive type reads

The original inference call graph is interpreted with a threaded private
name supply. Every actual annotation read instantiates its schema anew;
recursive children return their advanced supply to the parent. Freshening is
not keyed only by the subject, and a completed nonground reply is not reused
as a persistent type instance. Each returned type's names remain protected
from all later reads, including names produced by normalization.

This supplies the missing occurrence semantics. Representation of the native
frame identity, full scalar/matcher/normalizer codecs and whole-language
argument delivery retain their separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open NativeTypeCallGraph NativeTypeSourcePorts
open TypeReadSupply (Supply remember freshList)
open RetainedTypePayloads (ExternalView)

def retain (supply : Supply) : Option Reply → Supply
  | some (.types types) => remember supply types
  | _ => supply

theorem retain_old (supply : Supply) (reply : Option Reply) : supply.used ⊆ (retain supply reply).used := by
  cases reply with
  | none => exact fun _ member => member
  | some reply =>
      cases reply with
      | types types => exact TypeReadSupply.remember_old supply types
      | class_ _ | kind _ => exact fun _ member => member

def primitive (source : Source) (world : ExternalView) (supply : Supply) : Primitive → Option Reply × Supply
  | .annotations atom =>
      let result := freshList (remember supply [atom]) (rawDeclarations source world atom)
      (some (.types result.1), result.2)
  | .closure seeds =>
      let result := ScopedSubtypeReads.completeTypes world source.rows source.subtypeFresh
        source.alpha source.subtypeBudget seeds supply
      (result.1.map (fun types => .types types), retain result.2 (result.1.map (fun types => .types types)))
  | key =>
      let answer := NativeTypeSourcePorts.primitive source world key
      (answer, retain supply answer)

theorem primitive_remembers (source : Source) (world : ExternalView) (supply : Supply) (key : Primitive) :
    supply.used ⊆ (primitive source world supply key).2.used := by
  cases key with
  | annotations atom =>
      exact fun _ member => TypeReadSupply.freshList_remembers _ _
        (TypeReadSupply.remember_old supply [atom] member)
  | closure seeds =>
      exact fun _ member => retain_old _ _
        (ScopedSubtypeReads.completeTypes_remembers world source.rows source.subtypeFresh source.alpha
          source.subtypeBudget seeds supply member)
  | intrinsic _ | kind _ | classify _ _ => exact retain_old _ _

/-- A read's returned type variables remain allocated after the read. -/
theorem primitive_retains_reply (source : Source) (world : ExternalView) (supply : Supply)
    (key : Primitive) (types : List Atom) (returned : (primitive source world supply key).1 = some (.types types)) :
    atomListVariables types ⊆ (primitive source world supply key).2.used := by
  cases key with
  | annotations atom =>
      have same := NativeTypeDemand.ViewReply.types.inj (Option.some.inj returned)
      cases same
      exact TypeReadSupply.freshList_output_remembers _ _
  | closure seeds =>
      change (ScopedSubtypeReads.completeTypes world source.rows source.subtypeFresh source.alpha
        source.subtypeBudget seeds supply).1.map (fun types => (NativeTypeDemand.ViewReply.types types : Reply)) =
          some (NativeTypeDemand.ViewReply.types types : Reply) at returned
      simp only [Option.map_eq_some_iff] at returned
      obtain ⟨values, completed, equal⟩ := returned
      cases NativeTypeDemand.ViewReply.types.inj equal
      simp only [primitive, completed, Option.map_some, retain]
      exact TypeReadSupply.remember_new _ _
  | intrinsic atom =>
      change NativeTypeSourcePorts.primitive source world (.intrinsic atom) = some (.types types) at returned
      simp only [primitive, returned, retain]
      exact TypeReadSupply.remember_new _ _
  | kind atom => cases returned
  | classify head values => cases returned

def evaluate (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (world : ExternalView) : Nat → Call → Supply → Option Reply × Supply
  | 0, _, supply => (none, supply)
  | depth + 1, call, supply =>
      let service : Supply → Question → Option Reply × Supply := fun current =>
        fun | .inl key => primitive source world current key
            | .inr child => evaluate ops source world depth child current
      let result := Mettapedia.Machines.QueryState.run service
        (Mettapedia.Machines.ReadOnlyQueryDemand.demand (body ops call)) supply
      let answer := NativeTypeRecursiveDriver.completed result.answer
      (answer, retain result.state answer)

theorem evaluate_remembers (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (world : ExternalView) (depth : Nat) : ∀ call supply,
    supply.used ⊆ (evaluate ops source world depth call supply).2.used := by
  induction depth with
  | zero => intro call supply; exact fun _ member => member
  | succ depth ih =>
      intro call supply
      dsimp only [evaluate]
      intro name member
      apply retain_old
      have preserves := Mettapedia.Machines.QueryState.state_extends
        (fun (current : Supply) => fun
          | .inl key => primitive source world current key
          | .inr child => evaluate ops source world depth child current)
        (fun before after : Supply => before.used ⊆ after.used)
        (fun _ _ present => present)
        (fun _ _ _ first second _ present => second (first present))
        (fun current key => by
          cases key with
          | inl key => exact primitive_remembers source world current key
          | inr child => exact ih child current)
        (Mettapedia.Machines.ReadOnlyQueryDemand.demand (body ops call)) supply
      exact preserves member

theorem evaluated_reply_retained (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (world : ExternalView) (depth : Nat) (call : Call) (supply : Supply)
    (types : List Atom) (returned : (evaluate ops source world depth call supply).1 = some (.types types)) :
    atomListVariables types ⊆ (evaluate ops source world depth call supply).2.used := by
  cases depth with
  | zero => cases returned
  | succ depth =>
      dsimp only [evaluate] at returned ⊢
      rw [returned]
      exact TypeReadSupply.remember_new _ _

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads
