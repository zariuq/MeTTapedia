import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldSourceLoop

/-! The actual function/context-space shell of the collection fold. Its
caller and two operation variables are retained, and the local space binder
is substituted by the existing minimal instruction rule. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldFunction

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation
open HECollectionFoldEmission HECollectionFoldReadback HECollectionFoldNativeEntry
open HECollectionFoldSourceLoop

def body (items : List Entry.Value) (init : Entry.Value) (left right spaceName : String)
    (operationMark : Entry.Status)
    (operatorName : String := CollectionStdlibSource.appendName) (itemsMark : Entry.Status := .active) : Entry.Value :=
  .expression .active [.symbol "chain", .expression .active [.symbol "context-space"], .var spaceName,
    .expression .active [.symbol "eval", call items init left right (operation operationMark left right (operatorName := operatorName)) (.var spaceName) (itemsMark := itemsMark)]]

def function (items : List Entry.Value) (init : Entry.Value) (left right spaceName : String)
    (operationMark : Entry.Status)
    (operatorName : String := CollectionStdlibSource.appendName) (itemsMark : Entry.Status := .active) : Entry.Value :=
  .expression .active [.symbol "function", body items init left right spaceName operationMark (operatorName := operatorName) (itemsMark := itemsMark)]

theorem source {Context World : Type} {environment : WorldEnvironment Context World}
    {snapshots : SnapshotServices Context World} {label world hidden}
    (emitter : Emitter environment label world hidden) (policy : Policy) (frame : Frame)
    (appendCalls : AppendCalls environment snapshots policy label world frame)
    (left right spaceName : String) (operationMark : Entry.Status) (different : left ≠ right)
    (operationActive : policy.reentry = .reinterpret ∨ operationMark = .active)
    (leftDifferent : left ≠ spaceName) (rightDifferent : right ≠ spaceName)
    (leftFixed : frame.read policy (.var left) = .var left)
    (rightFixed : frame.read policy (.var right) = .var right)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots label world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = [])
    (live : List Atom) (scope : List String) (caller : Option Atom)
    (listMark : Entry.Status) (values : List Entry.Value)
    (valuesClosed : TypeSubst.typeVarsList (values.map Entry.Value.erase) = []) :
    ∃ finalMark, Stateful.MinimalRel environment label world live scope caller
      (function pairs (.expression listMark values) left right spaceName operationMark) frame
      [(.expression finalMark (values ++ rows.map Prod.fst), frame)] world (policy := policy) := by
  let init := Entry.Value.expression listMark values
  let op := operation operationMark left right
  let context := Entry.Value.grounded (environment.services.contextPayload label)
  let functionLive := (.expression [.symbol "function", (body pairs init left right spaceName operationMark).erase]) :: live
  let functionCaller : Option Atom := some (.expression [.symbol "function", (body pairs init left right spaceName operationMark).erase])
  have initClosed : TypeSubst.typeVars init.erase = [] := by
    simpa only [init, Entry.Value.erase, TypeSubst.typeVars] using valuesClosed
  have pairClosed := pairs_closed stored closed
  have contextClosed : TypeSubst.typeVars context.erase = [] := by simp [context, Entry.Value.erase, TypeSubst.typeVars]
  obtain ⟨finalMark, completed⟩ := finish_emission emitter policy frame appendCalls left right operationMark different operationActive
    leftFixed rightFixed rows pairs stored closed functionLive scope functionCaller listMark values valuesClosed
  refine ⟨finalMark, ?_⟩
  apply Stateful.MinimalRel.function (world1 := world)
    (raw := [(.expression .active [.symbol "return", .expression finalMark (values ++ rows.map Prod.fst)], frame)])
  · rfl
  · refine Stateful.BodyRel.run (world1 := world)
      (raw := [(emission hidden functionLive scope frame pairs init left right op context, frame)]) ?_ ?_
    · apply Stateful.MinimalRel.chain (world1 := world) (selected := [(context, frame)])
      · exact .contextSpace
      · apply Stateful.BoundaryBatchRel.single_iff.mpr
        apply Stateful.BoundaryRel.chain
        rw [HECollectionClosedAppend.closed_read policy frame context contextClosed]
        have substituted : substituteBinder policy spaceName context
            (.expression .active [.symbol "eval", call pairs init left right op (.var spaceName)]) =
            .expression .active [.symbol "eval", call pairs init left right op context] := by
          simpa only [op, operation] using context_substitution policy spaceName left right context init pairs operationMark
            leftDifferent rightDifferent pairClosed initClosed
        rw [substituted]
        exact eval_entry emitter policy functionLive scope functionCaller frame pairs init left right context operationMark
          leftFixed rightFixed initClosed pairClosed contextClosed
    · exact Stateful.BoundaryBatchRel.single_iff.mpr completed
  · apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .functionReturn

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldFunction
