import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldNativeEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionClosedAppend

/-! Source execution of the emitted collection fold. Each induction step
executes one append through `metta`, substitutes its actual result through
`chain`, and invokes the next one-step helper through `eval`. The only
operation leaf supplied here is one append, never a completed fold. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldSourceLoop

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation
open HECollectionFoldEmission HECollectionFoldReadback HECollectionFoldNativeEntry

def operation (mark : Entry.Status) (left right : String) : Entry.Value :=
  .expression mark [.symbol CollectionStdlibSource.appendName, .var left, .var right]

/-- A local source call at the saved world, including its actual publication
status. The relation does not replace snapshot restore or compute a fold. -/
structure AppendCalls {Context World : Type} (environment : WorldEnvironment Context World)
    (snapshots : SnapshotServices Context World) (policy : Policy) (label : Context)
    (world : World) (frame : Frame) : Prop where
  source : ∀ live scope callMark listMark values row pair,
    (policy.reentry = .reinterpret ∨ callMark = .active) →
    StoredPairRel snapshots label world row pair → TypeSubst.typeVars row.1.erase = [] →
    TypeSubst.typeVarsList (values.map Entry.Value.erase) = [] →
    ∃ nextMark, Stateful.AtomRel environment label world live scope
      (.expression callMark [.symbol CollectionStdlibSource.appendName, .expression listMark values, pair])
      Atom.undefinedType frame [(.expression nextMark (values ++ [row.1]), frame)] world (policy := policy)

theorem stored_closed {Context World : Type} {snapshots : SnapshotServices Context World}
    {label world row pair} (stored : StoredPairRel snapshots label world row pair)
    (closed : TypeSubst.typeVars row.1.erase = []) : TypeSubst.typeVars pair.erase = [] := by
  obtain ⟨payload, rfl, _⟩ := stored
  simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList, closed]

theorem pairs_closed {Context World : Type} {snapshots : SnapshotServices Context World}
    {label world rows pairs} (stored : List.Forall₂ (StoredPairRel snapshots label world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = []) :
    TypeSubst.typeVarsList (pairs.map Entry.Value.erase) = [] := by
  induction stored with
  | nil => rfl
  | @cons row pair rows pairs head tail ih =>
      have first := stored_closed head (closed row (by simp))
      have rest := ih (fun value member => closed value (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, TypeSubst.typeVarsList, first, rest, List.nil_append]

theorem finish_emission {Context World : Type} {environment : WorldEnvironment Context World}
    {snapshots : SnapshotServices Context World} {label world hidden}
    (emitter : Emitter environment label world hidden) (policy : Policy) (frame : Frame)
    (appendCalls : AppendCalls environment snapshots policy label world frame)
    (left right : String) (operationMark : Entry.Status) (different : left ≠ right)
    (operationActive : policy.reentry = .reinterpret ∨ operationMark = .active)
    (leftFixed : frame.read policy (.var left) = .var left)
    (rightFixed : frame.read policy (.var right) = .var right)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots label world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = [])
    (live : List Atom) (scope : List String) (caller : Option Atom)
    (listMark : Entry.Status) (values : List Entry.Value)
    (valuesClosed : TypeSubst.typeVarsList (values.map Entry.Value.erase) = []) :
    ∃ finalMark, Stateful.BoundaryRel environment label world live scope caller .body
      (emission hidden live scope frame pairs (.expression listMark values) left right
        (operation operationMark left right) (.grounded (environment.services.contextPayload label))) frame
      [(.expression .active [.symbol "return", .expression finalMark (values ++ rows.map Prod.fst)], frame)] world
      (policy := policy) := by
  induction stored generalizing live scope caller listMark values with
  | nil =>
      refine ⟨listMark, ?_⟩
      have read : frame.read policy (.expression .active [.symbol "return", .expression listMark values]) =
          .expression .active [.symbol "return", .expression listMark values] :=
        HECollectionClosedAppend.closed_read policy frame _ (by
          simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList, valuesClosed])
      simpa only [emission, List.map_nil, List.append_nil, read] using
        (Stateful.BoundaryRel.bodyTerminal (environment := environment) (policy := policy)
          (frame := frame) (value := .expression .active [.symbol "return", .expression listMark values])
          (by rw [read]; simp [Entry.Value.erase, Minimal.embeddedInstruction]))
  | @cons row pair rows pairs head tail ih =>
      let context := Entry.Value.grounded (environment.services.contextPayload label)
      let op := operation operationMark left right
      let init := Entry.Value.expression listMark values
      let avoid := protectedNames hidden live scope frame (pair :: pairs) init left right op context
      let nextName := chainName avoid op
      let emitted := step avoid pair pairs init left right op context
      have firstClosed := closed row (by simp)
      have remainingClosed := fun value member => closed value (List.mem_cons_of_mem row member)
      have pairClosed := stored_closed head firstClosed
      have tailClosed := pairs_closed tail remainingClosed
      have contextClosed : TypeSubst.typeVars context.erase = [] := by
        simp [context, Entry.Value.erase, TypeSubst.typeVars]
      have initClosed : TypeSubst.typeVars init.erase = [] := by
        simpa only [init, Entry.Value.erase, TypeSubst.typeVars] using valuesClosed
      have nextDistinct : left ≠ nextName ∧ right ≠ nextName :=
        chain_distinct_from_parameters hidden live scope frame (pair :: pairs) init left right op context
      have emittedRead : frame.read policy emitted = emitted :=
        protected_step_read policy frame hidden live scope pair pairs init left right context operationMark
          different leftFixed rightFixed initClosed pairClosed tailClosed contextClosed
      obtain ⟨nextMark, appended⟩ := appendCalls.source (emitted.erase :: live) scope operationMark listMark values row pair
        operationActive head firstClosed valuesClosed
      let next := Entry.Value.expression nextMark (values ++ [row.1])
      have nextClosed : TypeSubst.typeVars next.erase = [] := by
        simp [next, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList_append,
          TypeSubst.typeVarsList, valuesClosed, firstClosed]
      have nextValuesClosed : TypeSubst.typeVarsList ((values ++ [row.1]).map Entry.Value.erase) = [] := by
        simpa only [next, Entry.Value.erase, TypeSubst.typeVars] using nextClosed
      obtain ⟨finalMark, finish⟩ := ih remainingClosed live scope caller nextMark (values ++ [row.1]) nextValuesClosed
      refine ⟨finalMark, ?_⟩
      apply Stateful.BoundaryRel.bodyResume
      · change Minimal.embeddedInstruction (frame.read policy emitted).erase = true
        rw [emittedRead]
        exact step_is_minimal_instruction avoid pair pairs init left right op context
      · change Stateful.BodyRel environment label world live scope caller (frame.read policy emitted) frame _ world (policy := policy)
        rw [emittedRead]
        refine Stateful.BodyRel.run (world1 := world)
          (raw := [(emission hidden live scope frame pairs next left right op context, frame)]) ?_ ?_
        · apply Stateful.MinimalRel.chain (world1 := world) (selected := [(next, frame)])
          · apply Stateful.MinimalRel.metta
            simpa only [emitted, step, op, operation, Entry.Value.erase, List.map_cons, List.map_nil,
              collapse_template avoid init pair left right different operationMark, init, next, Atom.undefinedType] using appended
          · apply Stateful.BoundaryBatchRel.single_iff.mpr
            apply Stateful.BoundaryRel.chain
            rw [HECollectionClosedAppend.closed_read policy frame next nextClosed]
            have substituted : substituteBinder policy (chainName avoid op) next
                (.expression .active [.symbol "eval", call pairs (.var (chainName avoid op)) left right op context]) =
                .expression .active [.symbol "eval", call pairs next left right op context] := by
              simpa only [nextName, op, operation] using
                next_call_substitution policy nextName left right next context pairs operationMark
                  nextDistinct.1 nextDistinct.2 tailClosed contextClosed
            rw [substituted]
            exact eval_entry emitter policy live scope caller frame pairs next left right context operationMark
              leftFixed rightFixed nextClosed tailClosed contextClosed
        · apply Stateful.BoundaryBatchRel.single_iff.mpr
          simpa only [List.map_cons, List.append_assoc, List.singleton_append] using finish

theorem eval_body {Context World : Type} {environment : WorldEnvironment Context World}
    {snapshots : SnapshotServices Context World} {label world hidden}
    (emitter : Emitter environment label world hidden) (policy : Policy) (frame : Frame)
    (appendCalls : AppendCalls environment snapshots policy label world frame)
    (left right : String) (operationMark : Entry.Status) (different : left ≠ right)
    (operationActive : policy.reentry = .reinterpret ∨ operationMark = .active)
    (leftFixed : frame.read policy (.var left) = .var left)
    (rightFixed : frame.read policy (.var right) = .var right)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots label world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = [])
    (live : List Atom) (scope : List String) (caller : Option Atom)
    (listMark : Entry.Status) (values : List Entry.Value)
    (valuesClosed : TypeSubst.typeVarsList (values.map Entry.Value.erase) = []) :
    ∃ finalMark, Stateful.BodyRel environment label world live scope caller
      (.expression .active [.symbol "eval", call pairs (.expression listMark values) left right
        (operation operationMark left right) (.grounded (environment.services.contextPayload label))]) frame
      [(.expression .active [.symbol "return", .expression finalMark (values ++ rows.map Prod.fst)], frame)] world
      (policy := policy) := by
  obtain ⟨finalMark, completed⟩ := finish_emission emitter policy frame appendCalls left right operationMark different operationActive
    leftFixed rightFixed rows pairs stored closed live scope caller listMark values valuesClosed
  refine ⟨finalMark, Stateful.BodyRel.run (world1 := world) ?_ (Stateful.BoundaryBatchRel.single_iff.mpr completed)⟩
  exact eval_entry emitter policy live scope caller frame pairs (.expression listMark values) left right _ operationMark
    leftFixed rightFixed (by simpa only [Entry.Value.erase, TypeSubst.typeVars] using valuesClosed)
    (pairs_closed stored closed) (by simp [Entry.Value.erase, TypeSubst.typeVars])

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldSourceLoop
