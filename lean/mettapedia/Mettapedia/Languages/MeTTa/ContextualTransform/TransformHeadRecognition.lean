import Mettapedia.Machines.SymbolTableHeadCache
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCallCache

/-!
# Transform-family recognition and source execution remain distinct

The runtime's current seven names instantiate the generic symbol-table cache.
Their public/native/name/run questions have separate declarations. A recognized
spelling is not permission to bypass authored definitions or quoted data.

The source adapter decodes an owned cached ID to the actual PeTTa syntax and
uses the independent source call/data rules in their existing contexts. It is
not a C correspondence theorem or a proof of native transform admission.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.TransformHeadRecognition

open Mettapedia.Machines.SymbolTableHeadCache
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open PeTTaActivation PeTTaContexts Unifying

def names : Fin 7 → String :=
  !["transform", "tf:split", "tf:propose", "tf:inst", "tf:fire", "tf:fire-into", "tf:run"]

inductive Question where
  | publicCall (arity : Nat)
  | nativeCall (arity : Nat)
  | runCall (arity : Nat)
  | name
  deriving DecidableEq, Repr

def arityFits (index : Fin 7) (arity : Nat) : Bool :=
  if index = 0 then arity == 3 || arity == 4
  else if index = 1 ∨ index = 3 then arity == 2
  else if index = 2 ∨ index = 4 then arity == 3
  else arity == 4

def permits (index : Fin 7) : Question → Bool
  | .publicCall arity => arityFits index arity
  | .nativeCall arity => decide (index ≠ 0) && arityFits index arity
  | .runCall arity => decide (index = 6) && arity == 4
  | .name => true

theorem names_distinct : (List.ofFn names).Nodup := by decide

def decodeCall (table : Table String) (reference : Reference) (arguments : List Atom) : Option Atom :=
  if Current table reference then
    (decode table reference.head).map fun head => .expression (.symbol head :: arguments)
  else none

/-- Re-interning the head preserves the actual source expression. Arguments
are already source atoms here; this is not a recursive native graph-copy law. -/
theorem transported_call_decodes (old target : Table String) (reference : Reference)
    (current : Current old reference) (nextReference : Reference) (nextTable : Table String)
    (moved : transport old target reference = some (nextReference, nextTable))
    (arguments : List Atom) :
    decodeCall nextTable nextReference arguments = decodeCall old reference arguments := by
  obtain ⟨valid, spelling, _⟩ := transport_result old target reference current
    nextReference nextTable moved
  simp only [decodeCall, valid, current, ↓reduceIte, spelling]

/-- Both decodings feed the independent source runner in the same live
registry. This covers every inspection budget, including a suspended result,
and arbitrary source contexts; it does not transfer another registry's authority. -/
theorem transported_call_run (old target : Table String) (reference : Reference)
    (current : Current old reference) (nextReference : Reference) (nextTable : Table String)
    (moved : transport old target reference = some (nextReference, nextTable))
    (arguments : List Atom) (registry : SpaceSemantics.Program) (context : Context)
    (base : Configuration) (bindings : Subst) (fuel : Nat) :
    (decodeCall nextTable nextReference arguments).map (fun expression =>
        run registry fuel (atExpression base bindings (plug context expression))) =
      (decodeCall old reference arguments).map (fun expression =>
        run registry fuel (atExpression base bindings (plug context expression))) := by
  rw [transported_call_decodes old target reference current nextReference nextTable moved arguments]

theorem cached_call_decodes (table : Table String) (cache : Cache 7)
    (good : Good table names cache) (index : Fin 7) (arguments : List Atom) :
    decodeCall table ⟨cache.owner, cache.ids index⟩ arguments =
      some (.expression (.symbol (names index) :: arguments)) := by
  simp [decodeCall, cached_reference_current table names cache good index, good.2 index]

/-- Live source callability is retained as a separate premise. The cached
family identification supplies the same written head, not a cached answer. -/
theorem cached_call_in_context (table : Table String) (cache : Cache 7)
    (good : Good table names cache) (index : Fin 7)
    (registry : SpaceSemantics.Program) (context : Context) (base : Configuration)
    (bindings : Subst) (arguments : List Atom) (frames : List Frame)
    (ready : frames? bindings context = some frames)
    (ordinary : sourceControlForm (.expression (.symbol (names index) :: arguments)) = false)
    (callableNow : callable registry (names index) = true) :
    ∃ expression, decodeCall table ⟨cache.owner, cache.ids index⟩ arguments = some expression ∧
      Relation.ReflTransGen (Transition registry)
        (atExpression base bindings (plug context expression))
        { base with
          control := .arguments bindings (.function (names index)) arguments [] 0
          frames := frames ++ base.frames } := by
  exact ⟨_, cached_call_decodes table cache good index arguments,
    written_call_in_context registry context base bindings (names index) arguments frames ready ordinary callableNow⟩

theorem cached_unknown_head_keeps_source_data_policy (table : Table String) (cache : Cache 7)
    (good : Good table names cache) (index : Fin 7) (registry : SpaceSemantics.Program)
    (base : Configuration) (bindings : Subst) (arguments : List Atom)
    (ordinary : sourceControlForm (.expression (.symbol (names index) :: arguments)) = false)
    (unknown : callable (codeRegistry registry base.privateCode) (names index) = false) :
    ∃ expression, decodeCall table ⟨cache.owner, cache.ids index⟩ arguments = some expression ∧
      step registry (atExpression base bindings expression) =
        some { base with control := .arguments bindings .data (.symbol (names index) :: arguments) [] 0 } := by
  exact ⟨_, cached_call_decodes table cache good index arguments,
    unknown_head_step registry base bindings (names index) arguments ordinary unknown⟩

theorem cached_quoted_call_stays_a_value (table : Table String) (cache : Cache 7)
    (good : Good table names cache) (index : Fin 7) (registry : SpaceSemantics.Program)
    (base : Configuration) (bindings : Subst) (arguments : List Atom) :
    ∃ expression, decodeCall table ⟨cache.owner, cache.ids index⟩ arguments = some expression ∧
      step registry (atExpression base bindings (.expression [.symbol "quote", expression])) =
        some { base with control := .returned [⟨resolve bindings expression, bindings⟩] } := by
  exact ⟨_, cached_call_decodes table cache good index arguments,
    quote_is_value registry base bindings _⟩

namespace Controls

def table : Table String := ⟨(4, 1), List.ofFn names ++ ["worker"], by decide⟩
def cache := compile table names

theorem public_and_native_questions_are_distinct :
    (query table names permits cache 1 (.publicCall 3)).1 = true ∧
      (query table names permits cache 1 (.nativeCall 3)).1 = false ∧
      (query table names permits cache 7 (.runCall 4)).1 = true := by decide

theorem recognized_family_does_not_supply_source_execution_authority :
    (query table names permits cache 1 (.publicCall 3)).1 = true ∧
      callable PeTTaActivation.Controls.emptyRegistry "transform" = false := by decide

theorem nonfamily_head_can_be_a_source_function :
    (query table names permits cache 8 (.publicCall 0)).1 = false ∧
      callable PeTTaCallCache.Controls.changedRegistry "worker" = true := by decide

theorem source_redefinition_is_not_an_id_cache_update :
    (query table names permits cache 8 (.publicCall 0)).1 = false ∧
      observed (run PeTTaCallCache.Controls.beforeBodyChange 40
        (start (Effects.loaded PeTTaCallCache.Controls.beforeBodyChange) PeTTaCallCache.Controls.worker)) =
          .answers [.symbol "before"] ∧
      observed (run PeTTaCallCache.Controls.afterBodyChange 40
        (start (Effects.loaded PeTTaCallCache.Controls.afterBodyChange) PeTTaCallCache.Controls.worker)) =
          .answers [.symbol "after"] :=
  ⟨by decide, PeTTaCallCache.Controls.classification_is_not_an_answer_cache.2⟩

end Controls

end Mettapedia.Languages.MeTTa.ContextualTransform.TransformHeadRecognition
