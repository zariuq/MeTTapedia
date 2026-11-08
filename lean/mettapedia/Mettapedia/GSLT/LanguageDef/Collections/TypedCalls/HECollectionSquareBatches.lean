import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareCalls

/-! The actual range frontier is converted to argument packets and numeric
square calls occurrence by occurrence. Empty takes the stopped-argument route
and remains a terminal occurrence until the collector filters it. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareBatches

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HERangeSuperposeSource (NumericOrEmpty)

/-- Structural packet observation on the proved Number-or-Empty profile. -/
def packet (row : Result) : Result :=
  match row.1 with
  | .symbol "Empty" => row
  | _ => (Entry.Value.argumentPacket [row.1], row.2)

def squared : Entry.Value → Entry.Value
  | .grounded (.int value) => .grounded (.int (value * value))
  | value => value

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem argument_branches (world : World) (policy : Policy) (live : List Atom) (scope : List String)
    (lower upper : Int) (rows : List Result) (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) :
    Stateful.ArgumentBranchesRel current sourceSpace world live scope (HERangeUntypedEntry.rangeCall lower upper) [] rows
      (rows.map packet) world (policy := policy) := by
  induction rows with
  | nil => exact .nil
  | cons row rows ih =>
      have first := numeric row (by simp)
      have tail := ih (fun item member => numeric item (List.mem_cons_of_mem _ member))
      rcases row with ⟨value, frame⟩
      cases first with
      | number value =>
          simpa only [List.map_cons, packet, List.map_nil, List.singleton_append, argumentPrepend_packet] using
            (Stateful.ArgumentBranchesRel.continuing (head := (Entry.Value.grounded (.int value), frame))
              (by simp [ArgumentStopped, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
              (Stateful.ArgumentsRel.nil (frame := frame)) tail)
      | empty =>
          simpa only [List.map_cons, packet] using
            (Stateful.ArgumentBranchesRel.stopped (head := (Entry.Value.symbol "Empty", frame))
              (by simp [ArgumentStopped, Entry.Value.erase, IsEmptyOrErrorRel, Atom.empty,
                HERangeUntypedEntry.rangeCall]) tail)

theorem calls (world : World) (policy : Policy) (live : List Atom) (scope : List String)
    (rows : List Result) (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) :
    ∃ output,
      Stateful.CallsRel current sourceSpace world live scope (.symbol "Number")
        ((rows.map packet).map (functionAssemble (.symbol "sq"))) output world (policy := policy) ∧
      (∀ row ∈ output, NumericOrEmpty row.1) ∧ output.map Prod.fst = rows.map (fun row => squared row.1) := by
  induction rows with
  | nil => exact ⟨[], .nil, by simp, rfl⟩
  | cons row rows ih =>
      have first := numeric row (by simp)
      obtain ⟨rest, restRun, restNumeric, restValues⟩ := ih (fun item member => numeric item (List.mem_cons_of_mem _ member))
      rcases row with ⟨value, frame⟩
      cases first with
      | number value =>
          obtain ⟨after, called⟩ := HECollectionSquareCalls.number_call minimal nativePolicy external active primitive subtypes
            world policy frame live scope value
          refine ⟨(.grounded (.int (value * value)), after) :: rest, ?_, ?_, ?_⟩
          · simpa only [List.map_cons, packet, functionAssemble, Entry.Value.unpackArguments_packet, List.singleton_append,
              HECollectionSquareFrame.call] using
              Stateful.CallsRel.cons (head := (HECollectionSquareFrame.call value, frame)) called restRun
          · intro result member
            rcases List.mem_cons.mp member with rfl | member
            · exact .number _
            · exact restNumeric result member
          · simp only [List.map_cons, squared, restValues]
      | empty =>
          refine ⟨(.symbol "Empty", frame) :: rest, ?_, ?_, ?_⟩
          · simpa only [List.map_cons, packet, functionAssemble, Entry.Value.unpackArguments, List.singleton_append] using
              Stateful.CallsRel.cons (head := (Entry.Value.symbol "Empty", frame))
                (HECollectionSquareCalls.empty_call minimal nativePolicy external active primitive subtypes world policy frame live scope (.symbol "Number")) restRun
          · intro result member
            rcases List.mem_cons.mp member with rfl | member
            · exact .empty
            · exact restNumeric result member
          · simp only [List.map_cons, squared, restValues]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareBatches
