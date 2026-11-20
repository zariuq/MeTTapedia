import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CellProposals
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Execution

/-!
# Finite proposal data for the actual checked-cell step

The packet carries a table ordinal and the output words. Decoding constructs
a total proposal from this finite data and checks coherence when the same key
occurs at several output positions. Successful decoding yields a canonical
firing. Every raw firing has such a packet with the same admission and result.
This is a local executable presentation; the ambient interface stays general.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FiniteCells

open Mettapedia.Machines.TIsa Cells CellEffects Control
open Kernel.CellOccurrences Kernel.CellProposals

universe u
variable {Key : Type u} [DecidableEq Key]

def lookup : List Key → List Word → Key → Option Word
  | first :: rest, value :: later, key => if key = first then some value else lookup rest later key
  | _, _, _ => none

theorem lookup_mapped (keys : List Key) (values : Key → Word) (key : Key) (member : key ∈ keys) :
    lookup keys (keys.map values) key = some (values key) := by
  induction keys with
  | nil => cases member
  | cons first rest ih =>
    by_cases same : key = first
    · subst first
      simp [lookup]
    · have later : key ∈ rest := (List.mem_cons.mp member).resolve_left same
      simpa [lookup, same] using ih later

def unpack {edges : List (Edge Key)} (code : OutputCode edges) : Firing edges where
  ordinal := code.1
  candidate key := (lookup edges[code.1].effect.outputs (List.ofFn code.2) key).getD 0

omit [DecidableEq Key] in
theorem code_list (keys : List Key) (values : Key → Word) :
    List.ofFn (fun index : Fin keys.length => values keys[index]) = keys.map values := by
  apply List.ext_getElem (by simp)
  intro index _ _
  simp

theorem unpack_outputCode {edges : List (Edge Key)} (firing : Firing edges) :
    outputCode (unpack (outputCode firing)) = outputCode firing := by
  apply congrArg (Sigma.mk firing.ordinal)
  funext index
  change (lookup firing.edge.effect.outputs
    (List.ofFn (fun i : Fin firing.edge.effect.outputs.length => firing.candidate firing.edge.effect.outputs[i]))
    firing.edge.effect.outputs[index]).getD 0 = firing.candidate firing.edge.effect.outputs[index]
  rw [code_list]
  exact congrArg (fun out : Option Word => out.getD 0)
    (lookup_mapped firing.edge.effect.outputs firing.candidate firing.edge.effect.outputs[index]
      (List.getElem_mem index.isLt))

def decode? {edges : List (Edge Key)} (code : OutputCode edges) : Option (Firing edges) :=
  if outputCode (unpack code) = code then some (normalize (unpack code)) else none

/-- Unused total-function values are erased by an actual finite decoder. -/
theorem decode_outputCode {edges : List (Edge Key)} (firing : Firing edges) :
    decode? (outputCode firing) = some (normalize firing) := by
  rw [decode?, if_pos (unpack_outputCode firing)]
  exact congrArg some ((normalize_eq_iff_code_eq _ _).mpr (unpack_outputCode firing))

theorem decode_sound {edges : List (Edge Key)} {code : OutputCode edges} {firing : Firing edges}
    (decoded : decode? code = some firing) :
    normalize firing = firing ∧ outputCode firing = code := by
  unfold decode? at decoded
  split at decoded
  · rename_i coherent
    cases Option.some.inj decoded
    exact ⟨normalize_idempotent _, (outputCode_normalize _).trans coherent⟩
  · cases decoded

/-- Read an untrusted ordinal and list of words without truncation,
padding or modular reduction of an out-of-range ordinal. -/
def packet? (edges : List (Edge Key)) (ordinal : Nat) (words : List Word) : Option (OutputCode edges) :=
  if inside : ordinal < edges.length then
    let index : Fin edges.length := ⟨ordinal, inside⟩
    if size : words.length = edges[index].effect.outputs.length then
      some ⟨index, fun slot => words[slot.val]'(by rw [size]; exact slot.isLt)⟩
    else none
  else none

omit [DecidableEq Key] in
theorem packet_outputCode {edges : List (Edge Key)} (firing : Firing edges) :
    packet? edges firing.ordinal.val (outputWords firing.edge firing.candidate) = some (outputCode firing) := by
  rcases firing with ⟨⟨ordinal, bound⟩, candidate⟩
  simp [packet?, outputWords, outputCode, Firing.edge, bound]

def fire? (edges : List (Edge Key)) (state : State Key) (code : OutputCode edges) : Option (State Key) :=
  match decode? code with
  | none => none
  | some firing =>
      if CheckedAdmission.eligible firing.edge state.keys state.values firing.candidate then
        some (result state firing)
      else none

theorem fire_sound {edges : List (Edge Key)} {state after : State Key} {code : OutputCode edges}
    (fired : fire? edges state code = some after) :
    LogicOverTheStep.StepSpan.Succ (step edges) state after := by
  unfold fire? at fired
  cases decoded : decode? code with
  | none => simp [decoded] at fired
  | some firing =>
    simp only [decoded] at fired
    split at fired
    · rename_i admitted
      exact ⟨firing, admitted, Option.some.inj fired⟩
    · cases fired

theorem fire_complete (edges : List (Edge Key)) (state : State Key) (firing : Firing edges)
    (admitted : (step edges).Admits (s := state) firing) :
    fire? edges state (outputCode firing) = some (result state firing) := by
  unfold fire?
  rw [decode_outputCode]
  have normalized := (admission_normalize edges state firing).mpr admitted
  change CheckedAdmission.eligible (normalize firing).edge state.keys state.values
    (normalize firing).candidate at normalized
  change (if CheckedAdmission.eligible (normalize firing).edge state.keys state.values
    (normalize firing).candidate then some (result state (normalize firing)) else none) = _
  rw [if_pos normalized]
  exact congrArg some (result_normalize edges state firing)

theorem successor_iff_packet (edges : List (Edge Key)) (state after : State Key) :
    LogicOverTheStep.StepSpan.Succ (step edges) state after ↔
      ∃ code : OutputCode edges, fire? edges state code = some after := by
  constructor
  · rintro ⟨firing, admitted, rfl⟩
    exact ⟨outputCode firing, fire_complete edges state firing admitted⟩
  · rintro ⟨code, fired⟩
    exact fire_sound fired

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FiniteCells

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FiniteCells.decode_outputCode
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FiniteCells.successor_iff_packet
