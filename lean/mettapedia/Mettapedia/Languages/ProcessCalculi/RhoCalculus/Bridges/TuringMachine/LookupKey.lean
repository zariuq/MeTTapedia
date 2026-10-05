import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Stack
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DropFreeTermination

/-!
# Reflective keys for state-symbol lookup

An output carrying the current state name and scanned-symbol code is ordinary
process data. Lifting that output creates a closed quoted key. This avoids
substituting into a literal quote. The existing depth-indexed structural
weights recover its state and symbol separately, so different pairs remain
different even modulo structural congruence. No finite alphabet bound is
needed. These keys also differ from every numeral-coded protocol port.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.LookupKey

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Stack DropFreeTermination

def data (state scanned : Nat) : Pattern := send (port state) (symbolCode scanned)

def key (state scanned : Nat) : Pattern := .apply "NQuote" [data state scanned]

private def inputAt (observed : Nat) : String → Nat → Nat :=
  fun constructor depth => if constructor = "PInput" ∧ depth = observed then 1 else 0

private def outputAt (observed : Nat) : String → Nat → Nat :=
  fun constructor depth => if constructor = "POutput" ∧ depth = observed then 1 else 0

private theorem inputAt_laws (observed : Nat) : NodeLaws (inputAt observed) := by
  constructor <;> intro depth <;> simp [inputAt]

private theorem outputAt_laws (observed : Nat) : NodeLaws (outputAt observed) := by
  constructor <;> intro depth <;> simp [outputAt]

private theorem inputAt_symbolCode (observed depth value : Nat) :
    weight (inputAt observed) depth (symbolCode value) =
      if depth = observed then value else 0 := by
  induction value with
  | zero => simp [symbolCode, zero, weight, weightArgs, inputAt]
  | succ value ih =>
      simp [symbolCode, receive, symbolPort, zero, weight, weightArgs, argDepth, inputAt, ih]
      split <;> simp_all [Nat.add_comm]

private theorem outputAt_symbolCode (observed depth value : Nat) :
    weight (outputAt observed) depth (symbolCode value) = 0 := by
  induction value with
  | zero => simp [symbolCode, zero, weight, weightArgs, outputAt]
  | succ value ih =>
      simp [symbolCode, receive, symbolPort, zero, weight, weightArgs, argDepth, outputAt, ih]

private theorem key_state (state scanned : Nat) :
    weight (inputAt 4) 0 (key state scanned) = state := by
  simp [key, data, port, send, weight, weightArgs, argDepth, inputAt, inputAt_symbolCode]

private theorem key_scanned (state scanned : Nat) :
    weight (inputAt 3) 0 (key state scanned) = scanned := by
  simp [key, data, port, send, weight, weightArgs, argDepth, inputAt, inputAt_symbolCode]

private theorem key_output (state scanned : Nat) :
    weight (outputAt 2) 0 (key state scanned) = 1 := by
  simp [key, data, port, send, weight, weightArgs, argDepth, outputAt, outputAt_symbolCode]

theorem key_sc_iff (state scanned otherState otherScanned : Nat) :
    StructuralCongruence (key state scanned) (key otherState otherScanned) ↔
      state = otherState ∧ scanned = otherScanned := by
  constructor
  · intro congruent
    have states := weight_sc (inputAt_laws 4) congruent 0
    have symbols := weight_sc (inputAt_laws 3) congruent 0
    simpa only [key_state, key_scanned] using And.intro states symbols
  · rintro ⟨rfl, rfl⟩
    exact .refl _

theorem key_not_port (state scanned index : Nat) :
    ¬ StructuralCongruence (key state scanned) (port index) := by
  intro congruent
  have outputs := weight_sc (outputAt_laws 2) congruent 0
  rw [key_output] at outputs
  have portOutputs : weight (outputAt 2) 0 (port index) = 0 := by
    simp [port, weight, weightArgs, argDepth, outputAt, outputAt_symbolCode]
  rw [portOutputs] at outputs
  exact Nat.one_ne_zero outputs

@[simp] theorem normalize_data (state scanned : Nat) :
    semanticNormalizeProc (data state scanned) = data state scanned := by
  simp [data, send, semanticNormalizeProc, normalize_symbolCode]

@[simp] theorem normalize_key (state scanned : Nat) :
    semanticNormalizeName (key state scanned) = key state scanned := by
  rw [key, semanticNormalizeName.eq_4 _ (by
    intro name same
    simp [data, send] at same), normalize_data]

@[simp] theorem subst_key (state scanned k : Nat) (replacement : Pattern) :
    semanticSubstName k replacement (key state scanned) = key state scanned := by
  unfold semanticSubstName semanticSubstNameMark
  rw [normalize_key]
  rfl

theorem key_coreShape (state scanned : Nat) :
    rhoNameCoreShape (key state scanned) = true := by
  simp [key, data, send, rhoNameCoreShape, rhoProcCoreShape, symbolCode_coreShape]

theorem key_binderSafe (state scanned depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" depth
      (key state scanned) = true := by
  simp [key, data, send, Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt,
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeListAt, symbolCode_binderSafe]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.LookupKey
