import Mettapedia.Languages.TuringMachine.Bridges.Computability.ConditionalPrefix

/-!
# Controls for prefix-language compilation

A one-bit program returns the auxiliary string; extending that program is
rejected by the compiled table. Its halting mass is exactly one half.
A constantly returning general table accepts both the empty program and a
proper extension, separating effectiveness from prefix-freeness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine.Bridges.Computability.Controls

open KolmogorovComplexity
open scoped Classical ENNReal BigOperators

/-- A single one-bit program returns the auxiliary input; every other
program diverges. -/
def echoOnce : ConditionalPrefixFreeMachine where
  compute := fun program condition => if program = [false] then some condition else none
  prefix_free := by
    intro condition first second _ different active
    have first_eq : first = [false] := by
      by_contra not_one_bit
      simp [not_one_bit] at active
    have second_ne : second ≠ [false] := by
      intro same
      exact different (first_eq.trans same.symm)
    simp [second_ne]

theorem echoOnce_effective :
    Partrec₂ fun program condition => Part.ofOption (echoOnce.compute program condition) := by
  have computed : Primrec fun input : BinString × BinString =>
      if input.1 = [false] then some input.2 else none :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const [false]))
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  exact computed.to_comp.ofOption.to₂

theorem echoOnce_halts_iff (program condition : BinString) :
    HaltsFrom (ConditionalPrefix.machine echoOnce echoOnce_effective)
      (ConditionalPrefix.inputConfiguration echoOnce echoOnce_effective program condition).term ↔
      program = [false] := by
  rw [ConditionalPrefix.halts_iff]
  by_cases one_bit : program = [false] <;> simp [echoOnce, one_bit]

/-- An admitted one-bit program returns the exact auxiliary string. -/
theorem echoOnce_returns (condition : BinString) :
    ∃ final, final ∈ _root_.StateTransition.eval
      (ConditionalPrefix.machine echoOnce echoOnce_effective).next?
      (ConditionalPrefix.inputConfiguration echoOnce echoOnce_effective [false] condition) ∧
      PartrecBridge.Represents (ConditionalPrefix.programCode echoOnce echoOnce_effective)
        (Turing.PartrecToTM2.halt [Encodable.encode condition]) final := by
  apply ConditionalPrefix.output_preserved
  simp [echoOnce]

/-- Properly extending a halting program must not admit another program. -/
theorem echoOnce_rejects_extension (condition : BinString) :
    ¬ HaltsFrom (ConditionalPrefix.machine echoOnce echoOnce_effective)
      (ConditionalPrefix.inputConfiguration echoOnce echoOnce_effective [false, true] condition).term := by
  rw [echoOnce_halts_iff]
  decide

theorem echoOnce_mass (condition : BinString) :
    ConditionalPrefix.haltingMass echoOnce echoOnce_effective condition =
      prefixProgramWeight [false] := by
  unfold ConditionalPrefix.haltingMass prefixProgramMass
  have domain : ConditionalPrefix.HaltingPrograms echoOnce echoOnce_effective condition =
      {program | program = [false]} := by
    ext program
    exact echoOnce_halts_iff _ _
  rw [domain]
  simp only [Set.mem_ofPred_eq]
  rw [tsum_eq_single [false]]
  · exact if_pos rfl
  · intro other different
    exact if_neg different

theorem echoOnce_mass_half (condition : BinString) :
    ConditionalPrefix.haltingMass echoOnce echoOnce_effective condition = 1 / 2 := by
  rw [echoOnce_mass, prefixProgramWeight]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- A general effective source need not have a prefix-free halting domain.
The constantly returning table accepts both an empty program and its extension. -/
theorem constant_code_not_prefix_free :
    ¬ PrefixFree {program : BinString |
      HaltsFrom (PartrecBridge.machine Turing.ToPartrec.Code.zero)
        (PartrecBridge.inputConfiguration Turing.ToPartrec.Code.zero
          [Encodable.encode program]).term} := by
  intro free
  have terminates : ∀ program : BinString,
      HaltsFrom (PartrecBridge.machine Turing.ToPartrec.Code.zero)
        (PartrecBridge.inputConfiguration Turing.ToPartrec.Code.zero
          [Encodable.encode program]).term := by
    intro program
    rw [PartrecBridge.halts_iff, Turing.ToPartrec.Code.zero_eval]
    trivial
  exact free [] (terminates []) [false] (terminates [false]) (by decide) (by simp)

end Mettapedia.Languages.TuringMachine.Bridges.Computability.Controls
