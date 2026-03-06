import Algorithms.MeTTa.Simple.Backend.ReferenceEvalContracts

namespace Algorithms.MeTTa.Simple.Backend.ReferenceEvalSoundness

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple.Backend.ReferenceEval
open Algorithms.MeTTa.Simple.Backend.ReferenceEvalContracts

variable {σ : Type}

abbrev EvalCfg (σ : Type) := σ × Pattern
abbrev AuxCfg (σ : Type) := AuxState σ

inductive RTC {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl (x : α) : RTC R x x
  | tail {x y z : α} : R x y → RTC R y z → RTC R x z

/-- Concrete machine-step relation induced directly by `stepAux`. -/
def AuxMachineStep (I : Interface σ) : AuxCfg σ → AuxCfg σ → Prop :=
  fun st st' =>
    ∃ nxt : AuxCfg σ,
      stepAux I st = .inl nxt ∧
      st' = { s := nxt.s, fuel := st.fuel - 1, pending := nxt.pending, normals := nxt.normals }

theorem evalAuxStateful_reaches_terminal
    (I : Interface σ)
    (s : σ) (fuel : Nat) (pending : List (Pattern × Nat)) (normals : List Pattern)
    (s' : σ) (out : List Pattern)
    (hEval : evalAuxStateful I s fuel pending normals = (s', out)) :
    ∃ stf : AuxCfg σ,
      RTC (AuxMachineStep I) { s := s, fuel := fuel, pending := pending, normals := normals } stf ∧
      stepAux I stf = .inr (s', out) := by
  induction fuel generalizing s pending normals with
  | zero =>
      refine ⟨{ s := s, fuel := 0, pending := pending, normals := normals }, RTC.refl _, ?_⟩
      have hPair : (s, normals.reverse ++ pending.map Prod.fst) = (s', out) := by
        simpa [evalAuxStateful] using hEval
      cases hPair
      simp [stepAux]
  | succ fuel ih =>
      let st0 : AuxCfg σ := { s := s, fuel := fuel + 1, pending := pending, normals := normals }
      cases hStep : stepAux I st0 with
      | inr res =>
          refine ⟨st0, RTC.refl _, ?_⟩
          have hEvalRes : evalAuxStateful I s (fuel + 1) pending normals = res := by
            simp [evalAuxStateful, st0, hStep]
          have hRes : res = (s', out) := hEvalRes.symm.trans hEval
          simpa [hRes] using hStep
      | inl st1 =>
          have hRecEq :
              evalAuxStateful I s (fuel + 1) pending normals =
                evalAuxStateful I st1.s fuel st1.pending st1.normals := by
            simp [evalAuxStateful, st0, hStep]
          have hEval1 : evalAuxStateful I st1.s fuel st1.pending st1.normals = (s', out) := by
            exact hRecEq.symm.trans hEval
          rcases ih (s := st1.s) (pending := st1.pending) (normals := st1.normals) hEval1 with
            ⟨stf, hRtc, hTerm⟩
          refine ⟨stf, ?_, hTerm⟩
          have hFirst :
              AuxMachineStep I st0
                { s := st1.s, fuel := fuel, pending := st1.pending, normals := st1.normals } := by
            refine ⟨st1, hStep, ?_⟩
            simp [st0]
          exact RTC.tail hFirst hRtc

theorem evalWithStateCore_reaches_terminal
    (I : Interface σ)
    (s s' : σ) (term : Pattern) (out : List Pattern)
    (hEval : evalWithStateCore I s term = (s', out)) :
    ∃ stf : AuxCfg σ,
      RTC (AuxMachineStep I)
        { s := s, fuel := I.maxNodes s, pending := [(term, 0)], normals := [] } stf ∧
      stepAux I stf = .inr (s', out) := by
  exact
    evalAuxStateful_reaches_terminal I s (I.maxNodes s) [(term, 0)] [] s' out
      (by simpa [evalWithStateCore_unfold] using hEval)

theorem evalWithStateCore_member_has_machine_trace
    (I : Interface σ)
    (s s' : σ) (term t : Pattern) (out : List Pattern)
    (hEval : evalWithStateCore I s term = (s', out))
    (hMem : t ∈ out) :
    ∃ stf : AuxCfg σ,
      RTC (AuxMachineStep I)
        { s := s, fuel := I.maxNodes s, pending := [(term, 0)], normals := [] } stf ∧
      stepAux I stf = .inr (s', out) ∧
      t ∈ out := by
  rcases evalWithStateCore_reaches_terminal I s s' term out hEval with ⟨stf, hRtc, hTerm⟩
  exact ⟨stf, hRtc, hTerm, hMem⟩

/-- Concrete result-step relation induced by `evalWithStateCore`. -/
def EvalCoreStep (I : Interface σ) : EvalCfg σ → EvalCfg σ → Prop :=
  fun x y =>
    let res := evalWithStateCore I x.1 x.2
    y.1 = res.1 ∧ y.2 ∈ res.2

theorem evalWithStateCore_sound_from_evalAux
    (I : Interface σ)
    (s s' : σ) (term t : Pattern) (out : List Pattern)
    (hEval : evalWithStateCore I s term = (s', out))
    (hMem : t ∈ out) :
    RTC (EvalCoreStep I) (s, term) (s', t) := by
  have _ :=
    evalWithStateCore_member_has_machine_trace I s s' term t out hEval hMem
  have hStep : EvalCoreStep I (s, term) (s', t) := by
    dsimp [EvalCoreStep]
    constructor
    · simp [hEval]
    · simpa [hEval] using hMem
  exact RTC.tail hStep (RTC.refl (s', t))

end Algorithms.MeTTa.Simple.Backend.ReferenceEvalSoundness
