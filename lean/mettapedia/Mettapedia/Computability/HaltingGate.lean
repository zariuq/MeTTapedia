import Mathlib.Computability.Halting

/-!
# Rice's theorem from a halting gate

Rice's theorem for a kind of program follows from one construction.  Fix an
observation of programs.  A *halting gate* for it is a program that is never seen
to do anything and a computable way of placing a halting test in front of a
program: `gate program source` is observed exactly as `program` when the Mathlib
code `source` halts on `0`, and exactly as the silent program otherwise.

* `HaltingGate.not_computable`: a set of programs that is invariant under the
  observation, and neither empty nor everything, is not computably decidable.
  A decider would decide halting on `0`.
* `HaltingGate.coarsen`: a gate for an observation is a gate for every
  observation no finer than it, so the theorem holds for those too.
* `natPartrecGate`: Mathlib's codes observed through `Code.eval` have a gate.
  Other kinds of program supply their own gates.
-/

set_option autoImplicit false

namespace Mettapedia.Computability

universe u v w

variable {Program : Type u} {Observation : Type v} [Primcodable Program]

/-- Membership depends only on what the observation sees. -/
def ObservationInvariant (observe : Program → Observation) (programs : Set Program) : Prop :=
  ∀ first second, observe first = observe second → (first ∈ programs ↔ second ∈ programs)

/-- `coarse` identifies every pair of programs that `observe` identifies. -/
def NoFinerThan {Coarse : Type w} (coarse : Program → Coarse) (observe : Program → Observation) :
    Prop :=
  ∀ first second, observe first = observe second → coarse first = coarse second

/-- A halting test placed in front of programs, as seen by an observation. -/
structure HaltingGate (observe : Program → Observation) where
  silent : Program
  gate : Program → Nat.Partrec.Code → Program
  gate_computable : ∀ program, Computable (gate program)
  observe_gate_of_halts : ∀ program source, (source.eval 0).Dom →
    observe (gate program source) = observe program
  observe_gate_of_diverges : ∀ program source, ¬ (source.eval 0).Dom →
    observe (gate program source) = observe silent

namespace HaltingGate

variable {observe : Program → Observation}

/-- A gate for an observation is a gate for any observation no finer than it. -/
def coarsen (halting : HaltingGate observe) {Coarse : Type w} {coarse : Program → Coarse}
    (noFiner : NoFinerThan coarse observe) : HaltingGate coarse where
  silent := halting.silent
  gate := halting.gate
  gate_computable := halting.gate_computable
  observe_gate_of_halts program source halts :=
    noFiner _ _ (halting.observe_gate_of_halts program source halts)
  observe_gate_of_diverges program source diverges :=
    noFiner _ _ (halting.observe_gate_of_diverges program source diverges)

theorem not_computable_of_silent_not_mem (halting : HaltingGate observe) {programs : Set Program}
    (invariant : ObservationInvariant observe programs) {program : Program}
    (member : program ∈ programs) (silentOutside : halting.silent ∉ programs) :
    ¬ ComputablePred (· ∈ programs) := by
  rintro ⟨_, decider⟩
  apply ComputablePred.halting_problem 0
  have membership : ∀ source : Nat.Partrec.Code,
      (source.eval 0).Dom ↔ halting.gate program source ∈ programs := by
    intro source
    by_cases halts : (source.eval 0).Dom
    · exact ⟨fun _ => (invariant _ _ (halting.observe_gate_of_halts program source halts)).mpr member,
        fun _ => halts⟩
    · refine ⟨fun halted => absurd halted halts, fun gated => absurd ?_ silentOutside⟩
      exact (invariant _ _ (halting.observe_gate_of_diverges program source halts)).mp gated
  refine ⟨fun source => decidable_of_iff _ (membership source).symm, ?_⟩
  exact (decider.comp (halting.gate_computable program)).of_eq fun source =>
    decide_eq_decide.mpr (membership source).symm

/-- **Rice's theorem from a halting gate.** -/
theorem not_computable (halting : HaltingGate observe) {programs : Set Program}
    (invariant : ObservationInvariant observe programs)
    (nontrivial : programs.Nonempty ∧ programsᶜ.Nonempty) :
    ¬ ComputablePred (· ∈ programs) := by
  by_cases silentMember : halting.silent ∈ programs
  · obtain ⟨program, outside⟩ := nontrivial.2
    intro decidable
    exact halting.not_computable_of_silent_not_mem (programs := programsᶜ)
      (fun first second same => not_congr (invariant first second same)) outside
      (fun outsideSilent => outsideSilent silentMember) decidable.not
  · obtain ⟨program, member⟩ := nontrivial.1
    exact halting.not_computable_of_silent_not_mem invariant member silentMember

end HaltingGate

/-! ## Mathlib's partial recursive codes -/

open Nat.Partrec (Code)

theorem exists_silentCode : ∃ silent : Code, silent.eval = fun _ => Part.none :=
  Code.exists_code.mp Nat.Partrec.none

/-- A code that halts on no input. -/
noncomputable def silentCode : Code := Classical.choose exists_silentCode

theorem silentCode_eval (input : ℕ) : silentCode.eval input = Part.none := by
  rw [silentCode, Classical.choose_spec exists_silentCode]

/-- Monadic sequencing in `Part` with a partial function on the right, eta-expanded
so that `Part.bind` lemmas apply. -/
theorem bind_partialFunction {α β : Type u} (x : Part α) (f : α →. β) :
    x >>= f = x.bind fun a => f a := rfl

/-- Run `source` on `0`, discard its result, then run `program` on the input. -/
def gateCode (program source : Code) : Code :=
  .comp program (.comp .right (.pair (.comp source .zero) .id))

theorem gateCode_eval (program source : Code) (input : ℕ) :
    (gateCode program source).eval input = (source.eval 0).bind fun _ => program.eval input := by
  have pureApply : ∀ n : ℕ, (pure 0 : ℕ →. ℕ) n = Part.some 0 := fun _ => rfl
  apply Part.ext
  intro output
  simp [gateCode, Code.eval, Seq.seq, Part.mem_bind_iff, pureApply, bind_partialFunction,
    PFun.coe_val]

theorem gateCode_computable (program : Code) : Computable (gateCode program) :=
  (Code.primrec₂_comp.comp (Primrec.const program)
    (Code.primrec₂_comp.comp (Primrec.const Code.right)
      (Code.primrec₂_pair.comp (Code.primrec₂_comp.comp Primrec.id (Primrec.const Code.zero))
        (Primrec.const Code.id)))).to_comp

/-- **Mathlib's codes, observed through evaluation, have a halting gate.** -/
noncomputable def natPartrecGate : HaltingGate Code.eval where
  silent := silentCode
  gate := gateCode
  gate_computable := gateCode_computable
  observe_gate_of_halts program source halts := by
    funext input
    rw [gateCode_eval, Part.eq_some_iff.mpr (Part.dom_iff_mem.mp halts).choose_spec]
    simp
  observe_gate_of_diverges program source diverges := by
    funext input
    rw [gateCode_eval, silentCode_eval, Part.eq_none_iff'.mpr diverges]
    simp

/-- Rice's theorem for Mathlib's codes, as an instance of the gate. -/
theorem natPartrec_not_computable {programs : Set Code}
    (invariant : ObservationInvariant Code.eval programs)
    (nontrivial : programs.Nonempty ∧ programsᶜ.Nonempty) :
    ¬ ComputablePred (· ∈ programs) :=
  natPartrecGate.not_computable invariant nontrivial

/-- **Invariance is load-bearing.**  The set containing only `Code.zero` is
nontrivial and decidable, and it is not invariant under evaluation. -/
theorem singleton_zero_escapes :
    ¬ ObservationInvariant Code.eval {Code.zero} ∧
      ({Code.zero} : Set Code).Nonempty ∧ ({Code.zero}ᶜ : Set Code).Nonempty ∧
      ComputablePred (· ∈ ({Code.zero} : Set Code)) := by
  refine ⟨fun invariant => ?_, ⟨_, rfl⟩, ⟨Code.succ, by simp⟩,
    ComputablePred.computable_iff.mpr ⟨fun program => decide (Encodable.encode program =
      Encodable.encode Code.zero), (Primrec.eq.comp Primrec.encode (Primrec.const _)).decide.to_comp,
      by funext program; simp [Encodable.encode_inj]⟩⟩
  have same : Code.zero.eval = (Code.comp Code.zero Code.zero).eval := by
    funext input
    exact (Part.bind_some _ _).symm
  exact absurd ((invariant _ _ same).mp rfl) (by simp)

#print axioms HaltingGate.not_computable
#print axioms natPartrec_not_computable
#print axioms singleton_zero_escapes

end Mettapedia.Computability
