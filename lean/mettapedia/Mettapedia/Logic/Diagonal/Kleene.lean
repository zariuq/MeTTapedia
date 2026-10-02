import Mathlib.Computability.Halting
import Mettapedia.Logic.Diagonal.Lawvere

/-!
# Kleene's recursion theorem and Rice's theorem as instances of the diagonal

Codes of partial recursive functions run on codes: `TwoStageCode.run a x` is a
code that runs `a` on the number of `x`, reads the answer as a code, and runs
that code on its own input.  Up to *extensional equality of programs*
(`SameBehaviour`), this code map is point-surjective onto the computable maps
`Code → Code` (`TwoStageCode.pointSurjectiveOn`): every computable map is
represented by some code, by the s-m-n construction (`curry`).  The class of
computable maps is closed under diagonal composites
(`TwoStageCode.diagonalComposite_computable`).

* **Positive reading** (`kleene`): every computable `f : Code → Code` has a code
  `c` with `eval (f c) = eval c`.  This is the statement of Mathlib's
  `Nat.Partrec.Code.fixed_point` (Rogers' form of Kleene's second recursion
  theorem), obtained here from `Mettapedia.Logic.Diagonal.exists_fixedPoint`.
* **Negative reading** (`not_computablePred_of_extensional`): a computable
  decider of an extensional property that holds somewhere and fails somewhere
  would make the swap map computable, and its diagonal composite would be
  represented; the abstract Rice theorem
  (`Mettapedia.Logic.Diagonal.not_representable_decider`) forbids it.  In
  particular extensional equality of programs has no computable decider
  (`not_computablePred_sameBehaviour`).

**Controls.**  Syntactic equality of codes is computably decidable
(`computablePred_codeEq`); this does not contradict the diagonal, because
syntactic equality is not extensional (`codeEq_not_extensional`: two distinct
codes with one behaviour), so the swap of its decider may have a fixed point up
to `SameBehaviour`.

Mathlib's computability library uses `Classical.choice`; every theorem here
inherits it from there (`exists_code`, `eval_curry`, `primrec₂_curry`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Diagonal.Kleene

open Nat.Partrec (Code)
open Nat.Partrec.Code
open Encodable Denumerable

/-- Extensional equality of programs: the same partial function. -/
def SameBehaviour (code code' : Code) : Prop :=
  eval code = eval code'

theorem sameBehaviour_equivalence : Equivalence SameBehaviour :=
  ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩

/-- The two-stage program, with its first stage packed into one number: run the
code numbered `pair.unpair.1` on `pair.unpair.2`, read the answer as a code,
and run that code on `input`. -/
def twoStage (pair input : ℕ) : Part ℕ :=
  eval (ofNat Code pair.unpair.1) pair.unpair.2 >>= fun answer => eval (ofNat Code answer) input

theorem twoStage_partrec : Partrec₂ twoStage :=
  (eval_part.comp ((Computable.ofNat Code).comp (Computable.fst.comp (Computable.unpair.comp
      Computable.fst))) (Computable.snd.comp (Computable.unpair.comp Computable.fst))).bind
    (eval_part.comp ((Computable.ofNat Code).comp Computable.snd)
      (Computable.snd.comp Computable.fst)).to₂

/-- A code implementing the two-stage program. -/
structure TwoStageCode where
  code : Code
  eval_code : ∀ pair input, eval code (Nat.pair pair input) = Part.map encode (twoStage pair input)

theorem exists_twoStageCode : Nonempty TwoStageCode := by
  obtain ⟨code, evaluates⟩ := exists_code.1 twoStage_partrec
  exact ⟨⟨code, fun pair input => by simp [evaluates]⟩⟩

namespace TwoStageCode

variable (universal : TwoStageCode)

/-- **Codes run on codes**: `run a x` runs `a` on the number of `x`, reads the
answer as a code, and runs it. -/
def run (code argument : Code) : Code :=
  curry universal.code (Nat.pair (encode code) (encode argument))

theorem eval_run (code argument : Code) (input : ℕ) :
    eval (universal.run code argument) input =
      eval code (encode argument) >>= fun answer => eval (ofNat Code answer) input := by
  simp [run, eval_curry, universal.eval_code, twoStage, Part.map_id']

theorem run_computable : Computable₂ universal.run :=
  (primrec₂_curry.comp (Primrec.const universal.code)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
      (Primrec.encode.comp Primrec.snd))).to_comp

/-- **Point-surjectivity up to extensional equality**: every computable map
`Code → Code` is represented by a code. -/
theorem pointSurjectiveOn :
    PointSurjectiveOn universal.run SameBehaviour {F : Code → Code | Computable F} := by
  intro F computable
  have partrec : Nat.Partrec fun number => (Part.some (encode (F (ofNat Code number)))) :=
    Partrec.nat_iff.mp
      (Computable.encode.comp (computable.comp (Computable.ofNat Code))).partrec
  obtain ⟨code, evaluates⟩ := exists_code.1 partrec
  refine ⟨code, fun argument => ?_⟩
  funext input
  rw [eval_run, evaluates]
  simp

/-- The diagonal composite of a computable map is computable. -/
theorem diagonalComposite_computable {f : Code → Code} (computable : Computable f) :
    Computable (diagonalComposite universal.run f) :=
  computable.comp (universal.run_computable.comp Computable.id Computable.id)

end TwoStageCode

/-- **Kleene's recursion theorem** (Rogers' form), from the diagonal step:
every computable map of codes has a code with the same behaviour as its
image.  The statement is Mathlib's `Nat.Partrec.Code.fixed_point`. -/
theorem kleene {f : Code → Code} (computable : Computable f) :
    ∃ code, eval (f code) = eval code := by
  obtain ⟨universal⟩ := exists_twoStageCode
  obtain ⟨code, fixed⟩ := exists_fixedPoint_of_pointSurjectiveOn universal.pointSurjectiveOn f
    (universal.diagonalComposite_computable computable)
  exact ⟨code, fixed.symm⟩

/-- **Rice's theorem from the diagonal**: no computable decider of an
extensional property of codes that holds at `yes` and fails at `no`. -/
theorem not_computablePred_of_extensional {P : Code → Prop}
    (extensional : ∀ {code code' : Code}, SameBehaviour code code' → (P code ↔ P code'))
    {yes no : Code} (yesHolds : P yes) (noFails : ¬ P no) : ¬ ComputablePred P := by
  rintro ⟨decidable, computable⟩
  obtain ⟨universal⟩ := exists_twoStageCode
  let decider : Code → Bool := fun code => @decide (P code) (decidable code)
  have correct : ∀ code, decider code = true ↔ P code := fun code => by
    simp [decider]
  have swapComputable : Computable (swap decider yes no) :=
    Computable.cond computable (Computable.const no) (Computable.const yes)
  exact not_representable_decider universal.run SameBehaviour extensional correct yesHolds
    noFails (universal.pointSurjectiveOn _ (universal.diagonalComposite_computable swapComputable))

/-- Two codes with different behaviour: the constant zero and the successor. -/
theorem zero_ne_succ_behaviour : ¬ SameBehaviour Code.zero Code.succ := by
  intro same
  have atZero : (Part.some 0 : Part ℕ) = Part.some 1 := congrFun same 0
  exact absurd (Part.some_injective atZero) (by decide)

/-- **Extensional equality of programs has no computable decider.** -/
theorem not_computablePred_sameBehaviour :
    ¬ ComputablePred fun pair : Code × Code => SameBehaviour pair.1 pair.2 := by
  rintro ⟨decidable, computable⟩
  have fixed : ComputablePred fun code : Code => SameBehaviour code Code.zero :=
    ⟨fun code => decidable (code, Code.zero),
      computable.comp (Computable.id.pair (Computable.const Code.zero))⟩
  exact not_computablePred_of_extensional
    (P := fun code => SameBehaviour code Code.zero)
    (fun same => ⟨fun held => (sameBehaviour_equivalence.symm same).trans held,
      fun held => same.trans held⟩)
    (sameBehaviour_equivalence.refl Code.zero)
    (fun same => zero_ne_succ_behaviour (sameBehaviour_equivalence.symm same)) fixed

/-! ## Control: syntactic equality is decidable and not extensional -/

/-- **Control.**  Syntactic equality of codes is computably decidable. -/
theorem computablePred_codeEq : ComputablePred fun pair : Code × Code => pair.1 = pair.2 :=
  PrimrecPred.computablePred Primrec.eq

/-- Two distinct codes with one behaviour: syntactic equality is not
extensional, so the diagonal gives no contradiction for it. -/
theorem codeEq_not_extensional :
    SameBehaviour Code.zero (Code.comp Code.zero Code.zero) ∧
      Code.zero ≠ Code.comp Code.zero Code.zero := by
  refine ⟨?_, nofun⟩
  funext input
  change (Part.some 0 : Part ℕ) = (Part.some 0).bind fun _ => Part.some 0
  simp

end Mettapedia.Logic.Diagonal.Kleene
