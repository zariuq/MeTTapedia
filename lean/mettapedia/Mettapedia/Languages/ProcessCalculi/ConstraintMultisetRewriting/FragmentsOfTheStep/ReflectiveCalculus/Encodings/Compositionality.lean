import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.FirstHalf

/-!
# `encode` is not compositional at output or input in Gorla's sense

Gorla's Property 1 asks, for each operator `op` and set of names `N`, one context `C` with
`⟦op(S₁, …, Sₖ)⟧ = C(⟦S₁⟧; …; ⟦Sₖ⟧)`: the same translation on both sides. `encode_output` and
`encode_input` show that `encode` of an output or an input is the one-row state of its twin term: the
holes of the communication rule's pattern are filled with twin terms, not with `encode` of the
arguments.

With `encode` of the argument, no function does it, a fortiori no context:

* `0` and the one-element bag `{0}` are equal modulo the equations (`nil_equiv_bagZero`) and have the
  same translation, the empty state (`encode_nil`, `encode_bagZero`);
* the outputs `@0!(0)` and `@0!({0})`, the output prefix on `@0` applied to them (`liftNil_shape`,
  `liftBag_shape`), have different translations (`encode_lifts_differ`): their rows are different
  terms;
* so no function `C` of states gives `encode (@0!(P)) = C (encode P)` at both arguments
  (`output_not_compositional`); the same holds for the input prefix on `@(@0!(0))` with a continuation
  that does not use its binder (`input_not_compositional`).

**Control** (`twin_lift`): the twin translation itself is compositional at the output prefix, as a
former of terms; the single-row translation `encodeRow` is a context ("the state with this row")
applied to it, which is Gorla's two-level form, and is not homomorphic on parallel composition
(`encodeRow_not_homomorphic`). So the translation that is homomorphic on `|` is not compositional at
the prefixes, and the one built from a compositional translation of the prefixes is not homomorphic.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open ByInstantiation (sig G Closed read inputT outputT zeroT bagT pnilT pconsT quoteT groundFrame)

/-! ## Translations of rows -/

/-- The twin of the process read back from a closed twin term is that term. -/
theorem twin_rowProcess (t : G [] .pr) (closed : Closed t) :
    twin (ByInstantiation.rowProcess t closed) = t := by
  have translated : ByInstantiation.toTwin 0 .pr (read t) = some t := ByInstantiation.toTwin_read t 0 rfl
  exact Option.some.inj ((toTwin_twin (ByInstantiation.rowProcess t closed)).symm.trans translated)

theorem encode_rowProcess (t : G [] .pr) (closed : Closed t) :
    encode (ByInstantiation.rowProcess t closed) = encodeAt t := by
  unfold encode
  rw [twin_rowProcess]

/-- The read-back of the row with identity `0`, grounded. -/
def rowZero (s : ByInstantiation.State) : Pattern :=
  match instantiateObservation (ByInstantiation.someGrounding s.frame) (s.label 0) with
  | ⟨_, _, t⟩ => read t

theorem rowZero_single (t : G [] .pr) : rowZero (single t) = read t := by
  show read (instantiate (ByInstantiation.someGrounding groundFrame) t) = read t
  rw [ByInstantiation.instantiate_ground]

/-! ## The arguments: `0` and `{0}` -/

/-- `{0}`, the one-element bag, as a twin term. -/
abbrev bagZeroT : G [] .pr := bagT (pconsT zeroT pnilT)

/-- `{0}` as a closed process. -/
def bagZero : RhoProcess := ByInstantiation.rowProcess bagZeroT (by decide)

theorem encode_nil : encode nil = emptyState := by
  unfold nil
  rw [encode_rowProcess]
  rfl

theorem encode_bagZero : encode bagZero = emptyState := by
  unfold bagZero
  rw [encode_rowProcess]
  rfl

/-- **`0` and `{0}` are equal modulo the equations.** -/
theorem nil_equiv_bagZero : rhoProcessEquations.r nil bagZero := by
  apply (fromProcess_eq_iff _ _).mp
  apply Subtype.ext
  rw [fromProcess_primes, fromProcess_primes]
  change primes (read (zeroT : G [] .pr)) = primes (read bagZeroT)
  rw [ByInstantiation.primes_bag_parts]
  change primes (.apply "PZero" []) = primes (.apply "PZero" []) + primes (.collection .hashBag [] none)
  rw [ByInstantiation.primes_empty_bag, add_zero]

/-! ## The output prefix on `@0` -/

/-- `@0!(0)`. -/
def liftNil : RhoProcess := ByInstantiation.rowProcess (outputT ByInstantiation.nameZero zeroT) (by decide)

/-- `@0!({0})`. -/
def liftBag : RhoProcess :=
  ByInstantiation.rowProcess (outputT ByInstantiation.nameZero bagZeroT) (by decide)

/-- `liftNil` is the output prefix on `@0` applied to `0`. -/
theorem liftNil_shape : liftNil.1 = .apply "POutput" [read ByInstantiation.nameZero, nil.1] := rfl

/-- `liftBag` is the output prefix on `@0` applied to `{0}`. -/
theorem liftBag_shape : liftBag.1 = .apply "POutput" [read ByInstantiation.nameZero, bagZero.1] := rfl

theorem encode_liftNil : encode liftNil = single (outputT ByInstantiation.nameZero zeroT) := by
  unfold liftNil
  rw [encode_rowProcess]
  rfl

theorem encode_liftBag : encode liftBag = single (outputT ByInstantiation.nameZero bagZeroT) := by
  unfold liftBag
  rw [encode_rowProcess]
  rfl

/-- The two outputs have different translations: their rows are different terms. -/
theorem encode_lifts_differ : encode liftNil ≠ encode liftBag := by
  intro same
  have rows := congrArg rowZero same
  rw [encode_liftNil, encode_liftBag, rowZero_single, rowZero_single] at rows
  revert rows
  decide

/-- **`encode` is not compositional at output**: no function of the translated payload gives the
translated output. -/
theorem output_not_compositional :
    ¬ ∃ C : ByInstantiation.State → ByInstantiation.State,
      C (encode nil) = encode liftNil ∧ C (encode bagZero) = encode liftBag := by
  rintro ⟨C, atNil, atBag⟩
  rw [encode_nil] at atNil
  rw [encode_bagZero] at atBag
  exact encode_lifts_differ (atNil.symm.trans atBag)

/-! ## The input prefix on `@(@0!(0))`, with a continuation that does not use its binder -/

/-- The channel `@(@0!(0))`. -/
abbrev otherName : G [] .nm := quoteT ByInstantiation.outputZero

/-- `@(@0!(0))(y).0`. -/
def inputNil : RhoProcess := ByInstantiation.rowProcess (inputT otherName zeroT) (by decide)

/-- `@(@0!(0))(y).{0}`. -/
def inputBag : RhoProcess :=
  ByInstantiation.rowProcess (inputT otherName (bagT (pconsT zeroT pnilT))) (by decide)

theorem encode_inputNil : encode inputNil = single (inputT otherName zeroT) := by
  unfold inputNil
  rw [encode_rowProcess]
  rfl

theorem encode_inputBag : encode inputBag = single (inputT otherName (bagT (pconsT zeroT pnilT))) := by
  unfold inputBag
  rw [encode_rowProcess]
  rfl

/-- **`encode` is not compositional at input**: no function of the translated continuation gives the
translated input. -/
theorem input_not_compositional :
    ¬ ∃ C : ByInstantiation.State → ByInstantiation.State,
      C (encode nil) = encode inputNil ∧ C (encode bagZero) = encode inputBag := by
  rintro ⟨C, atNil, atBag⟩
  rw [encode_nil] at atNil
  rw [encode_bagZero] at atBag
  have rows := congrArg rowZero (atNil.symm.trans atBag)
  rw [encode_inputNil, encode_inputBag, rowZero_single, rowZero_single] at rows
  revert rows
  decide

/-- **Control: the twin translation is compositional at the output prefix**, as a former of terms. -/
theorem twin_lift : twin liftNil = outputT ByInstantiation.nameZero (twin nil) ∧
    twin liftBag = outputT ByInstantiation.nameZero (twin bagZero) := by
  refine ⟨?_, ?_⟩
  · unfold liftNil nil
    rw [twin_rowProcess, twin_rowProcess]
  · unfold liftBag bagZero
    rw [twin_rowProcess, twin_rowProcess]

#print axioms twin_rowProcess
#print axioms encode_nil
#print axioms encode_bagZero
#print axioms nil_equiv_bagZero
#print axioms encode_lifts_differ
#print axioms output_not_compositional
#print axioms input_not_compositional
#print axioms twin_lift

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
