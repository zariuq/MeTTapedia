import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Carrier

/-!
# Compilation and readback on the whole clean target domain

Points are proof-bearing restrictions of the existing transform state type.
The certificate-based decoder is executable; selecting a certificate from
semantic membership uses choice. Equality of meanings is the source's actual
equations, not raw target-state equality and not an arbitrary relation that
identifies all states.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag

abbrev Point := {state : RawState // Clean state}

noncomputable def certificate (point : Point) : Certificate point.val := Classical.choice point.property
noncomputable def readback (point : Point) : RhoProcess := (certificate point).readback

def compile (process : RhoProcess) : Point :=
  ⟨Encodings.encode process, clean_of_represents (Encodings.encode_represents process)⟩

theorem readback_represents (point : Point) : ByInstantiation.Represents point.val (readback point) :=
  ⟨(certificate point).value, (certificate point).represents⟩

theorem readback_equations (point : Point) {process : RhoProcess}
    (represented : ByInstantiation.Represents point.val process) :
    rhoProcessEquations.r (readback point) process :=
  (certificate point).readback_equations represented

theorem representation_respects_equations {state : RawState} {first second : RhoProcess}
    (represented : ByInstantiation.Represents state first) (equal : rhoProcessEquations.r first second) :
    ByInstantiation.Represents state second := by
  obtain ⟨value, represented⟩ := represented
  refine ⟨value, represented.solvable, represented.determined, represented.closed, ?_⟩
  exact represented.inventory_eq.trans (congrArg Subtype.val ((fromProcess_eq_iff first second).mpr equal))

def Same (first second : Point) : Prop := rhoProcessEquations.r (readback first) (readback second)

def pointSetoid : Setoid Point where
  r := Same
  iseqv := ⟨fun _point => rhoProcessEquations.iseqv.refl _,
    fun same => rhoProcessEquations.iseqv.symm same,
    fun first second => rhoProcessEquations.iseqv.trans first second⟩

/-- The same meaning can be checked with any supplied row certificates. -/
theorem same_iff_inventory (first second : Point) (left : Certificate first.val) (right : Certificate second.val) :
    Same first second ↔ left.inventory = right.inventory := by
  have leftEq := readback_equations first ⟨left.value, left.represents⟩
  have rightEq := readback_equations second ⟨right.value, right.represents⟩
  have leftBags := (fromProcess_eq_iff _ _).mpr leftEq
  have rightBags := (fromProcess_eq_iff _ _).mpr rightEq
  simp only [Certificate.readback, fromProcess_toProcess] at leftBags rightBags
  change rhoProcessEquations.r (readback first) (readback second) ↔ _
  rw [← fromProcess_eq_iff, leftBags, rightBags]

theorem same_iff_common_process (first second : Point) :
    Same first second ↔ ∃ process : RhoProcess,
      ByInstantiation.Represents first.val process ∧ ByInstantiation.Represents second.val process := by
  constructor
  · intro same
    exact ⟨readback first, readback_represents first,
      representation_respects_equations (readback_represents second) (rhoProcessEquations.iseqv.symm same)⟩
  · rintro ⟨process, left, right⟩
    exact rhoProcessEquations.iseqv.trans (readback_equations first left)
      (rhoProcessEquations.iseqv.symm (readback_equations second right))

/-- Decoded points are canonical representatives. Equality of their declared
meanings is therefore equality of their actual decoded source processes. -/
theorem readback_eq_of_same {first second : Point} (same : Same first second) :
    readback first = readback second :=
  congrArg toProcess ((same_iff_inventory first second (certificate first) (certificate second)).mp same)

/-- The source round trip concerns the actual source equations. -/
theorem source_roundtrip (process : RhoProcess) :
    rhoProcessEquations.r (readback (compile process)) process :=
  readback_equations _ (Encodings.encode_represents process)

/-- Every clean point, including intermediate states, is reached by the
compiler up to the declared meaning equivalence. -/
theorem target_roundtrip (point : Point) : Same (compile (readback point)) point := source_roundtrip _

theorem compile_respects {first second : RhoProcess} (equal : rhoProcessEquations.r first second) :
    Same (compile first) (compile second) :=
  rhoProcessEquations.iseqv.trans (source_roundtrip first)
    (rhoProcessEquations.iseqv.trans equal (rhoProcessEquations.iseqv.symm (source_roundtrip second)))

theorem compile_reflects {first second : RhoProcess} (equal : Same (compile first) (compile second)) :
    rhoProcessEquations.r first second :=
  rhoProcessEquations.iseqv.trans (rhoProcessEquations.iseqv.symm (source_roundtrip first))
    (rhoProcessEquations.iseqv.trans equal (source_roundtrip second))

theorem compile_onto_meaning (point : Point) : ∃ process : RhoProcess, Same (compile process) point :=
  ⟨readback point, target_roundtrip point⟩

abbrev SourceQuotient := Quotient rhoProcessEquations
abbrev TargetQuotient := Quotient pointSetoid

/-- The genuine onto statement is between the source equation quotient and
the whole clean target quotient. It does not assert raw-state surjectivity. -/
noncomputable def quotientEquiv : SourceQuotient ≃ TargetQuotient where
  toFun := Quotient.map compile (fun _ _ equal => compile_respects equal)
  invFun := Quotient.map readback (fun _ _ equal => equal)
  left_inv := by
    intro point
    refine Quotient.inductionOn point ?_
    intro process
    exact Quotient.sound (source_roundtrip process)
  right_inv := by
    intro point
    refine Quotient.inductionOn point ?_
    intro state
    exact Quotient.sound (target_roundtrip state)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment
