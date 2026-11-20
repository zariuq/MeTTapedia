import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment.Operational

/-!
# Parallel composition on the clean rho fragment

The operation is the existing tensor of actual target states, with distinct
occurrence identities and declaration frames. No source process is executed
to manufacture a target step. The clean domain is closed, compilation is
homomorphic, and its equational meaning respects parallel contexts. This
sharing policy keeps contextual unknowns apart; it does not model arbitrary
shared unification variables or arbitrary transform contexts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag

theorem tensor_represents {left right : RawState} {first second : RhoProcess}
    (onLeft : ByInstantiation.Represents left first) (onRight : ByInstantiation.Represents right second) :
    ByInstantiation.Represents (Encodings.tensor left right) (Encodings.par first second) := by
  obtain ⟨leftValues, onLeft⟩ := onLeft
  obtain ⟨rightValues, onRight⟩ := onRight
  exact ⟨_, Encodings.tensor_represents onLeft onRight (Encodings.fromProcess_par first second)⟩

def parallel (first second : Point) : Point :=
  ⟨Encodings.tensor first.val second.val,
    clean_of_represents (tensor_represents (readback_represents first) (readback_represents second))⟩

theorem readback_parallel (first second : Point) :
    rhoProcessEquations.r (readback (parallel first second)) (Encodings.par (readback first) (readback second)) :=
  readback_equations _ (tensor_represents (readback_represents first) (readback_represents second))

theorem compile_parallel (first second : RhoProcess) :
    compile (Encodings.par first second) = parallel (compile first) (compile second) :=
  Subtype.ext (Encodings.encode_par first second)

theorem source_parallel_respects {first first' second second' : RhoProcess}
    (left : rhoProcessEquations.r first first') (right : rhoProcessEquations.r second second') :
    rhoProcessEquations.r (Encodings.par first second) (Encodings.par first' second') := by
  apply (fromProcess_eq_iff _ _).mp
  apply Subtype.ext
  rw [Encodings.fromProcess_par, Encodings.fromProcess_par,
    (fromProcess_eq_iff _ _).mpr left, (fromProcess_eq_iff _ _).mpr right]

/-- The chosen equational meaning is a congruence for this actual tensor,
unlike an arbitrary observational equivalence. -/
theorem parallel_respects {first first' second second' : Point}
    (left : Same first first') (right : Same second second') :
    Same (parallel first second) (parallel first' second') :=
  rhoProcessEquations.iseqv.trans (readback_parallel first second)
    (rhoProcessEquations.iseqv.trans (source_parallel_respects left right)
      (rhoProcessEquations.iseqv.symm (readback_parallel first' second')))

theorem parallel_comm (first second : Point) : Same (parallel first second) (parallel second first) := by
  apply (same_iff_common_process _ _).mpr
  refine ⟨Encodings.par (readback first) (readback second),
    tensor_represents (readback_represents first) (readback_represents second), ?_⟩
  apply representation_respects_equations
    (tensor_represents (readback_represents second) (readback_represents first))
  apply (fromProcess_eq_iff _ _).mp
  apply Subtype.ext
  rw [Encodings.fromProcess_par, Encodings.fromProcess_par, add_comm]

theorem parallel_assoc (first second third : Point) :
    Same (parallel (parallel first second) third) (parallel first (parallel second third)) := by
  apply (same_iff_common_process _ _).mpr
  let P := readback first
  let Q := readback second
  let R := readback third
  have left := tensor_represents
    (tensor_represents (readback_represents first) (readback_represents second)) (readback_represents third)
  have right := tensor_represents (readback_represents first)
    (tensor_represents (readback_represents second) (readback_represents third))
  refine ⟨Encodings.par (Encodings.par P Q) R, left, representation_respects_equations right ?_⟩
  apply (fromProcess_eq_iff _ _).mp
  apply Subtype.ext
  rw [Encodings.fromProcess_par, Encodings.fromProcess_par, Encodings.fromProcess_par,
    Encodings.fromProcess_par, add_assoc]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment
