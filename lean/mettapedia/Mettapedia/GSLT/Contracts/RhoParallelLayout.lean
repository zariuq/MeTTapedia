import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalRepresentativeStep
import Mathlib.Data.List.Perm.Basic

/-!
# The authored rho step ignores the outer parallel layout

A permutation of one parallel bag transports the chosen occurrences
of a COMM (or the selected child of ParCong), leaving the residual
bag permuted. This is a direct result about the authored matcher,
not an inference from equality of source keys.

Only the outer layout is changed here: terms inside that bag are
unchanged. Full hereditary normalization also changes children's
spellings and is covered by separate coherence results.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.RhoParallelLayout

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open DerivedContextualStep (RhoStep)
open CanonicalRepresentativeStep (rhoStepAt_cases rhoStepAt_comm_at rhoStepAt_par_at
  canonicalize_hashBag_eq_of_perm)

private theorem select_under_perm {A : Type*} {left right : List A} (permutation : left.Perm right)
    {i : Nat} (inside : i < left.length) :
    ∃ (j : Nat) (inRight : j < right.length),
      right[j]'inRight = left[i] ∧ (left.eraseIdx i).Perm (right.eraseIdx j) := by
  obtain ⟨j, inRight, selects⟩ := List.mem_iff_getElem.mp
    (permutation.mem_iff.mp (List.getElem_mem inside))
  have leftFront := List.getElem_cons_eraseIdx_perm inside
  have rightFront := List.getElem_cons_eraseIdx_perm inRight
  rw [selects] at rightFront
  exact ⟨j, inRight, selects, (leftFront.trans (permutation.trans rightFront.symm)).cons_inv⟩

private theorem eq_of_result_permutation {left right : List Pattern} (same : left.Perm right) :
    canonicalize rhoReflectivePresentation (.collection .hashBag left none) =
      canonicalize rhoReflectivePresentation (.collection .hashBag right none) :=
  canonicalize_hashBag_eq_of_perm (parallelContents_perm _ (same.map _))

/-- Transport one raw step through any permutation of its outer bag.
Removing the selected input *before* transporting the selected
output preserves occurrence distinctness and all duplicate rows. -/
theorem permute_outer_step {elements arranged : List Pattern} {rest : Option String}
    (permutation : elements.Perm arranged) {target : Pattern}
    (step : RhoStep (.collection .hashBag elements rest) target) :
    ∃ result, RhoStep (.collection .hashBag arranged rest) result ∧
      canonicalize rhoReflectivePresentation target = canonicalize rhoReflectivePresentation result := by
  obtain ⟨fuel, atFuel⟩ := step
  rcases rhoStepAt_cases atFuel with
    ⟨pieces, tail, inputIndex, inputBound, outputIndex, outputBound, inputChannel, body,
      binder, outputChannel, payload, sourceEq, inputEq, outputEq, channels, targetEq⟩ |
    ⟨smaller, pieces, tail, index, bound, candidate, _, sourceEq, childStep, targetEq⟩
  · cases sourceEq
    obtain ⟨inputAt, inputIn, inputUnchanged, withoutInput⟩ :=
      select_under_perm permutation inputBound
    obtain ⟨outputAt, outputIn, outputUnchanged, withoutBoth⟩ :=
      select_under_perm withoutInput outputBound
    have transported := rhoStepAt_comm_at inputIn outputIn
      (inputUnchanged.trans inputEq) (outputUnchanged.trans outputEq) channels (termRest := rest)
    refine ⟨_, ⟨1, transported⟩, ?_⟩
    rw [targetEq]
    exact eq_of_result_permutation (List.Perm.cons _ withoutBoth)
  · cases sourceEq
    obtain ⟨position, available, same, kept⟩ := select_under_perm permutation bound
    have transported := rhoStepAt_par_at (termRest := rest) (index := position) available
      (same.symm ▸ childStep)
    refine ⟨_, ⟨smaller + 1, transported⟩, ?_⟩
    rw [targetEq]
    exact eq_of_result_permutation (List.Perm.cons _ kept)

/-- Sorting the outer frontier by any permutation-producing order
preserves and reflects the full set of canonical successor classes. -/
theorem successor_classes_iff {elements arranged : List Pattern} {rest : Option String}
    (permutation : elements.Perm arranged) (canonicalResult : Pattern) :
    (∃ target, RhoStep (.collection .hashBag elements rest) target ∧
      canonicalize rhoReflectivePresentation target = canonicalResult) ↔
    (∃ target, RhoStep (.collection .hashBag arranged rest) target ∧
      canonicalize rhoReflectivePresentation target = canonicalResult) := by
  constructor
  · rintro ⟨target, step, observes⟩
    obtain ⟨result, secondStep, agrees⟩ := permute_outer_step permutation step
    exact ⟨result, secondStep, agrees.symm.trans observes⟩
  · rintro ⟨target, step, observes⟩
    obtain ⟨result, secondStep, agrees⟩ := permute_outer_step permutation.symm step
    exact ⟨result, secondStep, agrees.symm.trans observes⟩

#print axioms permute_outer_step
#print axioms successor_classes_iff

end Mettapedia.GSLT.Contracts.RhoParallelLayout
