import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Core.Induction.Goertzel
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples.SemidirectNoSeparation

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples

open Classical KnuthSkillingAlgebra
open Mettapedia.ProbabilityTheory.KnuthSkilling.Additive

/-!
# `NewAtomCommutes` is not derivable from the base axioms

This file records a minimal negative result about the extra hypothesis used to unblock the
`B = ∅` extension step in `.../Core/Induction/Goertzel.lean`.

`SemidirectNoSeparation` builds a noncommutative `KnuthSkillingAlgebra` (`SD`).  Taking a singleton
atom-family on `exX` and the “new atom” `exY`, `NewAtomCommutes` fails.

This does **not** address the harder open question “is `NewAtomCommutes` forced by `KSSeparation`?”,
because the semidirect model is explicitly constructed to *fail* `KSSeparation`.
-/

theorem exists_not_newAtomCommutes :
    ∃ (F : AtomFamily SD 1) (d : SD), ¬ NewAtomCommutes F d := by
  -- Build a 1-atom family with atom `exX`.
  have hle : (ident : SD) ≤ SD.exX := ident_le _
  have hne : (ident : SD) ≠ SD.exX := by
    simp [KnuthSkillingAlgebraBase.ident, SD.ident, SD.exX]
  have hpos : (ident : SD) < SD.exX := lt_of_le_of_ne hle hne
  let F : AtomFamily SD 1 := singletonAtomFamily (α := SD) SD.exX hpos
  refine ⟨F, SD.exY, ?_⟩
  intro hcomm
  have h0 := hcomm ⟨0, by decide⟩
  have :
      KnuthSkillingAlgebraBase.op SD.exX SD.exY = KnuthSkillingAlgebraBase.op SD.exY SD.exX := by
    simpa [NewAtomCommutes, F, singletonAtomFamily] using h0
  exact SD.op_not_comm this

private lemma op_comm_of_iter2_decompose {α : Type*} [KnuthSkillingAlgebra α] (a d : α)
    (h :
      iterate_op (op a d) 2 =
        op (iterate_op a 2) (iterate_op d 2)) :
    op a d = op d a := by
  -- Expand the `2`-fold iterates and cancel.
  have h0 : op (op a d) (op a d) = op (op a a) (op d d) := by
    simpa [KnuthSkillingAlgebra.iterate_op, op_ident_right] using h
  have h1 : op a (op d (op a d)) = op a (op a (op d d)) := by
    calc
      op a (op d (op a d)) = op (op a d) (op a d) := by
        simpa using (op_assoc a d (op a d)).symm
      _ = op (op a a) (op d d) := h0
      _ = op a (op a (op d d)) := by
        simpa using (op_assoc a a (op d d))
  have h2 : op d (op a d) = op a (op d d) := (op_strictMono_right a).injective h1
  have h3 : op (op d a) d = op (op a d) d := by
    calc
      op (op d a) d = op d (op a d) := by simpa using (op_assoc d a d)
      _ = op a (op d d) := h2
      _ = op (op a d) d := by simpa using (op_assoc a d d).symm
  exact (op_strictMono_left d).injective h3.symm

theorem exists_not_newAtomDecompose :
    ∃ (F : AtomFamily SD 1) (d : SD), ¬ NewAtomDecompose F d := by
  -- Use the same 1-atom family with atom `exX`.
  have hle : (ident : SD) ≤ SD.exX := ident_le _
  have hne : (ident : SD) ≠ SD.exX := by
    simp [KnuthSkillingAlgebraBase.ident, SD.ident, SD.exX]
  have hpos : (ident : SD) < SD.exX := lt_of_le_of_ne hle hne
  let F : AtomFamily SD 1 := singletonAtomFamily (α := SD) SD.exX hpos
  refine ⟨F, SD.exY, ?_⟩
  intro hdec
  have hdec' := hdec (unitMulti (k := 1) ⟨0, by decide⟩ 1) 1 2
  have hμ : mu F (unitMulti (k := 1) ⟨0, by decide⟩ 1) = SD.exX := by
    simpa [F, singletonAtomFamily, KnuthSkillingAlgebra.iterate_op_one] using (mu_unitMulti F ⟨0, by decide⟩ 1)
  have hop :
      KnuthSkillingAlgebraBase.op SD.exX SD.exY = KnuthSkillingAlgebraBase.op SD.exY SD.exX := by
    -- Specialize the decomposition law to `r = exX`, `u = 1`, `m = 2`, then cancel as above.
    have hiter :
        iterate_op (op SD.exX SD.exY) 2 =
          op (iterate_op SD.exX 2) (iterate_op SD.exY 2) := by
      simpa [NewAtomDecompose, hμ, KnuthSkillingAlgebra.iterate_op_one] using hdec'
    simpa using (op_comm_of_iter2_decompose (a := SD.exX) (d := SD.exY) hiter)
  exact SD.op_not_comm hop

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples
