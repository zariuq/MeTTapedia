import Mettapedia.Languages.ProcessCalculi.CCS.Bialgebraic
import Mettapedia.OSLF.Bridges.TypeTheory.FiniteBranchingHypersetSemantics

/-!
# Material hyperset semantics of the finite-name CCS fragment

Input, output and silent actions have distinct finite-ordinal readings.
Decorating the actual CCS transition graph agrees with first taking its
initial-to-final GSOS semantics. Material equality is exactly the existing
CCS bisimilarity. The comparison preserves parallel congruence and the bag
laws, while still identifying distinct programs and omitting a silent-loop
behaviour from the image of the finite process syntax.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.CCS.HypersetSemantics

open Bialgebraic
open Mettapedia.OSLF.FiniteBranching
open Mettapedia.TypeTheory.MaterialSets.Hypersets

variable {count : Nat}

/-- Zero is silent; positive odd/even codes distinguish input and output. -/
def labelNumber : Label (Fin count) → Nat
  | .input name => 2 * name.val + 1
  | .output name => 2 * name.val + 2
  | .tau => 0

theorem labelNumber_injective : Function.Injective (labelNumber (count := count)) := by
  intro first second same
  cases first <;> cases second <;> simp only [labelNumber] at same
  all_goals first | rfl | omega | (congr 1; apply Fin.ext; omega)

def labels (_ : (signature (Fin count)).Srt) (action : Label (Fin count)) : HSet.{0} :=
  HSet.numeralLabel (labelNumber action)

theorem labels_injective (sort : (signature (Fin count)).Srt) :
    Function.Injective (labels (count := count) sort) :=
  HSet.numeralLabel_injective.comp labelNumber_injective

def meaning (process : Closed (Fin count)) : HSet.{0} :=
  OSLF.FiniteBranching.HypersetSemantics.readout (closedSystem (Fin count)) labels
    PUnit.unit () process

theorem meaning_eq_iff_bisimilar (first second : Closed (Fin count)) :
    meaning first = meaning second ↔ Bialgebraic.Bisimilar first second :=
  OSLF.FiniteBranching.HypersetSemantics.readout_eq_iff_bisimilar
    (closedSystem (Fin count)) (closedSystem (Fin count))
    labels labels_injective PUnit.unit () first second

/-- The material reading is the same along the independent final-tree route. -/
theorem meaning_via_final (process : Closed (Fin count)) :
    OSLF.FiniteBranching.HypersetSemantics.readout
        (FinalSemantics.finalObject (signature (Fin count)) (actions (Fin count))) labels
        PUnit.unit () ((FinalBialgebra.semantics (law (Name := Fin count))).f.f
          PUnit.unit () process) = meaning process :=
  OSLF.FiniteBranching.HypersetSemantics.initial_final_readout _ labels PUnit.unit () process

theorem parallel_congr {left left' right right' : Closed (Fin count)}
    (sameLeft : meaning left = meaning left') (sameRight : meaning right = meaning right') :
    meaning (Bialgebraic.par left right) = meaning (Bialgebraic.par left' right') :=
  (meaning_eq_iff_bisimilar _ _).mpr
    (par_congr ((meaning_eq_iff_bisimilar _ _).mp sameLeft)
      ((meaning_eq_iff_bisimilar _ _).mp sameRight))

theorem parallel_unit (process : Closed (Fin count)) :
    meaning (Bialgebraic.par process Bialgebraic.nil) = meaning process :=
  (meaning_eq_iff_bisimilar _ _).mpr (par_nil_bisimilar process)

theorem parallel_comm (left right : Closed (Fin count)) :
    meaning (Bialgebraic.par left right) = meaning (Bialgebraic.par right left) :=
  (meaning_eq_iff_bisimilar _ _).mpr (par_comm_bisimilar left right)

theorem parallel_assoc (first second third : Closed (Fin count)) :
    meaning (Bialgebraic.par (Bialgebraic.par first second) third) =
      meaning (Bialgebraic.par first (Bialgebraic.par second third)) :=
  (meaning_eq_iff_bisimilar _ _).mpr (par_assoc_bisimilar first second third)

/-- Canonical semantics still loses the distinction between two programs. -/
theorem meaning_not_injective : ¬ Function.Injective (meaning (count := count)) := by
  intro injective
  exact nil_ne_par_nil (injective (parallel_unit (Bialgebraic.nil : Closed (Fin count))))

def loopMeaning : HSet.{0} :=
  OSLF.FiniteBranching.HypersetSemantics.readout (silentLoop (Name := Fin count)) labels
    PUnit.unit () PUnit.unit

/-- The material universe also contains a behaviour outside this syntax's image. -/
theorem loop_not_in_image (process : Closed (Fin count)) : meaning process ≠ loopMeaning (count := count) := by
  intro same
  have related := (OSLF.FiniteBranching.HypersetSemantics.readout_eq_iff_bisimilar
    (closedSystem (Fin count)) (silentLoop (Name := Fin count)) labels labels_injective
    PUnit.unit () process PUnit.unit).mp same
  exact not_bisimilar_silentLoop process related

end Mettapedia.Languages.ProcessCalculi.CCS.HypersetSemantics
