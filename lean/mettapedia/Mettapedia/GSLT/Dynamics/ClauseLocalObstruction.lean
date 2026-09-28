import Mettapedia.GSLT.Dynamics.DialectObstructions
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Multiset.AddSub

/-!
# An equation-local translation obstruction

This module isolates one precise reason that lowering an ordered or committed
logic language to an unordered bag machine may require an external manager or
an explicit in-language control protocol.

An equation-local translation expands each source equation independently into a
finite target block.  Swapping two source equations therefore only swaps two
target blocks.  Ordinary bag observation cannot see that swap.  Committed
choice can see it, so no such translation preserves committed choice for all
programs.

This is not a computability separation.  A context-sensitive translation can
carry each source prefix into target guards; `chain_exact` in
`DialectObstructions.lean` proves that repair correct.  The theorem below says
that the prefix/control information is necessary somewhere: in generated
atoms, compiled guards, or a manager.  It cannot be recovered from an
order-insensitive equation-local image.
-/

namespace Mettapedia.GSLT.Dynamics.EquationLocalObstruction

open Mettapedia.GSLT.Dynamics.DialectTranslation

variable {TargetSub : Type}

/-- Expand each source equation independently, then concatenate the blocks. -/
def equationLocalImage
    (translate : Equation Unit Unit Nat -> List (Equation Unit TargetSub Nat))
    (equations : List (Equation Unit Unit Nat)) :
    List (Equation Unit TargetSub Nat) :=
  equations.flatMap translate

/-- An equation-local target observed as an answer bag cannot distinguish the
two orders of a two-equation source program. -/
theorem equationLocal_swap_invisible
    (translate : Equation Unit Unit Nat -> List (Equation Unit TargetSub Nat)) :
    (pettaAnswers
        (equationLocalImage translate [constEquation 0, constEquation 1]) () :
        Multiset Nat) =
      (pettaAnswers
        (equationLocalImage translate [constEquation 1, constEquation 0]) () :
        Multiset Nat) := by
  simp only [equationLocalImage, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, pettaAnswers, List.flatMap_append]
  rw [<- Multiset.coe_add, <- Multiset.coe_add]
  exact Multiset.add_comm _ _

/-- The same source-order swap is invisible after the still coarser support
observation. -/
theorem equationLocal_swap_support_invisible
    (translate : Equation Unit Unit Nat -> List (Equation Unit TargetSub Nat)) :
    (pettaAnswers
        (equationLocalImage translate [constEquation 0, constEquation 1]) () :
        Multiset Nat).toFinset =
      (pettaAnswers
        (equationLocalImage translate [constEquation 1, constEquation 0]) () :
        Multiset Nat).toFinset := by
  exact congrArg (fun answers : Multiset Nat => answers.toFinset)
    (equationLocal_swap_invisible translate)

/-- Correctness of an equation-local translation for committed choice under bag
observation. -/
def PreservesCommittedChoice
    (translate : Equation Unit Unit Nat -> List (Equation Unit TargetSub Nat)) :
    Prop :=
  forall equations : List (Equation Unit Unit Nat),
    (pettaAnswers (equationLocalImage translate equations) () : Multiset Nat) =
      (commitAnswers equations () : Multiset Nat)

/-- No finite equation-by-equation expansion into ordinary bag-observed equations
preserves committed choice for every source program. -/
theorem no_equationLocal_bag_translation_preserves_commit :
    Not (exists translate :
        Equation Unit Unit Nat -> List (Equation Unit TargetSub Nat),
      PreservesCommittedChoice translate) := by
  intro existsTranslation
  apply Exists.elim existsTranslation
  intro translate preserves
  have forward := preserves [constEquation 0, constEquation 1]
  have backward := preserves [constEquation 1, constEquation 0]
  have targetEqual := equationLocal_swap_invisible translate
  have sourceEqual :
      (commitAnswers [constEquation 0, constEquation 1] () : Multiset Nat) =
        (commitAnswers [constEquation 1, constEquation 0] () : Multiset Nat) :=
    forward.symm.trans (targetEqual.trans backward)
  have sourceDifferent :
      Not ((commitAnswers [constEquation 0, constEquation 1] () : Multiset Nat) =
        (commitAnswers [constEquation 1, constEquation 0] () : Multiset Nat)) := by
    simp [commitAnswers, contrib, constEquation]
  exact sourceDifferent sourceEqual

/-- Correctness of an equation-local translation for committed choice under
finite-support observation. -/
def PreservesCommittedSupport
    (translate : Equation Unit Unit Nat -> List (Equation Unit TargetSub Nat)) :
    Prop :=
  forall equations : List (Equation Unit Unit Nat),
    (pettaAnswers (equationLocalImage translate equations) () :
      Multiset Nat).toFinset =
      (commitAnswers equations () : Multiset Nat).toFinset

/-- The obstruction persists for MM2-style support observation. -/
theorem no_equationLocal_support_translation_preserves_commit :
    Not (exists translate :
        Equation Unit Unit Nat -> List (Equation Unit TargetSub Nat),
      PreservesCommittedSupport translate) := by
  intro existsTranslation
  apply Exists.elim existsTranslation
  intro translate preserves
  have forward := preserves [constEquation 0, constEquation 1]
  have backward := preserves [constEquation 1, constEquation 0]
  have targetEqual := equationLocal_swap_support_invisible translate
  have sourceEqual :
      (commitAnswers [constEquation 0, constEquation 1] () :
          Multiset Nat).toFinset =
        (commitAnswers [constEquation 1, constEquation 0] () :
          Multiset Nat).toFinset :=
    forward.symm.trans (targetEqual.trans backward)
  have sourceDifferent :
      Not ((commitAnswers [constEquation 0, constEquation 1] () :
          Multiset Nat).toFinset =
        (commitAnswers [constEquation 1, constEquation 0] () :
          Multiset Nat).toFinset) := by
    decide
  exact sourceDifferent sourceEqual

end Mettapedia.GSLT.Dynamics.EquationLocalObstruction
