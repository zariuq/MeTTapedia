import Mettapedia.GSLT.Dynamics.DialectObstructions
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Multiset.AddSub

/-!
# A clause-local translation obstruction

This module isolates one precise reason that lowering an ordered or committed
logic language to an unordered bag machine may require an external manager or
an explicit in-language control protocol.

A clause-local translation expands each source clause independently into a
finite target block.  Swapping two source clauses therefore only swaps two
target blocks.  Ordinary bag observation cannot see that swap.  Committed
choice can see it, so no such translation preserves committed choice for all
programs.

This is not a computability separation.  A context-sensitive translation can
carry each source prefix into target guards; `chain_exact` in
`DialectObstructions.lean` proves that repair correct.  The theorem below says
that the prefix/control information is necessary somewhere: in generated
atoms, compiled guards, or a manager.  It cannot be recovered from an
order-insensitive clause-local image.
-/

namespace Mettapedia.GSLT.Dynamics.ClauseLocalObstruction

open Mettapedia.GSLT.Dynamics.DialectTranslation

variable {TargetSub : Type}

/-- Expand each source clause independently, then concatenate the blocks. -/
def clauseLocalImage
    (translate : Clause Unit Unit Nat -> List (Clause Unit TargetSub Nat))
    (clauses : List (Clause Unit Unit Nat)) :
    List (Clause Unit TargetSub Nat) :=
  clauses.flatMap translate

/-- A clause-local target observed as an answer bag cannot distinguish the
two orders of a two-clause source program. -/
theorem clauseLocal_swap_invisible
    (translate : Clause Unit Unit Nat -> List (Clause Unit TargetSub Nat)) :
    (pettaAnswers
        (clauseLocalImage translate [constClause 0, constClause 1]) () :
        Multiset Nat) =
      (pettaAnswers
        (clauseLocalImage translate [constClause 1, constClause 0]) () :
        Multiset Nat) := by
  simp only [clauseLocalImage, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, pettaAnswers, List.flatMap_append]
  rw [<- Multiset.coe_add, <- Multiset.coe_add]
  exact Multiset.add_comm _ _

/-- The same source-order swap is invisible after the still coarser support
observation. -/
theorem clauseLocal_swap_support_invisible
    (translate : Clause Unit Unit Nat -> List (Clause Unit TargetSub Nat)) :
    (pettaAnswers
        (clauseLocalImage translate [constClause 0, constClause 1]) () :
        Multiset Nat).toFinset =
      (pettaAnswers
        (clauseLocalImage translate [constClause 1, constClause 0]) () :
        Multiset Nat).toFinset := by
  exact congrArg (fun answers : Multiset Nat => answers.toFinset)
    (clauseLocal_swap_invisible translate)

/-- Correctness of a clause-local translation for committed choice under bag
observation. -/
def PreservesCommittedChoice
    (translate : Clause Unit Unit Nat -> List (Clause Unit TargetSub Nat)) :
    Prop :=
  forall clauses : List (Clause Unit Unit Nat),
    (pettaAnswers (clauseLocalImage translate clauses) () : Multiset Nat) =
      (commitAnswers clauses () : Multiset Nat)

/-- No finite clause-by-clause expansion into ordinary bag-observed clauses
preserves committed choice for every source program. -/
theorem no_clauseLocal_bag_translation_preserves_commit :
    Not (exists translate :
        Clause Unit Unit Nat -> List (Clause Unit TargetSub Nat),
      PreservesCommittedChoice translate) := by
  intro existsTranslation
  apply Exists.elim existsTranslation
  intro translate preserves
  have forward := preserves [constClause 0, constClause 1]
  have backward := preserves [constClause 1, constClause 0]
  have targetEqual := clauseLocal_swap_invisible translate
  have sourceEqual :
      (commitAnswers [constClause 0, constClause 1] () : Multiset Nat) =
        (commitAnswers [constClause 1, constClause 0] () : Multiset Nat) :=
    forward.symm.trans (targetEqual.trans backward)
  have sourceDifferent :
      Not ((commitAnswers [constClause 0, constClause 1] () : Multiset Nat) =
        (commitAnswers [constClause 1, constClause 0] () : Multiset Nat)) := by
    simp [commitAnswers, contrib, constClause]
  exact sourceDifferent sourceEqual

/-- Correctness of a clause-local translation for committed choice under
finite-support observation. -/
def PreservesCommittedSupport
    (translate : Clause Unit Unit Nat -> List (Clause Unit TargetSub Nat)) :
    Prop :=
  forall clauses : List (Clause Unit Unit Nat),
    (pettaAnswers (clauseLocalImage translate clauses) () :
      Multiset Nat).toFinset =
      (commitAnswers clauses () : Multiset Nat).toFinset

/-- The obstruction persists for MM2-style support observation. -/
theorem no_clauseLocal_support_translation_preserves_commit :
    Not (exists translate :
        Clause Unit Unit Nat -> List (Clause Unit TargetSub Nat),
      PreservesCommittedSupport translate) := by
  intro existsTranslation
  apply Exists.elim existsTranslation
  intro translate preserves
  have forward := preserves [constClause 0, constClause 1]
  have backward := preserves [constClause 1, constClause 0]
  have targetEqual := clauseLocal_swap_support_invisible translate
  have sourceEqual :
      (commitAnswers [constClause 0, constClause 1] () :
          Multiset Nat).toFinset =
        (commitAnswers [constClause 1, constClause 0] () :
          Multiset Nat).toFinset :=
    forward.symm.trans (targetEqual.trans backward)
  have sourceDifferent :
      Not ((commitAnswers [constClause 0, constClause 1] () :
          Multiset Nat).toFinset =
        (commitAnswers [constClause 1, constClause 0] () :
          Multiset Nat).toFinset) := by
    decide
  exact sourceDifferent sourceEqual

end Mettapedia.GSLT.Dynamics.ClauseLocalObstruction
