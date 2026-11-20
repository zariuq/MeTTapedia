import Mettapedia.Logic.LP.ConjunctiveUnification
import Mettapedia.Logic.LP.TermEquality
import Mettapedia.Data.List.OrderedPrefilter

/-!
# Bound argument indexing retains schematic candidates

The candidate view is the ordered merge of the bucket for a bound ground
key with the open-argument bucket. We specify it by stable filtering of
the original occurrence word. Matching still checks the whole row after
selection; this theorem does not replace unification with key equality.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.BoundArgumentIndex

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.ConjunctiveUnification (CommonInstance commonInstance_ground_iff)

variable {signature : LPSignature}
  [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols]

def candidate (key : Term signature) (argument : Term signature) : Bool :=
  decide (argument.freeVars ≠ ∅ ∨ argument = key)

theorem candidate_of_common_instance {key argument : Term signature} (ground : key.isGround)
    (match_ : CommonInstance key argument) :
    candidate key argument = true := by
  apply decide_eq_true
  by_cases openArg : argument.freeVars ≠ ∅
  · exact Or.inl openArg
  · have argumentGround := (argument.isGround_iff_freeVars_empty).mpr (not_not.mp openArg)
    exact Or.inr (((commonInstance_ground_iff ground argumentGround).mp match_).symm)

def narrow {Row : Type*} (key : Term signature) (argument : Row → Term signature)
    (rows : List Row) : List Row :=
  rows.filter (fun row => candidate key (argument row))

/-- Candidate narrowing preserves the exact ordered match word, not just
the set of matching values. The matcher's necessary argument condition is
the actual existence of a common instance, in either frame. -/
theorem filter_narrow_eq {Row : Type*} (key : Term signature) (argument : Row → Term signature)
    (rows : List Row) (matchesRow : Row → Bool) (ground : key.isGround)
    (sound : ∀ row ∈ rows, matchesRow row = true → CommonInstance key (argument row)) :
    (narrow key argument rows).filter matchesRow = rows.filter matchesRow := by
  exact (Mettapedia.Data.List.OrderedPrefilter.filter_filter_eq_iff
    (fun row => candidate key (argument row)) matchesRow rows).mpr
      (fun row inside matched => candidate_of_common_instance ground (sound row inside matched))

namespace Controls

abbrev sig : LPSignature := ⟨Nat, Nat, Empty, (fun e => nomatch e), Empty, (fun e => nomatch e)⟩

abbrev T := Term sig

def word : List (Nat × T) :=
  [(0, .const 8), (1, .var 4), (2, .const 7), (3, .const 7)]

theorem retains_order_and_equal_occurrences :
    narrow (.const 7 : T) Prod.snd word = [(1, .var 4), (2, .const 7), (3, .const 7)] := by
  decide +kernel

theorem exact_key_alone_loses_open_answer :
    CommonInstance (.const 7 : T) (.var 4) ∧ (.var 4 : T) ≠ (.const 7 : T) := by
  constructor
  · exact ⟨Subst.id sig, fun _ => .const 7, rfl⟩
  · intro impossible
    cases impossible

end Controls

#print axioms candidate_of_common_instance
#print axioms filter_narrow_eq
#print axioms Controls.retains_order_and_equal_occurrences
#print axioms Controls.exact_key_alone_loses_open_answer

end Mettapedia.GSLT.Compilation.BoundArgumentIndex
