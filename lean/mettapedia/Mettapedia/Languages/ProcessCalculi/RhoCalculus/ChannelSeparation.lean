import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu

/-!
# A term whose outputs and inputs are on separated channels does not reduce

Communication needs an output and an input on one channel.  Fix a set of
names.  Count the top-level outputs whose channel mentions none of the names
together with the top-level inputs whose channel mentions one of them.  The
count is invariant under structural congruence, and it is positive on every
term that reduces: the channel of the communicating pair either mentions one
of the names, and then its input is counted, or mentions none, and then its
output is.

So a term in which every top-level output is on a channel that mentions one
of the names, and every top-level input is on a channel that mentions none,
has no reduction, whatever structural congruence does to it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu

/-- Two lists that agree position by position under a function have the same
image. -/
theorem map_eq_of_get {value : Type} (measure : Pattern → value) :
    ∀ {first second : List Pattern}, first.length = second.length →
      (∀ index (firstBound : index < first.length) (secondBound : index < second.length),
        measure (first.get ⟨index, firstBound⟩) = measure (second.get ⟨index, secondBound⟩)) →
      first.map measure = second.map measure
  | [], [], _, _ => rfl
  | [], _ :: _, sameLength, _ => by simp at sameLength
  | _ :: _, [], sameLength, _ => by simp at sameLength
  | _ :: first, _ :: second, sameLength, agree => by
      have head := agree 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      have tail := map_eq_of_get measure (first := first) (second := second)
        (by simpa using sameLength) fun index firstBound secondBound =>
          agree (index + 1) (Nat.succ_lt_succ firstBound) (Nat.succ_lt_succ secondBound)
      simp only [List.map_cons]
      exact congrArg₂ List.cons head tail

/-- Occurrences in a pattern of free names from a list. -/
def nameCount (names : List String) : Pattern → Nat
  | .bvar _ => 0
  | .fvar name => if name ∈ names then 1 else 0
  | .apply _ arguments => (arguments.map (nameCount names)).sum
  | .lambda _ body => nameCount names body
  | .multiLambda _ _ body => nameCount names body
  | .subst body replacement => nameCount names body + nameCount names replacement
  | .collection _ elements _ => (elements.map (nameCount names)).sum

theorem nameCount_fvar_of_mem {names : List String} {name : String} (listed : name ∈ names) :
    nameCount names (.fvar name) = 1 := by
  simp [nameCount, listed]

theorem nameCount_fvar_of_not_mem {names : List String} {name : String}
    (unlisted : name ∉ names) : nameCount names (.fvar name) = 0 := by
  simp [nameCount, unlisted]

/-- Structural congruence preserves the occurrences of free names. -/
theorem nameCount_SC (names : List String) {left right : Pattern}
    (related : StructuralCongruence left right) :
    nameCount names left = nameCount names right := by
  induction related with
  | alpha _ _ same => subst same; rfl
  | refl _ => rfl
  | symm _ _ _ recurse => exact recurse.symm
  | trans _ _ _ _ _ first second => exact first.trans second
  | par_singleton pattern => simp [nameCount]
  | par_nil_left pattern => simp [nameCount]
  | par_nil_right pattern => simp [nameCount]
  | par_comm first second => simp [nameCount]; omega
  | par_assoc first second third => simp [nameCount]; omega
  | par_cong first second sameLength _ recurse =>
      simp only [nameCount, map_eq_of_get (nameCount names) sameLength recurse]
  | par_flatten outer inner => simp [nameCount]
  | par_perm _ _ permutation =>
      simp only [nameCount]
      exact (permutation.map _).sum_eq
  | set_perm _ _ permutation =>
      simp only [nameCount]
      exact (permutation.map _).sum_eq
  | set_cong first second sameLength _ recurse =>
      simp only [nameCount, map_eq_of_get (nameCount names) sameLength recurse]
  | lambda_cong _ _ _ _ recurse => simpa [nameCount] using recurse
  | apply_cong constructor first second sameLength _ recurse =>
      simp only [nameCount, map_eq_of_get (nameCount names) sameLength recurse]
  | collection_general_cong _ first second _ sameLength _ recurse =>
      simp only [nameCount, map_eq_of_get (nameCount names) sameLength recurse]
  | multiLambda_cong _ _ _ _ _ recurse => simpa [nameCount] using recurse
  | subst_cong _ _ _ _ _ _ body replacement => simp [nameCount, body, replacement]
  | quote_drop pattern => simp [nameCount]
  | par_empty => simp [nameCount]

/-- What an application contributes, from the counts of its arguments and
the occurrences of the names in them: an output on a channel mentioning none
of the names, an input on a channel mentioning one, and whatever lies
beneath a quotation or a dereference. -/
def separationHead (label : String) (counts mentions : List Nat) : Nat :=
  if label = "POutput" then
    match mentions with
    | [channel, _] => if channel = 0 then 1 else 0
    | _ => 0
  else if label = "PInput" then
    match mentions with
    | [channel, _] => if channel = 0 then 0 else 1
    | _ => 0
  else if label = "NQuote" ∨ label = "PDrop" then
    match counts with
    | [inner] => inner
    | _ => 0
  else 0

/-- The top-level outputs on channels mentioning none of the names, together
with the top-level inputs on channels mentioning one of them. -/
def separation (names : List String) : Pattern → Nat
  | .apply label arguments =>
      separationHead label (arguments.map (separation names))
        (arguments.map (nameCount names))
  | .collection _ elements _ => (elements.map (separation names)).sum
  | _ => 0

/-- **Structural congruence preserves the count.** -/
theorem separation_SC (names : List String) {left right : Pattern}
    (related : StructuralCongruence left right) :
    separation names left = separation names right := by
  induction related with
  | alpha _ _ same => subst same; rfl
  | refl _ => rfl
  | symm _ _ _ recurse => exact recurse.symm
  | trans _ _ _ _ _ first second => exact first.trans second
  | par_singleton pattern => simp [separation]
  | par_nil_left pattern => simp [separation, separationHead]
  | par_nil_right pattern => simp [separation, separationHead]
  | par_comm first second => simp [separation]; omega
  | par_assoc first second third => simp [separation]; omega
  | par_cong first second sameLength _ recurse =>
      simp only [separation, map_eq_of_get (separation names) sameLength recurse]
  | par_flatten outer inner => simp [separation]
  | par_perm _ _ permutation =>
      simp only [separation]
      exact (permutation.map _).sum_eq
  | set_perm _ _ permutation =>
      simp only [separation]
      exact (permutation.map _).sum_eq
  | set_cong first second sameLength _ recurse =>
      simp only [separation, map_eq_of_get (separation names) sameLength recurse]
  | lambda_cong _ _ _ _ _ => simp [separation]
  | apply_cong constructor first second sameLength pointwise recurse =>
      simp only [separation, map_eq_of_get (separation names) sameLength recurse,
        map_eq_of_get (nameCount names) sameLength
          (fun index firstBound secondBound =>
            nameCount_SC names (pointwise index firstBound secondBound))]
  | collection_general_cong _ first second _ sameLength _ recurse =>
      simp only [separation, map_eq_of_get (separation names) sameLength recurse]
  | multiLambda_cong _ _ _ _ _ _ => simp [separation]
  | subst_cong _ _ _ _ _ _ _ _ => simp [separation]
  | quote_drop pattern => simp [separation, separationHead]
  | par_empty => simp [separation, separationHead]

/-- **Every term that reduces has a positive count.** -/
theorem separation_pos_of_reduces (names : List String) {source target : Pattern}
    (step : Reduces source target) : 0 < separation names source := by
  induction step with
  | @comm channel payload body rest =>
      simp only [separation, separationHead, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil]
      by_cases mentions : nameCount names channel = 0 <;> simp [mentions]
  | @equiv source redex target contractum sourceRelated _ _ recurse =>
      rw [separation_SC names sourceRelated]
      exact recurse
  | par _ recurse =>
      simp only [separation, List.map_cons, List.sum_cons]
      omega
  | par_any _ recurse =>
      simp only [separation, List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil]
      omega

/-- **Separated channels: no reduction.**  A term whose count is zero has no
reduction. -/
theorem not_reduces_of_separation_eq_zero (names : List String) {source : Pattern}
    (separated : separation names source = 0) (target : Pattern) :
    IsEmpty (Reduces source target) :=
  ⟨fun step => absurd (separation_pos_of_reduces names step) (by omega)⟩

/-- The replications that can be unfolded: at the root, or as components of
nested parallel compositions. -/
def unfoldCount : Pattern → Nat
  | .apply "PReplicate" [_] => 1
  | .collection .hashBag elements none => (elements.map unfoldCount).sum
  | _ => 0

/-- A term that takes a derived step reduces or has a replication to
unfold. -/
theorem separation_or_unfold_pos_of_reducesDerived (names : List String)
    {source target : Pattern} (step : ReducesDerived source target) :
    0 < separation names source ∨ 0 < unfoldCount source := by
  induction step with
  | core reduction => exact .inl (separation_pos_of_reduces names reduction)
  | rep_unfold => exact .inr (by simp [unfoldCount])
  | par _ recurse =>
      rcases recurse with positive | positive
      · left
        simp only [separation, List.map_cons, List.sum_cons]
        omega
      · right
        simp only [unfoldCount, List.map_cons, List.sum_cons]
        omega
  | par_any _ recurse =>
      rcases recurse with positive | positive
      · left
        simp only [separation, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil]
        omega
      · right
        simp only [unfoldCount, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil]
        omega

/-- A term with separated channels and no replication to unfold takes no
derived step. -/
theorem not_reducesDerived_of_separation_eq_zero (names : List String) {source : Pattern}
    (separated : separation names source = 0) (rigid : unfoldCount source = 0)
    (target : Pattern) : IsEmpty (ReducesDerived source target) :=
  ⟨fun step => by
    rcases separation_or_unfold_pos_of_reducesDerived names step with positive | positive <;>
      omega⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
