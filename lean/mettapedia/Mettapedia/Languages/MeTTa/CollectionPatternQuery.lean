import Mettapedia.Algebra.Collections.Unification
import Mettapedia.Languages.MeTTa.SpaceQueryPolicy

/-!
# Collection patterns inside space queries

`SpaceQueryPolicy.query` binds a space to a matcher that gives at most one
answer per stored atom, as syntactic matching does. A collection pattern
gives several answers per atom: `{$x | $r}` against a stored bag has one
answer per occurrence. A matcher that returns a weighted bag of answers per
atom (`queryMany`) keeps every law of `query`:

* additivity in the space, and singleton spaces (`queryMany_add`,
  `queryMany_single`, `queryMany_zero`);
* a change of annotation along a semiring homomorphism commutes with the query
  (`mapK_queryMany`);
* a key index that is sound for the matcher returns exactly the query's
  answers (`indexedQueryMany_eq_queryMany`), and a key the matcher does not
  respect loses answers (`Controls.unsound_key_loses_answers`);
* the single-answer query is the case of at most one answer
  (`query_eq_queryMany`).

**Bag patterns and spaces agree.** The answers of `{$x | $r}` against a bag
value, read at `$x`, are the answers of `$x` against that bag thawed into a
space, with the same multiplicities (`bagRest_project`,
`bagRest_project_eq_query`). Over a space whose atoms are bags, reading the
pattern at `$x` is the flattening of the space (`queryMany_bagRest_project`).
A repeated element is answered once per occurrence, as `match` answers a
repeated atom of a bag space (`Controls.repeated_occurrence_counts`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.CollectionPatternQuery

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.Languages.MeTTa.SpaceQueryPolicy
open Mettapedia.Algebra.Collections.Rest Mettapedia.Algebra.Collections.Unification

universe u

variable {K : Type u} {Atom Pat Res : Type*}

/-! ## Queries with several answers per stored atom -/

section Query

variable [Semiring K] (matcher : Pat → Atom → Ans K Res)

/-- The answers of a pattern when one stored atom may answer several times:
the space bound to the matcher. -/
noncomputable def queryMany (space : Space K Atom) (pattern : Pat) : Ans K Res :=
  Ans.bind space (matcher pattern)

theorem queryMany_add (left right : Space K Atom) (pattern : Pat) :
    queryMany matcher (left + right) pattern =
      queryMany matcher left pattern + queryMany matcher right pattern :=
  Ans.add_bind left right _

theorem queryMany_single (atom : Atom) (weight : K) (pattern : Pat) :
    queryMany matcher (Finsupp.single atom weight) pattern = weight • matcher pattern atom :=
  Ans.single_bind atom weight _

theorem queryMany_zero (pattern : Pat) : queryMany matcher (0 : Space K Atom) pattern = 0 :=
  Ans.zero_bind _

/-- A change of annotation commutes with every query. -/
theorem mapK_queryMany {L : Type*} [Semiring L] (φ : K →+* L) (space : Space K Atom)
    (pattern : Pat) :
    Ans.mapK φ (queryMany matcher space pattern) =
      queryMany (fun pattern atom => Ans.mapK φ (matcher pattern atom)) (Ans.mapK φ space)
        pattern :=
  Ans.mapK_bind φ space _

omit [Semiring K] in
/-- The single-answer query is the case of at most one answer per atom. -/
theorem query_eq_queryMany [Semiring K] (single : Pat → Atom → Option Res) :
    query (K := K) single = queryMany (contribution single) := rfl

variable {κ : Type*} [DecidableEq κ]

/-- A rigid key is sound for a matcher when every atom that answers a pattern
is filed under the pattern's key. -/
def KeySoundMany (keyOf : Atom → κ) (patternKey : Pat → Option κ) : Prop :=
  ∀ pattern atom key, patternKey pattern = some key → matcher pattern atom ≠ 0 →
    keyOf atom = key

/-- Query only the atoms filed under the pattern's key, if it has one. -/
noncomputable def indexedQueryMany (keyOf : Atom → κ) (patternKey : Pat → Option κ)
    (space : Space K Atom) (pattern : Pat) : Ans K Res :=
  match patternKey pattern with
  | some key => queryMany matcher (keyFilter keyOf space key) pattern
  | none => queryMany matcher space pattern

/-- **An index changes where answers are found, never which answers there
are**, for matchers with several answers per atom. -/
theorem indexedQueryMany_eq_queryMany (keyOf : Atom → κ) (patternKey : Pat → Option κ)
    (sound : KeySoundMany matcher keyOf patternKey) (space : Space K Atom) (pattern : Pat) :
    indexedQueryMany matcher keyOf patternKey space pattern = queryMany matcher space pattern := by
  unfold indexedQueryMany
  cases rigid : patternKey pattern with
  | none => rfl
  | some key =>
      simp only
      conv_rhs => rw [← Finsupp.filter_add_filter_not space (fun atom => keyOf atom = key)]
      rw [queryMany_add]
      suffices outside :
          queryMany matcher (space.filter fun atom => ¬ keyOf atom = key) pattern = 0 by
        rw [outside, add_zero]
        rfl
      unfold queryMany Ans.bind
      rw [Finsupp.sum, Finset.sum_eq_zero]
      intro atom member
      rw [Finsupp.support_filter, Finset.mem_filter] at member
      by_cases silent : matcher pattern atom = 0
      · rw [silent, smul_zero]
      · exact absurd (sound pattern atom key rigid silent) member.2

end Query

/-! ## Bag patterns against bags and against spaces of bags -/

section Bags

variable {α : Type*} [DecidableEq α]

/-- The matcher of `{$x | $r}`: one answer per occurrence of the stored bag. -/
noncomputable def bagRestMatcher (_ : Unit) (stored : Multiset α) : Ans ℕ (α × Multiset α) :=
  Multiset.toFinsupp (selectOccurrences stored)

/-- The matcher of `{$x₁ … $xₖ | $r}`: one answer per ordered choice of `k`
occurrences. -/
noncomputable def selectionsMatcher (k : ℕ) (_ : Unit) (stored : Multiset α) :
    Ans ℕ (List α × Multiset α) :=
  Multiset.toFinsupp (selections k stored)

/-- Each stored bag contributes its occurrence choices, weighted by how often
the bag is stored. -/
theorem queryMany_selections_apply (k : ℕ) (space : Space ℕ (Multiset α))
    (answer : List α × Multiset α) :
    queryMany (selectionsMatcher k) space () answer =
      space.sum fun stored count => count * (selections k stored).count answer := by
  unfold queryMany
  rw [Ans.bind_apply]
  simp only [selectionsMatcher, Multiset.toFinsupp_apply]

omit [DecidableEq α] in
/-- Mapping a bag's answers along a function is the bag of the mapped
elements. -/
theorem toFinsupp_map {β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (value : Multiset α) :
    Multiset.toFinsupp (value.map f) = Finsupp.mapDomain f (Multiset.toFinsupp value) := by
  rw [← Finsupp.toMultiset_toFinsupp (Finsupp.mapDomain f (Multiset.toFinsupp value)),
    ← Finsupp.toMultiset_map, Multiset.toFinsupp_toMultiset]

/-- **A bag pattern's element variable sees what `match` sees.** Read at
`$x`, the answers of `{$x | $r}` against a bag are the bag itself, with its
multiplicities. -/
theorem bagRest_project (value : Multiset α) :
    Ans.map Prod.fst (bagRestMatcher () value) = Multiset.toFinsupp value := by
  rw [Ans.map_eq_mapDomain, bagRestMatcher, ← toFinsupp_map, selectOccurrences,
    Multiset.map_map]
  simp only [Function.comp_def, Multiset.map_id']

/-- The same answers are the query of `$x` against the bag thawed into a
space. -/
theorem bagRest_project_eq_query (value : Multiset α) :
    Ans.map Prod.fst (bagRestMatcher () value) =
      query (K := ℕ) (fun (_ : Unit) (atom : α) => some atom) (Multiset.toFinsupp value) () := by
  rw [bagRest_project, query_identity (fun (_ : Unit) (atom : α) => some atom) () id
    (fun _ => rfl), Finsupp.mapDomain_id]

/-- Projecting answers commutes with binding. -/
theorem map_bind {K : Type u} [Semiring K] {X Y Z : Type*} (h : Y → Z) (A : Ans K X)
    (f : X → Ans K Y) :
    Ans.map h (Ans.bind A f) = Ans.bind A (fun x => Ans.map h (f x)) := by
  unfold Ans.map
  rw [Ans.bind_assoc]

/-- **Over a space of stored bags, reading `{$x | $r}` at `$x` flattens the
space**: each stored bag contributes its elements, weighted by how often the
bag is stored. -/
theorem queryMany_bagRest_project (space : Space ℕ (Multiset α)) :
    Ans.map Prod.fst (queryMany bagRestMatcher space ()) =
      Ans.bind space Multiset.toFinsupp := by
  unfold queryMany
  rw [map_bind]
  congr 1
  funext stored
  exact bagRest_project stored

end Bags

/-! ## Controls -/

namespace Controls

/-- A stored bag `{1, 1}` answers `{$x | $r}` with `(1, {1})` twice, once per
occurrence: the multiplicity `match` gives to a repeated atom. -/
theorem repeated_occurrence_counts :
    queryMany bagRestMatcher (Finsupp.single ({1, 1} : Multiset ℕ) 1) () (1, {1}) = 2 := by
  rw [queryMany_single, one_smul, bagRestMatcher, Multiset.toFinsupp_apply]
  decide

/-- A key the matcher does not respect: the pattern claims key `0`, but the
matcher answers an atom filed under `1`, so the indexed query loses it. -/
theorem unsound_key_loses_answers :
    let matcher : Unit → ℕ × ℕ → Ans ℕ ℕ := fun _ pair => Finsupp.single pair.2 1
    let space : Space ℕ (ℕ × ℕ) := Finsupp.single (1, 5) 1
    indexedQueryMany matcher Prod.fst (fun _ => some 0) space () ≠ queryMany matcher space () := by
  intro matcher space same
  have := congrArg (fun answers : Ans ℕ ℕ => answers 5) same
  rw [show indexedQueryMany matcher Prod.fst (fun _ => some 0) space () =
      queryMany matcher (keyFilter Prod.fst space 0) () from rfl,
    show keyFilter Prod.fst space 0 = 0 from
      Finsupp.filter_single_of_neg (p := fun pair : ℕ × ℕ => pair.1 = 0) (by simp),
    queryMany_zero] at this
  simp [space, queryMany_single, matcher] at this

end Controls

end Mettapedia.Languages.MeTTa.CollectionPatternQuery
