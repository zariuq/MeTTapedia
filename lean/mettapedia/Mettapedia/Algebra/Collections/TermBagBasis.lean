import Mettapedia.Algebra.Collections.TermBagSubsumption
import Mettapedia.Algebra.Collections.FiniteUnifierBasis

/-!
# Complete irredundant bases for bags of first-order terms

The families of `TermBagUnifiers` (one per consistent partial matching, by the
total unifier of its pairs) are pruned by the stable selector of
`FiniteUnifierBasis`: a family strictly less general than another is removed,
and of equivalent families the first in enumeration order is kept.

* **Soundness and completeness** survive pruning (`sound`, `complete`,
  `solves_iff`): every solution, element variables bound to arbitrary terms, is
  an instance of a retained family.
* **Redundancy control**: no retained family is more general than another
  (`no_subsumption`), the basis has no duplicates (`nodup`), and it is a
  finite minimal complete set (`minimal_complete`, `finite`), so the problem is
  finitary (`finitary`).
* **Sides without a rest** are the instances with that rest empty: the
  solutions of `{t₁ … tₙ} = {u₁ … u_m}` are the instances of the retained
  families whose two bases are empty, with no common bag
  (`closed_solves_iff`), and those of `{t₁ … tₙ | R} = {u₁ … u_m}` are the
  instances of those whose right base is empty (`right_closed_solves_iff`).
  **A rest shared by both sides** cancels, leaving the closed problem with
  that rest unconstrained (`shared_rest_solves_iff`). With at most one rest a
  side, these are all the ways the rests of one bag can occur.
* The answers represented do not depend on the order in which either side
  lists its elements (`permutation_preserves_solutions`); the retained
  representatives may.

The selector needs generality to be decidable. On a finite type of variables
the checker of `TermBagSubsumption` decides it (`executable`); for an arbitrary
type of variables a finite minimal complete set exists classically
(`exists_minimal_complete`).
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.TermBagBasis

open Mettapedia.Logic.LP (LPSignature Term Subst)
open TermBagUnifiers (Answer Family Instance MoreGeneral families genericAnswer instantiate Solves)

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- Every instance of the family solves the problem. -/
def Unifier (left right : List (Term σ)) (family : Family σ) : Prop :=
  ∀ answer, Instance family answer → Solves left right answer

section Selection

variable [DecidableRel (MoreGeneral : Family σ → Family σ → Prop)]

/-- The families of the search, pruned to the most general ones, first
representative kept. -/
def basis (left right : List (Term σ)) : List (Family σ) :=
  FiniteUnifierBasis.select (families left right) MoreGeneral

theorem mem_families {left right : List (Term σ)} {family : Family σ} (member : family ∈ basis left right) :
    family ∈ families left right :=
  FiniteUnifierBasis.selected_from_input (families left right) MoreGeneral member

theorem sound (left right : List (Term σ)) (family : Family σ) (member : family ∈ basis left right) :
    Unifier left right family :=
  TermBagUnifiers.sound left right family (mem_families member)

/-- Every family of the search is covered by a retained one. -/
theorem covers (left right : List (Term σ)) {family : Family σ} (member : family ∈ families left right) :
    ∃ retained ∈ basis left right, MoreGeneral retained family :=
  FiniteUnifierBasis.covers_input (families left right) MoreGeneral TermBagUnifiers.MoreGeneral.refl
    (fun first second => TermBagUnifiers.MoreGeneral.trans first second) member

/-- **Completeness after pruning.** -/
theorem complete (left right : List (Term σ)) (answer : Answer σ) (solved : Solves left right answer) :
    ∃ family ∈ basis left right, Instance family answer := by
  obtain ⟨raw, member, instanceOf⟩ := TermBagUnifiers.complete left right answer solved
  obtain ⟨retained, selected, moreGeneral⟩ := covers left right member
  exact ⟨retained, selected, TermBagUnifiers.instance_factor moreGeneral instanceOf⟩

theorem solves_iff (left right : List (Term σ)) (answer : Answer σ) :
    Solves left right answer ↔ ∃ family ∈ basis left right, Instance family answer :=
  ⟨complete left right answer, fun ⟨family, member, instanceOf⟩ => sound left right family member answer instanceOf⟩

/-- **No retained family is more general than another.** -/
theorem no_subsumption (left right : List (Term σ)) (first second : Family σ)
    (firstMember : first ∈ basis left right) (secondMember : second ∈ basis left right)
    (general : MoreGeneral first second) : first = second :=
  FiniteUnifierBasis.no_subsumed_distinct (families left right) MoreGeneral firstMember secondMember general

theorem nodup (left right : List (Term σ)) : (basis left right).Nodup :=
  FiniteUnifierBasis.selected_nodup (families left right) MoreGeneral TermBagUnifiers.MoreGeneral.refl

/-- The retained families keep their enumeration order. -/
theorem stable_indices (left right : List (Term σ)) :
    (FiniteUnifierBasis.indices (families left right) MoreGeneral).Sublist
      (List.finRange (families left right).length) :=
  FiniteUnifierBasis.indices_sublist _ _

theorem length_le (left right : List (Term σ)) :
    (basis left right).length ≤ (Unification.matchings left right).length := by
  unfold basis FiniteUnifierBasis.select
  rw [List.length_map]
  calc (FiniteUnifierBasis.indices (families left right) MoreGeneral).length
      ≤ (List.finRange (families left right).length).length := (stable_indices left right).length_le
    _ = (families left right).length := List.length_finRange
    _ ≤ (Unification.matchings left right).length := List.length_filterMap_le _ _

theorem minimal_complete (left right : List (Term σ)) :
    Unification.IsMinimalComplete (Unifier left right) MoreGeneral {family | family ∈ basis left right} where
  sound family member := sound left right family member
  covers family solves := by
    obtain ⟨general, member, covered⟩ := complete left right (genericAnswer family)
      (solves _ (TermBagUnifiers.generic_instance family))
    exact ⟨general, member, covered⟩
  minimal first firstMember second secondMember general :=
    no_subsumption left right first second firstMember secondMember general

theorem finite (left right : List (Term σ)) : {family | family ∈ basis left right}.Finite :=
  List.finite_toSet _

/-- Permuting either side can change the retained representatives, not the
answers they represent. -/
theorem permutation_preserves_solutions (left right otherLeft otherRight : List (Term σ))
    (leftPerm : left.Perm otherLeft) (rightPerm : right.Perm otherRight) (answer : Answer σ) :
    (∃ family ∈ basis left right, Instance family answer) ↔
      ∃ family ∈ basis otherLeft otherRight, Instance family answer := by
  rw [← solves_iff, ← solves_iff]
  unfold Solves
  rw [Multiset.coe_eq_coe.mpr (leftPerm.map answer.elements.applyTerm),
    Multiset.coe_eq_coe.mpr (rightPerm.map answer.elements.applyTerm)]

/-! ## Sides without a rest -/

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableRel (MoreGeneral : Family σ → Family σ → Prop)] in
theorem eq_zero_of_add_eq_zero {first second : Multiset (Term σ)} (sum : first + second = 0) :
    first = 0 ∧ second = 0 := by
  have count := congrArg Multiset.card sum
  rw [Multiset.card_add, Multiset.card_zero] at count
  exact ⟨Multiset.card_eq_zero.mp (by omega), Multiset.card_eq_zero.mp (by omega)⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableRel (MoreGeneral : Family σ → Family σ → Prop)] in
theorem map_eq_zero {base : Multiset (Term σ)} {remainder : Subst σ}
    (empty : base.map remainder.applyTerm = 0) : base = 0 :=
  Multiset.map_eq_zero.mp empty

/-- **Closed bags.** The element substitutions that make `{t₁ … tₙ}` and
`{u₁ … u_m}` the same bag are exactly the instances of retained families with
both bases empty. -/
theorem closed_solves_iff (left right : List (Term σ)) (assignment : Subst σ) :
    (left.map assignment.applyTerm : Multiset (Term σ)) = right.map assignment.applyTerm ↔
      ∃ family ∈ basis left right, family.base .left = 0 ∧ family.base .right = 0 ∧
        ∃ remainder, assignment = remainder ∘ₛ family.elements := by
  constructor
  · intro same
    have solved : Solves left right ⟨assignment, fun _ => 0⟩ := by
      change (left.map assignment.applyTerm : Multiset (Term σ)) + 0 = right.map assignment.applyTerm + 0
      rw [same]
    obtain ⟨family, member, remainder, common, represented⟩ := complete left right _ solved
    have elements := congrArg Answer.elements represented
    have leftRest := congrFun (congrArg Answer.rest represented) .left
    have rightRest := congrFun (congrArg Answer.rest represented) .right
    obtain ⟨leftBase, -⟩ := eq_zero_of_add_eq_zero leftRest.symm
    obtain ⟨rightBase, -⟩ := eq_zero_of_add_eq_zero rightRest.symm
    exact ⟨family, member, map_eq_zero leftBase, map_eq_zero rightBase, remainder, elements⟩
  · rintro ⟨family, member, leftEmpty, rightEmpty, remainder, rfl⟩
    have solved := sound left right family member (instantiate family remainder 0) ⟨remainder, 0, rfl⟩
    change (left.map (remainder ∘ₛ family.elements).applyTerm : Multiset (Term σ)) +
        ((family.base .left).map remainder.applyTerm + 0) =
      (right.map (remainder ∘ₛ family.elements).applyTerm : Multiset (Term σ)) +
        ((family.base .right).map remainder.applyTerm + 0) at solved
    simpa [leftEmpty, rightEmpty] using solved

/-- **A side without a rest.** The solutions of `{t₁ … tₙ | R} = {u₁ … u_m}`
are the instances, with no common bag, of retained families whose right base
is empty; the rest `R` is the instance of the left base. -/
theorem right_closed_solves_iff (left right : List (Term σ)) (assignment : Subst σ) (rest : Multiset (Term σ)) :
    (left.map assignment.applyTerm : Multiset (Term σ)) + rest = right.map assignment.applyTerm ↔
      ∃ family ∈ basis left right, family.base .right = 0 ∧
        ∃ remainder, assignment = remainder ∘ₛ family.elements ∧
          rest = (family.base .left).map remainder.applyTerm := by
  constructor
  · intro same
    have solved : Solves left right ⟨assignment, fun slot => match slot with | .left => rest | .right => 0⟩ := by
      change (left.map assignment.applyTerm : Multiset (Term σ)) + rest = right.map assignment.applyTerm + 0
      rw [same, add_zero]
    obtain ⟨family, member, remainder, common, represented⟩ := complete left right _ solved
    have elements := congrArg Answer.elements represented
    have leftRest := congrFun (congrArg Answer.rest represented) .left
    have rightRest := congrFun (congrArg Answer.rest represented) .right
    change 0 = (family.base .right).map remainder.applyTerm + common at rightRest
    obtain ⟨rightBase, noCommon⟩ := eq_zero_of_add_eq_zero rightRest.symm
    change rest = (family.base .left).map remainder.applyTerm + common at leftRest
    rw [noCommon, add_zero] at leftRest
    exact ⟨family, member, map_eq_zero rightBase, remainder, elements, leftRest⟩
  · rintro ⟨family, member, rightEmpty, remainder, rfl, rfl⟩
    have solved := sound left right family member (instantiate family remainder 0) ⟨remainder, 0, rfl⟩
    change (left.map (remainder ∘ₛ family.elements).applyTerm : Multiset (Term σ)) +
        ((family.base .left).map remainder.applyTerm + 0) =
      (right.map (remainder ∘ₛ family.elements).applyTerm : Multiset (Term σ)) +
        ((family.base .right).map remainder.applyTerm + 0) at solved
    simpa [rightEmpty] using solved

/-- **A rest shared by the two sides cancels.** `{t₁ … tₙ | R} = {u₁ … u_m | R}`
holds exactly when the closed bags are equal, whatever `R` is: its solutions
are the instances of retained families with both bases empty, with any bag for
`R`. -/
theorem shared_rest_solves_iff (left right : List (Term σ)) (assignment : Subst σ) (rest : Multiset (Term σ)) :
    (left.map assignment.applyTerm : Multiset (Term σ)) + rest = right.map assignment.applyTerm + rest ↔
      ∃ family ∈ basis left right, family.base .left = 0 ∧ family.base .right = 0 ∧
        ∃ remainder, assignment = remainder ∘ₛ family.elements :=
  (add_left_inj rest).trans (closed_solves_iff left right assignment)

end Selection

/-- A finite minimal complete set exists for every type of variables. -/
theorem exists_minimal_complete (left right : List (Term σ)) :
    ∃ result : Set (Family σ), Unification.IsMinimalComplete (Unifier left right) MoreGeneral result ∧
      result.Finite := by
  classical
  exact ⟨_, minimal_complete left right, finite left right⟩

/-- **Unification of two bags of first-order terms with independent rests is
finitary.** It is not unitary in general
(`TermBagBasis.Controls.swap_not_unitary`). -/
theorem finitary (left right : List (Term σ)) : Unification.Finitary (Unifier left right) MoreGeneral := by
  obtain ⟨result, minimal, finite⟩ := exists_minimal_complete left right
  exact ⟨result, minimal.toIsComplete, finite⟩

/-- On a finite type of variables, the basis computed with the proved
generality checker. -/
def executable [Fintype σ.vars] (left right : List (Term σ)) : List (Family σ) := basis left right

theorem executable_solves_iff [Fintype σ.vars] (left right : List (Term σ)) (answer : Answer σ) :
    Solves left right answer ↔ ∃ family ∈ executable left right, Instance family answer :=
  solves_iff left right answer

theorem executable_irredundant [Fintype σ.vars] (left right : List (Term σ)) :
    Unification.IsMinimalComplete (Unifier left right) MoreGeneral {family | family ∈ executable left right} :=
  minimal_complete left right

end Mettapedia.Algebra.Collections.TermBagBasis
