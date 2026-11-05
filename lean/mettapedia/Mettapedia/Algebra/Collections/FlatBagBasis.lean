import Mettapedia.Algebra.Collections.FlatBagSubsumption
import Mettapedia.Algebra.Collections.FiniteUnifierBasis

/-!
# Complete irredundant bases for flat bags with independent rests

The actual occurrence matcher and element unifier produce candidates. The
proved factorization checker decides generality on finite active contexts.
Stable pruning retains maximal classes in original enumeration order.
Mathematical existence for arbitrary variable universes is classical, not
an executable semantic oracle. Nested AC and aliased rest slots are separate.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.FlatBagBasis

open FlatElementEncoding (Element)
open FlatBagUnifiers (Answer Family Instance MoreGeneral families genericAnswer)

variable {A X : Type*} [DecidableEq A] [DecidableEq X]

def Unifier (left right : List (Element A X)) (family : Family A X) : Prop :=
  ∀ answer, Instance family answer → FlatBagUnifiers.Solves left right answer

section Selection

variable [DecidableRel (MoreGeneral : Family A X → Family A X → Prop)]

def basis (left right : List (Element A X)) : List (Family A X) :=
  FiniteUnifierBasis.select (families left right) MoreGeneral

theorem sound (left right : List (Element A X)) (family : Family A X)
    (member : family ∈ basis left right) : Unifier left right family :=
  FlatBagUnifiers.sound left right family
    (FiniteUnifierBasis.selected_from_input (families left right) MoreGeneral member)

theorem complete (left right : List (Element A X)) (answer : Answer A X)
    (solved : FlatBagUnifiers.Solves left right answer) :
    ∃ family ∈ basis left right, Instance family answer := by
  obtain ⟨raw, member, instanceOf⟩ := FlatBagUnifiers.complete left right answer solved
  obtain ⟨retained, selected, moreGeneral⟩ := FiniteUnifierBasis.covers_input (families left right) MoreGeneral
    FlatBagUnifiers.MoreGeneral.refl (fun first second => FlatBagUnifiers.MoreGeneral.trans first second) member
  exact ⟨retained, selected, FlatBagUnifiers.instance_factor moreGeneral instanceOf⟩

theorem solves_iff (left right : List (Element A X)) (answer : Answer A X) :
    FlatBagUnifiers.Solves left right answer ↔ ∃ family ∈ basis left right, Instance family answer :=
  ⟨complete left right answer, fun ⟨family, member, instanceOf⟩ => sound left right family member answer instanceOf⟩

/-- Permuting the presentations can change representative order, not the
solutions represented by the retained families. -/
theorem permutation_preserves_solutions (left right otherLeft otherRight : List (Element A X))
    (leftPerm : left.Perm otherLeft) (rightPerm : right.Perm otherRight) (answer : Answer A X) :
    (∃ family ∈ basis left right, Instance family answer) ↔
      ∃ family ∈ basis otherLeft otherRight, Instance family answer := by
  rw [← solves_iff, ← solves_iff]
  unfold FlatBagUnifiers.Solves
  rw [Multiset.coe_eq_coe.mpr (leftPerm.map (FlatElementEncoding.apply answer.elements)),
    Multiset.coe_eq_coe.mpr (rightPerm.map (FlatElementEncoding.apply answer.elements))]

theorem no_subsumption (left right : List (Element A X)) (first second : Family A X)
    (firstMember : first ∈ basis left right) (secondMember : second ∈ basis left right)
    (general : MoreGeneral first second) : first = second :=
  FiniteUnifierBasis.no_subsumed_distinct (families left right) MoreGeneral firstMember secondMember general

theorem nodup (left right : List (Element A X)) : (basis left right).Nodup :=
  FiniteUnifierBasis.selected_nodup (families left right) MoreGeneral FlatBagUnifiers.MoreGeneral.refl

theorem stable_indices (left right : List (Element A X)) :
    (FiniteUnifierBasis.indices (families left right) MoreGeneral).Sublist
      (List.finRange (families left right).length) :=
  FiniteUnifierBasis.indices_sublist _ _

theorem minimal_complete (left right : List (Element A X)) :
    Unification.IsMinimalComplete (Unifier left right) MoreGeneral {family | family ∈ basis left right} where
  sound family member := sound left right family member
  covers family solves := by
    obtain ⟨general, member, covered⟩ := complete left right (genericAnswer family)
      (solves _ (FlatBagUnifiers.generic_instance family))
    exact ⟨general, member, covered⟩
  minimal first firstMember second secondMember general := no_subsumption left right first second firstMember secondMember general

theorem finite (left right : List (Element A X)) : {family | family ∈ basis left right}.Finite :=
  List.finite_toSet _

end Selection

/-- A mathematical basis exists without a finite ambient variable type. -/
theorem exists_minimal_complete (left right : List (Element A X)) :
    ∃ result : Set (Family A X), Unification.IsMinimalComplete (Unifier left right) MoreGeneral result ∧ result.Finite := by
  classical
  exact ⟨_, minimal_complete left right, finite left right⟩

/-- Finite contexts use the proved finite factorization checker. -/
def executable [Fintype X] (left right : List (Element A X)) : List (Family A X) := basis left right

theorem executable_complete [Fintype X] (left right : List (Element A X)) (answer : Answer A X) :
    FlatBagUnifiers.Solves left right answer ↔ ∃ family ∈ executable left right, Instance family answer :=
  solves_iff left right answer

theorem executable_irredundant [Fintype X] (left right : List (Element A X)) :
    Unification.IsMinimalComplete (Unifier left right) MoreGeneral {family | family ∈ executable left right} :=
  minimal_complete left right

end Mettapedia.Algebra.Collections.FlatBagBasis
