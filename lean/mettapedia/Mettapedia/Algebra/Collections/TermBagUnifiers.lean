import Mettapedia.Algebra.Collections.FlatBagUnifiers
import Mettapedia.Logic.LP.TermEquality

/-!
# Bags of first-order terms: unifier families per partial matching

Two bag patterns `{t₁ … tₙ | R}` and `{u₁ … u_m | S}` whose elements are
first-order terms over free function symbols (`Logic.LP.Term`), with two
independent rest slots `R` and `S`. An answer assigns terms to the element
variables and bags to the rest slots (`Answer`); it solves the problem when
both sides instantiate to the same bag (`Solves`).

* **One family per consistent partial matching.** A partial matching pairs
  some left elements with right elements (`Unification.matchings`). The
  answers that realize it, with its pairs unified and the rests in solved
  form, are exactly the instances of one family: the most general unifier
  of the matched pairs, computed by the occurs-checked total unifier
  (`Logic.LP.unifyTotal`), with each rest the other side's unmatched elements
  under that unifier plus one common bag parameter (`realizes_iff`). A matching
  whose pairs do not unify has no answer and no family.
* **Soundness and completeness**: every instance of a family produced by the
  finite search solves the problem, and every solution is an instance of one
  of them (`sound`, `complete`, `solves_iff`); the families are finitely many
  (`finite_families`).
* **Generality** between families is a preorder (`MoreGeneral.refl`,
  `MoreGeneral.trans`), and a more general family has more instances
  (`moreGeneral_iff_instances_subset`).

Element equations are syntactic, with the occurs check: `{x | R} = {f(x) | S}`
has no family pairing `x` with `f(x)`, only the family leaving both unmatched
(`TermBagBasis.Controls.occurs_basis`). The flat problem, elements that are
constants or variables, is the case of a signature without function symbols
(`TermBagFunctionFree.flat_basis_eq`).

Scope: one bag at the root; its elements are first-order terms over free
function symbols, in which no bag, set or sequence symbol occurs; the two rest
slots are distinct bag variables that occur nowhere else, and element
variables stand for single elements. A side without a rest is the case of an
empty rest (`TermBagBasis.closed_solves_iff`,
`TermBagBasis.right_closed_solves_iff`), and a rest shared by the two sides
cancels (`TermBagBasis.shared_rest_solves_iff`). Bags nested inside elements
are not covered (`TermBagBasis.Controls.inner_bag_is_not_free_syntax`).
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.TermBagUnifiers

open Mettapedia.Logic.LP (LPSignature Term Subst Unifies unifyTotal)
open Unification (matchings flat_bag_unify_iff)
open FlatBagUnifiers (RestSlot)

variable {σ : LPSignature}

/-- Terms for the element variables and bags for the two rest slots. -/
@[ext] structure Answer (σ : LPSignature) where
  elements : Subst σ
  rest : RestSlot → Multiset (Term σ)

/-- A family of answers: an element substitution and the base of each rest
slot, to be extended by one common bag. -/
@[ext] structure Family (σ : LPSignature) where
  elements : Subst σ
  base : RestSlot → Multiset (Term σ)

/-- The answer of a family under a further substitution and a common bag. -/
def instantiate (family : Family σ) (remainder : Subst σ) (common : Multiset (Term σ)) : Answer σ where
  elements := remainder ∘ₛ family.elements
  rest slot := (family.base slot).map remainder.applyTerm + common

def genericAnswer (family : Family σ) : Answer σ := ⟨family.elements, family.base⟩

def Instance (family : Family σ) (answer : Answer σ) : Prop :=
  ∃ remainder common, answer = instantiate family remainder common

/-- A family is more general than another when the other's generic answer is
one of its instances. -/
def MoreGeneral (general specific : Family σ) : Prop := Instance general (genericAnswer specific)

theorem instantiate_id (family : Family σ) : instantiate family (Subst.id σ) 0 = genericAnswer family := by
  apply Answer.ext
  · exact Subst.comp_id_left family.elements
  · funext slot
    simp [instantiate, genericAnswer, Subst.applyTerm_id]

theorem generic_instance (family : Family σ) : Instance family (genericAnswer family) :=
  ⟨Subst.id σ, 0, (instantiate_id family).symm⟩

theorem instance_factor {general specific : Family σ} {answer : Answer σ}
    (covers : MoreGeneral general specific) (instanceOf : Instance specific answer) : Instance general answer := by
  obtain ⟨first, commonFirst, represented⟩ := covers
  obtain ⟨second, commonSecond, rfl⟩ := instanceOf
  have elements := congrArg Answer.elements represented
  have rests := congrArg Answer.rest represented
  refine ⟨second ∘ₛ first, commonFirst.map second.applyTerm + commonSecond, ?_⟩
  apply Answer.ext
  · change second ∘ₛ specific.elements = (second ∘ₛ first) ∘ₛ general.elements
    have same : specific.elements = first ∘ₛ general.elements := elements
    rw [same, Subst.comp_assoc]
  · funext slot
    have same : specific.base slot = (general.base slot).map first.applyTerm + commonFirst := congrFun rests slot
    simp only [instantiate, same, Multiset.map_add, Multiset.map_map, add_assoc]
    congr 1
    apply Multiset.map_congr rfl
    intro term _
    exact (Subst.applyTerm_comp second first term).symm

theorem MoreGeneral.refl (family : Family σ) : MoreGeneral family family := generic_instance family

theorem MoreGeneral.trans {first second third : Family σ}
    (earlier : MoreGeneral first second) (later : MoreGeneral second third) : MoreGeneral first third :=
  instance_factor earlier later

theorem moreGeneral_iff_instances_subset (general specific : Family σ) :
    MoreGeneral general specific ↔ ∀ answer, Instance specific answer → Instance general answer :=
  ⟨fun covers _ instanceOf => instance_factor covers instanceOf,
    fun included => included (genericAnswer specific) (generic_instance specific)⟩

/-- Both sides instantiate to the same bag. -/
def Solves (left right : List (Term σ)) (answer : Answer σ) : Prop :=
  (left.map answer.elements.applyTerm : Multiset (Term σ)) + answer.rest .left =
    (right.map answer.elements.applyTerm : Multiset (Term σ)) + answer.rest .right

/-- A partial matching: the matched pairs, the unmatched left elements and the
unmatched right elements. -/
abbrev Matching (σ : LPSignature) := List (Term σ × Term σ) × List (Term σ) × List (Term σ)

/-- An answer realizes a matching when it unifies the matched pairs and each
rest is the other side's unmatched elements plus one common bag. -/
def Realizes (matching : Matching σ) (answer : Answer σ) : Prop :=
  (∀ pair ∈ matching.1, answer.elements.applyTerm pair.1 = answer.elements.applyTerm pair.2) ∧
    ∃ common, answer.rest .left = (matching.2.2.map answer.elements.applyTerm : Multiset (Term σ)) + common ∧
      answer.rest .right = (matching.2.1.map answer.elements.applyTerm : Multiset (Term σ)) + common

/-- The family of a matching under a unifier of its pairs: the rests in solved
form. -/
def fromMatching (matching : Matching σ) (general : Subst σ) : Family σ where
  elements := general
  base
    | .left => (matching.2.2.map general.applyTerm : Multiset (Term σ))
    | .right => (matching.2.1.map general.applyTerm : Multiset (Term σ))

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- **Solutions are the answers that realize some partial matching.** -/
theorem solves_iff_realizes (left right : List (Term σ)) (answer : Answer σ) :
    Solves left right answer ↔ ∃ matching ∈ matchings left right, Realizes matching answer := by
  unfold Solves
  rw [flat_bag_unify_iff answer.elements.applyTerm left right (answer.rest .left) (answer.rest .right)]
  rfl

/-- The family of a matching, when its pairs unify. -/
def candidate (matching : Matching σ) : Option (Family σ) :=
  (unifyTotal matching.1).map (fromMatching matching)

/-- **One most general family per matching**: the answers realizing a matching
are exactly the instances of its family, the unifier of the matched pairs with
the rests in solved form. -/
theorem realizes_iff (matching : Matching σ) (answer : Answer σ) :
    Realizes matching answer ↔ ∃ family, candidate matching = some family ∧ Instance family answer := by
  constructor
  · rintro ⟨paired, common, leftRest, rightRest⟩
    obtain ⟨general, accepted⟩ := Mettapedia.Logic.LP.unifyTotal_complete (equations := matching.1)
      ⟨answer.elements, paired⟩
    obtain ⟨remainder, factors⟩ := Mettapedia.Logic.LP.unifyTotal_mgu matching.1 general accepted
      answer.elements paired
    have composite : answer.elements = remainder ∘ₛ general := funext factors
    have mapped (terms : List (Term σ)) :
        (terms.map answer.elements.applyTerm : Multiset (Term σ)) =
          ((terms.map general.applyTerm : List (Term σ)) : Multiset (Term σ)).map remainder.applyTerm := by
      rw [Multiset.map_coe, List.map_map, composite]
      congr 1
      apply List.map_congr_left
      intro term _
      exact Subst.applyTerm_comp remainder general term
    refine ⟨fromMatching matching general, by simp [candidate, accepted], remainder, common, ?_⟩
    apply Answer.ext
    · exact composite
    · funext slot
      cases slot with
      | left => rw [leftRest, mapped]; rfl
      | right => rw [rightRest, mapped]; rfl
  · rintro ⟨family, produced, remainder, common, rfl⟩
    unfold candidate at produced
    obtain ⟨general, accepted, rfl⟩ := Option.map_eq_some_iff.mp produced
    have unified := Mettapedia.Logic.LP.unifyTotal_sound matching.1 general accepted
    have mapped (terms : List (Term σ)) :
        ((terms.map general.applyTerm : List (Term σ)) : Multiset (Term σ)).map remainder.applyTerm =
          (terms.map (remainder ∘ₛ general).applyTerm : Multiset (Term σ)) := by
      rw [Multiset.map_coe, List.map_map]
      congr 1
      apply List.map_congr_left
      intro term _
      exact (Subst.applyTerm_comp remainder general term).symm
    refine ⟨fun pair member => ?_, common, ?_, ?_⟩
    · change (remainder ∘ₛ general).applyTerm pair.1 = (remainder ∘ₛ general).applyTerm pair.2
      rw [Subst.applyTerm_comp, Subst.applyTerm_comp, unified pair member]
    · change ((matching.2.2.map general.applyTerm : List (Term σ)) : Multiset (Term σ)).map
          remainder.applyTerm + common = _
      rw [mapped]
      rfl
    · change ((matching.2.1.map general.applyTerm : List (Term σ)) : Multiset (Term σ)).map
          remainder.applyTerm + common = _
      rw [mapped]
      rfl

/-- A matching whose pairs do not unify is realized by no answer. -/
theorem no_family_no_answer (matching : Matching σ) (rejected : candidate matching = none)
    (answer : Answer σ) : ¬ Realizes matching answer := by
  intro realized
  obtain ⟨family, produced, -⟩ := (realizes_iff matching answer).mp realized
  rw [rejected] at produced
  cases produced

/-- The families of the finite occurrence search. -/
def families (left right : List (Term σ)) : List (Family σ) :=
  (matchings left right).filterMap candidate

/-- **Soundness.** -/
theorem sound (left right : List (Term σ)) (family : Family σ) (member : family ∈ families left right)
    (answer : Answer σ) (instanceOf : Instance family answer) : Solves left right answer := by
  obtain ⟨matching, selected, produced⟩ := List.mem_filterMap.mp member
  exact (solves_iff_realizes left right answer).mpr
    ⟨matching, selected, (realizes_iff matching answer).mpr ⟨family, produced, instanceOf⟩⟩

/-- **Completeness**: every solution, element variables bound to arbitrary
terms, is an instance of a family of the search. -/
theorem complete (left right : List (Term σ)) (answer : Answer σ) (solved : Solves left right answer) :
    ∃ family ∈ families left right, Instance family answer := by
  obtain ⟨matching, selected, realized⟩ := (solves_iff_realizes left right answer).mp solved
  obtain ⟨family, produced, instanceOf⟩ := (realizes_iff matching answer).mp realized
  exact ⟨family, List.mem_filterMap.mpr ⟨matching, selected, produced⟩, instanceOf⟩

theorem solves_iff (left right : List (Term σ)) (answer : Answer σ) :
    Solves left right answer ↔ ∃ family ∈ families left right, Instance family answer :=
  ⟨complete left right answer, fun ⟨family, member, instanceOf⟩ => sound left right family member answer instanceOf⟩

theorem finite_families (left right : List (Term σ)) : {family | family ∈ families left right}.Finite :=
  (families left right).finite_toSet

theorem generated_family_solves (left right : List (Term σ)) (family : Family σ)
    (member : family ∈ families left right) : Solves left right (genericAnswer family) :=
  sound left right family member (genericAnswer family) (generic_instance family)

end Mettapedia.Algebra.Collections.TermBagUnifiers
