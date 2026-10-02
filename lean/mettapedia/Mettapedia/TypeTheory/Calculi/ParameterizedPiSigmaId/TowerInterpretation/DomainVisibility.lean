import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.ZFC.Basic

/-!
# Truth-valued propositions hide the domains of quantifiers

A computation rule of a constant holds in the set tower at the typed instances
of its left side, and fails at others (`TypedInstances`,
`Instances.TowerInterpretation.ComputationControls`).  One way to make soundness
go through without typing premises in the rule would be a reading in which a
function carries its domain, so that an application outside the domain is
detectable.  This module shows where that reading must stop.

The decoder rule of an impredicative quantifier, `holds (all A P) ⟶ Π x : A.
holds (P x)`, identifies the value of a proposition with the value of a
dependent function type.  If there are more quantifier domains than
propositions, two domains receive the same function type.  So a reading in
which the value of `Π x : A. B` determines `A` cannot read propositions as
truth values; it has to read them as data.

* `not_injective_pi_of_decoderRule`: with the decoder rule, and no injection
  from domains into propositions, the reading of `Π x : A. ⊤` is not injective
  in `A`.
* `not_injective_pi_of_subsets`: this applies when every set of propositions is
  a quantifier domain (Cantor).
* `exists_domains_of_card_lt`: and when domains and propositions are finite and
  there are more domains.
* `ThreeDomains.exists_same_value`: with two truth values, among the domains
  `∅`, `{∅}` and `{∅, {∅}}` two have the same function type, for every reading
  whatever.  The tower's trace encoding is one such reading
  (`Instances.TowerInterpretation.tracePiSet_domain_invisible`).
* Control, `Data.injective_pi_with_decoderRule`: with propositions read as the
  codes themselves, the decoder rule holds for an injective reading.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.DomainVisibility

universe u v w

section Abstract

variable {Domain : Type u} {Proposition : Type v} {Value : Type w}

/-- **With the decoder rule, and fewer propositions than domains, the value of
`Π x : A. ⊤` does not determine `A`.**  `all A` is the proposition
`∀ x : A. ⊤`, `decode` reads a proposition as a type, and `pi A` reads the
function type. -/
theorem not_injective_pi_of_decoderRule (all : Domain → Proposition) (decode : Proposition → Value)
    (pi : Domain → Value) (decoderRule : ∀ A, decode (all A) = pi A)
    (fewer : ∀ code : Domain → Proposition, ¬ Function.Injective code) :
    ¬ Function.Injective pi := by
  intro injective
  refine fewer all fun first second same => injective ?_
  rw [← decoderRule first, ← decoderRule second, same]

theorem exists_domains_of_decoderRule (all : Domain → Proposition) (decode : Proposition → Value)
    (pi : Domain → Value) (decoderRule : ∀ A, decode (all A) = pi A)
    (fewer : ∀ code : Domain → Proposition, ¬ Function.Injective code) :
    ∃ first second, first ≠ second ∧ pi first = pi second := by
  by_contra none
  refine not_injective_pi_of_decoderRule all decode pi decoderRule fewer fun first second same => ?_
  by_contra distinct
  exact none ⟨first, second, distinct, same⟩

/-- When every set of propositions is a quantifier domain, there are fewer
propositions than domains. -/
theorem not_injective_pi_of_subsets (all : Domain → Proposition) (decode : Proposition → Value)
    (pi : Domain → Value) (decoderRule : ∀ A, decode (all A) = pi A)
    (subsets : Set Proposition → Domain) (subsetsInjective : Function.Injective subsets) :
    ¬ Function.Injective pi :=
  not_injective_pi_of_decoderRule all decode pi decoderRule fun code injective =>
    Function.cantor_injective (code ∘ subsets) (injective.comp subsetsInjective)

/-- Finitely many propositions and more domains. -/
theorem exists_domains_of_card_lt [Fintype Domain] [Fintype Proposition]
    (all : Domain → Proposition) (decode : Proposition → Value) (pi : Domain → Value)
    (decoderRule : ∀ A, decode (all A) = pi A)
    (more : Fintype.card Proposition < Fintype.card Domain) :
    ∃ first second, first ≠ second ∧ pi first = pi second :=
  exists_domains_of_decoderRule all decode pi decoderRule fun code injective =>
    absurd (Fintype.card_le_of_injective code injective) (Nat.not_le.mpr more)

end Abstract

/-! ## Two truth values and three domains -/

namespace ThreeDomains

/-- The domains `∅`, `{∅}` and `{∅, {∅}}`. -/
def domain : Fin 3 → ZFSet.{u}
  | 0 => ∅
  | 1 => {∅}
  | 2 => {∅, {∅}}

theorem empty_ne_singleton : (∅ : ZFSet.{u}) ≠ {∅} := by
  intro same
  have member : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [← same] at member
  exact ZFSet.notMem_empty ∅ member

theorem empty_ne_pair : (∅ : ZFSet.{u}) ≠ {∅, {∅}} := by
  intro same
  have member : (∅ : ZFSet.{u}) ∈ ({∅, {∅}} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inl rfl)
  rw [← same] at member
  exact ZFSet.notMem_empty ∅ member

theorem singleton_ne_pair : ({∅} : ZFSet.{u}) ≠ {∅, {∅}} := by
  intro same
  have member : ({∅} : ZFSet.{u}) ∈ ({∅, {∅}} : ZFSet.{u}) := ZFSet.mem_pair.mpr (Or.inr rfl)
  rw [← same] at member
  exact empty_ne_singleton (ZFSet.mem_singleton.mp member).symm

/-- The three domains are distinct. -/
theorem domain_injective : Function.Injective domain.{u}
  | 0, 0, _ => rfl
  | 1, 1, _ => rfl
  | 2, 2, _ => rfl
  | 0, 1, same => absurd same empty_ne_singleton
  | 1, 0, same => absurd same.symm empty_ne_singleton
  | 0, 2, same => absurd same empty_ne_pair
  | 2, 0, same => absurd same.symm empty_ne_pair
  | 1, 2, same => absurd same singleton_ne_pair
  | 2, 1, same => absurd same.symm singleton_ne_pair

/-- **Two of the three domains have one function type**, for every reading of
function types and every reading of the two truth values. -/
theorem exists_same_value (all : ZFSet.{u} → Bool) (decode : Bool → ZFSet.{u})
    (pi : ZFSet.{u} → ZFSet.{u}) (decoderRule : ∀ A, decode (all A) = pi A) :
    ∃ first second : ZFSet.{u}, first ≠ second ∧ pi first = pi second := by
  obtain ⟨first, second, distinct, same⟩ :=
    exists_domains_of_card_lt (fun index => all (domain index)) decode
      (fun index => pi (domain index)) (fun index => decoderRule (domain index)) (by decide)
  exact ⟨domain first, domain second, fun equal => distinct (domain_injective equal), same⟩

end ThreeDomains

/-! ## Control: propositions as data -/

namespace Data

variable {Domain : Type u} {Value : Type w}

/-- **With propositions read as the codes themselves, the decoder rule holds for
an injective reading of function types.** -/
theorem injective_pi_with_decoderRule (pi : Domain → Value) (injective : Function.Injective pi) :
    ∃ (all : Domain → Domain) (decode : Domain → Value),
      (∀ A, decode (all A) = pi A) ∧ Function.Injective pi :=
  ⟨id, pi, fun _ => rfl, injective⟩

end Data

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.DomainVisibility
