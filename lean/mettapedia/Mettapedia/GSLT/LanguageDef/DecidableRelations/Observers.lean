import Mettapedia.GSLT.LanguageDef.DecidableRelations.Membership
import Mettapedia.Cybernetics.DistinctionCalculus.Basic

/-!
# Complemented relations from observers, and keyed indexes

In the distinction calculus an observer is a tolerance. It finds two states either indistinguishable or apart, where
apartness is a witnessed distinction. Non-membership is relative to an observer: nothing in a collection is
indistinguishable from the element asked about.

- **An observer decides its own distinctions** (`Tolerance.distinctions_complemented`). It decides non-membership relative
  to it, with membership relative to it as the complement (`Tolerance.nonMembership_complemented`).
- **Non-membership is antitone in the observer**: an observer that identifies more finds fewer non-members
  (`Tolerance.nonMember_of_extends`).
- **The sharp observer** identifies only equal patterns. On the signature's terms:
  - its apartness is exactly the disequality the language derives (`derives_unequal_iff_sharp_apart`);
  - non-membership relative to it is exactly the non-membership the language derives (`derives_nonMember_iff_sharp`).
- **A keyed index** answers membership by looking up the key of the element asked about (`indexContains`). It decides
  membership relative to the observer of its keys, `Tolerance.ofReport key` (`indexContains_iff_indistinguishable`).
  - It hosts a relation exactly when its keys are a canonical form for that relation: equal keys are exactly related
    elements (`index_hosts_iff`).
  - With injective keys, such as the serialization a prefix trie stores, its verdict is the non-membership the language
    derives (`index_misses_iff_derives_nonMember`).
  - Keys that lose a distinction must decline: an index keyed by head constructors reports a placement as a member
    that the language derives a non-member (`headIndex_not_hosting`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DecidableRelations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Cybernetics.DistinctionCalculus

universe u v

/-! ## Observers decide their distinctions -/

namespace Tolerance

variable {V : Type u}

/-- **An observer decides its own distinctions**: two states are indistinguishable or apart, never both. -/
theorem distinctions_complemented (observer : Tolerance V ℚ) :
    Complemented (fun pair : V × V => observer.Indistinguishable pair.1 pair.2)
      (fun pair => observer.Apart pair.1 pair.2) (fun _ => True) where
  disjoint pair _ same apart := by
    unfold Tolerance.Indistinguishable at same
    unfold Tolerance.Apart at apart
    rw [same] at apart
    exact lt_irrefl 0 apart
  exhaustive pair _ := by
    rcases (observer.distance_nonnegative pair.1 pair.2).lt_or_eq with apart | same
    · exact .inr apart
    · exact .inl same.symm

/-- **Non-membership relative to an observer** is complemented: something in the collection is indistinguishable from the
element asked about, or everything in it is apart from it. -/
theorem nonMembership_complemented (observer : Tolerance V ℚ) :
    Complemented (fun asked : V × List V => ∃ x ∈ asked.2, observer.Indistinguishable x asked.1)
      (fun asked => ∀ x ∈ asked.2, observer.Apart x asked.1) (fun _ => True) where
  disjoint asked _ found missing := by
    obtain ⟨x, member, same⟩ := found
    exact (distinctions_complemented observer).disjoint (x, asked.1) trivial same (missing x member)
  exhaustive asked _ := by
    by_cases present : ∃ x ∈ asked.2, observer.Indistinguishable x asked.1
    · exact .inl present
    · refine .inr fun x member => ?_
      exact ((distinctions_complemented observer).exhaustive (x, asked.1) trivial).resolve_left
        fun same => present ⟨x, member, same⟩

/-- An observer that identifies more is apart less. -/
theorem apart_of_extends {base model : Tolerance V ℚ} (extended : base.Extends model) {x y : V}
    (apart : model.Apart x y) : base.Apart x y :=
  lt_of_lt_of_le apart (Tolerance.distance_le_of_extends extended x y)

/-- **Non-membership is antitone in the observer**: what an observer that identifies more finds missing, a finer one
does too. -/
theorem nonMember_of_extends {base model : Tolerance V ℚ} (extended : base.Extends model) {element : V}
    {stored : List V} (missing : ∀ x ∈ stored, model.Apart x element) : ∀ x ∈ stored, base.Apart x element :=
  fun x member => apart_of_extends extended (missing x member)

end Tolerance

/-! ## The sharp observer is the language's own equality -/

/-- **The sharp observer** of patterns: it identifies only equal patterns. -/
def sharp : Tolerance Pattern ℚ := Tolerance.ofReport id ℚ

/-- Two patterns are apart for the sharp observer exactly when they differ. -/
theorem sharp_apart_iff {first second : Pattern} : sharp.Apart first second ↔ first ≠ second := by
  rw [← not_iff_not, Tolerance.not_apart_iff_indistinguishable, not_not]
  exact Tolerance.ofReport_indistinguishable id first second

section Language

variable {relEnv : RelationEnv} {language : LanguageDef} {signature : List (String × Nat)} {kind : CollType}

/-- **The language derives disequality exactly where the sharp observer finds a distinction.** -/
theorem derives_unequal_iff_sharp_apart (rules : ∀ rule ∈ disequalityRules signature, rule ∈ language.rewrites)
    (privacy : Private language signature) (names : (signature.map Prod.fst).Nodup) {first second : Pattern}
    (firstOver : TermOf signature first) (secondOver : TermOf signature second) :
    Derives relEnv language unequalJudgment [first, second] ↔ sharp.Apart first second :=
  (derives_unequal_iff rules privacy names firstOver secondOver).trans sharp_apart_iff.symm

/-- **The language derives non-membership exactly where every element is apart for the sharp observer.** -/
theorem derives_nonMember_iff_sharp (rules : ∀ rule ∈ membershipRules signature kind, rule ∈ language.rewrites)
    (privacy : MembershipPrivate language signature kind) (names : (signature.map Prod.fst).Nodup)
    (notVector : kind ≠ .vec) {element : Pattern} {elements : List Pattern}
    (elementOver : TermOf signature element) (elementsOver : ∀ value ∈ elements, TermOf signature value) :
    Derives relEnv language nonMemberJudgment [element, .collection kind elements none] ↔
      ∀ x ∈ elements, sharp.Apart x element := by
  rw [derives_nonMember_iff rules privacy names notVector elementOver elementsOver]
  simp only [sharp_apart_iff]
  constructor
  · intro missing x member same
    exact missing (same ▸ member)
  · intro apart member
    exact apart element member rfl

end Language

/-! ## Keyed indexes -/

section Keyed

variable {V : Type u} {K : Type v} [DecidableEq K]

/-- **A keyed index**: it answers membership by looking up the key of the element asked about among the stored keys. -/
def indexContains (key : V → K) (stored : List V) (element : V) : Bool :=
  (stored.map key).contains (key element)

/-- The index finds an element present exactly when some stored element has its key. -/
theorem indexContains_iff (key : V → K) (stored : List V) (element : V) :
    indexContains key stored element = true ↔ ∃ x ∈ stored, key x = key element := by
  simp [indexContains]

/-- **A keyed index decides membership relative to the observer of its keys.** -/
theorem indexContains_iff_indistinguishable (key : V → K) (stored : List V) (element : V) :
    indexContains key stored element = true ↔
      ∃ x ∈ stored, (Tolerance.ofReport key ℚ).Indistinguishable x element := by
  simp only [indexContains_iff, Tolerance.ofReport_indistinguishable]

/-- **A keyed index hosts a relation exactly when its keys are a canonical form for it**: it answers membership modulo
`related`, for every store and element, if and only if equal keys are exactly related elements. -/
theorem index_hosts_iff (key : V → K) (related : V → V → Prop) :
    (∀ stored element, indexContains key stored element = true ↔ ∃ x ∈ stored, related x element) ↔
      ∀ x y, key x = key y ↔ related x y := by
  constructor
  · intro hosts x y
    have single := hosts [x] y
    rw [indexContains_iff] at single
    simpa using single
  · intro canonical stored element
    rw [indexContains_iff]
    exact exists_congr fun x => and_congr_right fun _ => canonical x element

end Keyed

section Language

variable {relEnv : RelationEnv} {language : LanguageDef} {signature : List (String × Nat)} {kind : CollType}
  {K : Type v} [DecidableEq K]

/-- **An index keyed injectively misses exactly the non-members the language derives**, as a prefix trie of the
terms' serializations does. -/
theorem index_misses_iff_derives_nonMember (key : Pattern → K) (injective : Function.Injective key)
    (rules : ∀ rule ∈ membershipRules signature kind, rule ∈ language.rewrites)
    (privacy : MembershipPrivate language signature kind) (names : (signature.map Prod.fst).Nodup)
    (notVector : kind ≠ .vec) {element : Pattern} {elements : List Pattern}
    (elementOver : TermOf signature element) (elementsOver : ∀ value ∈ elements, TermOf signature value) :
    indexContains key elements element = false ↔
      Derives relEnv language nonMemberJudgment [element, .collection kind elements none] := by
  rw [derives_nonMember_iff rules privacy names notVector elementOver elementsOver, ← Bool.not_eq_true,
    indexContains_iff]
  constructor
  · intro notContained member
    exact notContained ⟨element, member, rfl⟩
  · rintro missing ⟨x, member, same⟩
    exact missing (injective same ▸ member)

end Language

end Mettapedia.GSLT.LanguageDef.DecidableRelations
