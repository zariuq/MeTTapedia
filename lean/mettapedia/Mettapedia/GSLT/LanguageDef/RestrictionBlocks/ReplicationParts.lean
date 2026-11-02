import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationContent

/-!
# A component's parts read canonically

With fuel that settles it, reading a component again (`recanon`) reads each of its parts canonically: a named
multiset's argument as the multiset of its canonical block (`multisetPart`), any other argument through
`canonArgument`, a binder's body and a collection's members by their canonical forms (`recanon_apply_multiset`,
`recanon_apply_other`, `recanon_lambda`, `recanon_multiLambda`, `recanon_collection`); variables and explicit
substitutions stay. A lone atom is its own canonical block, its parts read again (`canonicalOf_atom`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {block : ReplicationBlock}

/-- **A named multiset's argument read canonically**: an open collection's members by their canonical forms, an
explicit substitution as written, any other argument as the multiset of its canonical block. -/
def multisetPart (block : ReplicationBlock) : Pattern → Pattern
  | .collection kind elements (some rest) => .collection kind (elements.map (canonicalOf block)) (some rest)
  | .subst body replacement => .subst body replacement
  | argument => multisetOf block.toBlock (normal block (decompose block.toBlock argument))

/-- With enough fuel, a pattern's canonical block is its canonical form's block. -/
theorem toPattern_normalizeWith_settled {pattern : Pattern} {fuel : Nat} (enough : 3 * size pattern + 3 ≤ fuel) :
    Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock pattern)) =
      canonicalOf block pattern := by
  have lighter := mass_decompose (block := block.toBlock) pattern
  rw [normalizeWith_settled (by omega)]
  rfl

theorem recanonMultisetWith_other {fuel : Nat} {argument : Pattern}
    (notOpen : ∀ kind elements rest, argument ≠ .collection kind elements (some rest))
    (notSubst : ∀ body replacement, argument ≠ .subst body replacement) :
    recanonMultisetWith block (fuel + 1) argument =
      multisetOf block.toBlock (normalizeWith block fuel (decompose block.toBlock argument)) := by
  cases argument with
  | collection kind elements rest =>
      cases rest with
      | none => simp only [recanonMultisetWith]
      | some rest => exact absurd rfl (notOpen kind elements rest)
  | subst body replacement => exact absurd rfl (notSubst body replacement)
  | bvar => simp only [recanonMultisetWith]
  | fvar => simp only [recanonMultisetWith]
  | apply => simp only [recanonMultisetWith]
  | lambda => simp only [recanonMultisetWith]
  | multiLambda => simp only [recanonMultisetWith]

theorem multisetPart_other {argument : Pattern}
    (notOpen : ∀ kind elements rest, argument ≠ .collection kind elements (some rest))
    (notSubst : ∀ body replacement, argument ≠ .subst body replacement) :
    multisetPart block argument = multisetOf block.toBlock (normal block (decompose block.toBlock argument)) := by
  cases argument with
  | collection kind elements rest =>
      cases rest with
      | none => rfl
      | some rest => exact absurd rfl (notOpen kind elements rest)
  | subst body replacement => exact absurd rfl (notSubst body replacement)
  | bvar => rfl
  | fvar => rfl
  | apply => rfl
  | lambda => rfl
  | multiLambda => rfl

theorem recanonMultisetWith_settled {argument : Pattern} {fuel : Nat} (enough : 3 * size argument + 4 ≤ fuel) :
    recanonMultisetWith block fuel argument = multisetPart block argument := by
  obtain ⟨fuel, rfl⟩ : ∃ smaller, fuel = smaller + 1 := ⟨fuel - 1, by omega⟩
  by_cases isOpen : ∃ kind elements rest, argument = .collection kind elements (some rest)
  · obtain ⟨kind, elements, rest, rfl⟩ := isOpen
    simp only [recanonMultisetWith, multisetPart]
    congr 1
    refine List.map_congr_left fun element member => toPattern_normalizeWith_settled ?_
    have := size_lt_of_mem member
    simp only [size] at enough
    omega
  · push Not at isOpen
    by_cases isSubst : ∃ body replacement, argument = .subst body replacement
    · obtain ⟨body, replacement, rfl⟩ := isSubst
      rfl
    · push Not at isSubst
      rw [recanonMultisetWith_other isOpen isSubst, multisetPart_other isOpen isSubst, normalizeWith_settled]
      have := mass_decompose (block := block.toBlock) argument
      omega

theorem recanon_apply_restrict (arguments : List Pattern) :
    recanon block (.apply block.restrict arguments) = .apply block.restrict arguments := by
  unfold recanon
  obtain ⟨fuel, fuelIs⟩ : ∃ fuel, 3 * size (Pattern.apply block.restrict arguments) + 2 = fuel + 1 := ⟨_, rfl⟩
  rw [fuelIs]
  simp only [recanonWith, if_true]

theorem recanon_apply_multiset {label : String} {arguments : List Pattern} (notRestrict : label ≠ block.restrict)
    (listed : label ∈ block.multisets) :
    recanon block (.apply label arguments) = .apply label (arguments.map (multisetPart block)) := by
  unfold recanon
  obtain ⟨fuel, fuelIs⟩ : ∃ fuel, 3 * size (Pattern.apply label arguments) + 2 = fuel + 1 := ⟨_, rfl⟩
  rw [fuelIs]
  simp only [recanonWith, if_neg notRestrict, if_pos listed]
  congr 1
  refine List.map_congr_left fun argument member => recanonMultisetWith_settled ?_
  have := size_lt_of_mem member
  simp only [size] at fuelIs
  omega

theorem recanon_apply_other {label : String} {arguments : List Pattern} (notRestrict : label ≠ block.restrict)
    (notListed : label ∉ block.multisets) :
    recanon block (.apply label arguments) = .apply label (arguments.map (canonArgument (canonicalOf block))) := by
  unfold recanon
  obtain ⟨fuel, fuelIs⟩ : ∃ fuel, 3 * size (Pattern.apply label arguments) + 2 = fuel + 1 := ⟨_, rfl⟩
  rw [fuelIs]
  simp only [recanonWith, if_neg notRestrict, if_neg notListed]
  congr 1
  refine List.map_congr_left fun argument member => canonArgument_congr fun pattern small =>
    toPattern_normalizeWith_settled ?_
  have := size_lt_of_mem member
  simp only [size] at fuelIs
  omega

theorem recanon_lambda (binder : Option String) (body : Pattern) :
    recanon block (.lambda binder body) = .lambda binder (canonicalOf block body) := by
  unfold recanon
  obtain ⟨fuel, fuelIs⟩ : ∃ fuel, 3 * size (Pattern.lambda binder body) + 2 = fuel + 1 := ⟨_, rfl⟩
  rw [fuelIs]
  simp only [recanonWith]
  simp only [size] at fuelIs
  rw [toPattern_normalizeWith_settled (by omega)]

theorem recanon_multiLambda (arity : Nat) (binders : List String) (body : Pattern) :
    recanon block (.multiLambda arity binders body) = .multiLambda arity binders (canonicalOf block body) := by
  unfold recanon
  obtain ⟨fuel, fuelIs⟩ : ∃ fuel, 3 * size (Pattern.multiLambda arity binders body) + 2 = fuel + 1 := ⟨_, rfl⟩
  rw [fuelIs]
  simp only [recanonWith]
  simp only [size] at fuelIs
  rw [toPattern_normalizeWith_settled (by omega)]

theorem recanon_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    recanon block (.collection kind elements rest) = .collection kind (elements.map (canonicalOf block)) rest := by
  unfold recanon
  obtain ⟨fuel, fuelIs⟩ : ∃ fuel, 3 * size (Pattern.collection kind elements rest) + 2 = fuel + 1 := ⟨_, rfl⟩
  rw [fuelIs]
  simp only [recanonWith]
  congr 1
  refine List.map_congr_left fun element member => toPattern_normalizeWith_settled ?_
  have := size_lt_of_mem member
  simp only [size] at fuelIs
  omega

theorem recanon_bvar (index : Nat) : recanon block (.bvar index) = .bvar index := rfl

theorem recanon_fvar (name : String) : recanon block (.fvar name) = .fvar name := rfl

theorem recanon_subst (body replacement : Pattern) :
    recanon block (.subst body replacement) = .subst body replacement := rfl

/-- **A lone atom is its own canonical block, its parts read again.** -/
theorem canonicalOf_atom {component : Pattern}
    (atomic : decompose block.toBlock component = Prenex.atom component) :
    canonicalOf block component = recanon block component := by
  have noCopy : ∀ canonical, absorbOnce block canonical ⟨0, [component]⟩ = none := by
    intro canonical
    cases component
    case apply label arguments =>
      rcases arguments with _ | ⟨argument, _ | ⟨second, rest⟩⟩
      · simp [absorbOnce]
      · by_cases isReplicate : label = block.replicate
        · simp [absorbOnce, isReplicate, groupsThrough]
        · simp [absorbOnce, isReplicate]
      · simp [absorbOnce]
    all_goals simp [absorbOnce]
  have absorbed : absorb block (canonicalOf block) (Prenex.atom component) = Prenex.atom component := by
    unfold absorb
    simp only [Prenex.atom, List.length_singleton, absorbRounds, noCopy, prune_zero]
  have identity : Prenex.permute 0 [] = id := permute_range 0
  unfold canonicalOf
  rw [normal_eq_reading, atomic, absorbed]
  simp only [readingsR, Prenex.atom, readingOrders_zero, List.map_cons, List.map_nil, identity, rename_id,
    least, List.foldl_nil]
  have sorted : sortComponents [recanon block component] = [recanon block component] := rfl
  have single : dedupReplicated block [recanon block component] = [recanon block component] := by
    simp [dedupReplicated]
  simp only [sorted, single, Prenex.toPattern, Prenex.restricts, Prenex.body]

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
