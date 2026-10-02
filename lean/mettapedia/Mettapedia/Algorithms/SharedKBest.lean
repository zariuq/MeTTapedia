import Mettapedia.Algorithms.LazyUnionPrefixes

/-!
# Shared k-best derivations in a finite acyclic dependency hypergraph

Nodes are authored in a topological order. Each physical family lists its
ordered child-node references and a natural charge. Source derivations are
defined independently by those references and families. The solver constructs
one bounded cache per node, shares it at every child reference, and combines
the caches through lazy products and alternative unions.

All child and alternative combinations retain derivation identities. Costs
are additive; this is a constructive monotone instance, not a theorem for
arbitrary nonmonotone scoring functions or cyclic dependency graphs.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.SharedKBest

open DerivationPrefix

inductive Derivation where
  | node (owner family charge : Nat) (children : List Derivation)
  deriving Repr

mutual
  def cost : Derivation → Nat
    | .node _ _ charge children => charge + childCost children
  def childCost : List Derivation → Nat
    | [] => 0
    | first :: rest => cost first + childCost rest
end

structure Family (previous : Nat) where
  charge : Nat
  children : List (Fin previous)
  deriving Repr, DecidableEq

inductive Network : Nat → Type where
  | empty : Network 0
  | append {previous : Nat} (prior : Network previous)
      (families : List (Family previous)) : Network (previous + 1)

def FamilyAllows {previous : Nat} (childSource : Fin previous → Derivation → Prop)
    (owner row : Nat) (family : Family previous) (derivation : Derivation) : Prop :=
  ∃ children, List.Forall₂ childSource family.children children ∧
    derivation = .node owner row family.charge children

def AlternativesAllow {previous : Nat} (childSource : Fin previous → Derivation → Prop)
    (owner : Nat) : Nat → List (Family previous) → Derivation → Prop
  | _, [], _ => False
  | row, family :: rest, derivation =>
      FamilyAllows childSource owner row family derivation ∨
        AlternativesAllow childSource owner (row + 1) rest derivation

/-- Independent exhaustive tree semantics. A node may share a child store,
but each occurrence in a derivation chooses a child derivation separately. -/
def Source : {size : Nat} → Network size → Fin size → Derivation → Prop
  | 0, .empty, index, _ => Fin.elim0 index
  | previous + 1, .append prior families, index, derivation =>
      if earlier : index.val < previous then
        Source prior ⟨index.val, earlier⟩ derivation
      else AlternativesAllow (Source prior) previous 0 families derivation

structure Certified (requested : Nat) (Value : Type) (price : Value → Nat)
    (source : Value → Prop) where
  cache : LazyProductPrefixes.Cache Value price
  correct : Correct requested price source cache.values

def Certified.relabel {Value : Type} {requested : Nat} {price : Value → Nat}
    {first second : Value → Prop} (cache : Certified requested Value price first)
    (equivalent : ∀ value, first value ↔ second value) :
    Certified requested Value price second where
  cache := cache.cache
  correct := by
    have same : first = second := funext fun value => propext (equivalent value)
    rw [← same]
    exact cache.correct

def Certified.map {Value Other : Type} {requested : Nat}
    {price : Value → Nat} {source : Value → Prop}
    (cache : Certified requested Value price source) (otherPrice : Other → Nat)
    (reconstruct : Value → Other)
    (faithful : ∀ first, source first → ∀ second, source second →
      reconstruct first = reconstruct second → first = second)
    (sameCost : ∀ value, otherPrice (reconstruct value) = price value) :
    Certified requested Other otherPrice
      (fun other => ∃ value, source value ∧ reconstruct value = other) := by
  let correct := map_correct_on requested price otherPrice source cache.cache.values
    cache.correct reconstruct faithful sameCost
  exact ⟨⟨cache.cache.values.map reconstruct, correct.distinct, correct.ordered⟩, correct⟩

def emptyCache (requested : Nat) : Certified requested Derivation cost (fun _ => False) :=
  ⟨⟨[], List.nodup_nil, List.Pairwise.nil⟩,
    empty_correct requested cost (fun _ => False) (fun _ impossible => impossible)⟩

def emptyChildren (requested : Nat) :
    Certified requested (List Derivation) childCost (fun children => children = []) := by
  by_cases zero : requested = 0
  · subst requested
    exact ⟨⟨[], List.nodup_nil, List.Pairwise.nil⟩, zero_correct childCost _⟩
  · refine ⟨⟨[[]], by simp, by simp⟩, ?_⟩
    constructor
    · simp
    · intro children member; simpa using member
    · simp
    · simp; omega
    · intro children allowed absent
      subst children
      exact False.elim (absent (List.mem_singleton.mpr rfl))

def prepend (requested : Nat) (headSource : Derivation → Prop)
    (tailSource : List Derivation → Prop)
    (head : Certified requested Derivation cost headSource)
    (tail : Certified requested (List Derivation) childCost tailSource) :
    Certified requested (List Derivation) childCost
      (fun children => ∃ pair : Derivation × List Derivation,
        (headSource pair.1 ∧ tailSource pair.2) ∧ pair.1 :: pair.2 = children) := by
  let correct := LazyProductPrefixes.selected_source_correct requested cost childCost
    headSource tailSource head.cache tail.cache head.correct tail.correct
  let pairs : Certified requested (Derivation × List Derivation)
      (pairCost cost childCost) (fun pair => headSource pair.1 ∧ tailSource pair.2) :=
    ⟨LazyProductPrefixes.combined requested cost childCost head.cache tail.cache, correct⟩
  exact pairs.map childCost (fun pair => pair.1 :: pair.2)
    (fun first _ second _ same => Prod.ext (List.cons.inj same).1 (List.cons.inj same).2)
    (fun _ => rfl)

def childrenCache {previous : Nat} (requested : Nat)
    (childSource : Fin previous → Derivation → Prop)
    (store : ∀ index, Certified requested Derivation cost (childSource index)) :
    (children : List (Fin previous)) →
      Certified requested (List Derivation) childCost
        (fun values => List.Forall₂ childSource children values)
  | [] => (emptyChildren requested).relabel (by intro values; simp)
  | first :: rest =>
      (prepend requested (childSource first) _ (store first)
        (childrenCache requested childSource store rest)).relabel (by
          intro values
          cases values with
          | nil => simp
          | cons head tail => simp [List.forall₂_cons])

def familyCache {previous : Nat} (requested : Nat)
    (childSource : Fin previous → Derivation → Prop)
    (store : ∀ index, Certified requested Derivation cost (childSource index))
    (owner row : Nat) (family : Family previous) :
    Certified requested Derivation cost (FamilyAllows childSource owner row family) := by
  let children := childrenCache requested childSource store family.children
  let shifted : Certified requested (List Derivation)
      (fun children => family.charge + childCost children)
      (fun values => List.Forall₂ childSource family.children values) := by
    refine ⟨⟨children.cache.values, children.cache.distinct, ?_⟩, ?_⟩
    · exact children.cache.ordered.imp (fun order => Nat.add_le_add_left order _)
    · refine ⟨children.correct.distinct, children.correct.sound,
        children.cache.ordered.imp (fun order => Nat.add_le_add_left order _),
        children.correct.bounded, ?_⟩
      intro value allowed omitted
      have full := children.correct.omitted value allowed omitted
      exact ⟨full.1, fun selected member => Nat.add_le_add_left (full.2 selected member) _⟩
  exact (shifted.map cost (Derivation.node owner row family.charge)
    (fun first _ second _ same => by cases same; rfl) (fun _ => rfl)).relabel (by
      intro derivation
      simp only [FamilyAllows]
      constructor
      · rintro ⟨values, allowed, same⟩; exact ⟨values, allowed, same.symm⟩
      · rintro ⟨values, allowed, same⟩; exact ⟨values, allowed, same.symm⟩)

theorem family_row {previous : Nat} (childSource : Fin previous → Derivation → Prop)
    (owner row : Nat) (family : Family previous) (derivation : Derivation)
    (allowed : FamilyAllows childSource owner row family derivation) :
    ∃ charge children, derivation = .node owner row charge children := by
  obtain ⟨children, _, same⟩ := allowed
  exact ⟨family.charge, children, same⟩

theorem alternative_row {previous : Nat} (childSource : Fin previous → Derivation → Prop)
    (owner row : Nat) (families : List (Family previous)) (derivation : Derivation)
    (allowed : AlternativesAllow childSource owner row families derivation) :
    ∃ actual charge children, row ≤ actual ∧ derivation = .node owner actual charge children := by
  induction families generalizing row with
  | nil => exact False.elim allowed
  | cons family rest ih =>
      rcases allowed with current | later
      · obtain ⟨charge, children, same⟩ := family_row childSource owner row family derivation current
        exact ⟨row, charge, children, le_rfl, same⟩
      · obtain ⟨actual, charge, children, lower, same⟩ := ih (row + 1) later
        exact ⟨actual, charge, children, by omega, same⟩

def alternativesCache {previous : Nat} (requested : Nat)
    (childSource : Fin previous → Derivation → Prop)
    (store : ∀ index, Certified requested Derivation cost (childSource index))
    (owner : Nat) : (row : Nat) → (families : List (Family previous)) →
      Certified requested Derivation cost (AlternativesAllow childSource owner row families)
  | _, [] => emptyCache requested
  | row, family :: rest => by
      let head := familyCache requested childSource store owner row family
      let tail := alternativesCache requested childSource store owner (row + 1) rest
      let correct := LazyUnionPrefixes.selected_source_correct requested cost cost _ _
        head.cache tail.cache head.correct tail.correct
      let union : Certified requested (Derivation ⊕ Derivation)
          (LazyUnionPrefixes.sumCost cost cost)
          (LazyUnionPrefixes.sumSource (FamilyAllows childSource owner row family)
            (AlternativesAllow childSource owner (row + 1) rest)) :=
        ⟨LazyUnionPrefixes.combined requested cost cost head.cache tail.cache, correct⟩
      let reconstruct : Derivation ⊕ Derivation → Derivation := Sum.elim id id
      refine (union.map cost reconstruct ?_ ?_).relabel ?_
      · intro first allowedFirst second allowedSecond same
        cases first with
        | inl first =>
            cases second with
            | inl second => exact congrArg Sum.inl same
            | inr second =>
                obtain ⟨charge, children, firstEq⟩ :=
                  family_row childSource owner row family first allowedFirst
                obtain ⟨actual, otherCharge, otherChildren, lower, secondEq⟩ :=
                  alternative_row childSource owner (row + 1) rest second allowedSecond
                change first = second at same
                rw [firstEq, secondEq] at same
                have indexEq := (Derivation.node.inj same).2.1
                omega
        | inr first =>
            cases second with
            | inr second => exact congrArg Sum.inr same
            | inl second =>
                obtain ⟨actual, charge, children, lower, firstEq⟩ :=
                  alternative_row childSource owner (row + 1) rest first allowedFirst
                obtain ⟨otherCharge, otherChildren, secondEq⟩ :=
                  family_row childSource owner row family second allowedSecond
                change first = second at same
                rw [firstEq, secondEq] at same
                have indexEq := (Derivation.node.inj same).2.1
                omega
      · intro value; cases value <;> rfl
      · intro derivation
        constructor
        · rintro ⟨value, allowed, same⟩
          cases value with
          | inl value => exact Or.inl (same ▸ allowed)
          | inr value => exact Or.inr (same ▸ allowed)
        · intro allowed
          rcases allowed with headAllowed | tailAllowed
          · exact ⟨.inl derivation, headAllowed, rfl⟩
          · exact ⟨.inr derivation, tailAllowed, rfl⟩

/-- Materialized node caches. A child reference reads this store; it does not
recursively recompute the child solver. -/
inductive Store : {size : Nat} → Network size → Nat → Type where
  | empty (requested : Nat) : Store Network.empty requested
  | append {previous : Nat} {prior : Network previous} {families : List (Family previous)}
      {requested : Nat} (priorStore : Store prior requested)
      (current : Certified requested Derivation cost
        (AlternativesAllow (Source prior) previous 0 families)) :
      Store (.append prior families) requested

def Store.lookup : {size : Nat} → {network : Network size} → {requested : Nat} →
    Store network requested → (index : Fin size) →
      Certified requested Derivation cost (Source network index)
  | 0, .empty, _, .empty _, index => Fin.elim0 index
  | previous + 1, .append prior families, requested, .append priorStore current, index => by
      by_cases earlier : index.val < previous
      · exact (priorStore.lookup ⟨index.val, earlier⟩).relabel (by
          intro derivation; simp only [Source, dif_pos earlier])
      · exact current.relabel (by
          intro derivation; simp only [Source, dif_neg earlier])

/-- Build each node cache once in topological order. All family/child
combination steps use bounded lazy prefixes and the preceding shared store. -/
def build : {size : Nat} → (network : Network size) → (requested : Nat) → Store network requested
  | 0, .empty, requested => .empty requested
  | previous + 1, .append prior families, requested =>
      let priorStore := build prior requested
      let current := alternativesCache requested (Source prior) priorStore.lookup previous 0 families
      .append priorStore current

def solve {size : Nat} (network : Network size) (requested : Nat) (index : Fin size) :
    Certified requested Derivation cost (Source network index) :=
  (build network requested).lookup index

theorem solve_correct {size : Nat} (network : Network size) (requested : Nat) (index : Fin size) :
    Correct requested cost (Source network index) (solve network requested index).cache.values :=
  (solve network requested index).correct

namespace Controls

def first : Network 1 := .append .empty [⟨1, []⟩, ⟨2, []⟩]
def shared : Network 2 := .append first
  [⟨0, [⟨0, by decide⟩, ⟨0, by decide⟩]⟩, ⟨3, []⟩]

example : ((solve shared 4 ⟨1, by decide⟩).cache.values.map cost) = [2, 3, 3, 3] := by decide
example : (solve shared 7 ⟨1, by decide⟩).cache.values.length = 5 := by decide
example : (solve shared 0 ⟨1, by decide⟩).cache.values.length = 0 := by decide

/-- Sharing the child node does not force both derivation occurrences to
choose the same child rank. The tied mixed derivations remain distinct. -/
example : ((solve shared 7 ⟨1, by decide⟩).cache.values.filter (fun proof => cost proof == 3)).length
    = 3 := by decide

end Controls

end Mettapedia.Algorithms.SharedKBest
