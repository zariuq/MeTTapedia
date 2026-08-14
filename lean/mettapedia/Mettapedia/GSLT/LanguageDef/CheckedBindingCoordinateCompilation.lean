import Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation

/-!
# Checked first-binding coordinate compilation

A generated term traversal may record the first binding-table coordinate of
each finite source variable.  At execution time the coordinate is only a
hint: the table entry must still carry the expected epoch-qualified key.  A
failed check returns to authoritative suffix lookup.

The fast result is exact when the admitted binding suffix was built by fresh
insertion.  This is the same local property used by append-only rule-machine
environments; no guest-language role or constructor is mentioned here.
-/

namespace Mettapedia.GSLT.LanguageDef.CheckedBindingCoordinateCompilation

open MonotoneUniqueIndexCompilation

structure Shape (Var : Type) where
  firstOccurrences : List Var
  variableCount : Nat
  freshAppendOnly : Bool
  suffixStable : Bool
  producerIndex : Nat
  deriving Repr

structure Plan (Var : Type) where
  firstOccurrences : List Var
  producerIndex : Nat
  deriving DecidableEq, Repr

/-- Structural admission for the compact physical realization. -/
def Admitted [DecidableEq Var] (shape : Shape Var) : Prop :=
  shape.firstOccurrences.Nodup ∧
  shape.firstOccurrences.length ≤ shape.variableCount ∧
  shape.freshAppendOnly = true ∧
  shape.suffixStable = true ∧
  shape.producerIndex < 65535

instance [DecidableEq Var] (shape : Shape Var) : Decidable (Admitted shape) :=
  by
    unfold Admitted
    infer_instance

def recognize? [DecidableEq Var] (shape : Shape Var) : Option (Plan Var) :=
  if Admitted shape then
    some {
      firstOccurrences := shape.firstOccurrences
      producerIndex := shape.producerIndex
    }
  else
    none

theorem recognize?_sound [DecidableEq Var]
    {shape : Shape Var} {plan : Plan Var}
    (accepted : recognize? shape = some plan) : Admitted shape := by
  simp only [recognize?] at accepted
  split at accepted
  · assumption
  · contradiction

/-- The generated offset is the left-to-right first-occurrence coordinate in
the finite binding inventory. -/
def firstBindingOffset? [DecidableEq Var]
    (plan : Plan Var) (source : Var) : Option Nat :=
  if source ∈ plan.firstOccurrences then
    some (plan.firstOccurrences.idxOf source)
  else
    none

theorem firstBindingOffset?_sound [DecidableEq Var]
    (plan : Plan Var) (source : Var) (offset : Nat)
    (compiled : firstBindingOffset? plan source = some offset) :
    plan.firstOccurrences[offset]? = some source := by
  simp only [firstBindingOffset?] at compiled
  split at compiled
  next present =>
    simp only [Option.some.injEq] at compiled
    subst offset
    rw [List.getElem?_eq_getElem
      (List.idxOf_lt_length_of_mem present)]
    exact congrArg some
      (List.idxOf_get (List.idxOf_lt_length_of_mem present))
  next absent => contradiction

/-- Physical checked hint.  `firstEntry` is the boundary between an older
environment prefix and the fresh activation suffix. -/
def checkedCoordinateLookup [BEq Key]
    (entries : List (Key × Value)) (firstEntry offset : Nat) (query : Key) :
    Option Value :=
  let suffix := entries.drop firstEntry
  match suffix[offset]? with
  | some (key, value) =>
      if key == query then some value else sourceLookup query suffix
  | none => sourceLookup query suffix

private theorem sourceLookup_eq_some_of_getElem?_nodup
    [BEq Key] [LawfulBEq Key]
    (entries : List (Key × Value)) (query : Key) (value : Value)
    (offset : Nat) (distinct : (entries.map Prod.fst).Nodup)
    (entryAt : entries[offset]? = some (query, value)) :
    sourceLookup query entries = some value := by
  induction entries generalizing offset with
  | nil => simp at entryAt
  | cons entry entries inductionHypothesis =>
      rcases entry with ⟨headKey, headValue⟩
      obtain ⟨headAbsent, tailDistinct⟩ := List.nodup_cons.mp distinct
      cases offset with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq,
            Prod.mk.injEq] at entryAt
          obtain ⟨rfl, rfl⟩ := entryAt
          simp [sourceLookup]
      | succ offset =>
          simp only [List.getElem?_cons_succ] at entryAt
          have queryPresent : query ∈ entries.map Prod.fst := by
            have pairPresent : (query, value) ∈ entries :=
              List.mem_of_getElem? entryAt
            exact List.mem_map.mpr ⟨(query, value), pairPresent, rfl⟩
          have headNe : headKey ≠ query := by
            intro equal
            subst query
            exact headAbsent queryPresent
          simp [sourceLookup, headNe,
            inductionHypothesis offset tailDistinct entryAt]

/-- A checked coordinate is observationally identical to authoritative suffix
lookup for every fresh-insertion suffix.  A stale coordinate takes the source
lookup branch; an exact coordinate is unique by `Nodup`. -/
theorem checkedCoordinateLookup_eq_sourceLookup
    [BEq Key] [LawfulBEq Key]
    (entries : List (Key × Value)) (firstEntry offset : Nat) (query : Key)
    (freshSuffix : ((entries.drop firstEntry).map Prod.fst).Nodup) :
    checkedCoordinateLookup entries firstEntry offset query =
      sourceLookup query (entries.drop firstEntry) := by
  simp only [checkedCoordinateLookup]
  cases entryAt : (entries.drop firstEntry)[offset]? with
  | none => rfl
  | some entry =>
      rcases entry with ⟨key, value⟩
      by_cases same : key = query
      · subst key
        simp only [beq_self_eq_true, ↓reduceIte]
        exact (sourceLookup_eq_some_of_getElem?_nodup
          (entries.drop firstEntry) query value offset freshSuffix entryAt).symm
      · simp [same]

/-! ## Honest cost boundary -/

def coordinateHitCost : Nat := 1

def coordinateFallbackCost (sourceCost : Nat) : Nat := 1 + sourceCost

theorem coordinate_hit_strictly_cheaper (sourceCost : Nat)
    (nontrivial : 1 < sourceCost) : coordinateHitCost < sourceCost := by
  exact nontrivial

theorem coordinate_fallback_pays_validation (sourceCost : Nat) :
    sourceCost < coordinateFallbackCost sourceCost := by
  simp [coordinateFallbackCost]

/-! ## Independent witnesses and rejecting mutations -/

private def parserShape : Shape Nat := {
  firstOccurrences := [3, 5]
  variableCount := 2
  freshAppendOnly := true
  suffixStable := true
  producerIndex := 12
}

private def proofRuleShape : Shape Nat := {
  firstOccurrences := [7, 11, 13]
  variableCount := 3
  freshAppendOnly := true
  suffixStable := true
  producerIndex := 29
}

private def parserPlan : Plan Nat := {
  firstOccurrences := [3, 5]
  producerIndex := 12
}

example : (recognize? parserShape).isSome = true := by decide

example : (recognize? proofRuleShape).isSome = true := by decide

example : recognize? parserShape = some parserPlan := by decide

example : firstBindingOffset? parserPlan 5 = some 1 := by decide

/-- A nonlinear term still has one first binding coordinate per variable. -/
private def nonlinearPlan : Plan Nat := {
  firstOccurrences := [3, 5]
  producerIndex := 12
}

example : firstBindingOffset? nonlinearPlan 3 = some 0 := by decide

example : firstBindingOffset? nonlinearPlan 8 = none := by decide

/-- Overwrite destroys the fresh-suffix invariant and is rejected. -/
example :
    (recognize? { parserShape with freshAppendOnly := false }).isSome = false := by
  decide

/-- A producer coordinate that cannot be represented by the compact carrier
is rejected rather than truncated. -/
example :
    (recognize? { proofRuleShape with producerIndex := 65535 }).isSome = false := by
  decide

/-- A stale physical offset falls back to authoritative lookup. -/
example :
    checkedCoordinateLookup [(3, "parser"), (5, "proof")] 0 1 3 =
      some "parser" := by decide

end Mettapedia.GSLT.LanguageDef.CheckedBindingCoordinateCompilation
