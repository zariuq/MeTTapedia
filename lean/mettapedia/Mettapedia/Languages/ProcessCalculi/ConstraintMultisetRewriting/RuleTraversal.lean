import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep

/-! # Partial term interpretation across every rule position

Traversal preserves order and multiplicity in takes, reads, tells, checks
and outputs. A refused term refuses the rule; no position is discarded or
filled by a default. Total successful interpretations specialize to the
existing rule map.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

universe u v
variable {T : Type u} {U : Type v}

def Check.traverse? (read : T → Option U) : Check T → Option (Check U)
  | .equal left right => do return .equal (← read left) (← read right)
  | .absent term => Check.absent <$> read term
  | .count term number => (fun value => Check.count value number) <$> read term

def RuleInstance.traverse? (read : T → Option U) (rule : RuleInstance T) : Option (RuleInstance U) := do
  return {
    take := ← rule.take.mapM read
    read := ← rule.read.mapM read
    tell := ← rule.tell.mapM (fun pair => do return (← read pair.1, ← read pair.2))
    checks := ← rule.checks.mapM (Check.traverse? read)
    produce := ← rule.produce.mapM read }

theorem list_mapM_some (read : T → Option U) (map : T → U)
    (agrees : ∀ term, read term = some (map term)) (terms : List T) :
    terms.mapM read = some (terms.map map) := by
  induction terms with
  | nil => rfl
  | cons first rest earlier => simp [List.mapM_cons, agrees, earlier]

theorem Check.traverse?_eq_map (read : T → Option U) (map : T → U)
    (agrees : ∀ term, read term = some (map term)) (check : Check T) :
    check.traverse? read = some (check.map map) := by
  cases check <;> simp [Check.traverse?, Check.map, agrees]

theorem RuleInstance.traverse?_eq_map (read : T → Option U) (map : T → U)
    (agrees : ∀ term, read term = some (map term)) (rule : RuleInstance T) :
    rule.traverse? read = some (rule.map map) := by
  have pairs : ∀ pair : T × T,
      (do return (← read pair.1, ← read pair.2)) = some (map pair.1, map pair.2) := by
    intro pair
    simp only [agrees]
    rfl
  simp only [RuleInstance.traverse?, list_mapM_some read map agrees,
    list_mapM_some _ _ pairs,
    list_mapM_some _ _ (Check.traverse?_eq_map read map agrees)]
  rfl

theorem Check.traverse?_map (write : T → U) (read : U → Option T)
    (roundtrip : ∀ term, read (write term) = some term) (check : Check T) :
    (check.map write).traverse? read = some check := by
  cases check <;> simp [Check.map, Check.traverse?, roundtrip]

theorem RuleInstance.traverse?_map (write : T → U) (read : U → Option T)
    (roundtrip : ∀ term, read (write term) = some term) (rule : RuleInstance T) :
    (rule.map write).traverse? read = some rule := by
  have terms (values : List T) : (values.map write).mapM read = some values := by
    induction values with
    | nil => rfl
    | cons first rest earlier => simp [List.mapM_cons, roundtrip, earlier]
  have pairs (values : List (T × T)) :
      (values.map (fun pair => (write pair.1, write pair.2))).mapM
        (fun pair => do return (← read pair.1, ← read pair.2)) = some values := by
    induction values with
    | nil => rfl
    | cons first rest earlier =>
        simp only [List.map_cons, List.mapM_cons, roundtrip, earlier]
        rfl
  have checks (values : List (Check T)) :
      (values.map (Check.map write)).mapM (Check.traverse? read) = some values := by
    induction values with
    | nil => rfl
    | cons first rest earlier =>
        simp only [List.map_cons, List.mapM_cons, Check.traverse?_map write read roundtrip, earlier]
        rfl
  cases rule
  simp only [RuleInstance.map, RuleInstance.traverse?, terms, pairs, checks]
  rfl

#print axioms RuleInstance.traverse?_eq_map
#print axioms RuleInstance.traverse?_map

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
