import Mettapedia.Logic.BinEvNat

/-!
# Maple Court Coalition Demo: Elevator Maintenance Quorum

Three apartments vote on elevator maintenance. A quorum of 2 is
required before the building's elevator-health evidence state can
be revised. This is a semitopology: unions of actionable coalitions
are actionable, but intersections are NOT.

All proofs by `decide`.

Reference: wm-pln-book_v3.tex, §3.3 (Non-Additive Perimeter),
Maple Court box: "The building requires a majority of apartments
to agree before updating the elevator-health assessment."

0 sorry.
-/

namespace Mettapedia.Logic.PLNMapleCourtCoalitionDemo

open Mettapedia.Logic

/-! ## §1: Three apartments, quorum = 2

Apartments: A (Fin 3 = 0), B (1), C (2)
A coalition is actionable if it has ≥ 2 members. -/

def quorum : Nat := 2

-- Represent coalitions as lists of apartment IDs
def coalAB : List (Fin 3) := [0, 1]
def coalAC : List (Fin 3) := [0, 2]
def coalA  : List (Fin 3) := [0]
def coalABC : List (Fin 3) := [0, 1, 2]

def isActionable (coal : List (Fin 3)) : Bool := coal.length ≥ quorum

/-! ## §2: Quorum checks -/

theorem quorum_AB_actionable : isActionable coalAB = true := by decide
theorem quorum_AC_actionable : isActionable coalAC = true := by decide
theorem quorum_ABC_actionable : isActionable coalABC = true := by decide

-- A single apartment CANNOT force revision
theorem singleton_A_not_actionable : isActionable coalA = false := by decide

/-! ## §3: Semitopology: unions closed, intersections NOT

The intersection of {A,B} and {A,C} is {A} — a singleton,
which does NOT pass quorum. This is why it's a semitopology
(weaker than a topology). -/

-- Intersection: elements in both coalitions
def intersect (c1 c2 : List (Fin 3)) : List (Fin 3) :=
  c1.filter (fun x => c2.contains x)

theorem intersection_is_singleton :
    intersect coalAB coalAC = [0] := by decide

theorem intersection_not_actionable :
    isActionable (intersect coalAB coalAC) = false := by decide

-- Union: elements in either coalition (deduplicated)
def union (c1 c2 : List (Fin 3)) : List (Fin 3) :=
  (c1 ++ c2.filter (fun x => !c1.contains x))

theorem union_is_ABC :
    union coalAB coalAC = [0, 1, 2] := by decide

theorem union_actionable :
    isActionable (union coalAB coalAC) = true := by decide

/-! ## §4: Evidence revision under quorum

Each apartment submits evidence about elevator health.
Only coalitions that pass quorum can revise the building state. -/

def evidenceA : BinEvNat := ⟨2, 0⟩  -- A says: elevator is healthy
def evidenceB : BinEvNat := ⟨1, 1⟩  -- B says: mixed
def evidenceC : BinEvNat := ⟨0, 3⟩  -- C says: elevator needs repair

-- If A and B form a coalition (quorum met): combined evidence
def coalAB_evidence : BinEvNat := evidenceA + evidenceB

theorem coalAB_evidence_value : coalAB_evidence = ⟨3, 1⟩ := by decide

-- If A and C form a coalition: very different conclusion
def coalAC_evidence : BinEvNat := evidenceA + evidenceC

theorem coalAC_evidence_value : coalAC_evidence = ⟨2, 3⟩ := by decide

-- Coalition choice changes the conclusion:
-- AB says healthy (3:1), AC says needs repair (2:3)
theorem coalition_choice_matters :
    coalAB_evidence.pos > coalAB_evidence.neg ∧
    coalAC_evidence.neg > coalAC_evidence.pos := by decide

/-! ## §5: A alone cannot revise (quorum not met) -/

-- Even though A has strong evidence ⟨2, 0⟩, it cannot
-- unilaterally update the building state
theorem A_blocked : isActionable coalA = false := by decide

/-! ## §6: End-to-end summary -/

theorem end_to_end :
    -- AB and AC pass quorum
    isActionable coalAB = true ∧
    isActionable coalAC = true ∧
    -- A alone does not
    isActionable coalA = false ∧
    -- Intersection is not actionable (semitopology, not topology)
    isActionable (intersect coalAB coalAC) = false ∧
    -- Union is actionable (closed under unions)
    isActionable (union coalAB coalAC) = true ∧
    -- Different coalitions yield different conclusions
    coalAB_evidence.pos > coalAB_evidence.neg ∧
    coalAC_evidence.neg > coalAC_evidence.pos := by decide

end Mettapedia.Logic.PLNMapleCourtCoalitionDemo
