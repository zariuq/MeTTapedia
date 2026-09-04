import Mettapedia.Logic.FinitaryRuleSystem.Tree

/-!
# Bounded no-bottom receipts for finite replay trees

A bounded receipt consists of a finite candidate list together with proofs that
every listed tree is within the bound and every tree within the bound occurs in
the list.  Exhaustive Boolean replay over that exact enumeration decides the
corresponding bounded no-bottom claim.  No unbounded consistency claim is
inferred.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem

open Mettapedia.Logic

universe u v

/-- No accepted certificate of at most `bound` nodes concludes `bottom`. -/
def BoundedNoBottom {J : Type u} {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) (bottom : J) (bound : Nat) : Prop :=
  ∀ certificate : Derivation J interface.W,
    certificate.nodeCount ≤ bound →
    certificate.valid interface = true →
    certificate.concl ≠ bottom

/-- An exact finite enumeration of all certificate trees within one node
bound.  `within` prevents irrelevant larger candidates from strengthening the
Boolean test, while `covers` prevents omitted candidates from weakening it. -/
structure ExactBoundedEnumeration (J : Type u) (W : Type v)
    (bound : Nat) where
  candidates : List (Derivation J W)
  within : ∀ certificate, certificate ∈ candidates →
    certificate.nodeCount ≤ bound
  covers : ∀ certificate, certificate.nodeCount ≤ bound →
    certificate ∈ candidates

/-- Exhaustively reject every enumerated certificate that both replays and
concludes bottom. -/
def checkNoBottom {J : Type u} [DecidableEq J]
    {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (bottom : J) {bound : Nat}
    (enumeration : ExactBoundedEnumeration J interface.W bound) : Bool :=
  enumeration.candidates.all fun certificate =>
    !(certificate.valid interface && decide (certificate.concl = bottom))

/-- Exact enumeration makes the executable receipt equivalent to its bounded
logical claim. -/
theorem checkNoBottom_eq_true_iff {J : Type u} [DecidableEq J]
    {rules : List J → J → Prop} (interface : RuleWitness.{u, v} rules)
    (bottom : J) {bound : Nat}
    (enumeration : ExactBoundedEnumeration J interface.W bound) :
    checkNoBottom interface bottom enumeration = true ↔
      BoundedNoBottom interface bottom bound := by
  constructor
  · intro checked certificate size accepted concludesBottom
    have member := enumeration.covers certificate size
    have rejected := (List.all_eq_true.mp checked) certificate member
    simp [accepted, concludesBottom] at rejected
  · intro bounded
    apply List.all_eq_true.mpr
    intro certificate member
    cases acceptedBottom :
        (certificate.valid interface &&
          decide (certificate.concl = bottom)) with
    | false => rfl
    | true =>
        exfalso
        rw [Bool.and_eq_true] at acceptedBottom
        exact bounded certificate (enumeration.within certificate member)
          acceptedBottom.1 (of_decide_eq_true acceptedBottom.2)

namespace Canary

inductive Witness where
  | trueAxiom
  | trueToFalse
deriving DecidableEq

/-- A two-rule calculus whose first bottom proof has two nodes. -/
inductive Rules : List Bool → Bool → Prop where
  | trueAxiom : Rules [] true
  | trueToFalse : Rules [true] false

def isInstance (witness : Witness) (premises : List Bool)
    (conclusion : Bool) : Bool :=
  match witness with
  | .trueAxiom => decide (premises = [] ∧ conclusion = true)
  | .trueToFalse => decide (premises = [true] ∧ conclusion = false)

def interface : RuleWitness Rules where
  W := Witness
  isInstance := isInstance
  sound witness premises conclusion accepted := by
    cases witness with
    | trueAxiom =>
        simp only [isInstance, decide_eq_true_eq] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact Rules.trueAxiom
    | trueToFalse =>
        simp only [isInstance, decide_eq_true_eq] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact Rules.trueToFalse
  complete premises conclusion rule := by
    cases rule with
    | trueAxiom => exact ⟨.trueAxiom, by decide⟩
    | trueToFalse => exact ⟨.trueToFalse, by decide⟩

def leaf (conclusion : Bool) (witness : Witness) :
    Derivation Bool Witness :=
  .node conclusion witness 0 (fun i => Fin.elim0 i)

def oneNodeCandidates : List (Derivation Bool Witness) :=
  [ leaf false .trueAxiom
  , leaf false .trueToFalse
  , leaf true .trueAxiom
  , leaf true .trueToFalse ]

theorem oneNodeCandidates_within (certificate : Derivation Bool Witness)
    (member : certificate ∈ oneNodeCandidates) :
    certificate.nodeCount ≤ 1 := by
  simp only [oneNodeCandidates, List.mem_cons] at member
  simp only [List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem oneNodeCandidates_cover (certificate : Derivation Bool Witness)
    (size : certificate.nodeCount ≤ 1) :
    certificate ∈ oneNodeCandidates := by
  cases certificate with
  | node conclusion witness n children =>
      cases n with
      | zero =>
          have childrenEqual : children = fun i : Fin 0 => Fin.elim0 i := by
            funext i
            exact Fin.elim0 i
          subst children
          cases conclusion <;> cases witness <;>
            simp [oneNodeCandidates, leaf]
      | succ n =>
          have childPositive := Derivation.nodeCount_pos (children 0)
          have childBelowSum :
              (children 0).nodeCount ≤
                ∑ i : Fin (n + 1), (children i).nodeCount := by
            exact Finset.single_le_sum
              (fun i _member => Nat.zero_le (children i).nodeCount)
              (Finset.mem_univ (0 : Fin (n + 1)))
          simp only [Derivation.nodeCount_node] at size
          omega

def oneNodeEnumeration : ExactBoundedEnumeration Bool Witness 1 where
  candidates := oneNodeCandidates
  within := oneNodeCandidates_within
  covers := oneNodeCandidates_cover

theorem oneNode_check_succeeds :
    checkNoBottom interface false oneNodeEnumeration = true := by
  rfl

/-- Positive bounded receipt: no one-node proof concludes false. -/
theorem boundedNoBottom_one : BoundedNoBottom interface false 1 :=
  (checkNoBottom_eq_true_iff interface false oneNodeEnumeration).mp
    oneNode_check_succeeds

def twoNodeBottomCertificate : Derivation Bool interface.W :=
  .node false .trueToFalse 1 (fun _ => leaf true .trueAxiom)

theorem twoNodeBottomCertificate_size :
    twoNodeBottomCertificate.nodeCount = 2 := rfl

theorem twoNodeBottomCertificate_valid :
    twoNodeBottomCertificate.valid interface = true := rfl

/-- Negative boundary: the next certificate size contains a real bottom proof,
so the size-one receipt is not global consistency. -/
theorem not_boundedNoBottom_two :
    ¬ BoundedNoBottom interface false 2 := by
  intro bounded
  exact bounded twoNodeBottomCertificate
    (by change 2 ≤ 2; omega)
    twoNodeBottomCertificate_valid rfl

end Canary

end Mettapedia.Logic.FinitaryRuleSystem
