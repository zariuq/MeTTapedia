import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mettapedia.Logic.PLNMarkovLogicFiniteRestriction

/-!
# Clause-Level MLN Semantics

This module adds an actual grounded-clause layer to the infinite-first MLN story.

- worlds are Boolean valuations of atoms,
- grounded clauses are finite disjunctions of literals,
- weighted grounded clauses induce clause potentials,
- finite clause supports induce exact world weights,
- finite atom types recover the existing countable/WM bridge as a specialization.

The goal is to fix the semantic scope gap in the earlier abstract `worldWeight`
layer without giving up the already-proved infinite-first architecture.
-/

namespace Mettapedia.Logic.PLNMarkovLogicClauseSemantics

open scoped ENNReal BigOperators
open Mettapedia.Logic.PLNMarkovLogicAbstract
open Mettapedia.Logic.PLNMarkovLogicCountable
open Mettapedia.Logic.PLNMarkovLogicFiniteRestriction

/-- A Boolean valuation of ground atoms. -/
abbrev AtomValuation (Atom : Type*) := Atom → Bool

/-- Ground literals over atoms. -/
inductive Literal (Atom : Type*) where
  | pos : Atom → Literal Atom
  | neg : Atom → Literal Atom
deriving DecidableEq

namespace Literal

/-- The atom mentioned by a literal. -/
def atom : Literal Atom → Atom
  | pos a => a
  | neg a => a

/-- Satisfaction of a literal in a Boolean valuation. -/
def holds (W : AtomValuation Atom) : Literal Atom → Prop
  | pos a => W a = true
  | neg a => W a = false

@[simp] theorem holds_pos (W : AtomValuation Atom) (a : Atom) :
    holds W (.pos a) ↔ W a = true := Iff.rfl

@[simp] theorem holds_neg (W : AtomValuation Atom) (a : Atom) :
    holds W (.neg a) ↔ W a = false := Iff.rfl

end Literal

/-- A grounded clause is a finite disjunction of literals. -/
abbrev GroundClause (Atom : Type*) := Finset (Literal Atom)

namespace GroundClause

variable {Atom : Type*} [DecidableEq Atom]

/-- A clause holds when one of its literals holds. -/
def holds (C : GroundClause Atom) (W : AtomValuation Atom) : Prop :=
  ∃ l, l ∈ C ∧ Literal.holds W l

noncomputable instance holdsDecidable (C : GroundClause Atom) (W : AtomValuation Atom) :
    Decidable (C.holds W) := by
  classical
  unfold holds
  infer_instance

/-- The set of atoms mentioned by a clause. -/
def atoms (C : GroundClause Atom) : Finset Atom :=
  C.image Literal.atom

theorem atom_mem_atoms {C : GroundClause Atom} {l : Literal Atom} (hl : l ∈ C) :
    l.atom ∈ C.atoms := by
  exact Finset.mem_image.mpr ⟨l, hl, rfl⟩

/-- Scoped clause satisfaction uses only the atoms mentioned by the clause. -/
def scopedHolds (C : GroundClause Atom) (W : ∀ a ∈ C.atoms, Bool) : Prop :=
  ∃ l, ∃ hl : l ∈ C,
    match l with
    | .pos a => W a (atom_mem_atoms hl) = true
    | .neg a => W a (atom_mem_atoms hl) = false

noncomputable instance scopedHoldsDecidable (C : GroundClause Atom) (W : ∀ a ∈ C.atoms, Bool) :
    Decidable (C.scopedHolds W) := by
  classical
  unfold scopedHolds
  infer_instance

theorem scopedHolds_iff_holds (C : GroundClause Atom) (W : AtomValuation Atom) :
    C.scopedHolds (fun a _ => W a) ↔ C.holds W := by
  constructor
  · intro h
    rcases h with ⟨l, hl, hval⟩
    refine ⟨l, hl, ?_⟩
    cases l <;> simpa [Literal.holds] using hval
  · intro h
    rcases h with ⟨l, hl, hval⟩
    refine ⟨l, hl, ?_⟩
    cases l <;> simpa [Literal.holds] using hval

end GroundClause

/-- A grounded weighted clause with explicit satisfied/unsatisfied potentials. -/
structure WeightedGroundClause (Atom : Type*) where
  clause : GroundClause Atom
  satisfiedPotential : ENNReal
  unsatisfiedPotential : ENNReal
  satisfied_ne_top : satisfiedPotential ≠ ⊤
  unsatisfied_ne_top : unsatisfiedPotential ≠ ⊤

namespace WeightedGroundClause

variable {Atom : Type*} [DecidableEq Atom]

/-- Clause potential under a full Boolean valuation. -/
noncomputable def eval (wc : WeightedGroundClause Atom) (W : AtomValuation Atom) : ENNReal :=
  by
    classical
    exact if wc.clause.holds W then wc.satisfiedPotential else wc.unsatisfiedPotential

omit [DecidableEq Atom] in
theorem eval_ne_top (wc : WeightedGroundClause Atom) (W : AtomValuation Atom) :
    wc.eval W ≠ ⊤ := by
  classical
  unfold eval
  split_ifs with h
  · exact wc.satisfied_ne_top
  · exact wc.unsatisfied_ne_top

/-- Clause potential computed from a valuation restricted to the clause scope. -/
noncomputable def evalOnScope
    (wc : WeightedGroundClause Atom)
    (W : ∀ a ∈ wc.clause.atoms, Bool) : ENNReal :=
  by
    classical
    exact if wc.clause.scopedHolds W then wc.satisfiedPotential else wc.unsatisfiedPotential

theorem evalOnScope_eq_eval (wc : WeightedGroundClause Atom) (W : AtomValuation Atom) :
    wc.evalOnScope (fun a _ => W a) = wc.eval W := by
  classical
  by_cases hs : wc.clause.scopedHolds (fun a _ => W a)
  · have h : wc.clause.holds W := (wc.clause.scopedHolds_iff_holds W).1 hs
    simp [evalOnScope, eval, hs, h]
  · have h : ¬ wc.clause.holds W := by
      intro hh
      exact hs ((wc.clause.scopedHolds_iff_holds W).2 hh)
    simp [evalOnScope, eval, hs, h]

end WeightedGroundClause

/-- A grounded MLN is a family of weighted grounded clauses. -/
structure GroundMLN (Atom ClauseId : Type*) where
  clauseData : ClauseId → WeightedGroundClause Atom

namespace GroundMLN

variable {Atom ClauseId Query : Type*} [DecidableEq Atom]

noncomputable instance atomEncodable [Fintype Atom] : Encodable Atom :=
  Fintype.toEncodable Atom

noncomputable instance atomValuationEncodable [Fintype Atom] :
    Encodable (AtomValuation Atom) := by
  infer_instance

/-- Active clause ids for a finite-support MLN view. -/
abbrev ActiveClause (support : Finset ClauseId) := support.attach

/-- Exact world weight induced by a finite active clause support. -/
noncomputable def worldWeight
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) (W : AtomValuation Atom) : ENNReal :=
  ∏ i : support.attach, (M.clauseData i.1).eval W

omit [DecidableEq Atom] in
theorem worldWeight_ne_top
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId) (W : AtomValuation Atom) :
    M.worldWeight support W ≠ ⊤ := by
  classical
  unfold worldWeight
  exact ENNReal.prod_ne_top (by
    intro i hi
    exact WeightedGroundClause.eval_ne_top (M.clauseData i.1) W)

/-- Clause-level MLN semantics induces an abstract MLN semantics object. -/
noncomputable def toAbstractMLNSemantics
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId)
    (queryHolds : Query → AtomValuation Atom → Prop) :
    AbstractMLNSemantics (AtomValuation Atom) Query (ActiveClause support) where
  worldWeight := M.worldWeight support
  queryHolds := queryHolds
  featurePotential := fun i W => (M.clauseData i.1).eval W

omit [DecidableEq Atom] in
theorem worldWeight_eq_featureProduct
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId)
    (queryHolds : Query → AtomValuation Atom → Prop)
    (W : AtomValuation Atom) :
    (M.toAbstractMLNSemantics (Query := Query) support queryHolds).worldWeight W =
      ∏ i : ActiveClause support,
        (M.toAbstractMLNSemantics (Query := Query) support queryHolds).featurePotential i W := by
  rfl

/-- Finite atom types recover the existing countable-MLN interface exactly. -/
noncomputable def toCountableMLNSemantics
    [Fintype Atom]
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId)
    (queryHolds : Query → AtomValuation Atom → Prop) :
    CountableMLNSemantics (AtomValuation Atom) Query (ActiveClause support) where
  worldWeight := M.worldWeight support
  queryHolds := queryHolds
  featurePotential := fun i W => (M.clauseData i.1).eval W
  totalMass_ne_top := by
    classical
    rw [tsum_eq_sum (s := (Finset.univ : Finset (AtomValuation Atom)))
      (fun x hx => (hx (Finset.mem_univ x)).elim)]
    exact (ENNReal.sum_ne_top).2 (by
      intro W hW
      exact M.worldWeight_ne_top support W)

/-- Because the finite-atom world space is finite, `univ` is an exact support witness. -/
theorem finiteSupportWitness_univ
    [Fintype Atom]
    (M : GroundMLN Atom ClauseId)
    (support : Finset ClauseId)
    (queryHolds : Query → AtomValuation Atom → Prop) :
    FiniteSupportWitness
      (M.toCountableMLNSemantics (Query := Query) support queryHolds)
      (Finset.univ : Finset (AtomValuation Atom)) := by
  refine ⟨?_⟩
  intro W hW
  exact False.elim (hW (Finset.mem_univ W))

end GroundMLN

/-- Classical MLN clause from a real log-weight. False clauses contribute factor `1`. -/
noncomputable def classicalWeightedClause
    {Atom : Type*} (clause : GroundClause Atom) (logWeight : ℝ) :
    WeightedGroundClause Atom where
  clause := clause
  satisfiedPotential := ENNReal.ofReal (Real.exp logWeight)
  unsatisfiedPotential := 1
  satisfied_ne_top := ENNReal.ofReal_ne_top
  unsatisfied_ne_top := by simp

/-- Classical grounded MLN presentation: clauses plus real log-weights. -/
structure ClassicalGroundMLN (Atom ClauseId : Type*) where
  clause : ClauseId → GroundClause Atom
  logWeight : ClauseId → ℝ

namespace ClassicalGroundMLN

variable {Atom ClauseId : Type*} [DecidableEq Atom]

/-- Forgetting only the Gibbs/log-weight view yields the positive-potential ground MLN. -/
noncomputable def toGroundMLN
    (M : ClassicalGroundMLN Atom ClauseId) : GroundMLN Atom ClauseId where
  clauseData i := classicalWeightedClause (M.clause i) (M.logWeight i)

omit [DecidableEq Atom] in
theorem eval_toGroundMLN_eq_logWeightPotential
    (M : ClassicalGroundMLN Atom ClauseId)
    (i : ClauseId) (W : AtomValuation Atom) :
    (M.toGroundMLN.clauseData i).eval W =
      logWeightPotential (M.logWeight i) ((M.clause i).holds W) := by
  unfold toGroundMLN classicalWeightedClause WeightedGroundClause.eval logWeightPotential
  by_cases h : (M.clause i).holds W <;> simp [h]

omit [DecidableEq Atom] in
theorem worldWeight_eq_gibbsProduct
    (M : ClassicalGroundMLN Atom ClauseId)
    (support : Finset ClauseId) (W : AtomValuation Atom) :
    (M.toGroundMLN.worldWeight support W) =
      ∏ i : support.attach, logWeightPotential (M.logWeight i.1) ((M.clause i.1).holds W) := by
  classical
  unfold GroundMLN.worldWeight
  simp [eval_toGroundMLN_eq_logWeightPotential]

end ClassicalGroundMLN

end Mettapedia.Logic.PLNMarkovLogicClauseSemantics
