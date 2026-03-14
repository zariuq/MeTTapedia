import Mettapedia.Logic.PLNMarkovLogicClauseWorldModel
import Mettapedia.Logic.PLNMarkovLogicGrounding

/-!
# Social Smoking MLN Canary

The classic Alchemy social-smoking tutorial, formalized as a ground MLN.

## Setup

After evidence absorption (Friends(alice,bob)=T, Smokes(alice)=T), the ground
clauses over 4 atoms {S(a), S(b), C(a), C(b)} are:

1. ¬Smokes(alice) ∨ Cancer(alice) — hard (sat=1, unsat=0)
2. ¬Smokes(bob) ∨ Cancer(bob)     — hard (sat=1, unsat=0)
3. ¬Smokes(alice) ∨ Smokes(bob)   — soft (sat=3, unsat=1)
4. Smokes(alice)                   — hard evidence (sat=1, unsat=0)

Clause 3 arises from grounding `Friends(x,y) ∧ Smokes(x) → Smokes(y)` with
evidence `Friends(alice,bob) = true`.  The soft weight (3:1) encodes
`exp(w) ≈ 3` for the friendship-influence rule.

## Results

- Z = 5
- P(Smokes(bob)) = 3/5
- P(Cancer(bob)) = 4/5

## First-order template demonstration

The `friendsInfluenceABTemplate` and `evidenceSmokesATemplate` below show how
`Term.const` encodes evidence-absorbed atoms within the first-order framework.
The canary proof uses a direct ground MLN for computational tractability; the
first-order templates serve as documentation of the full pipeline.
-/

namespace Mettapedia.Logic.PLNMarkovLogicSocialSmoking

open scoped ENNReal BigOperators
open Mettapedia.Logic.PLNMarkovLogicAbstract
open Mettapedia.Logic.PLNMarkovLogicCountable
open Mettapedia.Logic.PLNMarkovLogicClauseSemantics
open Mettapedia.Logic.PLNMarkovLogicClauseFactorGraph
open Mettapedia.Logic.PLNMarkovLogicClauseWorldModel
open Mettapedia.Logic.PLNMarkovLogicGrounding

/-! ## First-Order Templates (demonstrating Term.const) -/

section Templates

/-- Evidence-absorbed friend-influence: `¬Smokes(alice) ∨ Smokes(bob)`.
Both arguments use `Term.const`, so the clause is substitution-invariant. -/
def friendsInfluenceABTemplate : WeightedClauseTemplate SmokePred X Person where
  clause := [
    .neg ⟨1, .smokes, fun _ => .const .alice⟩,
    .pos ⟨1, .smokes, fun _ => .const .bob⟩
  ]
  satisfiedPotential := 3
  unsatisfiedPotential := 1
  satisfied_ne_top := by norm_num
  unsatisfied_ne_top := by norm_num

/-- Evidence atom: `Smokes(alice)`, all terms constant. -/
def evidenceSmokesATemplate : WeightedClauseTemplate SmokePred X Person where
  clause := [
    .pos ⟨1, .smokes, fun _ => .const .alice⟩
  ]
  satisfiedPotential := 1
  unsatisfiedPotential := 0
  satisfied_ne_top := by norm_num
  unsatisfied_ne_top := by norm_num

/-- The grounding of a `Term.const` is substitution-invariant. -/
theorem groundTerm_const_inv (d : Person) (θ₁ θ₂ : Subst X Person) :
    groundTerm θ₁ (.const d : Term X Person) = groundTerm θ₂ (.const d) := by
  simp [groundTerm]

end Templates

/-! ## Ground MLN (evidence-absorbed) -/

section SocialSmoking

open Mettapedia.Logic.PLNWorldModel

/-- Clause identifiers for the social-smoking ground MLN. -/
inductive SocialClauseId where
  | smokesCancerAlice
  | smokesCancerBob
  | friendsInfluenceAB
  | evidenceSmokesA
deriving DecidableEq, Fintype

/-! ### Named ground atoms -/

private def sAlice : GroundAtom SmokePred Person := ⟨1, .smokes, fun _ => .alice⟩
private def sBob   : GroundAtom SmokePred Person := ⟨1, .smokes, fun _ => .bob⟩
private def cAlice : GroundAtom SmokePred Person := ⟨1, .cancer, fun _ => .alice⟩
private def cBob   : GroundAtom SmokePred Person := ⟨1, .cancer, fun _ => .bob⟩

/-! ### Fintype instance for ground atoms -/

private instance : Fintype (SmokePred 1) :=
  ⟨{.smokes, .cancer}, fun p => by cases p <;> simp⟩

private def smokePredArityOne' : SmokePred n → n = 1
  | .smokes => rfl
  | .cancer => rfl

private noncomputable def socialGroundAtomEquiv :
    GroundAtom SmokePred Person ≃ SmokePred 1 × Person where
  toFun a :=
    let hn := smokePredArityOne' a.pred
    ⟨hn ▸ a.pred, a.args ⟨0, by omega⟩⟩
  invFun p := ⟨1, p.1, fun _ => p.2⟩
  left_inv a := by
    obtain ⟨n, pred, args⟩ := a
    have hn : n = 1 := smokePredArityOne' pred
    subst hn
    simp only [GroundAtom.mk.injEq, heq_eq_eq, true_and]
    funext i; fin_cases i; rfl
  right_inv p := by simp

private noncomputable instance : Fintype (GroundAtom SmokePred Person) :=
  Fintype.ofEquiv (SmokePred 1 × Person) socialGroundAtomEquiv.symm

/-! ### The ground MLN -/

/-- The social-smoking ground MLN: 4 clauses after evidence absorption. -/
noncomputable def socialGroundMLN :
    GroundMLN (GroundAtom SmokePred Person) SocialClauseId where
  clauseData
  | .smokesCancerAlice => {
      clause := {.neg sAlice, .pos cAlice}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num
    }
  | .smokesCancerBob => {
      clause := {.neg sBob, .pos cBob}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num
    }
  | .friendsInfluenceAB => {
      clause := {.neg sAlice, .pos sBob}
      satisfiedPotential := 3
      unsatisfiedPotential := 1
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num
    }
  | .evidenceSmokesA => {
      clause := {.pos sAlice}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num
    }

/-- Full clause support. -/
noncomputable def socialFullSupport : Finset SocialClauseId := Finset.univ

/-! ### Queries -/

/-- Query: Smokes(bob) = true. -/
def smokesBobQuery : ConstraintQuery (GroundAtom SmokePred Person) :=
  [⟨sBob, true⟩]

/-- Query: Cancer(bob) = true. -/
def cancerBobQuery : ConstraintQuery (GroundAtom SmokePred Person) :=
  [⟨cBob, true⟩]

/-! ### Valuation equivalence -/

/-- Reindex valuations as (sa, ca, sb, cb). -/
private noncomputable def socialValEquiv :
    (GroundAtom SmokePred Person → Bool) ≃ Bool × Bool × Bool × Bool where
  toFun W := (W sAlice, W cAlice, W sBob, W cBob)
  invFun b a :=
    match socialGroundAtomEquiv a with
    | (.smokes, .alice) => b.1
    | (.cancer, .alice) => b.2.1
    | (.smokes, .bob)   => b.2.2.1
    | (.cancer, .bob)   => b.2.2.2
  left_inv W := by
    funext a
    rw [show a = socialGroundAtomEquiv.symm (socialGroundAtomEquiv a) from
        (socialGroundAtomEquiv.symm_apply_apply a).symm]
    rcases socialGroundAtomEquiv a with ⟨_ | _, _ | _⟩ <;> rfl
  right_inv b := rfl

/-! ### Support enumeration -/

theorem socialFullSupport_eq :
    socialFullSupport =
      ({.smokesCancerAlice, .smokesCancerBob, .friendsInfluenceAB, .evidenceSmokesA} :
        Finset SocialClauseId) := by
  ext x; simp [socialFullSupport]; cases x <;> simp

/-! ### World-weight factorization -/

set_option maxHeartbeats 400000 in
/-- The world weight for the full support decomposes into 4 clause factors. -/
theorem social_worldWeight_fullSupport_eq
    (W : AtomValuation (GroundAtom SmokePred Person)) :
    socialGroundMLN.worldWeight socialFullSupport W =
      (if W sAlice = true ∧ W cAlice = false then 0 else 1) *
      (if W sBob   = true ∧ W cBob   = false then 0 else 1) *
      (if W sAlice = true ∧ W sBob   = false then 1 else 3) *
      (if W sAlice = false then 0 else 1) := by
  classical
  unfold GroundMLN.worldWeight
  rw [socialFullSupport_eq]
  -- Convert Fintype product to Finset product
  let s : Finset SocialClauseId :=
    {.smokesCancerAlice, .smokesCancerBob, .friendsInfluenceAB, .evidenceSmokesA}
  have hsort :
      (∏ i : s.attach,
          (socialGroundMLN.clauseData i.1).eval W) =
        ∏ i ∈ s.attach, (socialGroundMLN.clauseData i.1).eval W := by
    simpa [s] using
      (Finset.prod_coe_sort s.attach
        (fun i => (socialGroundMLN.clauseData i.1).eval W))
  rw [hsort]
  have hattach :
      (∏ i ∈ s.attach, (socialGroundMLN.clauseData i.1).eval W) =
        ∏ i ∈ s, (socialGroundMLN.clauseData i).eval W := by
    simpa [s] using
      (Finset.prod_attach (s := s)
        (f := fun i => (socialGroundMLN.clauseData i).eval W))
  rw [hattach]
  rw [show s = ({.smokesCancerAlice, .smokesCancerBob, .friendsInfluenceAB, .evidenceSmokesA} :
      Finset SocialClauseId) from rfl]
  rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]
  -- Helpers: extract eval when clause holds or doesn't hold
  have eval_sat : ∀ (wc : WeightedGroundClause (GroundAtom SmokePred Person)),
      wc.clause.holds W → wc.eval W = wc.satisfiedPotential := by
    intro wc h
    classical
    unfold WeightedGroundClause.eval
    exact if_pos h
  have eval_unsat : ∀ (wc : WeightedGroundClause (GroundAtom SmokePred Person)),
      ¬ wc.clause.holds W → wc.eval W = wc.unsatisfiedPotential := by
    intro wc h
    classical
    unfold WeightedGroundClause.eval
    exact if_neg h
  -- Prove clause-not-holds (unsatisfied) for 2-literal clauses
  -- Pattern: clause = {neg a, pos b}, bad ↔ W a = true ∧ W b = false
  have clause_not_holds_2 :
      ∀ (a b : GroundAtom SmokePred Person),
        W a = true → W b = false →
          ¬ ({.neg a, .pos b} : GroundClause _).holds W := by
    intro a b ha hb ⟨l, hl, hW⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp [Literal.holds] at hW; exact Bool.false_ne_true (hW.symm.trans ha)
    · simp [Literal.holds] at hW; exact Bool.false_ne_true (hb.symm.trans hW)
  -- Prove clause-holds (satisfied) for 2-literal clauses
  have clause_holds_neg :
      ∀ (a b : GroundAtom SmokePred Person),
        W a = false →
          ({.neg a, .pos b} : GroundClause _).holds W := by
    intro a b ha
    exact ⟨.neg a, Finset.mem_insert_self _ _, by simp [Literal.holds, ha]⟩
  have clause_holds_pos :
      ∀ (a b : GroundAtom SmokePred Person),
        W b = true →
          ({.neg a, .pos b} : GroundClause _).holds W := by
    intro a b hb
    exact ⟨.pos b, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
           by simp [Literal.holds, hb]⟩
  -- Now expand each clause eval
  have hSCA :
      (socialGroundMLN.clauseData .smokesCancerAlice).eval W =
        if W sAlice = true ∧ W cAlice = false then 0 else 1 := by
    simp only [socialGroundMLN]
    by_cases hbad : W sAlice = true ∧ W cAlice = false
    · rw [if_pos hbad]
      exact eval_unsat _ (clause_not_holds_2 sAlice cAlice hbad.1 hbad.2)
    · rw [if_neg hbad]; push_neg at hbad
      by_cases hs : W sAlice = true
      · exact eval_sat _ (clause_holds_pos sAlice cAlice
          (by cases h : W cAlice <;> simp_all))
      · exact eval_sat _ (clause_holds_neg sAlice cAlice
          (by cases h : W sAlice <;> simp_all))
  have hSCB :
      (socialGroundMLN.clauseData .smokesCancerBob).eval W =
        if W sBob = true ∧ W cBob = false then 0 else 1 := by
    simp only [socialGroundMLN]
    by_cases hbad : W sBob = true ∧ W cBob = false
    · rw [if_pos hbad]
      exact eval_unsat _ (clause_not_holds_2 sBob cBob hbad.1 hbad.2)
    · rw [if_neg hbad]; push_neg at hbad
      by_cases hs : W sBob = true
      · exact eval_sat _ (clause_holds_pos sBob cBob
          (by cases h : W cBob <;> simp_all))
      · exact eval_sat _ (clause_holds_neg sBob cBob
          (by cases h : W sBob <;> simp_all))
  have hFI :
      (socialGroundMLN.clauseData .friendsInfluenceAB).eval W =
        if W sAlice = true ∧ W sBob = false then 1 else 3 := by
    simp only [socialGroundMLN]
    by_cases hbad : W sAlice = true ∧ W sBob = false
    · rw [if_pos hbad]
      exact eval_unsat _ (clause_not_holds_2 sAlice sBob hbad.1 hbad.2)
    · rw [if_neg hbad]; push_neg at hbad
      by_cases hs : W sAlice = true
      · exact eval_sat _ (clause_holds_pos sAlice sBob
          (by cases h : W sBob <;> simp_all))
      · exact eval_sat _ (clause_holds_neg sAlice sBob
          (by cases h : W sAlice <;> simp_all))
  have hEV :
      (socialGroundMLN.clauseData .evidenceSmokesA).eval W =
        if W sAlice = false then 0 else 1 := by
    simp only [socialGroundMLN]
    by_cases hbad : W sAlice = false
    · rw [if_pos hbad]
      apply eval_unsat
      intro ⟨l, hl, hW⟩
      rw [Finset.mem_singleton] at hl; subst hl
      simp [Literal.holds] at hW; exact Bool.false_ne_true (hbad.symm.trans hW)
    · rw [if_neg hbad]
      apply eval_sat
      have hs : W sAlice = true := by cases h : W sAlice <;> simp_all
      exact ⟨.pos sAlice, Finset.mem_singleton_self _, by simp [Literal.holds, hs]⟩
  rw [hSCA, hSCB, hFI, hEV]
  ring

/-! ### Mass theorems -/

private noncomputable def socialWorldWeightFn : Bool × Bool × Bool × Bool → ENNReal :=
  fun ⟨sa, ca, sb, cb⟩ =>
    (if sa = true ∧ ca = false then (0 : ENNReal) else 1) *
    (if sb = true ∧ cb = false then 0 else 1) *
    (if sa = true ∧ sb = false then 1 else 3) *
    (if sa = false then 0 else 1)

private theorem social_sum_worldWeight_eq_five_aux :
    ∑ W : AtomValuation (GroundAtom SmokePred Person),
      socialGroundMLN.worldWeight socialFullSupport W = 5 := by
  simp only [social_worldWeight_fullSupport_eq]
  rw [show ∑ W : GroundAtom SmokePred Person → Bool,
        (if W sAlice = true ∧ W cAlice = false then (0:ENNReal) else 1) *
        (if W sBob = true ∧ W cBob = false then 0 else 1) *
        (if W sAlice = true ∧ W sBob = false then 1 else 3) *
        (if W sAlice = false then 0 else 1) =
      ∑ b : Bool × Bool × Bool × Bool, socialWorldWeightFn b
    from Equiv.sum_comp socialValEquiv socialWorldWeightFn]
  simp only [socialWorldWeightFn, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

private theorem social_sum_smokesBob_aux :
    ∑ W : AtomValuation (GroundAtom SmokePred Person),
      (if ∀ c ∈ smokesBobQuery, W c.1 = c.2 then
          socialGroundMLN.worldWeight socialFullSupport W
        else 0) = 3 := by
  simp only [social_worldWeight_fullSupport_eq]
  let f : AtomValuation (GroundAtom SmokePred Person) → ENNReal := fun W =>
    (if W sAlice = true ∧ W cAlice = false then (0 : ENNReal) else 1) *
    (if W sBob = true ∧ W cBob = false then 0 else 1) *
    (if W sAlice = true ∧ W sBob = false then 1 else 3) *
    (if W sAlice = false then 0 else 1)
  have hquery :
      ∀ W : AtomValuation (GroundAtom SmokePred Person),
        (∀ c ∈ smokesBobQuery, W c.1 = c.2) ↔ W sBob = true := by
    intro W; simp [smokesBobQuery]
  have hsum :
      (∑ W : AtomValuation (GroundAtom SmokePred Person),
        if ∀ c ∈ smokesBobQuery, W c.1 = c.2 then f W else 0) =
      ∑ W : AtomValuation (GroundAtom SmokePred Person),
        if W sBob = true then f W else 0 := by
    apply Fintype.sum_congr
    intro W
    by_cases h : W sBob = true <;> simp [f, h, hquery W]
  rw [show (∑ W : AtomValuation (GroundAtom SmokePred Person),
        if ∀ c ∈ smokesBobQuery, W c.1 = c.2 then f W else 0) =
      ∑ W : AtomValuation (GroundAtom SmokePred Person),
        if W sBob = true then f W else 0 from hsum]
  rw [show ∑ W : GroundAtom SmokePred Person → Bool,
        (if W sBob = true then f W else 0) =
      ∑ b : Bool × Bool × Bool × Bool,
        (if b.2.2.1 = true then
          (if b.1 = true ∧ b.2.1 = false then (0:ENNReal) else 1) *
          (if b.2.2.1 = true ∧ b.2.2.2 = false then 0 else 1) *
          (if b.1 = true ∧ b.2.2.1 = false then 1 else 3) *
          (if b.1 = false then 0 else 1) else 0)
    from Equiv.sum_comp socialValEquiv (fun b =>
      if b.2.2.1 = true then
        (if b.1 = true ∧ b.2.1 = false then (0 : ENNReal) else 1) *
        (if b.2.2.1 = true ∧ b.2.2.2 = false then 0 else 1) *
        (if b.1 = true ∧ b.2.2.1 = false then 1 else 3) *
        (if b.1 = false then 0 else 1)
      else 0)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

private theorem social_sum_cancerBob_aux :
    ∑ W : AtomValuation (GroundAtom SmokePred Person),
      (if ∀ c ∈ cancerBobQuery, W c.1 = c.2 then
          socialGroundMLN.worldWeight socialFullSupport W
        else 0) = 4 := by
  simp only [social_worldWeight_fullSupport_eq]
  let f : AtomValuation (GroundAtom SmokePred Person) → ENNReal := fun W =>
    (if W sAlice = true ∧ W cAlice = false then (0 : ENNReal) else 1) *
    (if W sBob = true ∧ W cBob = false then 0 else 1) *
    (if W sAlice = true ∧ W sBob = false then 1 else 3) *
    (if W sAlice = false then 0 else 1)
  have hquery :
      ∀ W : AtomValuation (GroundAtom SmokePred Person),
        (∀ c ∈ cancerBobQuery, W c.1 = c.2) ↔ W cBob = true := by
    intro W; simp [cancerBobQuery]
  have hsum :
      (∑ W : AtomValuation (GroundAtom SmokePred Person),
        if ∀ c ∈ cancerBobQuery, W c.1 = c.2 then f W else 0) =
      ∑ W : AtomValuation (GroundAtom SmokePred Person),
        if W cBob = true then f W else 0 := by
    apply Fintype.sum_congr
    intro W
    by_cases h : W cBob = true <;> simp [f, h, hquery W]
  rw [show (∑ W : AtomValuation (GroundAtom SmokePred Person),
        if ∀ c ∈ cancerBobQuery, W c.1 = c.2 then f W else 0) =
      ∑ W : AtomValuation (GroundAtom SmokePred Person),
        if W cBob = true then f W else 0 from hsum]
  rw [show ∑ W : GroundAtom SmokePred Person → Bool,
        (if W cBob = true then f W else 0) =
      ∑ b : Bool × Bool × Bool × Bool,
        (if b.2.2.2 = true then
          (if b.1 = true ∧ b.2.1 = false then (0:ENNReal) else 1) *
          (if b.2.2.1 = true ∧ b.2.2.2 = false then 0 else 1) *
          (if b.1 = true ∧ b.2.2.1 = false then 1 else 3) *
          (if b.1 = false then 0 else 1) else 0)
    from Equiv.sum_comp socialValEquiv (fun b =>
      if b.2.2.2 = true then
        (if b.1 = true ∧ b.2.1 = false then (0 : ENNReal) else 1) *
        (if b.2.2.1 = true ∧ b.2.2.2 = false then 0 else 1) *
        (if b.1 = true ∧ b.2.2.1 = false then 1 else 3) *
        (if b.1 = false then 0 else 1)
      else 0)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-! ### Top-level mass and probability theorems -/

theorem social_totalMass_eq_five :
    (clauseMassSemantics socialGroundMLN socialFullSupport).totalMass = 5 := by
  change CountableMLNSemantics.totalMass
    (socialGroundMLN.toCountableMLNSemantics (Query := ConstraintQuery _)
      socialFullSupport constraintQueryHolds) = 5
  unfold CountableMLNSemantics.totalMass GroundMLN.toCountableMLNSemantics
  rw [tsum_eq_sum (s := Finset.univ) (fun W hW => (hW (Finset.mem_univ W)).elim)]
  exact social_sum_worldWeight_eq_five_aux

theorem social_queryMass_smokesBob_eq_three :
    (clauseMassSemantics socialGroundMLN socialFullSupport).queryMass smokesBobQuery = 3 := by
  change CountableMLNSemantics.queryMass
    (socialGroundMLN.toCountableMLNSemantics (Query := ConstraintQuery _)
      socialFullSupport constraintQueryHolds) smokesBobQuery = 3
  simp only [CountableMLNSemantics.queryMass, GroundMLN.toCountableMLNSemantics,
             constraintQueryHolds, satisfiesConstraints]
  rw [tsum_eq_sum (s := Finset.univ) (fun W hW => (hW (Finset.mem_univ W)).elim)]
  exact social_sum_smokesBob_aux

theorem social_queryMass_cancerBob_eq_four :
    (clauseMassSemantics socialGroundMLN socialFullSupport).queryMass cancerBobQuery = 4 := by
  change CountableMLNSemantics.queryMass
    (socialGroundMLN.toCountableMLNSemantics (Query := ConstraintQuery _)
      socialFullSupport constraintQueryHolds) cancerBobQuery = 4
  simp only [CountableMLNSemantics.queryMass, GroundMLN.toCountableMLNSemantics,
             constraintQueryHolds, satisfiesConstraints]
  rw [tsum_eq_sum (s := Finset.univ) (fun W hW => (hW (Finset.mem_univ W)).elim)]
  exact social_sum_cancerBob_aux

theorem social_queryProb_smokesBob_eq_three_fifths :
    (clauseMassSemantics socialGroundMLN socialFullSupport).queryProb smokesBobQuery =
      (3 : ENNReal) / 5 := by
  have htotal : (clauseMassSemantics socialGroundMLN socialFullSupport).totalMass ≠ 0 := by
    rw [social_totalMass_eq_five]; norm_num
  unfold MassSemantics.queryProb
  rw [if_neg htotal, social_queryMass_smokesBob_eq_three, social_totalMass_eq_five]

theorem social_queryProb_cancerBob_eq_four_fifths :
    (clauseMassSemantics socialGroundMLN socialFullSupport).queryProb cancerBobQuery =
      (4 : ENNReal) / 5 := by
  have htotal : (clauseMassSemantics socialGroundMLN socialFullSupport).totalMass ≠ 0 := by
    rw [social_totalMass_eq_five]; norm_num
  unfold MassSemantics.queryProb
  rw [if_neg htotal, social_queryMass_cancerBob_eq_four, social_totalMass_eq_five]

/-! ### Canary theorems -/

/-- **Social smoking canary**: P(Smokes(bob)) = 3/5 given evidence
Friends(alice,bob)=T and Smokes(alice)=T with friend-influence weight 3:1. -/
theorem social_queryStrength_smokesBob_eq_three_fifths :
    WorldModel.queryStrength (clauseWMState socialGroundMLN socialFullSupport) smokesBobQuery =
      (3 : ENNReal) / 5 := by
  rw [clauseWM_queryStrength_eq_queryProb]
  exact social_queryProb_smokesBob_eq_three_fifths

/-- **Social smoking canary**: P(Cancer(bob)) = 4/5 given evidence
Friends(alice,bob)=T and Smokes(alice)=T with friend-influence weight 3:1
and hard constraint Smokes(x) → Cancer(x). -/
theorem social_queryStrength_cancerBob_eq_four_fifths :
    WorldModel.queryStrength (clauseWMState socialGroundMLN socialFullSupport) cancerBobQuery =
      (4 : ENNReal) / 5 := by
  rw [clauseWM_queryStrength_eq_queryProb]
  exact social_queryProb_cancerBob_eq_four_fifths

end SocialSmoking

end Mettapedia.Logic.PLNMarkovLogicSocialSmoking
