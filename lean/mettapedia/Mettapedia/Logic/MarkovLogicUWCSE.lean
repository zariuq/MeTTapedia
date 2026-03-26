import Mettapedia.Logic.MarkovLogicClauseWorldModel
import Mettapedia.Logic.MarkovLogicGrounding

/-!
# UW-CSE MLN Canary

A micro-slice of the UW-CSE benchmark (language area), formalized as a ground MLN.
This is the first canary exercising **mixed-arity predicates** (unary + binary).

## Setup

Real entities from `data/uw-cse/language.db`:
- Person335: professor, Faculty
- Person429: student, Post_Quals, advisedBy(Person429, Person335)

Predicates:
- `student/1`, `professor/1` (unary)
- `advisedBy/2` (binary) — target predicate, convention `advisedBy(student, professor)`

Ground atoms (8 total, 256 worlds):
- student(335), student(429), professor(335), professor(429)
- advisedBy(335,335), advisedBy(335,429), advisedBy(429,335), advisedBy(429,429)

Rules (all hard, from uw.mln semantics, corrected for data convention):
1. advisedBy(x,y) → student(x) — 4 groundings
2. advisedBy(x,y) → professor(y) — 4 groundings
3. ¬student(x) ∨ ¬professor(x) — 2 groundings
4. ¬advisedBy(x,x) — 2 groundings
5. student(429) — evidence
6. professor(335) — evidence

## Results

Hard constraints force all atoms except advisedBy(429,335):
- Z = 2
- P(advisedBy(429,335)) = 1/2

## Reference

Richardson & Domingos (2006), "Markov Logic Networks", Machine Learning 62(1-2).
UW-CSE benchmark: https://alchemy.cs.washington.edu/data/uw-cse/
-/

namespace Mettapedia.Logic.MarkovLogicUWCSE

open scoped ENNReal BigOperators
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicCountable
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicClauseWorldModel
open Mettapedia.Logic.MarkovLogicGrounding

/-! ## Predicates and Domain -/

/-- UW-CSE predicates indexed by arity. -/
inductive UWPred : ℕ → Type where
  | student : UWPred 1
  | professor : UWPred 1
  | advisedBy : UWPred 2
deriving DecidableEq

/-- Two persons from the language area. -/
inductive UWPerson where
  | p335  -- professor, Faculty
  | p429  -- student, Post_Quals
deriving DecidableEq, Fintype

/-! ## Fintype for mixed-arity ground atoms -/

private theorem uwPredArity : ∀ {n : ℕ}, UWPred n → n = 1 ∨ n = 2
  | _, .student => Or.inl rfl
  | _, .professor => Or.inl rfl
  | _, .advisedBy => Or.inr rfl

private instance : Fintype (UWPred 1) :=
  ⟨{.student, .professor}, fun p => by cases p <;> simp⟩

private instance : Fintype (UWPred 2) :=
  ⟨{.advisedBy}, fun p => by cases p; simp⟩

/-- Ground atoms biject with the sum of unary and binary atoms. -/
private noncomputable def uwGroundAtomEquiv :
    GroundAtom UWPred UWPerson ≃ (UWPred 1 × UWPerson) ⊕ (UWPred 2 × UWPerson × UWPerson) where
  toFun a :=
    match h : a.n, a.pred with
    | 1, p => Sum.inl ⟨p, a.args ⟨0, by omega⟩⟩
    | 2, p => Sum.inr ⟨p, a.args ⟨0, by omega⟩, a.args ⟨1, by omega⟩⟩
  invFun
    | Sum.inl ⟨p, d⟩ => ⟨1, p, fun _ => d⟩
    | Sum.inr ⟨p, d₁, d₂⟩ => ⟨2, p, fun i => if i = 0 then d₁ else d₂⟩
  left_inv a := by
    obtain ⟨n, pred, args⟩ := a
    rcases uwPredArity pred with rfl | rfl
    · simp only [GroundAtom.mk.injEq, heq_eq_eq, true_and]
      funext i; fin_cases i; rfl
    · simp only [GroundAtom.mk.injEq, heq_eq_eq, true_and]
      funext i; fin_cases i <;> simp
  right_inv b := by
    rcases b with ⟨p, d⟩ | ⟨p, d₁, d₂⟩ <;> simp

private noncomputable instance : Fintype (GroundAtom UWPred UWPerson) :=
  Fintype.ofEquiv _ uwGroundAtomEquiv.symm

/-! ## Named ground atoms -/

section Atoms

open UWPred UWPerson

private def s335 : GroundAtom UWPred UWPerson := ⟨1, .student, fun _ => .p335⟩
private def s429 : GroundAtom UWPred UWPerson := ⟨1, .student, fun _ => .p429⟩
private def p335 : GroundAtom UWPred UWPerson := ⟨1, .professor, fun _ => .p335⟩
private def p429 : GroundAtom UWPred UWPerson := ⟨1, .professor, fun _ => .p429⟩
private def a33 : GroundAtom UWPred UWPerson :=
  ⟨2, .advisedBy, fun i => if i = 0 then .p335 else .p335⟩
private def a34 : GroundAtom UWPred UWPerson :=
  ⟨2, .advisedBy, fun i => if i = 0 then .p335 else .p429⟩
private def a43 : GroundAtom UWPred UWPerson :=
  ⟨2, .advisedBy, fun i => if i = 0 then .p429 else .p335⟩
private def a44 : GroundAtom UWPred UWPerson :=
  ⟨2, .advisedBy, fun i => if i = 0 then .p429 else .p429⟩

end Atoms

/-! ## Ground MLN -/

section UWCSE

open Mettapedia.Logic.PLNWorldModel

/-- Clause identifiers for the UW-CSE micro-slice ground MLN.
Naming: rule family + grounding substitution. -/
inductive UWClauseId where
  -- advisedBy(x,y) → student(x), 4 groundings
  | advStudent_33  -- x=335, y=335
  | advStudent_34  -- x=335, y=429
  | advStudent_43  -- x=429, y=335
  | advStudent_44  -- x=429, y=429
  -- advisedBy(x,y) → professor(y), 4 groundings
  | advProf_33
  | advProf_34
  | advProf_43
  | advProf_44
  -- ¬student(x) ∨ ¬professor(x), 2 groundings
  | mutExcl_3  -- x=335
  | mutExcl_4  -- x=429
  -- ¬advisedBy(x,x), 2 groundings
  | noSelf_3   -- x=335
  | noSelf_4   -- x=429
  -- BinaryEvidence
  | evStudent429
  | evProfessor335
deriving DecidableEq, Fintype

/-- The UW-CSE micro-slice ground MLN: 14 hard clauses.

Convention: `advisedBy(student, professor)` — first arg is the student.
All clauses are hard (sat=1, unsat=0). -/
noncomputable def uwcseGroundMLN :
    GroundMLN (GroundAtom UWPred UWPerson) UWClauseId where
  clauseData
  -- advisedBy(x,y) → student(x) ≡ ¬advisedBy(x,y) ∨ student(x)
  | .advStudent_33 => {
      clause := {.neg a33, .pos s335}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  | .advStudent_34 => {
      clause := {.neg a34, .pos s335}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  | .advStudent_43 => {
      clause := {.neg a43, .pos s429}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  | .advStudent_44 => {
      clause := {.neg a44, .pos s429}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  -- advisedBy(x,y) → professor(y) ≡ ¬advisedBy(x,y) ∨ professor(y)
  | .advProf_33 => {
      clause := {.neg a33, .pos p335}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  | .advProf_34 => {
      clause := {.neg a34, .pos p429}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  | .advProf_43 => {
      clause := {.neg a43, .pos p335}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  | .advProf_44 => {
      clause := {.neg a44, .pos p429}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  -- ¬student(x) ∨ ¬professor(x)
  | .mutExcl_3 => {
      clause := {.neg s335, .neg p335}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  | .mutExcl_4 => {
      clause := {.neg s429, .neg p429}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  -- ¬advisedBy(x,x)
  | .noSelf_3 => {
      clause := {.neg a33}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  | .noSelf_4 => {
      clause := {.neg a44}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  -- BinaryEvidence: student(429), professor(335)
  | .evStudent429 => {
      clause := {.pos s429}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }
  | .evProfessor335 => {
      clause := {.pos p335}
      satisfiedPotential := 1
      unsatisfiedPotential := 0
      satisfied_ne_top := by norm_num
      unsatisfied_ne_top := by norm_num }

noncomputable def uwcseFullSupport : Finset UWClauseId := Finset.univ

/-! ### Query -/

/-- Query: advisedBy(429, 335) = true.
In UW-CSE language.db: advisedBy(Person429, Person335). -/
def advisedBy429_335Query : ConstraintQuery (GroundAtom UWPred UWPerson) :=
  [⟨a43, true⟩]

/-! ### Valuation equivalence -/

/-- Reindex valuations as (s335, s429, p335, p429, a33, a34, a43, a44). -/
private noncomputable def uwValEquiv :
    (GroundAtom UWPred UWPerson → Bool) ≃
    Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool where
  toFun W := (W s335, W s429, W p335, W p429, W a33, W a34, W a43, W a44)
  invFun b a :=
    match uwGroundAtomEquiv a with
    | Sum.inl (.student, .p335) => b.1
    | Sum.inl (.student, .p429) => b.2.1
    | Sum.inl (.professor, .p335) => b.2.2.1
    | Sum.inl (.professor, .p429) => b.2.2.2.1
    | Sum.inr (.advisedBy, .p335, .p335) => b.2.2.2.2.1
    | Sum.inr (.advisedBy, .p335, .p429) => b.2.2.2.2.2.1
    | Sum.inr (.advisedBy, .p429, .p335) => b.2.2.2.2.2.2.1
    | Sum.inr (.advisedBy, .p429, .p429) => b.2.2.2.2.2.2.2
  left_inv W := by
    funext a
    rw [show a = uwGroundAtomEquiv.symm (uwGroundAtomEquiv a) from
        (uwGroundAtomEquiv.symm_apply_apply a).symm]
    rcases uwGroundAtomEquiv a with ⟨_ | _, _ | _⟩ | ⟨⟨⟩, _ | _, _ | _⟩ <;> rfl
  right_inv b := rfl

/-! ### Support enumeration -/

theorem uwcseFullSupport_eq :
    uwcseFullSupport =
      ({.advStudent_33, .advStudent_34, .advStudent_43, .advStudent_44,
        .advProf_33, .advProf_34, .advProf_43, .advProf_44,
        .mutExcl_3, .mutExcl_4, .noSelf_3, .noSelf_4,
        .evStudent429, .evProfessor335} : Finset UWClauseId) := by
  ext x; simp [uwcseFullSupport]; cases x <;> simp

/-! ### Clause eval helpers -/

private theorem eval_hard_np (a b : GroundAtom UWPred UWPerson)
    (W : GroundAtom UWPred UWPerson → Bool) :
    ({ clause := ({.neg a, .pos b} : GroundClause _),
       satisfiedPotential := 1, unsatisfiedPotential := 0,
       satisfied_ne_top := by norm_num,
       unsatisfied_ne_top := by norm_num } : WeightedGroundClause _).eval W =
      if W a = true ∧ W b = false then 0 else 1 := by
  classical
  unfold WeightedGroundClause.eval GroundClause.holds
  simp only [Finset.mem_insert, Finset.mem_singleton]
  cases h₁ : W a <;> cases h₂ : W b <;> simp [Literal.holds, h₁, h₂]

private theorem eval_hard_nn (a b : GroundAtom UWPred UWPerson)
    (W : GroundAtom UWPred UWPerson → Bool) :
    ({ clause := ({.neg a, .neg b} : GroundClause _),
       satisfiedPotential := 1, unsatisfiedPotential := 0,
       satisfied_ne_top := by norm_num,
       unsatisfied_ne_top := by norm_num } : WeightedGroundClause _).eval W =
      if W a = true ∧ W b = true then 0 else 1 := by
  classical
  unfold WeightedGroundClause.eval GroundClause.holds
  simp only [Finset.mem_insert, Finset.mem_singleton]
  cases h₁ : W a <;> cases h₂ : W b <;> simp [Literal.holds, h₁, h₂]

private theorem eval_hard_n (a : GroundAtom UWPred UWPerson)
    (W : GroundAtom UWPred UWPerson → Bool) :
    ({ clause := ({.neg a} : GroundClause _),
       satisfiedPotential := 1, unsatisfiedPotential := 0,
       satisfied_ne_top := by norm_num,
       unsatisfied_ne_top := by norm_num } : WeightedGroundClause _).eval W =
      if W a = true then 0 else 1 := by
  classical
  unfold WeightedGroundClause.eval GroundClause.holds
  simp only [Finset.mem_singleton]
  cases h : W a <;> simp [Literal.holds, h]

private theorem eval_hard_p (a : GroundAtom UWPred UWPerson)
    (W : GroundAtom UWPred UWPerson → Bool) :
    ({ clause := ({.pos a} : GroundClause _),
       satisfiedPotential := 1, unsatisfiedPotential := 0,
       satisfied_ne_top := by norm_num,
       unsatisfied_ne_top := by norm_num } : WeightedGroundClause _).eval W =
      if W a = false then 0 else 1 := by
  classical
  unfold WeightedGroundClause.eval GroundClause.holds
  simp only [Finset.mem_singleton]
  cases h : W a <;> simp [Literal.holds, h]

/-! ### World-weight factorization -/

set_option maxHeartbeats 3200000 in
/-- For all-hard MLN, the world weight is either 0 (any clause violated) or 1.
Each clause contributes `if clause_violated then 0 else 1`.

Clause satisfaction conditions (negated = violation):
- `{.neg X, .pos Y}`: violated when `X=T ∧ Y=F`
- `{.neg X, .neg Y}`: violated when `X=T ∧ Y=T`
- `{.neg X}`: violated when `X=T`
- `{.pos X}`: violated when `X=F` -/
theorem uwcse_worldWeight_fullSupport_eq
    (W : AtomValuation (GroundAtom UWPred UWPerson)) :
    uwcseGroundMLN.worldWeight uwcseFullSupport W =
      -- Right-associated to match Finset.prod_insert output
      (if W a33 = true ∧ W s335 = false then 0 else 1) *
      ((if W a34 = true ∧ W s335 = false then 0 else 1) *
      ((if W a43 = true ∧ W s429 = false then 0 else 1) *
      ((if W a44 = true ∧ W s429 = false then 0 else 1) *
      ((if W a33 = true ∧ W p335 = false then 0 else 1) *
      ((if W a34 = true ∧ W p429 = false then 0 else 1) *
      ((if W a43 = true ∧ W p335 = false then 0 else 1) *
      ((if W a44 = true ∧ W p429 = false then 0 else 1) *
      ((if W s335 = true ∧ W p335 = true then 0 else 1) *
      ((if W s429 = true ∧ W p429 = true then 0 else 1) *
      ((if W a33 = true then 0 else 1) *
      ((if W a44 = true then 0 else 1) *
      ((if W s429 = false then 0 else 1) *
      (if W p335 = false then 0 else 1))))))))))))) := by
  classical
  unfold GroundMLN.worldWeight
  rw [uwcseFullSupport_eq]
  let s : Finset UWClauseId :=
    {.advStudent_33, .advStudent_34, .advStudent_43, .advStudent_44,
     .advProf_33, .advProf_34, .advProf_43, .advProf_44,
     .mutExcl_3, .mutExcl_4, .noSelf_3, .noSelf_4,
     .evStudent429, .evProfessor335}
  have hsort :
      (∏ i : s.attach,
          (uwcseGroundMLN.clauseData i.1).eval W) =
        ∏ i ∈ s.attach, (uwcseGroundMLN.clauseData i.1).eval W :=
    Finset.prod_coe_sort s.attach
      (fun i => (uwcseGroundMLN.clauseData i.1).eval W)
  rw [hsort]
  have hattach :
      (∏ i ∈ s.attach, (uwcseGroundMLN.clauseData i.1).eval W) =
        ∏ i ∈ s, (uwcseGroundMLN.clauseData i).eval W :=
    Finset.prod_attach s (fun i => (uwcseGroundMLN.clauseData i).eval W)
  rw [hattach]
  rw [show s = ({.advStudent_33, .advStudent_34, .advStudent_43, .advStudent_44,
       .advProf_33, .advProf_34, .advProf_43, .advProf_44,
       .mutExcl_3, .mutExcl_4, .noSelf_3, .noSelf_4,
       .evStudent429, .evProfessor335} : Finset UWClauseId) from rfl]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]
  -- Each clause eval unfolds to an if-then-else via helpers
  simp only [uwcseGroundMLN]
  congr 1; · exact eval_hard_np a33 s335 W
  congr 1; · exact eval_hard_np a34 s335 W
  congr 1; · exact eval_hard_np a43 s429 W
  congr 1; · exact eval_hard_np a44 s429 W
  congr 1; · exact eval_hard_np a33 p335 W
  congr 1; · exact eval_hard_np a34 p429 W
  congr 1; · exact eval_hard_np a43 p335 W
  congr 1; · exact eval_hard_np a44 p429 W
  congr 1; · exact eval_hard_nn s335 p335 W
  congr 1; · exact eval_hard_nn s429 p429 W
  congr 1; · exact eval_hard_n a33 W
  congr 1; · exact eval_hard_n a44 W
  congr 1; · exact eval_hard_p s429 W
  exact eval_hard_p p335 W

/-! ### Mass theorems -/

private noncomputable def uwWorldWeightFn :
    Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool → ENNReal :=
  fun ⟨vs335, vs429, vp335, vp429, va33, va34, va43, va44⟩ =>
    (if va33 = true ∧ vs335 = false then (0 : ENNReal) else 1) *
    ((if va34 = true ∧ vs335 = false then 0 else 1) *
    ((if va43 = true ∧ vs429 = false then 0 else 1) *
    ((if va44 = true ∧ vs429 = false then 0 else 1) *
    ((if va33 = true ∧ vp335 = false then 0 else 1) *
    ((if va34 = true ∧ vp429 = false then 0 else 1) *
    ((if va43 = true ∧ vp335 = false then 0 else 1) *
    ((if va44 = true ∧ vp429 = false then 0 else 1) *
    ((if vs335 = true ∧ vp335 = true then 0 else 1) *
    ((if vs429 = true ∧ vp429 = true then 0 else 1) *
    ((if va33 = true then 0 else 1) *
    ((if va44 = true then 0 else 1) *
    ((if vs429 = false then 0 else 1) *
    (if vp335 = false then 0 else 1)))))))))))))

private theorem uwcse_sum_worldWeight_eq_two :
    ∑ W : AtomValuation (GroundAtom UWPred UWPerson),
      uwcseGroundMLN.worldWeight uwcseFullSupport W = 2 := by
  simp only [uwcse_worldWeight_fullSupport_eq]
  rw [show ∑ W : GroundAtom UWPred UWPerson → Bool,
        (if W a33 = true ∧ W s335 = false then (0:ENNReal) else 1) *
        ((if W a34 = true ∧ W s335 = false then 0 else 1) *
        ((if W a43 = true ∧ W s429 = false then 0 else 1) *
        ((if W a44 = true ∧ W s429 = false then 0 else 1) *
        ((if W a33 = true ∧ W p335 = false then 0 else 1) *
        ((if W a34 = true ∧ W p429 = false then 0 else 1) *
        ((if W a43 = true ∧ W p335 = false then 0 else 1) *
        ((if W a44 = true ∧ W p429 = false then 0 else 1) *
        ((if W s335 = true ∧ W p335 = true then 0 else 1) *
        ((if W s429 = true ∧ W p429 = true then 0 else 1) *
        ((if W a33 = true then 0 else 1) *
        ((if W a44 = true then 0 else 1) *
        ((if W s429 = false then 0 else 1) *
        (if W p335 = false then 0 else 1))))))))))))) =
      ∑ b : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool,
        uwWorldWeightFn b
    from Equiv.sum_comp uwValEquiv uwWorldWeightFn]
  simp only [uwWorldWeightFn, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

private theorem uwcse_sum_advisedBy_eq_one :
    ∑ W : AtomValuation (GroundAtom UWPred UWPerson),
      (if ∀ c ∈ advisedBy429_335Query, W c.1 = c.2 then
          uwcseGroundMLN.worldWeight uwcseFullSupport W
        else 0) = 1 := by
  simp only [uwcse_worldWeight_fullSupport_eq]
  have hquery :
      ∀ W : AtomValuation (GroundAtom UWPred UWPerson),
        (∀ c ∈ advisedBy429_335Query, W c.1 = c.2) ↔ W a43 = true := by
    intro W; simp [advisedBy429_335Query]
  let f : AtomValuation (GroundAtom UWPred UWPerson) → ENNReal := fun W =>
    (if W a33 = true ∧ W s335 = false then (0 : ENNReal) else 1) *
    ((if W a34 = true ∧ W s335 = false then 0 else 1) *
    ((if W a43 = true ∧ W s429 = false then 0 else 1) *
    ((if W a44 = true ∧ W s429 = false then 0 else 1) *
    ((if W a33 = true ∧ W p335 = false then 0 else 1) *
    ((if W a34 = true ∧ W p429 = false then 0 else 1) *
    ((if W a43 = true ∧ W p335 = false then 0 else 1) *
    ((if W a44 = true ∧ W p429 = false then 0 else 1) *
    ((if W s335 = true ∧ W p335 = true then 0 else 1) *
    ((if W s429 = true ∧ W p429 = true then 0 else 1) *
    ((if W a33 = true then 0 else 1) *
    ((if W a44 = true then 0 else 1) *
    ((if W s429 = false then 0 else 1) *
    (if W p335 = false then 0 else 1)))))))))))))
  have hsum :
      (∑ W : AtomValuation (GroundAtom UWPred UWPerson),
        if ∀ c ∈ advisedBy429_335Query, W c.1 = c.2 then f W else 0) =
      ∑ W : AtomValuation (GroundAtom UWPred UWPerson),
        if W a43 = true then f W else 0 := by
    apply Fintype.sum_congr
    intro W
    by_cases h : W a43 = true <;> simp [f, h, hquery W]
  rw [show (∑ W : AtomValuation (GroundAtom UWPred UWPerson),
        if ∀ c ∈ advisedBy429_335Query, W c.1 = c.2 then f W else 0) =
      ∑ W : AtomValuation (GroundAtom UWPred UWPerson),
        if W a43 = true then f W else 0 from hsum]
  rw [show ∑ W : GroundAtom UWPred UWPerson → Bool,
        (if W a43 = true then f W else 0) =
      ∑ b : Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool,
        (if b.2.2.2.2.2.2.1 = true then
          (if b.2.2.2.2.1 = true ∧ b.1 = false then (0:ENNReal) else 1) *
          ((if b.2.2.2.2.2.1 = true ∧ b.1 = false then 0 else 1) *
          ((if b.2.2.2.2.2.2.1 = true ∧ b.2.1 = false then 0 else 1) *
          ((if b.2.2.2.2.2.2.2 = true ∧ b.2.1 = false then 0 else 1) *
          ((if b.2.2.2.2.1 = true ∧ b.2.2.1 = false then 0 else 1) *
          ((if b.2.2.2.2.2.1 = true ∧ b.2.2.2.1 = false then 0 else 1) *
          ((if b.2.2.2.2.2.2.1 = true ∧ b.2.2.1 = false then 0 else 1) *
          ((if b.2.2.2.2.2.2.2 = true ∧ b.2.2.2.1 = false then 0 else 1) *
          ((if b.1 = true ∧ b.2.2.1 = true then 0 else 1) *
          ((if b.2.1 = true ∧ b.2.2.2.1 = true then 0 else 1) *
          ((if b.2.2.2.2.1 = true then 0 else 1) *
          ((if b.2.2.2.2.2.2.2 = true then 0 else 1) *
          ((if b.2.1 = false then 0 else 1) *
          (if b.2.2.1 = false then 0 else 1))))))))))))) else 0)
    from Equiv.sum_comp uwValEquiv (fun b =>
      if b.2.2.2.2.2.2.1 = true then
        (if b.2.2.2.2.1 = true ∧ b.1 = false then (0 : ENNReal) else 1) *
        ((if b.2.2.2.2.2.1 = true ∧ b.1 = false then 0 else 1) *
        ((if b.2.2.2.2.2.2.1 = true ∧ b.2.1 = false then 0 else 1) *
        ((if b.2.2.2.2.2.2.2 = true ∧ b.2.1 = false then 0 else 1) *
        ((if b.2.2.2.2.1 = true ∧ b.2.2.1 = false then 0 else 1) *
        ((if b.2.2.2.2.2.1 = true ∧ b.2.2.2.1 = false then 0 else 1) *
        ((if b.2.2.2.2.2.2.1 = true ∧ b.2.2.1 = false then 0 else 1) *
        ((if b.2.2.2.2.2.2.2 = true ∧ b.2.2.2.1 = false then 0 else 1) *
        ((if b.1 = true ∧ b.2.2.1 = true then 0 else 1) *
        ((if b.2.1 = true ∧ b.2.2.2.1 = true then 0 else 1) *
        ((if b.2.2.2.2.1 = true then 0 else 1) *
        ((if b.2.2.2.2.2.2.2 = true then 0 else 1) *
        ((if b.2.1 = false then 0 else 1) *
        (if b.2.2.1 = false then 0 else 1)))))))))))))
      else 0)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-! ### Top-level mass and probability theorems -/

theorem uwcse_totalMass_eq_two :
    (clauseMassSemantics uwcseGroundMLN uwcseFullSupport).totalMass = 2 := by
  change CountableMLNSemantics.totalMass
    (uwcseGroundMLN.toCountableMLNSemantics (Query := ConstraintQuery _)
      uwcseFullSupport constraintQueryHolds) = 2
  unfold CountableMLNSemantics.totalMass GroundMLN.toCountableMLNSemantics
  rw [tsum_eq_sum (s := Finset.univ) (fun W hW => (hW (Finset.mem_univ W)).elim)]
  exact uwcse_sum_worldWeight_eq_two

theorem uwcse_queryMass_advisedBy_eq_one :
    (clauseMassSemantics uwcseGroundMLN uwcseFullSupport).queryMass
      advisedBy429_335Query = 1 := by
  change CountableMLNSemantics.queryMass
    (uwcseGroundMLN.toCountableMLNSemantics (Query := ConstraintQuery _)
      uwcseFullSupport constraintQueryHolds) advisedBy429_335Query = 1
  simp only [CountableMLNSemantics.queryMass, GroundMLN.toCountableMLNSemantics,
             constraintQueryHolds, satisfiesConstraints]
  rw [tsum_eq_sum (s := Finset.univ) (fun W hW => (hW (Finset.mem_univ W)).elim)]
  exact uwcse_sum_advisedBy_eq_one

theorem uwcse_queryProb_advisedBy_eq_half :
    (clauseMassSemantics uwcseGroundMLN uwcseFullSupport).queryProb
      advisedBy429_335Query = (1 : ENNReal) / 2 := by
  have htotal : (clauseMassSemantics uwcseGroundMLN uwcseFullSupport).totalMass ≠ 0 := by
    rw [uwcse_totalMass_eq_two]; norm_num
  unfold MassSemantics.queryProb
  rw [if_neg htotal, uwcse_queryMass_advisedBy_eq_one, uwcse_totalMass_eq_two]

/-! ### Canary theorem -/

/-- **UW-CSE canary**: P(advisedBy(Person429, Person335)) = 1/2 given evidence
student(Person429)=T and professor(Person335)=T with structural hard constraints
from uw.mln.

This is the first canary exercising mixed-arity predicates (unary + binary).
Real entities from the UW-CSE language area (Richardson & Domingos 2006). -/
theorem uwcse_queryStrength_advisedBy429_335_eq_half :
    BinaryWorldModel.queryStrength (clauseWMState uwcseGroundMLN uwcseFullSupport)
      advisedBy429_335Query = (1 : ENNReal) / 2 := by
  rw [clauseWM_queryStrength_eq_queryProb]
  exact uwcse_queryProb_advisedBy_eq_half

end UWCSE

end Mettapedia.Logic.MarkovLogicUWCSE
