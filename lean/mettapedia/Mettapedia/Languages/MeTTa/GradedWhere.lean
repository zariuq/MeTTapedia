import Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
import Mettapedia.GSLT.Core.GradedSelectionIrreducibility

/-!
# Graded where-clauses on a match

A where-clause on a match gives every candidate match a value in a semiring `K`. The answer
of the match is then the sum, over the candidates, of the candidate's value times what its
template answers. This module states that one operation on the weighted answers of
`WeightedAnswerAlgebra` and proves what each way of writing a grade, and each way of carrying
it, amounts to.

## The operation

* A store is `S : Ans K X`: rows with an annotation. A plain bag is the case where each
  occurrence counts `1` (`plain`).
* A query `q : X → Ans K B` gives the bindings a row yields (none, one, or several).
* A where-clause is `ψ : B → K`, a value for each candidate's bindings.
* A template `t : B → Ans K Y` gives what a candidate answers.
* `gmatch S q ψ t` is the graded match.

## Where the grade is written

All of these denote `gmatch`:

* a clause on the match (`gmatch` itself);
* a factor written inside the template (`gmatch_eq_template`);
* a factor applied to the template's results, over a commutative `K` (`gmatch_post`);
* a join with a space of weight facts, where the clause is the lookup of the candidate's key
  (`gmatch_weight_space`); several facts for one key add (`annotate_apply`,
  `two_weight_facts_add`);
* a grade stored in the row itself, read by the clause (`annotate_bind`). A weighted rule is
  this case, with the rule's weight as the stored grade.

Two clauses on one match multiply (`gmatch_mul`); two alternative clauses add (`gmatch_add`).

## What a clause can and cannot do

* The clause `1` is no clause (`gmatch_one`), and a clause valued in `{0, 1}` is a guard
  (`gmatch_crisp`).
* A graded answer is among the answers of the candidates whose value is not `0`
  (`support_gmatch_subset`), and over annotations that cannot cancel it is exactly those
  (`support_gmatch`). Where annotations can cancel, a clause can bring back an answer that the
  ungraded sum cancels (`grading_can_uncancel`): "a grade only removes answers" is true
  against the candidates, and false against the ungraded sum in a ring.
* A clause that agrees with another on the candidates found gives the same answer
  (`gmatch_congr`). So a clause computed from the bindings alone does not depend on when it
  is evaluated, and a clause that reads rows depends on the store exactly through the rows of
  the candidates' keys.
* Independent graded matches commute over a commutative `K` (`gmatch_comm`).

## Readings

A semiring homomorphism commutes with the graded match (`mapK_gmatch`), so a reading that is
a homomorphism may be taken at any point. A reading that is not additive may only be taken
at the end. Keeping the answers whose summed annotation reaches a threshold is one
(`prune_not_additive`); the squared modulus of an amplitude is another
(`AnnotatedRunsAmplitude.born_add` gives its exact defect, the interference term). A
threshold on a candidate's own value is different: it is a guard on the candidate
(`GSLT.Core.thresholdSelection_pointwise`). Where addition selects one of
its arguments, a property of a sum is a property of one summand (`selective_sum`), which is
what makes pruning before the sum sound for such annotations.

## Grades carried as data

`Multiset (Y × K)` holds answers that carry their grade as data, one entry per derivation;
`dbind` sequences them, multiplying grades. Summing the entries (`annotate`) is a morphism of
this sequencing onto `Ans.bind` (`annotate_dbind`). So a library that carries grades as data
and sums at the end computes `gmatch` (`annotate_map`). The data form keeps more: the number
of entries is not a function of the summed annotation (`occurrences_not_determined`), and
that number is what a consuming match needs.

## Relation to the modules this builds on

* `WeightedAnswerAlgebra` supplies `Ans K`, its sequencing and change of annotation.
* `WeightedMuScheduler.WeighClause` is the language of clauses; its `tensor` and `plus` are
  the product and sum of clauses here (`gmatch_tensor`, `gmatch_plus`).
* `GSLT.Core.GradedSelectionIrreducibility` proves, on bags, that a crisp clause is an `if`
  in the template (`GSLT.Core.whereDeliver_eq_ifDeliver`) and defines the graded delivery of
  a bag (`GSLT.Core.gradedDeliver`), whose sum is the graded match
  (`annotate_gradedDeliver`). It also proves that picking the best candidate is not a clause
  on one candidate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.GradedWhere

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.GSLT.Core.WeightedMuScheduler (WeighClause)
open Mettapedia.GSLT.Core (gradedDeliver)

universe u

variable {K : Type u} {X B B' Y Z Key : Type*}

/-! ## The graded match -/

section Semiring

variable [Semiring K]

/-- The graded match: each candidate `b` of the query `q` on the store `S` contributes its
value `ψ b` times the answers of its template `t b`. -/
noncomputable def gmatch (S : Ans K X) (q : X → Ans K B) (ψ : B → K) (t : B → Ans K Y) :
    Ans K Y :=
  Ans.bind (Ans.bind S q) fun b => ψ b • t b

/-- The clause `1` is no clause. -/
@[simp] theorem gmatch_one (S : Ans K X) (q : X → Ans K B) (t : B → Ans K Y) :
    gmatch S q (fun _ => 1) t = Ans.bind (Ans.bind S q) t := by
  simp [gmatch]

/-- The clause `0` answers nothing. -/
@[simp] theorem gmatch_zero (S : Ans K X) (q : X → Ans K B) (t : B → Ans K Y) :
    gmatch S q (fun _ => 0) t = 0 := by
  simp [gmatch]

/-- **Conservativity.** A clause valued in `{0, 1}` is a guard: the candidates where it holds
answer as before, and the others answer nothing. -/
theorem gmatch_crisp (P : B → Prop) [DecidablePred P] (S : Ans K X) (q : X → Ans K B)
    (t : B → Ans K Y) :
    gmatch S q (fun b => if P b then 1 else 0) t =
      Ans.bind (Ans.bind S q) fun b => if P b then t b else 0 := by
  unfold gmatch
  congr 1
  funext b
  by_cases h : P b <;> simp [h]

/-- One occurrence in the store contributes the graded answers of its own candidates. -/
theorem gmatch_pure (x : X) (q : X → Ans K B) (ψ : B → K) (t : B → Ans K Y) :
    gmatch (Ans.pure x) q ψ t = Ans.bind (q x) fun b => ψ b • t b := by
  simp [gmatch]

/-- **Occurrences contribute separately.** The graded match is additive in the store. -/
theorem gmatch_add_store (S S' : Ans K X) (q : X → Ans K B) (ψ : B → K) (t : B → Ans K Y) :
    gmatch (S + S') q ψ t = gmatch S q ψ t + gmatch S' q ψ t := by
  simp only [gmatch, Ans.add_bind]

/-- Scaling the store scales the answer. -/
theorem gmatch_smul_store (c : K) (S : Ans K X) (q : X → Ans K B) (ψ : B → K)
    (t : B → Ans K Y) : gmatch (c • S) q ψ t = c • gmatch S q ψ t := by
  simp only [gmatch, Ans.smul_bind]

/-- **Two clauses on one match multiply.** -/
theorem gmatch_mul (S : Ans K X) (q : X → Ans K B) (ψ₁ ψ₂ : B → K) (t : B → Ans K Y) :
    gmatch S q ψ₁ (fun b => ψ₂ b • t b) = gmatch S q (fun b => ψ₁ b * ψ₂ b) t := by
  simp only [gmatch, mul_smul]

/-- **Two alternative clauses add.** -/
theorem gmatch_add (S : Ans K X) (q : X → Ans K B) (ψ₁ ψ₂ : B → K) (t : B → Ans K Y) :
    gmatch S q (fun b => ψ₁ b + ψ₂ b) t = gmatch S q ψ₁ t + gmatch S q ψ₂ t := by
  unfold gmatch
  simp only [add_smul]
  exact Ans.bind_add_right _ (fun b => ψ₁ b • t b) (fun b => ψ₂ b • t b)

/-- The product of two clauses of the clause language is the two clauses on one match. -/
theorem gmatch_tensor (S : Ans K X) (q : X → Ans K B) (c d : WeighClause K B)
    (t : B → Ans K Y) :
    gmatch S q (fun b => WeighClause.eval b (.tensor c d)) t =
      gmatch S q (fun b => WeighClause.eval b c) (fun b => WeighClause.eval b d • t b) :=
  (gmatch_mul S q _ _ t).symm

/-- The sum of two clauses of the clause language is the two clauses as alternatives. -/
theorem gmatch_plus (S : Ans K X) (q : X → Ans K B) (c d : WeighClause K B)
    (t : B → Ans K Y) :
    gmatch S q (fun b => WeighClause.eval b (.plus c d)) t =
      gmatch S q (fun b => WeighClause.eval b c) t +
        gmatch S q (fun b => WeighClause.eval b d) t :=
  gmatch_add S q _ _ t

/-- **A clause matters only on the candidates found.** Two clauses that agree on the
candidates of the query give the same answer. -/
theorem gmatch_congr (S : Ans K X) (q : X → Ans K B) {ψ ψ' : B → K} (t : B → Ans K Y)
    (same : ∀ b ∈ (Ans.bind S q).support, ψ b = ψ' b) :
    gmatch S q ψ t = gmatch S q ψ' t := by
  show (Ans.bind S q).sum (fun b a => a • ψ b • t b) =
    (Ans.bind S q).sum (fun b a => a • ψ' b • t b)
  exact Finsupp.sum_congr fun b hb => by rw [same b hb]

/-! ## A grade written in the template -/

/-- The factor `k` as an answer that carries no value: what a grade written inside a template
contributes to its derivation. -/
noncomputable def factor (k : K) : Ans K Unit := Finsupp.single () k

theorem factor_bind (k : K) (A : Ans K Y) : Ans.bind (factor k) (fun _ => A) = k • A :=
  Ans.single_bind () k _

theorem factor_add (a b : K) : factor (a + b) = factor a + factor b :=
  Finsupp.single_add () a b

/-- **A grade written in the template is the clause on the match.** -/
theorem gmatch_eq_template (S : Ans K X) (q : X → Ans K B) (ψ : B → K) (t : B → Ans K Y) :
    gmatch S q ψ t =
      Ans.bind (Ans.bind S q) fun b => Ans.bind (factor (ψ b)) fun _ => t b := by
  simp only [gmatch, factor_bind]

/-! ## Weight facts in a space -/

/-- Reading the weight facts of one key: their annotations, as one factor. -/
theorem lookup_bind [DecidableEq Key] (W : Ans K Key) (k₀ : Key) :
    Ans.bind W (fun k => if k = k₀ then factor 1 else 0) = factor (W k₀) := by
  induction W using Finsupp.induction_linear with
  | zero => simp [factor]
  | add A A' hA hA' => rw [Ans.add_bind, hA, hA', Finsupp.add_apply, factor_add]
  | single k a =>
      rw [Ans.single_bind, Finsupp.single_apply]
      split_ifs
      · simp [factor]
      · simp [factor]

/-- **A join with a space of weight facts is the clause that looks the key up.** Each
candidate reads the weight facts of its key, and continues with its template. -/
theorem gmatch_weight_space [DecidableEq Key] (S : Ans K X) (q : X → Ans K B)
    (W : Ans K Key) (key : B → Key) (t : B → Ans K Y) :
    (Ans.bind (Ans.bind S q) fun b =>
        Ans.bind (Ans.bind W fun k => if k = key b then factor 1 else 0) fun _ => t b) =
      gmatch S q (fun b => W (key b)) t := by
  simp only [lookup_bind, factor_bind, gmatch]

/-! ## Grades stored in rows -/

/-- A bag of rows, each occurrence counted once. -/
noncomputable def plain (m : Multiset X) : Ans K X := (m.map fun x => (Ans.pure x : Ans K X)).sum

@[simp] theorem plain_zero : (plain (0 : Multiset X) : Ans K X) = 0 := by simp [plain]

@[simp] theorem plain_cons (x : X) (m : Multiset X) :
    (plain (x ::ₘ m) : Ans K X) = Ans.pure x + plain m := by simp [plain]

/-- A bag of rows that each hold a grade, read as rows annotated by their grades. -/
noncomputable def annotate (m : Multiset (X × K)) : Ans K X :=
  (m.map fun e => Finsupp.single e.1 e.2).sum

@[simp] theorem annotate_zero : annotate (0 : Multiset (X × K)) = 0 := by simp [annotate]

@[simp] theorem annotate_cons (e : X × K) (m : Multiset (X × K)) :
    annotate (e ::ₘ m) = Finsupp.single e.1 e.2 + annotate m := by simp [annotate]

theorem annotate_add (m n : Multiset (X × K)) : annotate (m + n) = annotate m + annotate n := by
  simp [annotate]

/-- **A grade stored in the row is a clause that reads it.** Matching rows annotated by their
grades is the graded match on the plain bag of the same rows, with the clause that reads each
row's stored grade. A weighted rule is this case. -/
theorem annotate_bind (m : Multiset (X × K)) (f : X → Ans K Y) :
    Ans.bind (annotate m) f =
      gmatch (plain m) Ans.pure (fun e => e.2) (fun e => f e.1) := by
  induction m using Multiset.induction_on with
  | empty => simp [gmatch]
  | cons e m ih =>
      rw [annotate_cons, plain_cons, Ans.add_bind, gmatch_add_store, ih, Ans.single_bind]
      congr 1
      simp [gmatch]

/-- **Several facts for one key add.** The annotation of a row is the sum of the grades of
its occurrences. -/
theorem annotate_apply [DecidableEq X] (m : Multiset (X × K)) (x : X) :
    annotate m x = ((m.filter fun e => e.1 = x).map Prod.snd).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons e m ih =>
      rw [annotate_cons, Finsupp.add_apply, ih, Finsupp.single_apply, Multiset.filter_cons]
      split_ifs <;> simp

/-- Two weight facts for the same key are one fact with the sum of their grades. -/
theorem two_weight_facts_add (k : Key) (a b : K) :
    annotate ({(k, a), (k, b)} : Multiset (Key × K)) = Finsupp.single k (a + b) := by
  simp [annotate, Finsupp.single_add]

/-! ## Grades carried as data -/

/-- Sequencing answers that carry their grade as data: the bag's sequencing, with the grades
multiplied along each derivation. -/
def dbind (m : Multiset (X × K)) (f : X → Multiset (Y × K)) : Multiset (Y × K) :=
  m.bind fun e => (f e.1).map fun r => (r.1, e.2 * r.2)

theorem annotate_map_mul (k : K) (n : Multiset (Y × K)) :
    annotate (n.map fun r => (r.1, k * r.2)) = k • annotate n := by
  induction n using Multiset.induction_on with
  | empty => simp
  | cons r n ih => simp [ih, smul_add, Finsupp.smul_single]

/-- **Summing at the end.** Carrying grades as data through a sequence of steps and summing
the entries afterwards is the weighted sequencing of the summed answers. -/
theorem annotate_dbind (m : Multiset (X × K)) (f : X → Multiset (Y × K)) :
    annotate (dbind m f) = Ans.bind (annotate m) fun x => annotate (f x) := by
  induction m using Multiset.induction_on with
  | empty => simp [dbind]
  | cons e m ih =>
      have step : dbind (e ::ₘ m) f = ((f e.1).map fun r => (r.1, e.2 * r.2)) + dbind m f := by
        simp [dbind]
      rw [step, annotate_add, annotate_map_mul, ih, annotate_cons, Ans.add_bind,
        Ans.single_bind]

/-- **A bag of candidates that each answer one instance with its grade as data sums to the
graded match** on the plain bag of the candidates. -/
theorem annotate_map (m : Multiset B) (y : B → Y) (ψ : B → K) :
    annotate (m.map fun b => (y b, ψ b)) =
      gmatch (plain m) Ans.pure ψ (fun b => Ans.pure (y b)) := by
  induction m using Multiset.induction_on with
  | empty => simp [gmatch]
  | cons b m ih =>
      rw [Multiset.map_cons, annotate_cons, plain_cons, gmatch_add_store, ih]
      congr 1
      simp [gmatch, Ans.pure, Finsupp.smul_single, Ans.single_bind]

/-- The graded delivery of a bag, summed, is the graded match. -/
theorem annotate_gradedDeliver {V : Type*} [CommSemiring V] (ψ : B → V) (y : B → Y)
    (m : Multiset B) :
    annotate ((gradedDeliver ψ y m).map Prod.swap) =
      gmatch (plain m) Ans.pure ψ (fun b => Ans.pure (y b)) := by
  rw [← annotate_map]
  simp [gradedDeliver]

/-- **The data form keeps the occurrences.** Two bags of graded rows with the same summed
annotation can hold different numbers of occurrences, so how many times a consuming match can
fire is not a function of the annotation. -/
theorem occurrences_not_determined :
    annotate ({((), 1), ((), 1)} : Multiset (Unit × ℕ)) =
        annotate ({((), 2)} : Multiset (Unit × ℕ)) ∧
      Multiset.card ({((), 1), ((), 1)} : Multiset (Unit × ℕ)) ≠
        Multiset.card ({((), 2)} : Multiset (Unit × ℕ)) := by
  refine ⟨?_, by decide⟩
  simp [annotate, ← Finsupp.single_add]

/-! ## Readings -/

/-- **A homomorphism of annotations commutes with the graded match.** -/
theorem mapK_gmatch {L : Type*} [Semiring L] (φ : K →+* L) (S : Ans K X) (q : X → Ans K B)
    (ψ : B → K) (t : B → Ans K Y) :
    Ans.mapK φ (gmatch S q ψ t) =
      gmatch (Ans.mapK φ S) (fun x => Ans.mapK φ (q x)) (fun b => φ (ψ b))
        (fun b => Ans.mapK φ (t b)) := by
  simp only [gmatch, Ans.mapK_bind, Ans.mapK_smul]

open Classical in
/-- **A graded answer comes from a candidate whose value is not `0`.** -/
theorem support_gmatch_subset (S : Ans K X) (q : X → Ans K B) (ψ : B → K) (t : B → Ans K Y) :
    (gmatch S q ψ t).support ⊆
      ((Ans.bind S q).support.filter fun b => ψ b ≠ 0).biUnion fun b => (t b).support := by
  intro y hy
  rw [Finsupp.mem_support_iff, gmatch, Ans.bind_apply, Finsupp.sum] at hy
  obtain ⟨b, hb, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, ?_⟩, ?_⟩
  · intro h0
    exact hne (by simp [h0])
  · rw [Finsupp.mem_support_iff]
    intro h0
    exact hne (by simp [h0])

end Semiring

section Possibility

variable [Semiring K] [PartialOrder K] [CanonicallyOrderedAdd K] [NoZeroDivisors K]

open Classical in
/-- **Where annotations cannot cancel, the graded answers are exactly those of the candidates
whose value is not `0`.** -/
theorem support_gmatch (S : Ans K X) (q : X → Ans K B) (ψ : B → K) (t : B → Ans K Y) :
    (gmatch S q ψ t).support =
      ((Ans.bind S q).support.filter fun b => ψ b ≠ 0).biUnion fun b => (t b).support := by
  refine Finset.Subset.antisymm (support_gmatch_subset S q ψ t) ?_
  intro y hy
  obtain ⟨b, hb, hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨hb, hψ⟩ := Finset.mem_filter.mp hb
  rw [gmatch, Ans.support_bind]
  refine Finset.mem_biUnion.mpr ⟨b, hb, ?_⟩
  rw [Finsupp.mem_support_iff] at hy ⊢
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact mul_ne_zero hψ hy

end Possibility

section CommSemiring

variable [CommSemiring K]

/-- **Grade before or after the template.** Over commutative annotations, scaling a
candidate's template is scaling each of its results. -/
theorem gmatch_post (S : Ans K X) (q : X → Ans K B) (ψ : B → K) (t : B → Ans K Y) :
    gmatch S q ψ t =
      Ans.bind (Ans.bind S q) fun b => Ans.bind (t b) fun y => ψ b • Ans.pure y := by
  unfold gmatch
  congr 1
  funext b
  rw [Ans.bind_smul_right, Ans.bind_pure]

/-- **Independent graded matches commute** over commutative annotations. -/
theorem gmatch_comm (S : Ans K X) (q : X → Ans K B) (ψ : B → K) (S' : Ans K Z)
    (q' : Z → Ans K B') (ψ' : B' → K) (t : B → B' → Ans K Y) :
    gmatch S q ψ (fun b => gmatch S' q' ψ' (t b)) =
      gmatch S' q' ψ' (fun b' => gmatch S q ψ (fun b => t b b')) := by
  unfold gmatch
  simp only [← Ans.bind_smul_right]
  rw [Ans.bind_comm]
  congr 1
  funext b'
  congr 1
  funext b
  rw [smul_comm]

end CommSemiring

/-! ## Controls -/

/-- **A clause can bring back an answer that the ungraded sum cancels.** With integer
annotations `1` and `-1` on two candidates of one answer, the plain match answers nothing and
the match graded by `1` and `0` answers. -/
theorem grading_can_uncancel :
    ∃ (S : Ans ℤ Bool) (ψ : Bool → ℤ),
      Ans.bind S (fun _ => (Ans.pure () : Ans ℤ Unit)) = 0 ∧
        gmatch S Ans.pure ψ (fun _ => (Ans.pure () : Ans ℤ Unit)) ≠ 0 := by
  refine ⟨Finsupp.single true 1 + Finsupp.single false (-1), fun b => if b then 1 else 0, ?_, ?_⟩
  · rw [Ans.add_bind, Ans.single_bind, Ans.single_bind]
    simp
  · rw [gmatch, Ans.bind_pure, Ans.add_bind, Ans.single_bind, Ans.single_bind]
    simp [Ans.pure]

/-- Keep the answers whose count reaches a threshold. -/
noncomputable def prune (θ : ℕ) (A : Ans ℕ Y) : Ans ℕ Y := A.filter fun y => θ ≤ A y

/-- **Pruning by a threshold is not additive**: two derivations of one answer, each below the
threshold, reach it together. Pruning each derivation loses the answer. -/
theorem prune_not_additive :
    prune 2 (Finsupp.single () 1 + Finsupp.single () 1) ≠
      prune 2 (Finsupp.single () 1) + prune 2 (Finsupp.single () 1) := by
  intro h
  have := DFunLike.congr_fun h ()
  simp [prune] at this

/-- **Where addition selects, a property of a sum is a property of a summand.** This is the
condition under which pruning before the sum loses nothing. -/
theorem selective_sum [Add K] (selects : ∀ a b : K, a + b = a ∨ a + b = b) (P : K → Prop)
    {a b : K} (h : P (a + b)) : P a ∨ P b := by
  rcases selects a b with e | e
  · exact Or.inl (e ▸ h)
  · exact Or.inr (e ▸ h)

end Mettapedia.Languages.MeTTa.GradedWhere
