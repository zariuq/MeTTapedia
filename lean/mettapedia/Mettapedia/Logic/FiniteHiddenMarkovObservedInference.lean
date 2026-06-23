import Mettapedia.Logic.FiniteHiddenMarkovModel
import Mettapedia.Logic.MarkovDeFinettiMomentProblem
import Mettapedia.Logic.MarkovDeFinettiSequenceKernel
import Mettapedia.Logic.BinaryEvidence

/-!
# Observed-Only Inference for Finite Hidden Markov Models

This file formalizes the first honest observed-only inference layer for finite
HMMs:

* backward messages,
* initial-state backward decomposition of the observed-word law,
* forward terminal-state masses,
* the filtering mass identity.

Positive example:
* the observed-word probability is the sum of terminal latent-state masses.

Negative example:
* this does not yet claim full smoothing or hidden-state posterior recovery as
  an additive WM carrier.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.FiniteHiddenMarkovObservedInference

open Mettapedia.Logic
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.Logic.FiniteHiddenMarkovModel
open Mettapedia.Logic.EvidenceQuantale
open scoped BigOperators ENNReal NNReal

variable {latent obs : ℕ}

lemma ofFn_snoc {α : Type*} {n : ℕ} (a : α) (g : Fin n → α) :
    List.ofFn (Fin.snoc g a) = List.ofFn g ++ [a] := by
  have hlist : List.ofFn (Fin.snoc g a) = (List.ofFn g).concat a := by
    simpa [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last] using
      (List.ofFn_succ' (f := Fin.snoc g a))
  rw [hlist]
  simp [List.concat_eq_append]

lemma ofFn_precompose_cast {α : Type*} {m n : ℕ}
    (h : m = n) (f : Fin m → α) :
    List.ofFn (fun i : Fin n => f (Fin.cast h.symm i)) = List.ofFn f := by
  subst h
  simp

/-! ## Backward messages -/

/-- Backward continuation mass from a current latent state. -/
def backwardMessage (θ : FiniteHMMParam latent obs) :
    Fin latent → List (Fin obs) → ℝ≥0∞
  | _, [] => 1
  | x, y :: ys =>
      ∑ x' : Fin latent,
        (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
          (emissionProb θ x' y : ℝ≥0∞) *
            backwardMessage θ x' ys

@[simp] theorem backwardMessage_nil
    (θ : FiniteHMMParam latent obs) (x : Fin latent) :
    backwardMessage θ x [] = 1 := rfl

@[simp] theorem backwardMessage_cons
    (θ : FiniteHMMParam latent obs) (x : Fin latent)
    (y : Fin obs) (ys : List (Fin obs)) :
    backwardMessage θ x (y :: ys) =
      ∑ x' : Fin latent,
        (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
          (emissionProb θ x' y : ℝ≥0∞) *
            backwardMessage θ x' ys := rfl

/-- Backward message as the explicit latent-tail sum under `wordProbAux`. -/
theorem backwardMessage_eq_sum_wordProbAux_observationWeight
    (θ : FiniteHMMParam latent obs) (x : Fin latent) :
    ∀ ys : List (Fin obs),
      backwardMessage θ x ys =
        ∑ xs : Fin ys.length → Fin latent,
          (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
            observationWeight θ (List.ofFn xs) ys
  | [] => by
      simp [backwardMessage, MarkovDeFinettiHard.wordProbAux]
  | y :: ys => by
      let n := ys.length
      change backwardMessage θ x (y :: ys) =
        ∑ xs : Fin (n + 1) → Fin latent,
          (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
            observationWeight θ (List.ofFn xs) (y :: ys)
      have hdecomp :
          (∑ xs : Fin (n + 1) → Fin latent,
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) (y :: ys)) =
            ∑ p : Fin latent × (Fin n → Fin latent),
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn (Fin.cons p.1 p.2)) :
                  ℝ≥0∞) *
                observationWeight θ (List.ofFn (Fin.cons p.1 p.2)) (y :: ys) := by
        simpa [n] using
          (Fintype.sum_equiv
            (Fin.consEquiv (n := n) (α := fun _ : Fin (n + 1) => Fin latent))
            (fun p : Fin latent × (Fin n → Fin latent) =>
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn (Fin.cons p.1 p.2)) :
                  ℝ≥0∞) *
                observationWeight θ (List.ofFn (Fin.cons p.1 p.2)) (y :: ys))
            (fun xs : Fin (n + 1) → Fin latent =>
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) (y :: ys))
            (fun _ => rfl)).symm
      rw [backwardMessage_cons, hdecomp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl ?_
      intro x' hx'
      rw [backwardMessage_eq_sum_wordProbAux_observationWeight θ x' ys]
      have hmul :
          (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
              (emissionProb θ x' y : ℝ≥0∞) *
                ∑ xs : Fin n → Fin latent,
                  (wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                    observationWeight θ (List.ofFn xs) ys =
            ∑ xs : Fin n → Fin latent,
              (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
                ((emissionProb θ x' y : ℝ≥0∞) *
                  ((wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                    observationWeight θ (List.ofFn xs) ys)) := by
        calc
          ((stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
              (emissionProb θ x' y : ℝ≥0∞)) *
              ∑ xs : Fin n → Fin latent,
                (wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                  observationWeight θ (List.ofFn xs) ys
            =
              ∑ xs : Fin n → Fin latent,
                ((stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
                  (emissionProb θ x' y : ℝ≥0∞)) *
                    ((wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                      observationWeight θ (List.ofFn xs) ys) := by
                        simpa using
                          (Finset.mul_sum
                            (s := (Finset.univ : Finset (Fin n → Fin latent)))
                            (a := (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
                              (emissionProb θ x' y : ℝ≥0∞))
                            (f := fun xs : Fin n → Fin latent =>
                              (wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) :
                                  ℝ≥0∞) *
                                observationWeight θ (List.ofFn xs) ys))
          _ =
              ∑ xs : Fin n → Fin latent,
                (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
                  ((emissionProb θ x' y : ℝ≥0∞) *
                    ((wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                      observationWeight θ (List.ofFn xs) ys)) := by
                        refine Finset.sum_congr rfl ?_
                        intro xs hxs
                        simp [mul_assoc]
      calc
        (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
            (emissionProb θ x' y : ℝ≥0∞) *
            ∑ xs : Fin n → Fin latent,
              (wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) ys
          =
            ∑ xs : Fin n → Fin latent,
              (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
                ((emissionProb θ x' y : ℝ≥0∞) *
                  ((wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                    observationWeight θ (List.ofFn xs) ys)) := hmul
        _ =
            ∑ xs : Fin n → Fin latent,
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn (Fin.cons x' xs)) :
                  ℝ≥0∞) *
                observationWeight θ (List.ofFn (Fin.cons x' xs)) (y :: ys) := by
                  refine Finset.sum_congr rfl ?_
                  intro xs hxs
                  simp [MarkovDeFinettiHard.wordProbAux,
                    mul_assoc, mul_left_comm, mul_comm]

/-- The observed-word law decomposes through the initial latent state and the
backward continuation message. -/
theorem observedWordProb_cons_eq_sum_init_mul_emission_mul_backward
    (θ : FiniteHMMParam latent obs) (y : Fin obs) (ys : List (Fin obs)) :
    observedWordProb θ (y :: ys) =
      ∑ x : Fin latent,
        (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
          (emissionProb θ x y : ℝ≥0∞) *
            backwardMessage θ x ys := by
  let n := ys.length
  have hdecomp :
      observedWordProb θ (y :: ys) =
        ∑ p : Fin latent × (Fin n → Fin latent),
          wordProb (k := latent) θ.latentParam (List.ofFn (Fin.cons p.1 p.2)) *
            observationWeight θ (List.ofFn (Fin.cons p.1 p.2)) (y :: ys) := by
    unfold observedWordProb
    simpa [n] using
      (Fintype.sum_equiv
        (Fin.consEquiv (n := n) (α := fun _ : Fin (n + 1) => Fin latent))
        (fun p : Fin latent × (Fin n → Fin latent) =>
          wordProb (k := latent) θ.latentParam (List.ofFn (Fin.cons p.1 p.2)) *
            observationWeight θ (List.ofFn (Fin.cons p.1 p.2)) (y :: ys))
        (fun xs : Fin (n + 1) → Fin latent =>
          wordProb (k := latent) θ.latentParam (List.ofFn xs) *
            observationWeight θ (List.ofFn xs) (y :: ys))
        (fun _ => rfl)).symm
  rw [hdecomp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro x hx
  symm
  rw [backwardMessage_eq_sum_wordProbAux_observationWeight θ x ys]
  have hmul :
      (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
          (emissionProb θ x y : ℝ≥0∞) *
            ∑ xs : Fin n → Fin latent,
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) ys =
        ∑ xs : Fin n → Fin latent,
          (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
            ((emissionProb θ x y : ℝ≥0∞) *
              ((wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) ys)) := by
    calc
      ((initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
          (emissionProb θ x y : ℝ≥0∞)) *
          ∑ xs : Fin n → Fin latent,
            (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
              observationWeight θ (List.ofFn xs) ys
        =
          ∑ xs : Fin n → Fin latent,
            ((initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
              (emissionProb θ x y : ℝ≥0∞)) *
                ((wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                  observationWeight θ (List.ofFn xs) ys) := by
                    simpa using
                      (Finset.mul_sum
                        (s := (Finset.univ : Finset (Fin n → Fin latent)))
                        (a := (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
                          (emissionProb θ x y : ℝ≥0∞))
                        (f := fun xs : Fin n → Fin latent =>
                          (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) :
                              ℝ≥0∞) *
                            observationWeight θ (List.ofFn xs) ys))
      _ =
          ∑ xs : Fin n → Fin latent,
            (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
              ((emissionProb θ x y : ℝ≥0∞) *
                ((wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                  observationWeight θ (List.ofFn xs) ys)) := by
                    refine Finset.sum_congr rfl ?_
                    intro xs hxs
                    simp [mul_assoc]
  calc
    (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
        (emissionProb θ x y : ℝ≥0∞) *
        ∑ xs : Fin n → Fin latent,
          (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
            observationWeight θ (List.ofFn xs) ys
      =
        ∑ xs : Fin n → Fin latent,
          (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
            ((emissionProb θ x y : ℝ≥0∞) *
              ((wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) ys)) := hmul
    _ =
        ∑ xs : Fin n → Fin latent,
          wordProb (k := latent) θ.latentParam (List.ofFn (Fin.cons x xs)) *
            observationWeight θ (List.ofFn (Fin.cons x xs)) (y :: ys) := by
              refine Finset.sum_congr rfl ?_
              intro xs hxs
              simp [MarkovDeFinettiHard.wordProb, MarkovDeFinettiHard.wordProbNN,
                mul_assoc, mul_left_comm, mul_comm]

/-! ## Forward terminal-state masses -/

/-- Forward message: joint mass of an observed word together with the event
that the final latent state equals `x`. -/
def forwardMessage (θ : FiniteHMMParam latent obs) :
    List (Fin obs) → Fin latent → ℝ≥0∞
  | [], x => (initProb (k := latent) θ.latentParam x : ℝ≥0∞)
  | y :: ys, x =>
      ∑ xs : Fin ys.length → Fin latent,
        wordProb (k := latent) θ.latentParam (List.ofFn xs ++ [x]) *
          observationWeight θ (List.ofFn xs ++ [x]) (y :: ys)

@[simp] theorem forwardMessage_nil
    (θ : FiniteHMMParam latent obs) (x : Fin latent) :
    forwardMessage θ [] x = (initProb (k := latent) θ.latentParam x : ℝ≥0∞) := rfl

@[simp] theorem forwardMessage_singleton
    (θ : FiniteHMMParam latent obs) (y : Fin obs) (x : Fin latent) :
    forwardMessage θ [y] x =
      (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
        (emissionProb θ x y : ℝ≥0∞) := by
  simp [forwardMessage, MarkovDeFinettiHard.wordProb, MarkovDeFinettiHard.wordProbNN,
    MarkovDeFinettiHard.wordProbAux, observationWeight]

/-- The observed-word law is the terminal-state sum of the forward message. -/
theorem observedWordProb_eq_sum_forwardMessage
    (θ : FiniteHMMParam latent obs) :
    ∀ ys : List (Fin obs),
      observedWordProb θ ys = ∑ x : Fin latent, forwardMessage θ ys x
  | [] => by
      rw [observedWordProb_nil]
      simp [forwardMessage, initProb_sum_enn]
  | y :: ys => by
      let n := ys.length
      have hdecomp :
          observedWordProb θ (y :: ys) =
            ∑ p : Fin latent × (Fin n → Fin latent),
              wordProb (k := latent) θ.latentParam (List.ofFn (Fin.snoc p.2 p.1)) *
                observationWeight θ (List.ofFn (Fin.snoc p.2 p.1)) (y :: ys) := by
        unfold observedWordProb
        simpa [n] using
          (Fintype.sum_equiv
            (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin latent))
            (fun p : Fin latent × (Fin n → Fin latent) =>
              wordProb (k := latent) θ.latentParam (List.ofFn (Fin.snoc p.2 p.1)) *
                observationWeight θ (List.ofFn (Fin.snoc p.2 p.1)) (y :: ys))
            (fun xs : Fin (n + 1) → Fin latent =>
              wordProb (k := latent) θ.latentParam (List.ofFn xs) *
                observationWeight θ (List.ofFn xs) (y :: ys))
            (fun _ => rfl)).symm
      rw [hdecomp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hsnoc :
          ∑ xs : Fin n → Fin latent,
            wordProb (k := latent) θ.latentParam (List.ofFn (Fin.snoc xs x)) *
              observationWeight θ (List.ofFn (Fin.snoc xs x)) (y :: ys) =
            ∑ xs : Fin n → Fin latent,
              wordProb (k := latent) θ.latentParam (List.ofFn xs ++ [x]) *
                observationWeight θ (List.ofFn xs ++ [x]) (y :: ys) := by
        refine Finset.sum_congr rfl ?_
        intro xs hxs
        rw [ofFn_snoc (a := x) (g := xs)]
      simpa [forwardMessage] using hsnoc

/-- Appending a latent tail and an observed tail factors the observation
likelihood when the split boundary is aligned by length. This local helper is
placed here because forward-message snoc recursion depends on it. -/
theorem observationWeight_append_of_length_eq_aux
    (θ : FiniteHMMParam latent obs) :
    ∀ xs : List (Fin latent), ∀ zs : List (Fin obs),
      xs.length = zs.length →
      ∀ ys : List (Fin latent), ∀ us : List (Fin obs),
        observationWeight θ (xs ++ ys) (zs ++ us) =
          observationWeight θ xs zs * observationWeight θ ys us
  | [], [], hlen, ys, us => by
      simp [FiniteHiddenMarkovModel.observationWeight]
  | [], z :: zs, hlen, ys, us => by
      cases hlen
  | x :: xs, [], hlen, ys, us => by
      cases hlen
  | x :: xs, z :: zs, hlen, ys, us => by
      have htail : xs.length = zs.length := Nat.succ.inj hlen
      simp [FiniteHiddenMarkovModel.observationWeight,
        observationWeight_append_of_length_eq_aux (θ := θ) (xs := xs) (zs := zs) (ys := ys)
          (us := us) htail,
        mul_assoc]

/-- Snoc recursion for forward messages along any nonempty observed prefix. -/
theorem forwardMessage_append_singleton_of_ne_nil
    (θ : FiniteHMMParam latent obs)
    (ys : List (Fin obs)) (hys : ys ≠ [])
    (y : Fin obs) (x : Fin latent) :
    forwardMessage θ (ys ++ [y]) x =
      ∑ u : Fin latent,
        forwardMessage θ ys u *
          (stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
            (emissionProb θ x y : ℝ≥0∞) := by
  cases ys with
  | nil =>
      contradiction
  | cons z zs =>
      let n := zs.length
      have hfront :
          forwardMessage θ ((z :: zs) ++ [y]) x =
            ∑ ws : Fin (n + 1) → Fin latent,
              wordProb (k := latent) θ.latentParam (List.ofFn ws ++ [x]) *
                observationWeight θ (List.ofFn ws ++ [x]) ((z :: zs) ++ [y]) := by
        unfold forwardMessage
        let hlen : (zs ++ [y]).length = n + 1 := by
          simp [n]
        let e :
            (Fin ((zs ++ [y]).length) → Fin latent) ≃
              (Fin (n + 1) → Fin latent) :=
          { toFun := fun ws i => ws (Fin.cast hlen.symm i)
            invFun := fun ws i => ws (Fin.cast hlen i)
            left_inv := by
              intro ws
              funext i
              simp
            right_inv := by
              intro ws
              funext i
              simp }
        refine Fintype.sum_equiv e
          (fun ws : Fin ((zs ++ [y]).length) → Fin latent =>
            wordProb (k := latent) θ.latentParam (List.ofFn ws ++ [x]) *
              observationWeight θ (List.ofFn ws ++ [x]) ((z :: zs) ++ [y]))
          (fun ws : Fin (n + 1) → Fin latent =>
            wordProb (k := latent) θ.latentParam (List.ofFn ws ++ [x]) *
              observationWeight θ (List.ofFn ws ++ [x]) ((z :: zs) ++ [y])) ?_
        intro ws
        dsimp [e]
        rw [ofFn_precompose_cast (h := hlen) (f := ws)]
      rw [hfront]
      have hmain :
        (∑ ws : Fin (n + 1) → Fin latent,
          wordProb (k := latent) θ.latentParam (List.ofFn ws ++ [x]) *
            observationWeight θ (List.ofFn ws ++ [x]) ((z :: zs) ++ [y])) =
        ∑ u : Fin latent,
          forwardMessage θ (z :: zs) u *
            (stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
              (emissionProb θ x y : ℝ≥0∞) := by
        have hdecomp :
            (∑ ws : Fin (n + 1) → Fin latent,
              wordProb (k := latent) θ.latentParam
                  (List.ofFn ws ++ [x]) *
                observationWeight θ
                  (List.ofFn ws ++ [x]) ((z :: zs) ++ [y])) =
              ∑ p : Fin latent × (Fin n → Fin latent),
                wordProb (k := latent) θ.latentParam
                    (List.ofFn (Fin.snoc p.2 p.1) ++ [x]) *
                  observationWeight θ
                    (List.ofFn (Fin.snoc p.2 p.1) ++ [x]) ((z :: zs) ++ [y]) := by
          simpa [n] using
            (Fintype.sum_equiv
              (Fin.snocEquiv (α := fun _ : Fin (n + 1) => Fin latent))
              (fun p : Fin latent × (Fin n → Fin latent) =>
                wordProb (k := latent) θ.latentParam
                    (List.ofFn (Fin.snoc p.2 p.1) ++ [x]) *
                  observationWeight θ
                    (List.ofFn (Fin.snoc p.2 p.1) ++ [x]) ((z :: zs) ++ [y]))
              (fun ws : Fin (n + 1) → Fin latent =>
                wordProb (k := latent) θ.latentParam (List.ofFn ws ++ [x]) *
                  observationWeight θ (List.ofFn ws ++ [x]) ((z :: zs) ++ [y]))
              (fun _ => rfl)).symm
        rw [hdecomp, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl ?_
        intro u hu
        have hprefix :
            ∑ xs : Fin n → Fin latent,
              wordProb (k := latent) θ.latentParam (List.ofFn (Fin.snoc xs u)) *
                observationWeight θ (List.ofFn (Fin.snoc xs u)) (z :: zs) =
              forwardMessage θ (z :: zs) u := by
          have hsnoc :
              ∑ xs : Fin n → Fin latent,
                wordProb (k := latent) θ.latentParam (List.ofFn (Fin.snoc xs u)) *
                  observationWeight θ (List.ofFn (Fin.snoc xs u)) (z :: zs) =
                ∑ xs : Fin n → Fin latent,
                  wordProb (k := latent) θ.latentParam (List.ofFn xs ++ [u]) *
                    observationWeight θ (List.ofFn xs ++ [u]) (z :: zs) := by
            refine Finset.sum_congr rfl ?_
            intro xs hxs
            rw [ofFn_snoc]
          simpa [forwardMessage, n] using hsnoc
        calc
          ∑ xs : Fin n → Fin latent,
            wordProb (k := latent) θ.latentParam
                  (List.ofFn (Fin.snoc xs u) ++ [x]) *
                observationWeight θ
                  (List.ofFn (Fin.snoc xs u) ++ [x]) ((z :: zs) ++ [y]) =
              ∑ xs : Fin n → Fin latent,
                (wordProb (k := latent) θ.latentParam (List.ofFn (Fin.snoc xs u)) *
                  observationWeight θ (List.ofFn (Fin.snoc xs u)) (z :: zs)) *
                    ((stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
                      (emissionProb θ x y : ℝ≥0∞)) := by
                refine Finset.sum_congr rfl ?_
                intro xs hxs
                rw [ofFn_snoc]
                have hlen : (List.ofFn xs ++ [u]).length = (z :: zs).length := by
                  simp [n]
                have hlast : (List.ofFn xs ++ [u]).getLast (by simp) = u := by
                  simp
                rw [MarkovDeFinettiSequenceKernel.wordProb_append_singleton_of_ne_nil
                  (k := latent) (θ := θ.latentParam) (ys := List.ofFn xs ++ [u]) (b := x) (by simp)]
                rw [hlast]
                rw [observationWeight_append_of_length_eq_aux
                  (θ := θ) (xs := List.ofFn xs ++ [u]) (zs := z :: zs) hlen
                  (ys := [x]) (us := [y])]
                simp [FiniteHiddenMarkovModel.observationWeight,
                  mul_assoc, mul_left_comm, mul_comm]
            _ =
              (∑ xs : Fin n → Fin latent,
                wordProb (k := latent) θ.latentParam (List.ofFn (Fin.snoc xs u)) *
                  observationWeight θ (List.ofFn (Fin.snoc xs u)) (z :: zs)) *
                ((stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
                  (emissionProb θ x y : ℝ≥0∞)) := by
                    rw [Finset.sum_mul]
            _ =
              forwardMessage θ (z :: zs) u *
                ((stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
                  (emissionProb θ x y : ℝ≥0∞)) := by
                    rw [hprefix]
            _ =
              forwardMessage θ (z :: zs) u *
                (stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
                  (emissionProb θ x y : ℝ≥0∞) := by
                    ac_rfl
      exact hmain

/-! ## Filtering masses -/

/-- Unnormalized filtering mass at the final latent state after observing the
prefix `ys`. -/
def filteringMass (θ : FiniteHMMParam latent obs)
    (ys : List (Fin obs)) (x : Fin latent) : ℝ≥0∞ :=
  forwardMessage θ ys x

theorem filteringMass_sum_eq_observedWordProb
    (θ : FiniteHMMParam latent obs) (ys : List (Fin obs)) :
    ∑ x : Fin latent, filteringMass θ ys x = observedWordProb θ ys := by
  simpa [filteringMass] using (observedWordProb_eq_sum_forwardMessage θ ys).symm

/-- Observed-word probabilities are finite, since they are cylinder masses under
the observed sequence probability measure. -/
theorem observedWordProb_ne_top
    (θ : FiniteHMMParam latent obs) (ys : List (Fin obs)) :
    observedWordProb θ ys ≠ ⊤ := by
  rw [← observedSequenceMeasure_cylinder_eq_observedWordProb (latent := latent) (obs := obs)
    (θ := θ) ys]
  have hmono :
      observedSequenceMeasure (latent := latent) (obs := obs) θ
        (MarkovDeFinettiRecurrence.cylinder (k := obs) ys) ≤
      observedSequenceMeasure (latent := latent) (obs := obs) θ Set.univ := by
    exact MeasureTheory.measure_mono (by intro ω hω; simp)
  exact ne_top_of_le_ne_top (by simp) hmono

/-- Normalized filtering posterior mass at the final latent state after
observing the prefix `ys`. -/
def filteringPosteriorMass (θ : FiniteHMMParam latent obs)
    (ys : List (Fin obs)) (x : Fin latent) : ℝ≥0∞ :=
  filteringMass θ ys x / observedWordProb θ ys

theorem filteringPosteriorMass_sum_eq_one
    (θ : FiniteHMMParam latent obs) (ys : List (Fin obs))
    (hys : observedWordProb θ ys ≠ 0) :
    ∑ x : Fin latent, filteringPosteriorMass θ ys x = 1 := by
  have htop : observedWordProb θ ys ≠ ⊤ := observedWordProb_ne_top (θ := θ) ys
  unfold filteringPosteriorMass
  calc
    ∑ x : Fin latent, filteringMass θ ys x / observedWordProb θ ys
      = ∑ x : Fin latent, filteringMass θ ys x * (observedWordProb θ ys)⁻¹ := by
          simp [div_eq_mul_inv]
    _ = (∑ x : Fin latent, filteringMass θ ys x) * (observedWordProb θ ys)⁻¹ := by
          rw [Finset.sum_mul]
    _ = observedWordProb θ ys * (observedWordProb θ ys)⁻¹ := by
          rw [filteringMass_sum_eq_observedWordProb]
    _ = 1 := ENNReal.mul_inv_cancel hys htop

theorem filteringPosteriorMass_le_one
    (θ : FiniteHMMParam latent obs) (ys : List (Fin obs))
    (q : Fin latent) (hys : observedWordProb θ ys ≠ 0) :
    filteringPosteriorMass θ ys q ≤ 1 := by
  calc
    filteringPosteriorMass θ ys q ≤ ∑ x : Fin latent, filteringPosteriorMass θ ys x := by
      exact Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ q)
    _ = 1 := filteringPosteriorMass_sum_eq_one (θ := θ) (ys := ys) hys

/-- Binary WM-style evidence view induced by the observed-only filtering
posterior: positive mass for the queried latent state and negative mass its
posterior complement. -/
noncomputable def filteringPosteriorEvidence
    (θ : FiniteHMMParam latent obs)
    (ys : List (Fin obs)) (q : Fin latent) : BinaryEvidence :=
  ⟨filteringPosteriorMass θ ys q, 1 - filteringPosteriorMass θ ys q⟩

theorem filteringPosteriorEvidence_toStrength_eq_filteringPosteriorMass
    (θ : FiniteHMMParam latent obs) (ys : List (Fin obs))
    (q : Fin latent) (hys : observedWordProb θ ys ≠ 0) :
    BinaryEvidence.toStrength (filteringPosteriorEvidence θ ys q) =
      filteringPosteriorMass θ ys q := by
  have hq : filteringPosteriorMass θ ys q ≤ 1 :=
    filteringPosteriorMass_le_one (θ := θ) (ys := ys) q hys
  have htotal : (filteringPosteriorEvidence θ ys q).total = 1 := by
    unfold filteringPosteriorEvidence BinaryEvidence.total
    simpa [add_comm] using
      (tsub_add_cancel_of_le hq : 1 - filteringPosteriorMass θ ys q + filteringPosteriorMass θ ys q = 1)
  unfold BinaryEvidence.toStrength
  rw [if_neg]
  · rw [htotal]
    simp [filteringPosteriorEvidence]
  · simp [htotal]

/-! ## Smoothing masses -/

/-- Probability of appending a latent tail after a fixed terminal latent state. -/
theorem wordProbAux_append_terminal
    (θ : MarkovParam latent) (a x : Fin latent) :
    ∀ xs zs : List (Fin latent),
      (wordProbAux (k := latent) θ a ((xs ++ [x]) ++ zs) : ℝ≥0∞) =
        (wordProbAux (k := latent) θ a (xs ++ [x]) : ℝ≥0∞) *
          (wordProbAux (k := latent) θ x zs : ℝ≥0∞)
  | [], zs => by
      simp [MarkovDeFinettiHard.wordProbAux]
  | b :: xs, zs => by
      simp only [MarkovDeFinettiHard.wordProbAux, List.cons_append, ENNReal.coe_mul]
      rw [wordProbAux_append_terminal (θ := θ) (a := b) (x := x) (xs := xs) (zs := zs)]
      ac_rfl

/-- Appending a latent tail and an observed tail factors the observation
likelihood when the split boundary is aligned by length. -/
theorem observationWeight_append_of_length_eq
    (θ : FiniteHMMParam latent obs) :
    ∀ xs : List (Fin latent), ∀ zs : List (Fin obs),
      xs.length = zs.length →
      ∀ ys : List (Fin latent), ∀ us : List (Fin obs),
        observationWeight θ (xs ++ ys) (zs ++ us) =
          observationWeight θ xs zs * observationWeight θ ys us
  | [], [], hlen, ys, us => by
      simp [FiniteHiddenMarkovModel.observationWeight]
  | [], z :: zs, hlen, ys, us => by
      cases hlen
  | x :: xs, [], hlen, ys, us => by
      cases hlen
  | x :: xs, z :: zs, hlen, ys, us => by
      have htail : xs.length = zs.length := Nat.succ.inj hlen
      simp [FiniteHiddenMarkovModel.observationWeight,
        observationWeight_append_of_length_eq (θ := θ) (xs := xs) (zs := zs) (ys := ys)
          (us := us) htail,
        mul_assoc]

/-- Probability of a latent word split at a marked terminal state. -/
theorem wordProb_append_terminal
    (θ : MarkovParam latent) (x : Fin latent) :
    ∀ xs zs : List (Fin latent),
      wordProb (k := latent) θ ((xs ++ [x]) ++ zs) =
        wordProb (k := latent) θ (xs ++ [x]) *
          (wordProbAux (k := latent) θ x zs : ℝ≥0∞)
  | [], zs => by
      simp [MarkovDeFinettiHard.wordProb, MarkovDeFinettiHard.wordProbNN,
        MarkovDeFinettiHard.wordProbAux]
  | a :: xs, zs => by
      simp only [MarkovDeFinettiHard.wordProb, MarkovDeFinettiHard.wordProbNN,
        List.cons_append, ENNReal.coe_mul]
      rw [wordProbAux_append_terminal (θ := θ) (a := a) (x := x) (xs := xs) (zs := zs)]
      ac_rfl

/-- Unnormalized smoothing mass for a split observed word: the mass of all
latent trajectories whose state at the split point is `x`. -/
def smoothingMass (θ : FiniteHMMParam latent obs)
    (ys : List (Fin obs)) (zs : List (Fin obs)) (x : Fin latent) : ℝ≥0∞ :=
  forwardMessage θ ys x * backwardMessage θ x zs

/-- At a singleton observation prefix, smoothing masses sum to the full
observed-word probability across the split. This is the first honest
forward/backward total-mass identity. -/
theorem smoothingMass_sum_eq_observedWordProb_singleton
    (θ : FiniteHMMParam latent obs) (y : Fin obs) (zs : List (Fin obs)) :
    ∑ x : Fin latent, smoothingMass θ [y] zs x =
      observedWordProb θ (y :: zs) := by
  rw [observedWordProb_cons_eq_sum_init_mul_emission_mul_backward
    (θ := θ) (y := y) (ys := zs)]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [smoothingMass, forwardMessage_singleton]

/-- Appending one observed symbol to a nonempty prefix shifts the smoothing
split by one step. -/
theorem smoothingMass_sum_shift_append_singleton
    (θ : FiniteHMMParam latent obs)
    (ys : List (Fin obs)) (hys : ys ≠ [])
    (y : Fin obs) (zs : List (Fin obs)) :
    ∑ x : Fin latent, smoothingMass θ (ys ++ [y]) zs x =
      ∑ u : Fin latent, smoothingMass θ ys (y :: zs) u := by
  calc
    ∑ x : Fin latent, smoothingMass θ (ys ++ [y]) zs x =
      ∑ x : Fin latent,
        (∑ u : Fin latent,
          forwardMessage θ ys u *
            (stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
              (emissionProb θ x y : ℝ≥0∞)) *
          backwardMessage θ x zs := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            simp [smoothingMass,
              forwardMessage_append_singleton_of_ne_nil (θ := θ) (ys := ys) hys (y := y)]
    _ =
      ∑ x : Fin latent,
        ∑ u : Fin latent,
          (forwardMessage θ ys u *
            (stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
              (emissionProb θ x y : ℝ≥0∞)) *
            backwardMessage θ x zs := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [Finset.sum_mul]
    _ =
      ∑ u : Fin latent,
        ∑ x : Fin latent,
          (forwardMessage θ ys u *
            (stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
              (emissionProb θ x y : ℝ≥0∞)) *
            backwardMessage θ x zs := by
              rw [Finset.sum_comm]
    _ =
      ∑ u : Fin latent,
        forwardMessage θ ys u *
          ∑ x : Fin latent,
            (stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
              (emissionProb θ x y : ℝ≥0∞) *
                backwardMessage θ x zs := by
                  refine Finset.sum_congr rfl ?_
                  intro u hu
                  calc
                    ∑ x : Fin latent,
                      (forwardMessage θ ys u *
                        (stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
                          (emissionProb θ x y : ℝ≥0∞)) *
                        backwardMessage θ x zs =
                      ∑ x : Fin latent,
                        forwardMessage θ ys u *
                          (((stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
                            (emissionProb θ x y : ℝ≥0∞)) *
                              backwardMessage θ x zs) := by
                                refine Finset.sum_congr rfl ?_
                                intro x hx
                                ac_rfl
                    _ =
                      forwardMessage θ ys u *
                        ∑ x : Fin latent,
                          ((stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
                            (emissionProb θ x y : ℝ≥0∞)) *
                              backwardMessage θ x zs := by
                                rw [Finset.mul_sum]
                    _ =
                      forwardMessage θ ys u *
                        ∑ x : Fin latent,
                          (stepProb (k := latent) θ.latentParam u x : ℝ≥0∞) *
                            (emissionProb θ x y : ℝ≥0∞) *
                              backwardMessage θ x zs := by
                                refine congrArg (fun t => forwardMessage θ ys u * t) ?_
                                refine Finset.sum_congr rfl ?_
                                intro x hx
                                ac_rfl
    _ =
      ∑ u : Fin latent,
        forwardMessage θ ys u * backwardMessage θ u (y :: zs) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          simp [backwardMessage_cons, mul_left_comm, mul_comm]
    _ =
      ∑ u : Fin latent, smoothingMass θ ys (y :: zs) u := by
        refine Finset.sum_congr rfl ?_
        intro u hu
        simp [smoothingMass]

/-- Full nonempty-prefix forward/backward total-mass identity. -/
theorem smoothingMass_sum_eq_observedWordProb_append_of_ne_nil
    (θ : FiniteHMMParam latent obs) :
    ∀ ys : List (Fin obs), ys ≠ [] →
      ∀ zs : List (Fin obs),
        ∑ x : Fin latent, smoothingMass θ ys zs x =
          observedWordProb θ (ys ++ zs)
  | [], hys => False.elim (hys rfl)
  | ys, hys => by
      induction ys using List.reverseRecOn with
      | nil =>
          contradiction
      | append_singleton ys y ih =>
          intro zs
          cases ys with
          | nil =>
              simpa [List.nil_append] using
                smoothingMass_sum_eq_observedWordProb_singleton
                  (θ := θ) (y := y) (zs := zs)
          | cons y₀ ys' =>
              have hprefix : y₀ :: ys' ≠ [] := List.cons_ne_nil _ _
              calc
                ∑ x : Fin latent, smoothingMass θ ((y₀ :: ys') ++ [y]) zs x =
                  ∑ u : Fin latent, smoothingMass θ (y₀ :: ys') (y :: zs) u := by
                    exact smoothingMass_sum_shift_append_singleton
                      (θ := θ) (ys := y₀ :: ys') hprefix (y := y) (zs := zs)
                _ = observedWordProb θ ((y₀ :: ys') ++ (y :: zs)) := by
                    exact ih hprefix (y :: zs)
                _ = observedWordProb θ (((y₀ :: ys') ++ [y]) ++ zs) := by
                    simp

/-- Normalized smoothing posterior mass at the split latent state. -/
def smoothingPosteriorMass (θ : FiniteHMMParam latent obs)
    (ys : List (Fin obs)) (zs : List (Fin obs)) (x : Fin latent) : ℝ≥0∞ :=
  smoothingMass θ ys zs x / observedWordProb θ (ys ++ zs)

theorem smoothingPosteriorMass_sum_eq_one
    (θ : FiniteHMMParam latent obs)
    (ys zs : List (Fin obs))
    (hys : ys ≠ [])
    (hobs : observedWordProb θ (ys ++ zs) ≠ 0) :
    ∑ x : Fin latent, smoothingPosteriorMass θ ys zs x = 1 := by
  have htop : observedWordProb θ (ys ++ zs) ≠ ⊤ :=
    observedWordProb_ne_top (θ := θ) (ys ++ zs)
  unfold smoothingPosteriorMass
  calc
    ∑ x : Fin latent, smoothingMass θ ys zs x / observedWordProb θ (ys ++ zs) =
      ∑ x : Fin latent, smoothingMass θ ys zs x *
        (observedWordProb θ (ys ++ zs))⁻¹ := by
          simp [div_eq_mul_inv]
    _ =
      (∑ x : Fin latent, smoothingMass θ ys zs x) *
        (observedWordProb θ (ys ++ zs))⁻¹ := by
          rw [Finset.sum_mul]
    _ =
      observedWordProb θ (ys ++ zs) *
        (observedWordProb θ (ys ++ zs))⁻¹ := by
          rw [smoothingMass_sum_eq_observedWordProb_append_of_ne_nil
            (θ := θ) ys hys zs]
    _ = 1 := ENNReal.mul_inv_cancel hobs htop

/-! ## Observed-only boundary: hidden-label nonidentifiability -/

private def diracPM {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) : MeasureTheory.ProbabilityMeasure α :=
  ⟨MeasureTheory.Measure.dirac a, MeasureTheory.Measure.dirac.isProbabilityMeasure⟩

/-- Hidden state `0` is the live state, and emits observation `0`
deterministically. -/
private def hiddenLabelSwapHMM₀ : FiniteHMMParam 2 2 where
  latentParam :=
    { init := diracPM 0
      trans := fun i => diracPM i }
  emission := fun
    | 0 => diracPM 0
    | 1 => diracPM 1

/-- Same observed process as `hiddenLabelSwapHMM₀`, but with the hidden labels
swapped. -/
private def hiddenLabelSwapHMM₁ : FiniteHMMParam 2 2 where
  latentParam :=
    { init := diracPM 1
      trans := fun i => diracPM i }
  emission := fun
    | 0 => diracPM 1
    | 1 => diracPM 0

/-- Positive example: the two label-swapped HMMs agree on the observed
probability of the singleton word `[0]`. -/
theorem hiddenLabelSwap_observedWordProb_singleton :
    observedWordProb hiddenLabelSwapHMM₀ [0] =
      observedWordProb hiddenLabelSwapHMM₁ [0] := by
  rw [observedWordProb_cons_eq_sum_init_mul_emission_mul_backward
      (θ := hiddenLabelSwapHMM₀) (y := 0) (ys := []),
    observedWordProb_cons_eq_sum_init_mul_emission_mul_backward
      (θ := hiddenLabelSwapHMM₁) (y := 0) (ys := [])]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [backwardMessage_nil]
  change
    ((((initProb hiddenLabelSwapHMM₀.latentParam 0 * emissionProb hiddenLabelSwapHMM₀ 0 0) +
        (initProb hiddenLabelSwapHMM₀.latentParam 1 * emissionProb hiddenLabelSwapHMM₀ 1 0) :
          ℝ≥0) : ℝ≥0∞) =
      (((initProb hiddenLabelSwapHMM₁.latentParam 0 * emissionProb hiddenLabelSwapHMM₁ 0 0) +
        (initProb hiddenLabelSwapHMM₁.latentParam 1 * emissionProb hiddenLabelSwapHMM₁ 1 0) :
          ℝ≥0) : ℝ≥0∞))
  rw [ENNReal.coe_inj]
  simp [initProb, emissionProb, hiddenLabelSwapHMM₀, hiddenLabelSwapHMM₁, diracPM]
  have h00 : (0 : Fin 2) ∈ Set.singleton (0 : Fin 2) := by
    change Set.singleton (0 : Fin 2) 0
    rfl
  have h10 : (1 : Fin 2) ∉ Set.singleton (0 : Fin 2) := by
    change ¬ Set.singleton (0 : Fin 2) 1
    intro h
    cases h
  have h01 : (0 : Fin 2) ∉ Set.singleton (1 : Fin 2) := by
    change ¬ Set.singleton (1 : Fin 2) 0
    intro h
    cases h
  have h11 : (1 : Fin 2) ∈ Set.singleton (1 : Fin 2) := by
    change Set.singleton (1 : Fin 2) 1
    rfl
  simp [h00, h10, h01, h11]

/-- Positive example: under the first model, seeing a `0` places all
unnormalized filtering mass on hidden state `0`. -/
theorem hiddenLabelSwap_forwardMessage_state0_model0 :
    forwardMessage hiddenLabelSwapHMM₀ [0] 0 = 1 := by
  rw [forwardMessage_singleton]
  change (((initProb hiddenLabelSwapHMM₀.latentParam 0 * emissionProb hiddenLabelSwapHMM₀ 0 0 :
      ℝ≥0) : ℝ≥0∞) = 1)
  rw [ENNReal.coe_eq_one]
  simp [initProb, emissionProb, hiddenLabelSwapHMM₀, diracPM]
  have h00 : (0 : Fin 2) ∈ Set.singleton (0 : Fin 2) := by
    change Set.singleton (0 : Fin 2) 0
    rfl
  simp [h00]

/-- Under the first model, the same singleton observation puts zero
unnormalized filtering mass on hidden state `1`. -/
theorem hiddenLabelSwap_forwardMessage_state1_model0 :
    forwardMessage hiddenLabelSwapHMM₀ [0] 1 = 0 := by
  rw [forwardMessage_singleton]
  change (((initProb hiddenLabelSwapHMM₀.latentParam 1 * emissionProb hiddenLabelSwapHMM₀ 1 0 :
      ℝ≥0) : ℝ≥0∞) = 0)
  rw [ENNReal.coe_eq_zero]
  simp [initProb, emissionProb, hiddenLabelSwapHMM₀, diracPM]
  have h10 : (1 : Fin 2) ∉ Set.singleton (0 : Fin 2) := by
    change ¬ Set.singleton (0 : Fin 2) 1
    intro h
    cases h
  simp [h10]

/-- Under the first model, the observed singleton `[0]` has probability `1`. -/
theorem hiddenLabelSwap_observedWordProb_singleton_model0 :
    observedWordProb hiddenLabelSwapHMM₀ [0] = 1 := by
  rw [observedWordProb_eq_sum_forwardMessage, Fin.sum_univ_two,
    hiddenLabelSwap_forwardMessage_state0_model0,
    hiddenLabelSwap_forwardMessage_state1_model0]
  simp

/-- The label-swapped twin has the same observed singleton probability `1`. -/
theorem hiddenLabelSwap_observedWordProb_singleton_model1 :
    observedWordProb hiddenLabelSwapHMM₁ [0] = 1 := by
  rw [← hiddenLabelSwap_observedWordProb_singleton,
    hiddenLabelSwap_observedWordProb_singleton_model0]

/-- Negative example: under the label-swapped model, the same observation `0`
places zero filtering mass on hidden state `0`. -/
theorem hiddenLabelSwap_forwardMessage_state0_model1 :
    forwardMessage hiddenLabelSwapHMM₁ [0] 0 = 0 := by
  rw [forwardMessage_singleton]
  change (((initProb hiddenLabelSwapHMM₁.latentParam 0 * emissionProb hiddenLabelSwapHMM₁ 0 0 :
      ℝ≥0) : ℝ≥0∞) = 0)
  rw [ENNReal.coe_eq_zero]
  simp [initProb, emissionProb, hiddenLabelSwapHMM₁, diracPM]
  have h10 : (1 : Fin 2) ∉ Set.singleton (0 : Fin 2) := by
    change ¬ Set.singleton (0 : Fin 2) 1
    intro h
    cases h
  simp [h10]

/-- Under the first model, the normalized observed-only filtering posterior
puts full mass on hidden state `0`. -/
theorem hiddenLabelSwap_filteringPosterior_state0_model0 :
    filteringPosteriorMass hiddenLabelSwapHMM₀ [0] 0 = 1 := by
  unfold filteringPosteriorMass filteringMass
  rw [hiddenLabelSwap_forwardMessage_state0_model0,
    hiddenLabelSwap_observedWordProb_singleton_model0]
  simp

/-- Under the label-swapped model, the same observed singleton puts zero
posterior mass on hidden state `0`. -/
theorem hiddenLabelSwap_filteringPosterior_state0_model1 :
    filteringPosteriorMass hiddenLabelSwapHMM₁ [0] 0 = 0 := by
  unfold filteringPosteriorMass filteringMass
  rw [hiddenLabelSwap_forwardMessage_state0_model1,
    hiddenLabelSwap_observedWordProb_singleton_model1]
  simp

/-- Positive example: when the observed singleton has positive mass, the
filtering posterior normalizes to total mass `1`. -/
theorem hiddenLabelSwap_filteringPosterior_sum_model0 :
    ∑ x : Fin 2, filteringPosteriorMass hiddenLabelSwapHMM₀ [0] x = 1 := by
  apply filteringPosteriorMass_sum_eq_one
  rw [hiddenLabelSwap_observedWordProb_singleton_model0]
  simp

/-- Positive example: the WM-style strength view of filtering posterior
evidence recovers the actual posterior mass. -/
theorem hiddenLabelSwap_filteringPosteriorEvidence_strength_model0 :
    BinaryEvidence.toStrength
        (filteringPosteriorEvidence hiddenLabelSwapHMM₀ [0] 0) =
      filteringPosteriorMass hiddenLabelSwapHMM₀ [0] 0 := by
  apply filteringPosteriorEvidence_toStrength_eq_filteringPosteriorMass
  rw [hiddenLabelSwap_observedWordProb_singleton_model0]
  simp

/-- Positive example: singleton-prefix smoothing recovers the corresponding full
observed-word probability across the split. -/
theorem hiddenLabelSwap_smoothing_singleton_model0 :
    ∑ x : Fin 2, smoothingMass hiddenLabelSwapHMM₀ [0] [0] x =
      observedWordProb hiddenLabelSwapHMM₀ [0, 0] := by
  simpa using
    (smoothingMass_sum_eq_observedWordProb_singleton
      (θ := hiddenLabelSwapHMM₀) (y := 0) (zs := [0]))

/-- Honest observed-only boundary: even matching observed probability for a
concrete observation word does not determine the label-indexed filtering mass. -/
theorem exists_same_observedWordProb_different_forwardMessage :
    ∃ θ₀ θ₁ : FiniteHMMParam 2 2,
      observedWordProb θ₀ [0] = observedWordProb θ₁ [0] ∧
        forwardMessage θ₀ [0] 0 ≠ forwardMessage θ₁ [0] 0 := by
  refine ⟨hiddenLabelSwapHMM₀, hiddenLabelSwapHMM₁, hiddenLabelSwap_observedWordProb_singleton, ?_⟩
  rw [hiddenLabelSwap_forwardMessage_state0_model0,
    hiddenLabelSwap_forwardMessage_state0_model1]
  simp

/-- Honest observed-only WM obstruction: no unordered-observation multiset
consumer can uniformly recover the filtering posterior strength, because the
same observation multiset `{0}` arises from two models with different latent
posteriors. -/
theorem no_observedOnly_multiset_queryStrength_recovers_filteringPosteriorMass :
    ¬ ∃ e : Multiset (Fin 2) → Fin 2 → BinaryEvidence,
        ∀ θ : FiniteHMMParam 2 2, ∀ q : Fin 2,
          BinaryEvidence.toStrength (e ({(0 : Fin 2)} : Multiset (Fin 2)) q) =
            filteringPosteriorMass θ [0] q := by
  intro h
  rcases h with ⟨e, he⟩
  have h0 :
      BinaryEvidence.toStrength (e ({(0 : Fin 2)} : Multiset (Fin 2)) 0) =
        filteringPosteriorMass hiddenLabelSwapHMM₀ [0] 0 :=
    he hiddenLabelSwapHMM₀ 0
  have h1 :
      BinaryEvidence.toStrength (e ({(0 : Fin 2)} : Multiset (Fin 2)) 0) =
        filteringPosteriorMass hiddenLabelSwapHMM₁ [0] 0 :=
    he hiddenLabelSwapHMM₁ 0
  rw [hiddenLabelSwap_filteringPosterior_state0_model0] at h0
  rw [hiddenLabelSwap_filteringPosterior_state0_model1] at h1
  have hEq : (1 : ℝ≥0∞) = 0 := by
    calc
      (1 : ℝ≥0∞) = BinaryEvidence.toStrength (e ({(0 : Fin 2)} : Multiset (Fin 2)) 0) := h0.symm
      _ = 0 := h1
  simp at hEq

end Mettapedia.Logic.FiniteHiddenMarkovObservedInference
