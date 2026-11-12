import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreWeight
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# The graded where-clause on the step: sum over matches, product along a match

Offer finitely many candidate firings at every state, and weigh each firing in a commutative
semiring. The **transfer operator** sums, over the offered firings that are admitted, the weight
of the firing times a value at its result (`transfer`): one step of a graded where-clause, summed
over candidate matches. Its iterates are sums over runs:

* `transfer_eq_sum_runs`: `n` steps of the transfer are the sum, over the offered runs of length
  `n`, of the weight of the run (`account`, the product along it) times the value where it ends.
  This is the budgeted graded denotation `∑_h w(h) |Q⟩` of a weighted calculus, on the step.
* `transfer_add`: the iterates compose, `T^(m+n) = T^m ∘ T^n`.

Candidates are firings, and firings carry the identities they select: two matches of one pattern
on two occurrences are two summands.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

universe uO uT uH uOcc uS uF uK uL uM

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (P : Step X O State Firing)
  {K : Type uK} [CommSemiring K] (offers : (s : State) → Finset (Firing s))
  (weight : (t : State) → Firing t → K)

/-- The sum over a flattened list is the sum of the sums of its parts. -/
theorem sum_map_flatMap {α : Type uL} {β : Type uM} (l : List α) (g : α → List β) (h : β → K) :
    ((l.flatMap g).map h).sum = (l.map fun a => ((g a).map h).sum).sum := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

open Classical in
/-- The offered runs of length `n` from a state: each step an admitted offered firing. -/
noncomputable def offeredRuns : ℕ → (s : State) → List (P.Run s)
  | 0, s => [.nil s]
  | n + 1, s => (offers s).toList.flatMap fun f =>
      if allowed : P.Admits f then (offeredRuns n (P.result f allowed)).map (Step.Run.cons f allowed)
      else []

open Classical in
/-- **The transfer operator**: the sum over the offered admitted firings of the weight of the
firing times the value at its result, iterated `n` times. -/
noncomputable def transfer : ℕ → (State → K) → State → K
  | 0, value, s => value s
  | n + 1, value, s => ∑ f ∈ offers s,
      if allowed : P.Admits f then weight s f * transfer n value (P.result f allowed) else 0

/-- **The transfer is the sum over runs of their weights.** -/
theorem transfer_eq_sum_runs : ∀ (n : ℕ) (value : State → K) (s : State),
    transfer P offers weight n value s =
      ((offeredRuns P offers n s).map fun run => run.account weight * value run.last).sum
  | 0, value, s => by
      show value s = (Step.Run.nil (P := P) s).account weight * value s + 0
      rw [add_zero]
      exact (one_mul _).symm
  | n + 1, value, s => by
      classical
      have expand : ((offeredRuns P offers (n + 1) s).map
            fun run => run.account weight * value run.last).sum =
          ∑ f ∈ offers s, (((if allowed : P.Admits f then
            (offeredRuns P offers n (P.result f allowed)).map (Step.Run.cons f allowed) else []).map
              fun run => run.account weight * value run.last).sum) := by
        rw [offeredRuns, sum_map_flatMap, Finset.sum_map_toList]
      rw [expand, transfer]
      refine Finset.sum_congr rfl fun f _ => ?_
      by_cases allowed : P.Admits f
      · rw [dif_pos allowed, dif_pos allowed, List.map_map,
          transfer_eq_sum_runs n value (P.result f allowed), ← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun run _ => ?_
        show weight s f * (run.account weight * value run.last) =
          weight s f * run.account weight * value run.last
        rw [mul_assoc]
      · rw [dif_neg allowed, dif_neg allowed]
        rfl

/-- **The iterates compose.** -/
theorem transfer_add : ∀ (m n : ℕ) (value : State → K),
    transfer P offers weight (m + n) value =
      transfer P offers weight m (transfer P offers weight n value)
  | 0, n, value => by
      funext s
      rw [Nat.zero_add]
      rfl
  | m + 1, n, value => by
      classical
      funext s
      rw [show m + 1 + n = (m + n) + 1 by omega]
      show (∑ f ∈ offers s, if allowed : P.Admits f then
          weight s f * transfer P offers weight (m + n) value (P.result f allowed) else 0) =
        ∑ f ∈ offers s, if allowed : P.Admits f then
          weight s f * transfer P offers weight m (transfer P offers weight n value)
            (P.result f allowed) else 0
      rw [transfer_add m n value]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
