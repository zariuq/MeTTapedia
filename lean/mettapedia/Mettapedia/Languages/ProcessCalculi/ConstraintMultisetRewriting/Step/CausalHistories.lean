import Mettapedia.GSLT.Logic.GradedSupport
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Causal histories of a rate system: the race identity

A **rate system** gives every state a list of candidates, each a successor with a positive weight,
in the shape of `GradedSupport` (`S → List (S × ℝ)`). Its **jump chain** fires a candidate with its
weight divided by the state's race total (`total`, `pathProb`); this is the normalization of the
step's weighted firings (`Race.prob`, `Race.traceProb`), which normalize over every admitted firing.

## Parallel composition and schedules

The **composition** of two systems fires a candidate of either side and leaves the other side
where it was (`par`); its race total is the sum of the two totals (`total_par`). A **schedule** of
the composition records, move by move, which side fired and with which candidate. Its jump-chain
likelihood is `schedProb`, and it realizes a run of the composition with that likelihood
(`realize`, `pathProb_realize`, `isRun_realize`).

The **shuffles** of a run of each side are exactly the schedules whose two projections are the two
runs (`mem_shuffles_iff`), each listed once (`shuffles_nodup`). They are the linearizations of one
causal history of the composition: the two runs, with no order between their moves.

## The race identity

**Summed over its linearizations, the likelihood of a causal history of the composition is the
product of the two sides' likelihoods** (`sum_shuffles`, `history_factorizes`), for maximal runs and
positive weights. The two-move case is the identity `1/(a+b) · (1/a + 1/b) = 1/(ab)`.

* Rates compose by addition; the jump chain does not compose on words, and composes on causal
  histories by multiplication. Normalization local to a component is therefore a theorem about
  components that do not interfere, and only about them.
* **Autonomy**: the factor of one side does not depend on the other side's rates. A change of the
  rates of one side (an intervention there) changes the joint only through that side's factor.
* **A deterministic run is intervention-transparent** (`pathProb_determined`,
  `deterministic_transparent`): where every state of a run has one candidate, its factor is `1` for
  every positive weight, and the joint is the other side's factor alone. On schedules this fails:
  reweighting a deterministic candidate changes the likelihood of a schedule
  (`CausalHistoriesControls`).

## Restriction

A **restriction** keeps the candidates a constraint admits (`restrict`), as an intervention that
restricts and never overrides. Restrictions compose by conjunction (`restrict_restrict`), the
trivial constraint is the identity (`restrict_true`), and restricting a race to one candidate gives
it likelihood `1` whatever its weight was (`pathProb_restrict_single`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalHistories

open Mettapedia.GSLT.GradedSupport (IsNormal)

universe u v

/-! ## Rate systems and their jump chain -/

section System

variable {S : Type u} (step : S → List (S × ℝ))

/-- The race total of a state: the sum of its candidates' weights. -/
def total (s : S) : ℝ := ((step s).map Prod.snd).sum

/-- **The jump-chain likelihood of a run**: each move's weight over the race total of the state it
leaves. -/
def pathProb : S → List (S × ℝ) → ℝ
  | _, [] => 1
  | s, p :: rest => p.2 / total step s * pathProb p.1 rest

/-- A run: every move is a candidate of the state it leaves. -/
inductive IsRun : S → List (S × ℝ) → Prop
  | nil (s : S) : IsRun s []
  | cons {s : S} {p : S × ℝ} {rest : List (S × ℝ)} :
      p ∈ step s → IsRun p.1 rest → IsRun s (p :: rest)

/-- The state a run ends in. -/
def endState : S → List (S × ℝ) → S
  | s, [] => s
  | _, p :: rest => endState p.1 rest

/-- A maximal run: a run that ends where nothing is left to fire. -/
def Maximal (s : S) (α : List (S × ℝ)) : Prop :=
  IsRun step s α ∧ IsNormal step (endState s α)

/-- Every candidate has positive weight: a candidate of weight zero offers no transition. -/
def Positive : Prop := ∀ s, ∀ p ∈ step s, 0 < p.2

/-- A run along which every state it leaves has exactly one candidate. -/
inductive Determined : S → List (S × ℝ) → Prop
  | nil (s : S) : Determined s []
  | cons {s : S} {p : S × ℝ} {rest : List (S × ℝ)} :
      step s = [p] → Determined p.1 rest → Determined s (p :: rest)

/-- **A restriction**: the candidates a constraint admits, the others removed. -/
def restrict (keep : S → S × ℝ → Bool) (s : S) : List (S × ℝ) := (step s).filter (keep s)

variable {step}

theorem total_eq_zero_of_normal {s : S} (normal : IsNormal step s) : total step s = 0 := by
  unfold total
  apply List.sum_eq_zero
  intro x member
  obtain ⟨p, mem, rfl⟩ := List.mem_map.mp member
  exact normal p mem

/-- A state with a positive candidate has a positive race total. -/
theorem total_pos (positive : Positive step) {s : S} {p : S × ℝ} (member : p ∈ step s) :
    0 < total step s := by
  unfold total
  apply List.sum_pos
  · intro x mem
    obtain ⟨q, qmem, rfl⟩ := List.mem_map.mp mem
    exact positive s q qmem
  · intro empty
    have inside : p.2 ∈ (step s).map Prod.snd := List.mem_map.mpr ⟨p, member, rfl⟩
    rw [empty] at inside
    simp at inside

/-- **A deterministic run has likelihood `1`**, whatever its positive weights. -/
theorem pathProb_determined (positive : Positive step) {s : S} {α : List (S × ℝ)}
    (determined : Determined step s α) : pathProb step s α = 1 := by
  induction determined with
  | nil s => rfl
  | @cons s p rest single _ ih =>
      have hp : 0 < p.2 := positive s p (by rw [single]; exact List.mem_singleton_self p)
      have htotal : total step s = p.2 := by simp [total, single]
      rw [pathProb, htotal, div_self hp.ne', one_mul, ih]

theorem restrict_positive (positive : Positive step) (keep : S → S × ℝ → Bool) :
    Positive (restrict step keep) := fun s p member =>
  positive s p (List.mem_of_mem_filter member)

/-- **Restrictions compose by conjunction.** -/
theorem restrict_restrict (first second : S → S × ℝ → Bool) :
    restrict (restrict step first) second = restrict step (fun s p => first s p && second s p) := by
  funext s
  simp only [restrict, List.filter_filter, Bool.and_comm]

/-- **The trivial constraint is the identity.** -/
theorem restrict_true : restrict step (fun _ _ => true) = step := by
  funext s
  simp [restrict]

/-- **A hard intervention discards the weights**: restricted to one candidate, a race fires it with
likelihood `1`, whatever its weight. -/
theorem pathProb_restrict_single (positive : Positive step) {keep : S → S × ℝ → Bool} {s : S}
    {p : S × ℝ} (single : restrict step keep s = [p]) :
    pathProb (restrict step keep) s [p] = 1 :=
  pathProb_determined (restrict_positive positive keep) (.cons single (.nil _))

end System

/-! ## Shuffles -/

section Shuffles

variable {α : Type u} {β : Type v}

/-- **The shuffles of two words**: every interleaving, each move tagged with its side. -/
def shuffles : List α → List β → List (List (α ⊕ β))
  | [], ys => [ys.map Sum.inr]
  | x :: xs, [] => [(x :: xs).map Sum.inl]
  | x :: xs, y :: ys =>
      (shuffles xs (y :: ys)).map (Sum.inl x :: ·) ++ (shuffles (x :: xs) ys).map (Sum.inr y :: ·)

theorem shuffles_nil_right (xs : List α) : shuffles xs ([] : List β) = [xs.map Sum.inl] := by
  cases xs <;> simp [shuffles]

@[simp] theorem filterMap_getLeft_map_inl (xs : List α) :
    (xs.map Sum.inl : List (α ⊕ β)).filterMap Sum.getLeft? = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

@[simp] theorem filterMap_getRight_map_inl (xs : List α) :
    (xs.map Sum.inl : List (α ⊕ β)).filterMap Sum.getRight? = [] := by
  induction xs with
  | nil => rfl
  | cons x xs _ => simp

@[simp] theorem filterMap_getLeft_map_inr (ys : List β) :
    (ys.map Sum.inr : List (α ⊕ β)).filterMap Sum.getLeft? = [] := by
  induction ys with
  | nil => rfl
  | cons y ys _ => simp

@[simp] theorem filterMap_getRight_map_inr (ys : List β) :
    (ys.map Sum.inr : List (α ⊕ β)).filterMap Sum.getRight? = ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [ih]

/-- Every shuffle projects to the two words. -/
theorem projections_of_mem_shuffles : ∀ (xs : List α) (ys : List β), ∀ σ ∈ shuffles xs ys,
    σ.filterMap Sum.getLeft? = xs ∧ σ.filterMap Sum.getRight? = ys := by
  intro xs ys
  induction xs, ys using shuffles.induct with
  | case1 ys =>
      intro σ member
      simp only [shuffles, List.mem_singleton] at member
      subst member
      exact ⟨filterMap_getLeft_map_inr ys, filterMap_getRight_map_inr ys⟩
  | case2 x xs =>
      intro σ member
      simp only [shuffles, List.mem_singleton] at member
      subst member
      exact ⟨filterMap_getLeft_map_inl (x :: xs), filterMap_getRight_map_inl (x :: xs)⟩
  | case3 x xs y ys ih1 ih2 =>
      intro σ member
      simp only [shuffles, List.mem_append, List.mem_map] at member
      rcases member with ⟨τ, inτ, rfl⟩ | ⟨τ, inτ, rfl⟩
      · obtain ⟨l, r⟩ := ih1 τ inτ
        exact ⟨by rw [List.filterMap_cons_some Sum.getLeft?_inl, l],
          by rw [List.filterMap_cons_none Sum.getRight?_inl, r]⟩
      · obtain ⟨l, r⟩ := ih2 τ inτ
        exact ⟨by rw [List.filterMap_cons_none Sum.getLeft?_inr, l],
          by rw [List.filterMap_cons_some Sum.getRight?_inr, r]⟩

/-- Every interleaving of the two words is a shuffle. -/
theorem mem_shuffles_of_projections : ∀ (σ : List (α ⊕ β)) (xs : List α) (ys : List β),
    σ.filterMap Sum.getLeft? = xs → σ.filterMap Sum.getRight? = ys → σ ∈ shuffles xs ys
  | [], xs, ys, hl, hr => by
      subst hl
      subst hr
      simp [shuffles]
  | .inl x :: σ, xs, ys, hl, hr => by
      simp only [List.filterMap_cons, Sum.getLeft?_inl, Sum.getRight?_inl] at hl hr
      subst hl
      cases ys with
      | nil =>
          have inner := mem_shuffles_of_projections σ _ [] rfl hr
          rw [shuffles_nil_right, List.mem_singleton] at inner
          rw [shuffles_nil_right, List.mem_singleton, List.map_cons]
          exact congrArg _ inner
      | cons y ys =>
          simp only [shuffles]
          exact List.mem_append_left _
            (List.mem_map.mpr ⟨σ, mem_shuffles_of_projections σ _ (y :: ys) rfl hr, rfl⟩)
  | .inr y :: σ, xs, ys, hl, hr => by
      simp only [List.filterMap_cons, Sum.getLeft?_inr, Sum.getRight?_inr] at hl hr
      subst hr
      cases xs with
      | nil =>
          have inner := mem_shuffles_of_projections σ [] _ hl rfl
          simp only [shuffles, List.mem_singleton] at inner
          simp only [shuffles, List.mem_singleton, List.map_cons]
          exact congrArg _ inner
      | cons x xs =>
          simp only [shuffles]
          exact List.mem_append_right _
            (List.mem_map.mpr ⟨σ, mem_shuffles_of_projections σ (x :: xs) _ hl rfl, rfl⟩)

/-- **The shuffles are exactly the interleavings**: the schedules whose projections are the two
words. -/
theorem mem_shuffles_iff (xs : List α) (ys : List β) (σ : List (α ⊕ β)) :
    σ ∈ shuffles xs ys ↔ σ.filterMap Sum.getLeft? = xs ∧ σ.filterMap Sum.getRight? = ys :=
  ⟨projections_of_mem_shuffles xs ys σ, fun h => mem_shuffles_of_projections σ xs ys h.1 h.2⟩

/-- **Each interleaving is listed once.** -/
theorem shuffles_nodup : ∀ (xs : List α) (ys : List β), (shuffles xs ys).Nodup := by
  intro xs ys
  induction xs, ys using shuffles.induct with
  | case1 ys => simp [shuffles]
  | case2 x xs => simp [shuffles]
  | case3 x xs y ys ih1 ih2 =>
      simp only [shuffles]
      refine List.Nodup.append (List.Nodup.map List.cons_injective ih1)
        (List.Nodup.map List.cons_injective ih2) ?_
      intro σ in1 in2
      obtain ⟨τ1, _, rfl⟩ := List.mem_map.mp in1
      obtain ⟨τ2, _, same⟩ := List.mem_map.mp in2
      simp at same

end Shuffles

/-! ## Parallel composition and the race identity -/

section Composition

variable {A : Type u} {B : Type v} (stepA : A → List (A × ℝ)) (stepB : B → List (B × ℝ))

/-- **The parallel composition**: a candidate of either side fires, and the other side stays. -/
def par (x : A × B) : List ((A × B) × ℝ) :=
  (stepA x.1).map (fun p => ((p.1, x.2), p.2)) ++ (stepB x.2).map (fun q => ((x.1, q.1), q.2))

/-- **Rates compose by addition.** -/
theorem total_par (x : A × B) :
    total (par stepA stepB) x = total stepA x.1 + total stepB x.2 := by
  simp [total, par, Function.comp_def]

/-- The composition has nothing left to fire exactly when neither side has. -/
theorem isNormal_par_iff (x : A × B) :
    IsNormal (par stepA stepB) x ↔ IsNormal stepA x.1 ∧ IsNormal stepB x.2 := by
  simp only [IsNormal, par, List.mem_append, List.mem_map]
  constructor
  · intro normal
    exact ⟨fun p member => normal _ (Or.inl ⟨p, member, rfl⟩),
      fun q member => normal _ (Or.inr ⟨q, member, rfl⟩)⟩
  · rintro ⟨left, right⟩ r (⟨p, member, rfl⟩ | ⟨q, member, rfl⟩)
    · exact left p member
    · exact right q member

/-- **The jump-chain likelihood of a schedule of the composition**: the race total is the sum of
the two sides' totals. -/
def schedProb : A → B → List ((A × ℝ) ⊕ (B × ℝ)) → ℝ
  | _, _, [] => 1
  | a, b, .inl p :: rest => p.2 / (total stepA a + total stepB b) * schedProb p.1 b rest
  | a, b, .inr q :: rest => q.2 / (total stepA a + total stepB b) * schedProb a q.1 rest

/-- The run of the composition a schedule realizes. -/
def realize : A → B → List ((A × ℝ) ⊕ (B × ℝ)) → List ((A × B) × ℝ)
  | _, _, [] => []
  | _, b, .inl p :: rest => ((p.1, b), p.2) :: realize p.1 b rest
  | a, _, .inr q :: rest => ((a, q.1), q.2) :: realize a q.1 rest

/-- **A schedule's likelihood is the jump-chain likelihood of the run it realizes.** -/
theorem pathProb_realize : ∀ (a : A) (b : B) (σ : List ((A × ℝ) ⊕ (B × ℝ))),
    pathProb (par stepA stepB) (a, b) (realize a b σ) = schedProb stepA stepB a b σ
  | _, _, [] => rfl
  | a, b, .inl p :: rest => by
      simp only [realize, pathProb, schedProb, total_par, pathProb_realize p.1 b rest]
  | a, b, .inr q :: rest => by
      simp only [realize, pathProb, schedProb, total_par, pathProb_realize a q.1 rest]

theorem isRun_realize_inl (b : B) : ∀ (a : A) (α : List (A × ℝ)), IsRun stepA a α →
    IsRun (par stepA stepB) (a, b) (realize a b (α.map Sum.inl))
  | _, [], _ => .nil _
  | _, p :: rest, .cons member later =>
      .cons (List.mem_append_left _ (List.mem_map.mpr ⟨p, member, rfl⟩))
        (isRun_realize_inl b p.1 rest later)

theorem isRun_realize_inr (a : A) : ∀ (b : B) (β : List (B × ℝ)), IsRun stepB b β →
    IsRun (par stepA stepB) (a, b) (realize a b (β.map Sum.inr))
  | _, [], _ => .nil _
  | _, q :: rest, .cons member later =>
      .cons (List.mem_append_right _ (List.mem_map.mpr ⟨q, member, rfl⟩))
        (isRun_realize_inr a q.1 rest later)

/-- **Every shuffle of two runs realizes a run of the composition.** -/
theorem isRun_realize : ∀ (α : List (A × ℝ)) (β : List (B × ℝ)) (a : A) (b : B),
    IsRun stepA a α → IsRun stepB b β →
      ∀ σ ∈ shuffles α β, IsRun (par stepA stepB) (a, b) (realize a b σ) := by
  intro α β
  induction α, β using shuffles.induct with
  | case1 ys =>
      intro a b _ runB σ member
      simp only [shuffles, List.mem_singleton] at member
      subst member
      exact isRun_realize_inr stepA stepB a b ys runB
  | case2 x xs =>
      intro a b runA _ σ member
      simp only [shuffles, List.mem_singleton] at member
      subst member
      exact isRun_realize_inl stepA stepB b a (x :: xs) runA
  | case3 x xs y ys ih1 ih2 =>
      intro a b runA runB σ member
      cases runA with
      | cons memx runxs =>
      cases runB with
      | cons memy runys =>
      simp only [shuffles, List.mem_append, List.mem_map] at member
      rcases member with ⟨τ, inτ, rfl⟩ | ⟨τ, inτ, rfl⟩
      · exact .cons (List.mem_append_left _ (List.mem_map.mpr ⟨x, memx, rfl⟩))
          (ih1 x.1 b runxs (.cons memy runys) τ inτ)
      · exact .cons (List.mem_append_right _ (List.mem_map.mpr ⟨y, memy, rfl⟩))
          (ih2 a y.1 (.cons memx runxs) runys τ inτ)

theorem schedProb_inl {b : B} (deadB : total stepB b = 0) :
    ∀ (a : A) (α : List (A × ℝ)), schedProb stepA stepB a b (α.map Sum.inl) = pathProb stepA a α
  | _, [] => rfl
  | a, p :: rest => by
      simp only [List.map_cons, schedProb, pathProb, deadB, add_zero, schedProb_inl deadB p.1 rest]

theorem schedProb_inr {a : A} (deadA : total stepA a = 0) :
    ∀ (b : B) (β : List (B × ℝ)), schedProb stepA stepB a b (β.map Sum.inr) = pathProb stepB b β
  | _, [] => rfl
  | b, q :: rest => by
      simp only [List.map_cons, schedProb, pathProb, deadA, zero_add, schedProb_inr deadA q.1 rest]

/-- **The race identity.** Summed over the shuffles of a maximal run of each side, the jump-chain
likelihood of the composition's schedules is the product of the two sides' likelihoods. -/
theorem sum_shuffles (positiveA : Positive stepA) (positiveB : Positive stepB) :
    ∀ (α : List (A × ℝ)) (β : List (B × ℝ)) (a : A) (b : B),
      IsRun stepA a α → IsRun stepB b β →
      IsNormal stepA (endState a α) → IsNormal stepB (endState b β) →
      ((shuffles α β).map (schedProb stepA stepB a b)).sum =
        pathProb stepA a α * pathProb stepB b β := by
  intro α β
  induction α, β using shuffles.induct with
  | case1 ys =>
      intro a b _ _ deadA _
      have hA : total stepA a = 0 := total_eq_zero_of_normal deadA
      simp [shuffles, schedProb_inr stepA stepB hA, pathProb]
  | case2 x xs =>
      intro a b _ _ _ deadB
      have hB : total stepB b = 0 := total_eq_zero_of_normal deadB
      rw [shuffles_nil_right, List.map_singleton, List.sum_singleton,
        schedProb_inl stepA stepB hB]
      simp [pathProb]
  | case3 x xs y ys ih1 ih2 =>
      intro a b runA runB deadA deadB
      cases runA with
      | cons memx runxs =>
      cases runB with
      | cons memy runys =>
      have hA : 0 < total stepA a := total_pos positiveA memx
      have hB : 0 < total stepB b := total_pos positiveB memy
      have e1 := ih1 x.1 b runxs (.cons memy runys) deadA deadB
      have e2 := ih2 a y.1 (.cons memx runxs) runys deadA deadB
      have split : (shuffles (x :: xs) (y :: ys)).map (schedProb stepA stepB a b) =
          (shuffles xs (y :: ys)).map
              (fun σ => x.2 / (total stepA a + total stepB b) * schedProb stepA stepB x.1 b σ) ++
            (shuffles (x :: xs) ys).map
              (fun σ => y.2 / (total stepA a + total stepB b) * schedProb stepA stepB a y.1 σ) := by
        simp only [shuffles, List.map_append, List.map_map]
        rfl
      rw [split, List.sum_append, List.sum_map_mul_left, List.sum_map_mul_left, e1, e2]
      have hA' : total stepA a ≠ 0 := hA.ne'
      have hB' : total stepB b ≠ 0 := hB.ne'
      have hAB : total stepA a + total stepB b ≠ 0 := (add_pos hA hB).ne'
      simp only [pathProb]
      field_simp

/-- **A causal history's likelihood factorizes.** Summed over the runs of the composition that the
shuffles realize, the jump-chain likelihood is the product of the two sides' likelihoods. -/
theorem history_factorizes (positiveA : Positive stepA) (positiveB : Positive stepB)
    {a : A} {b : B} {α : List (A × ℝ)} {β : List (B × ℝ)}
    (maximalA : Maximal stepA a α) (maximalB : Maximal stepB b β) :
    ((shuffles α β).map fun σ => pathProb (par stepA stepB) (a, b) (realize a b σ)).sum =
      pathProb stepA a α * pathProb stepB b β := by
  simp only [pathProb_realize]
  exact sum_shuffles stepA stepB positiveA positiveB α β a b maximalA.1 maximalB.1
    maximalA.2 maximalB.2

/-- **A deterministic side is intervention-transparent on causal histories**: its factor is `1`
for every positive weight, so the history's likelihood is the other side's. -/
theorem deterministic_transparent (positiveA : Positive stepA) (positiveB : Positive stepB)
    {a : A} {b : B} {α : List (A × ℝ)} {β : List (B × ℝ)}
    (maximalA : Maximal stepA a α) (determined : Determined stepA a α)
    (maximalB : Maximal stepB b β) :
    ((shuffles α β).map fun σ => pathProb (par stepA stepB) (a, b) (realize a b σ)).sum =
      pathProb stepB b β := by
  rw [history_factorizes stepA stepB positiveA positiveB maximalA maximalB,
    pathProb_determined positiveA determined, one_mul]

end Composition

#print axioms total_pos
#print axioms pathProb_determined
#print axioms restrict_restrict
#print axioms restrict_true
#print axioms pathProb_restrict_single
#print axioms shuffles_nil_right
#print axioms mem_shuffles_iff
#print axioms shuffles_nodup
#print axioms total_par
#print axioms isNormal_par_iff
#print axioms pathProb_realize
#print axioms isRun_realize
#print axioms sum_shuffles
#print axioms history_factorizes
#print axioms deterministic_transparent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalHistories

end
