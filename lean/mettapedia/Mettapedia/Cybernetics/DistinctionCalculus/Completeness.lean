import Mettapedia.Cybernetics.DistinctionCalculus.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn

/-!
# Path lemmas and completeness for graded indistinguishability

Every concrete path in the seed is a derivation, and every metric extension
obeys every path bound. On a finite carrier the converse also holds: a bound
valid in every metric extension is the cost of a min-cost simple path, hence
derivable. The same simple-path infimum is the least metric extension of the
seed. Least extensions are unique (`leastMetricExtension_unique`). HS11.05
(the integral-quantale generalization) is not proved here.
-/

set_option autoImplicit false

universe u

namespace Mettapedia.Cybernetics.DistinctionCalculus

variable {V : Type u} {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Łukasiewicz (capped) path composition on distances. -/
def combine (r s : R) : R := min (1 : R) (r + s)

theorem combine_nonneg {r s : R} (hr : 0 ≤ r) (hs : 0 ≤ s) : 0 ≤ combine r s :=
  le_min (by norm_num) (add_nonneg hr hs)

omit [IsStrictOrderedRing R] in
theorem combine_le_one (r s : R) : combine r s ≤ 1 := min_le_left _ _

theorem combine_mono {r r' s s' : R} (hr : r ≤ r') (hs : s ≤ s') :
    combine r s ≤ combine r' s' :=
  min_le_min le_rfl (add_le_add hr hs)

/-- Capped cost of a node list. -/
def pathCost [DecidableEq V] (a : Tolerance V R) : List V → R
  | [] => 0
  | [_] => 0
  | x :: y :: rest => combine (a.distance x y) (pathCost a (y :: rest))

theorem pathCost_nonneg [DecidableEq V] (a : Tolerance V R) :
    ∀ p, 0 ≤ pathCost a p
  | [] => by simp [pathCost]
  | [_] => by simp [pathCost]
  | x :: y :: rest =>
      combine_nonneg (a.distance_nonnegative x y) (pathCost_nonneg a (y :: rest))

theorem pathCost_le_one [DecidableEq V] (a : Tolerance V R) :
    ∀ p, pathCost a p ≤ 1
  | [] => by simp [pathCost]
  | [_] => by simp [pathCost]
  | x :: y :: rest => combine_le_one _ _

theorem pathCost_pair [DecidableEq V] (a : Tolerance V R) (x y : V) :
    pathCost a [x, y] = a.distance x y := by
  have := a.distance_nonnegative x y
  have := a.distance_bounded x y
  simp [pathCost, combine]
  linarith

/-- Certificate of a nonempty node list. -/
def certFromPath : (p : List V) → p ≠ [] → Certificate V
  | [x], _ => .refl x
  | x :: y :: rest, _ =>
      .triangle (.edge x y) (certFromPath (y :: rest) (by simp))
  | [], h => (h rfl).elim

theorem infer_certFromPath [DecidableEq V] (a : Tolerance V) :
    ∀ (p : List V) (hp : p ≠ []) {x y : V},
      p.head? = some x → p.getLast? = some y →
      infer a (certFromPath p hp) = some ⟨x, y, pathCost a p⟩
  | [x], _, x', y', hx, hy => by
      simp [List.head?, List.getLast?] at hx hy
      subst hx
      subst hy
      simp [certFromPath, infer, pathCost]
  | x :: y :: rest, _, x', y', hx, hy => by
      simp [List.head?] at hx
      subst hx
      have hy' : (y :: rest).getLast? = some y' := by
        cases rest with
        | nil => simpa [List.getLast?] using hy
        | cons _ _ => simpa [List.getLast?] using hy
      have hx' : (y :: rest).head? = some y := rfl
      have ih := infer_certFromPath a (y :: rest) (by simp) hx' hy'
      simp [certFromPath, infer, pathCost, ih, combine]

/-- Every concrete path is a derivation of its capped cost. -/
theorem derives_of_path [DecidableEq V] (a : Tolerance V)
    (p : List V) (hp : p ≠ []) {x y : V}
    (hx : p.head? = some x) (hy : p.getLast? = some y) :
    Derives a ⟨x, y, pathCost a p⟩ :=
  infer_derives a (certFromPath p hp) (infer_certFromPath a p hp hx hy)

theorem derives_of_path_bound [DecidableEq V] (a : Tolerance V)
    (p : List V) (hp : p ≠ []) {x y : V} {r : ℚ}
    (hx : p.head? = some x) (hy : p.getLast? = some y)
    (hle : pathCost a p ≤ r) : Derives a ⟨x, y, r⟩ :=
  (derives_of_path a p hp hx hy).weaken hle

theorem getLast?_cons_of_ne_nil {α : Type u} (x : α) {p : List α} (hp : p ≠ []) :
    (x :: p).getLast? = p.getLast? := by
  cases p with
  | nil => exact (hp rfl).elim
  | cons _ _ => simp

/-- A metric extension cannot undercut any seed path. -/
theorem metric_le_path [DecidableEq V] {a model : Tolerance V R}
    (metric : model.Metric) (hExt : a.Extends model) :
    ∀ p x y, p ≠ [] → p.head? = some x → p.getLast? = some y →
      model.distance x y ≤ pathCost a p
  | [x], x', y', _, hx, hy => by
      simp [List.head?, List.getLast?] at hx hy
      subst hx
      subst hy
      simp [pathCost]
  | [x, y], x', y', _, hx, hy => by
      simp [List.head?, List.getLast?] at hx hy
      subst hx
      subst hy
      simpa [pathCost_pair] using Tolerance.distance_le_of_extends hExt x y
  | x :: y :: z :: rest, x', y', _, hx, hy => by
      simp [List.head?] at hx
      subst hx
      have hy' : (y :: z :: rest).getLast? = some y' := by
        simpa [getLast?_cons_of_ne_nil] using hy
      have ih := metric_le_path metric hExt (y :: z :: rest) y y'
        (by simp) (by simp) hy'
      have tri := metric x y y'
      have hxy := Tolerance.distance_le_of_extends hExt x y
      simp [pathCost]
      exact le_min (model.distance_bounded x y') (le_trans tri (add_le_add hxy ih))
  | [], _, _, hp, _, _ => (hp rfl).elim

/-- A path bound is derivable and holds in every metric extension.
This is soundness of a given path, not completeness. -/
theorem path_bound_derivable_and_valid [DecidableEq V] (a : Tolerance V)
    (p : List V) (hp : p ≠ []) {x y : V} {r : ℚ}
    (hx : p.head? = some x) (hy : p.getLast? = some y)
    (hle : pathCost a p ≤ r) :
    Derives a ⟨x, y, r⟩ ∧
      ∀ model, a.Extends model → model.Metric → model.distance x y ≤ r := by
  refine ⟨derives_of_path_bound a p hp hx hy hle, ?_⟩
  intro model hExt metric
  exact (metric_le_path metric hExt p x y hp hx hy).trans hle

/-- Seed-edge producer: reflexivity or the authored edge. -/
def produceSeed [DecidableEq V] (x y : V) : Certificate V :=
  if x = y then .refl x else .edge x y

theorem produceSeed_checks [DecidableEq V] (a : Tolerance V) (x y : V) :
    check a ⟨x, y, if x = y then 0 else a.distance x y⟩ (produceSeed x y) = true := by
  unfold check produceSeed
  split_ifs with hxy
  · subst hxy
    simp [infer]
  · simp [infer]

/-- Uncapped path cost. `pathCost` is this value capped at 1. -/
def rawPathCost [DecidableEq V] (a : Tolerance V R) : List V → R
  | [] => 0
  | [_] => 0
  | x :: y :: rest => a.distance x y + rawPathCost a (y :: rest)

theorem rawPathCost_nonneg [DecidableEq V] (a : Tolerance V R) :
    ∀ p, 0 ≤ rawPathCost a p
  | [] => by simp [rawPathCost]
  | [_] => by simp [rawPathCost]
  | x :: y :: rest =>
      add_nonneg (a.distance_nonnegative x y) (rawPathCost_nonneg a (y :: rest))

theorem min_one_add_min_one {d s : R} (hd : 0 ≤ d) (_hs : 0 ≤ s) :
    min (1 : R) (d + min 1 s) = min 1 (d + s) := by
  cases le_total s 1 with
  | inl h => rw [min_eq_right h]
  | inr h =>
      have h1 : (1 : R) ≤ d + 1 := by linarith
      have h2 : (1 : R) ≤ d + s := by linarith
      rw [min_eq_left h, min_eq_left h1, min_eq_left h2]

theorem pathCost_eq_min_raw [DecidableEq V] (a : Tolerance V R) :
    ∀ p, pathCost a p = min 1 (rawPathCost a p)
  | [] => by simp [pathCost, rawPathCost]
  | [_] => by simp [pathCost, rawPathCost]
  | x :: y :: rest => by
      have ih := pathCost_eq_min_raw a (y :: rest)
      have hd := a.distance_nonnegative x y
      have hs := rawPathCost_nonneg a (y :: rest)
      simp [pathCost, rawPathCost, combine, ih]
      exact min_one_add_min_one hd hs

theorem rawPathCost_concat_cons [DecidableEq V] (a : Tolerance V R) :
    ∀ (ys : List V) (x : V) (tail : List V),
      rawPathCost a (ys ++ x :: tail) =
        rawPathCost a (ys ++ [x]) + rawPathCost a (x :: tail)
  | [], x, tail => by simp [rawPathCost]
  | [y], x, tail => by simp [rawPathCost]
  | y :: z :: rest, x, tail => by
      have ih := rawPathCost_concat_cons a (z :: rest) x tail
      calc
        rawPathCost a (y :: z :: rest ++ x :: tail)
            = a.distance y z + rawPathCost a (z :: rest ++ x :: tail) := rfl
        _ = a.distance y z + (rawPathCost a (z :: rest ++ [x]) + rawPathCost a (x :: tail)) :=
          by rw [ih]
        _ = rawPathCost a (y :: z :: rest ++ [x]) + rawPathCost a (x :: tail) := by
          simp [rawPathCost, add_assoc]

theorem rawPathCost_drop_cycle [DecidableEq V] (a : Tolerance V R)
    (pre mid post : List V) (x : V) :
    rawPathCost a (pre ++ x :: post) ≤
      rawPathCost a (pre ++ x :: mid ++ x :: post) := by
  have hshort := rawPathCost_concat_cons a pre x post
  have hlong :
      rawPathCost a (pre ++ (x :: mid ++ x :: post)) =
        rawPathCost a (pre ++ [x]) + rawPathCost a (x :: mid ++ x :: post) :=
    rawPathCost_concat_cons a pre x (mid ++ x :: post)
  have hmid :
      rawPathCost a (x :: mid ++ x :: post) =
        rawPathCost a (x :: mid ++ [x]) + rawPathCost a (x :: post) :=
    rawPathCost_concat_cons a (x :: mid) x post
  have hnn := rawPathCost_nonneg a (x :: mid ++ [x])
  have : pre ++ x :: mid ++ x :: post = pre ++ (x :: mid ++ x :: post) := by
    simp [List.append_assoc]
  rw [hshort, this, hlong, hmid]
  linarith

theorem exists_double_occurrence {α : Type u} [DecidableEq α] {p : List α}
    (h : ¬ p.Nodup) :
    ∃ (x : α) (pre mid post : List α), p = pre ++ x :: mid ++ x :: post := by
  obtain ⟨x, hx⟩ : ∃ x, ¬ p.count x ≤ 1 := by
    have : ¬ ∀ x, p.count x ≤ 1 := fun hall => h (List.nodup_iff_count.mpr hall)
    simpa [not_forall] using this
  have hx2 : 2 ≤ p.count x := Nat.succ_le_of_lt (lt_of_not_ge hx)
  have hxmem : x ∈ p := List.count_pos_iff.mp (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hx2)
  obtain ⟨pre, rest, hp⟩ := List.mem_iff_append.mp hxmem
  have hcount : p.count x = pre.count x + rest.count x + 1 := by
    rw [hp, List.count_append, List.count_cons_self]
    ac_rfl
  have hmem : x ∈ pre ∨ x ∈ rest := by
    by_contra hneither
    simp only [not_or] at hneither
    have hpre : pre.count x = 0 := List.count_eq_zero.mpr hneither.1
    have hrest : rest.count x = 0 := List.count_eq_zero.mpr hneither.2
    omega
  cases hmem with
  | inl hpre =>
      obtain ⟨pre1, mid, hpre'⟩ := List.mem_iff_append.mp hpre
      refine ⟨x, pre1, mid, rest, ?_⟩
      simp [hp, hpre', List.append_assoc]
  | inr hrest =>
      obtain ⟨mid, post, hrest'⟩ := List.mem_iff_append.mp hrest
      refine ⟨x, pre, mid, post, ?_⟩
      simp [hp, hrest']

theorem head?_drop_cycle {α : Type u} (pre mid post : List α) (x : α) :
    (pre ++ x :: post).head? = (pre ++ x :: mid ++ x :: post).head? := by
  cases pre <;> simp [List.append_assoc]

theorem getLast?_drop_cycle {α : Type u} (pre mid post : List α) (x : α) :
    (pre ++ x :: post).getLast? = (pre ++ x :: mid ++ x :: post).getLast? := by
  simp only [List.getLast?_append]
  rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x post)]
  simp

theorem exists_simple_le [DecidableEq V] (a : Tolerance V R) (p : List V) :
    ∃ q, q.Nodup ∧ q.head? = p.head? ∧ q.getLast? = p.getLast? ∧
      rawPathCost a q ≤ rawPathCost a p ∧ (p ≠ [] → q ≠ []) := by
  generalize hlen : p.length = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
      subst hlen
      by_cases hnd : p.Nodup
      · exact ⟨p, hnd, rfl, rfl, le_rfl, id⟩
      · obtain ⟨x, pre, mid, post, hp⟩ := exists_double_occurrence hnd
        set p' := pre ++ x :: post
        have hlt : p'.length < p.length := by
          rw [hp]
          simp [p', List.length_append]
        obtain ⟨q, hqNodup, hqHead, hqLast, hqCost, hqNe⟩ := ih p'.length hlt p' rfl
        refine ⟨q, hqNodup, ?_, ?_, ?_, ?_⟩
        · rw [hqHead, hp]; exact head?_drop_cycle pre mid post x
        · rw [hqLast, hp]; exact getLast?_drop_cycle pre mid post x
        · exact hqCost.trans (by simpa [p', hp] using rawPathCost_drop_cycle a pre mid post x)
        · intro _
          have : p' ≠ [] := by simp [p']
          exact hqNe this

def listsOfLength [Fintype V] [DecidableEq V] (n : ℕ) : Finset (List V) :=
  (Finset.univ : Finset (Fin n → V)).image List.ofFn

theorem mem_listsOfLength [Fintype V] [DecidableEq V] {n : ℕ} {p : List V} :
    p ∈ listsOfLength (V := V) n ↔ p.length = n := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨f, -, hf⟩
    rw [← hf]; simp [List.length_ofFn]
  · intro hlen
    rw [show n = p.length from hlen.symm]
    exact Finset.mem_image.mpr ⟨p.get, Finset.mem_univ _, List.ofFn_get p⟩

def simplePaths [Fintype V] [DecidableEq V] (x y : V) : Finset (List V) :=
  (Finset.range (Fintype.card V + 1)).biUnion fun n =>
    (listsOfLength (V := V) n).filter fun p =>
      p.Nodup ∧ p.head? = some x ∧ p.getLast? = some y

theorem mem_simplePaths [Fintype V] [DecidableEq V] {x y : V} {p : List V} :
    p ∈ simplePaths x y ↔
      p.Nodup ∧ p.head? = some x ∧ p.getLast? = some y ∧
        p.length ≤ Fintype.card V := by
  constructor
  · intro h
    obtain ⟨n, hn, hp⟩ := Finset.mem_biUnion.mp h
    rw [Finset.mem_range] at hn
    rw [Finset.mem_filter, mem_listsOfLength] at hp
    rcases hp with ⟨hlen, hnd, hh, hl⟩
    exact ⟨hnd, hh, hl, Nat.lt_succ_iff.mp (hlen ▸ hn)⟩
  · intro ⟨hnd, hh, hl, hlen⟩
    refine Finset.mem_biUnion.mpr ⟨p.length, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hlen), ?_⟩
    rw [Finset.mem_filter, mem_listsOfLength]
    exact ⟨rfl, hnd, hh, hl⟩

theorem singleton_mem_simplePaths [Fintype V] [DecidableEq V] (x : V) :
    [x] ∈ simplePaths x x := by
  rw [mem_simplePaths]
  refine ⟨List.nodup_singleton x, rfl, rfl, ?_⟩
  simp
  exact Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨x⟩)

theorem pair_mem_simplePaths [Fintype V] [DecidableEq V] {x y : V} (h : x ≠ y) :
    [x, y] ∈ simplePaths x y := by
  rw [mem_simplePaths]
  refine ⟨?_, rfl, rfl, ?_⟩
  · simp [h]
  · have hcard : ({x, y} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr h),
        Finset.card_singleton]
    have : 2 ≤ Fintype.card V := hcard ▸ Finset.card_le_univ ({x, y} : Finset V)
    simpa using this

theorem simplePaths_nonempty [Fintype V] [DecidableEq V] (x y : V) :
    (simplePaths x y).Nonempty := by
  by_cases hxy : x = y
  · subst hxy
    exact ⟨[x], singleton_mem_simplePaths x⟩
  · exact ⟨[x, y], pair_mem_simplePaths hxy⟩

def shortestDistance [Fintype V] [DecidableEq V] (a : Tolerance V R) (x y : V) : R :=
  (simplePaths x y).inf' (simplePaths_nonempty x y) (pathCost a)

theorem shortestDistance_le [Fintype V] [DecidableEq V] (a : Tolerance V R)
    {x y : V} {p : List V} (hp : p ∈ simplePaths x y) :
    shortestDistance a x y ≤ pathCost a p :=
  Finset.inf'_le (pathCost a) hp

theorem le_shortestDistance [Fintype V] [DecidableEq V] (a : Tolerance V R)
    {x y : V} {r : R} (h : ∀ p ∈ simplePaths x y, r ≤ pathCost a p) :
    r ≤ shortestDistance a x y :=
  (Finset.le_inf'_iff _ _).mpr h

theorem reverse_mem_simplePaths [Fintype V] [DecidableEq V] {x y : V} {p : List V}
    (hp : p ∈ simplePaths x y) : p.reverse ∈ simplePaths y x := by
  rw [mem_simplePaths] at hp ⊢
  rcases hp with ⟨hnd, hh, hl, hlen⟩
  refine ⟨List.nodup_reverse.mpr hnd, ?_, ?_, by simpa using hlen⟩
  · simpa [List.head?_reverse] using hl
  · simpa [List.getLast?_reverse] using hh

theorem rawPathCost_snoc [DecidableEq V] (a : Tolerance V R) (p : List V) (x : V)
    (hp : p ≠ []) :
    rawPathCost a (p ++ [x]) =
      rawPathCost a p + a.distance (p.getLast hp) x := by
  have hsplit := List.dropLast_concat_getLast hp
  suffices h :
      rawPathCost a ((p.dropLast ++ [p.getLast hp]) ++ [x]) =
        rawPathCost a (p.dropLast ++ [p.getLast hp]) + a.distance (p.getLast hp) x by
    simpa [hsplit] using h
  simp [List.append_assoc]
  rw [rawPathCost_concat_cons]
  simp [rawPathCost]

theorem rawPathCost_reverse [DecidableEq V] (a : Tolerance V R) :
    ∀ p, rawPathCost a p.reverse = rawPathCost a p
  | [] => by simp [rawPathCost]
  | [x] => by simp [rawPathCost]
  | x :: y :: rest => by
      have ih := rawPathCost_reverse a (y :: rest)
      have hne : (y :: rest).reverse ≠ [] := by simp
      rw [List.reverse_cons, rawPathCost_snoc a ((y :: rest).reverse) x hne]
      have hlast : (y :: rest).reverse.getLast hne = y := by
        apply Option.some.inj
        rw [← List.getLast?_eq_some_getLast hne, List.getLast?_reverse]
        simp
      rw [hlast, ih, a.distance_symm y x]
      simp [rawPathCost]
      abel

theorem pathCost_reverse [DecidableEq V] (a : Tolerance V R) (p : List V) :
    pathCost a p.reverse = pathCost a p := by
  simp [pathCost_eq_min_raw, rawPathCost_reverse]

theorem shortestDistance_symm [Fintype V] [DecidableEq V] (a : Tolerance V R)
    (x y : V) : shortestDistance a x y = shortestDistance a y x := by
  refine le_antisymm ?_ ?_
  · apply le_shortestDistance
    intro p hp
    have := shortestDistance_le a (reverse_mem_simplePaths hp)
    simpa [pathCost_reverse] using this
  · apply le_shortestDistance
    intro p hp
    have := shortestDistance_le a (reverse_mem_simplePaths hp)
    simpa [pathCost_reverse] using this

theorem shortestDistance_le_seed [Fintype V] [DecidableEq V]
    (a : Tolerance V R) (x y : V) :
    shortestDistance a x y ≤ a.distance x y := by
  by_cases hxy : x = y
  · subst hxy
    simpa [pathCost, a.distance_self] using
      shortestDistance_le a (singleton_mem_simplePaths x)
  · simpa [pathCost_pair] using shortestDistance_le a (pair_mem_simplePaths hxy)

theorem shortestDistance_nonneg [Fintype V] [DecidableEq V]
    (a : Tolerance V R) (x y : V) : 0 ≤ shortestDistance a x y :=
  le_shortestDistance a fun p _ => pathCost_nonneg a p

theorem shortestDistance_le_one [Fintype V] [DecidableEq V]
    (a : Tolerance V R) (x y : V) : shortestDistance a x y ≤ 1 := by
  obtain ⟨p, hp⟩ := simplePaths_nonempty (x := x) (y := y)
  exact (shortestDistance_le a hp).trans (pathCost_le_one a p)

theorem shortestDistance_self [Fintype V] [DecidableEq V]
    (a : Tolerance V R) (x : V) : shortestDistance a x x = 0 := by
  refine le_antisymm ?_ (shortestDistance_nonneg a x x)
  simpa [a.distance_self] using shortestDistance_le_seed a x x

theorem min_one_add {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min (1 : R) (a + b) ≤ min 1 a + min 1 b := by
  have hmina : 0 ≤ min (1 : R) a := le_min (by norm_num) ha
  have hminb : 0 ≤ min (1 : R) b := le_min (by norm_num) hb
  cases le_total (a + b) 1 with
  | inl h =>
      have ha1 : a ≤ 1 := by linarith
      have hb1 : b ≤ 1 := by linarith
      simp [min_eq_right h, min_eq_right ha1, min_eq_right hb1]
  | inr h =>
      have : (1 : R) ≤ min 1 a + min 1 b := by
        cases le_total a 1 with
        | inl ha1 =>
            cases le_total b 1 with
            | inl hb1 =>
                simp [min_eq_right ha1, min_eq_right hb1]
                linarith
            | inr hb1 =>
                rw [min_eq_left hb1]
                exact le_add_of_nonneg_left hmina
        | inr ha1 =>
            rw [min_eq_left ha1]
            exact le_add_of_nonneg_right hminb
      simpa [min_eq_left h] using this

theorem rawPathCost_join [DecidableEq V] (a : Tolerance V R) {p q : List V}
    (hp : p ≠ []) (hq : q ≠ []) (hjoin : p.getLast? = q.head?) :
    rawPathCost a (p ++ q.tail) = rawPathCost a p + rawPathCost a q := by
  cases q with
  | nil => exact (hq rfl).elim
  | cons y rest =>
      have hy : p.getLast? = some y := by simpa [List.head?] using hjoin
      have hsplit := List.dropLast_concat_getLast hp
      have hlast : p.getLast hp = y := by
        have := List.getLast?_eq_some_getLast hp
        exact Option.some.inj (this.symm.trans hy)
      have : p ++ (y :: rest).tail = p.dropLast ++ y :: rest := by
        simp [List.tail]
        rw [← hsplit, hlast]
        simp [List.append_assoc]
      rw [this, rawPathCost_concat_cons]
      have hpre : p.dropLast ++ [y] = p := by
        rw [← hlast, hsplit]
      simp [hpre]

theorem pathCost_join [DecidableEq V] (a : Tolerance V R) {p q : List V}
    (hp : p ≠ []) (hq : q ≠ []) (hjoin : p.getLast? = q.head?) :
    pathCost a (p ++ q.tail) ≤ pathCost a p + pathCost a q := by
  have hraw := rawPathCost_join a hp hq hjoin
  rw [pathCost_eq_min_raw, pathCost_eq_min_raw, pathCost_eq_min_raw, hraw]
  exact min_one_add (rawPathCost_nonneg a p) (rawPathCost_nonneg a q)

theorem ne_nil_of_head? {α : Type u} {p : List α} {x : α}
    (h : p.head? = some x) : p ≠ [] := by
  intro hnil
  simp [hnil] at h

theorem shortestDistance_triangle [Fintype V] [DecidableEq V]
    (a : Tolerance V R) (x y z : V) :
    shortestDistance a x z ≤ shortestDistance a x y + shortestDistance a y z := by
  obtain ⟨px, hpx, hcx⟩ :=
    Finset.exists_mem_eq_inf' (simplePaths_nonempty (x := x) (y := y)) (pathCost a)
  obtain ⟨py, hpy, hcy⟩ :=
    Finset.exists_mem_eq_inf' (simplePaths_nonempty (x := y) (y := z)) (pathCost a)
  have hpxs := (mem_simplePaths (x := x) (y := y)).1 hpx
  have hpys := (mem_simplePaths (x := y) (y := z)).1 hpy
  have pxne : px ≠ [] := ne_nil_of_head? hpxs.2.1
  have pyne : py ≠ [] := ne_nil_of_head? hpys.2.1
  set r := px ++ py.tail with hr
  have hjoin : px.getLast? = py.head? := by
    rw [hpxs.2.2.1, hpys.2.1]
  have hr_head : r.head? = some x := by
    cases px with
    | nil => exact (pxne rfl).elim
    | cons => simpa [r] using hpxs.2.1
  have hr_last : r.getLast? = some z := by
    cases py with
    | nil => exact (pyne rfl).elim
    | cons y' rest =>
        have hy' : y' = y := by simpa [List.head?] using hpys.2.1
        subst y'
        cases rest with
        | nil =>
            have hyz : y = z := by simpa [List.getLast?] using hpys.2.2.1
            subst hyz
            simpa [r] using hpxs.2.2.1
        | cons _ _ =>
            simp [r, List.getLast?_append]
            simpa using hpys.2.2.1
  have hrne : r ≠ [] := by
    cases px with
    | nil => exact (pxne rfl).elim
    | cons => simp [r]
  obtain ⟨q, qnd, qh, ql, qcost, qne⟩ := exists_simple_le a r
  have hqne := qne hrne
  have hqmem : q ∈ simplePaths x z := by
    rw [mem_simplePaths]
    exact ⟨qnd, qh.trans hr_head, ql.trans hr_last, List.Nodup.length_le_card qnd⟩
  have hqr : pathCost a q ≤ pathCost a r := by
    rw [pathCost_eq_min_raw, pathCost_eq_min_raw]
    exact min_le_min le_rfl qcost
  have hrbound : pathCost a r ≤ pathCost a px + pathCost a py :=
    pathCost_join a pxne pyne hjoin
  calc
    shortestDistance a x z ≤ pathCost a q := shortestDistance_le a hqmem
    _ ≤ pathCost a r := hqr
    _ ≤ pathCost a px + pathCost a py := hrbound
    _ = shortestDistance a x y + shortestDistance a y z := by
        simp [shortestDistance, hcx, hcy]

theorem shortestDistance_le_pathCost [Fintype V] [DecidableEq V]
    (a : Tolerance V R) {p : List V} {x y : V} (_hp : p ≠ [])
    (hx : p.head? = some x) (hy : p.getLast? = some y) :
    shortestDistance a x y ≤ pathCost a p := by
  obtain ⟨q, qnd, qh, ql, qcost, qne⟩ := exists_simple_le a p
  have hqmem : q ∈ simplePaths x y := by
    rw [mem_simplePaths]
    exact ⟨qnd, qh.trans hx, ql.trans hy, List.Nodup.length_le_card qnd⟩
  have hle : pathCost a q ≤ pathCost a p := by
    rw [pathCost_eq_min_raw, pathCost_eq_min_raw]
    exact min_le_min le_rfl qcost
  exact (shortestDistance_le a hqmem).trans hle

def shortestTolerance [Fintype V] [DecidableEq V] (a : Tolerance V R) : Tolerance V R where
  similarity x y := 1 - shortestDistance a x y
  nonnegative x y := sub_nonneg.mpr (shortestDistance_le_one a x y)
  bounded x y := by
    have := shortestDistance_nonneg a x y
    linarith
  reflexive x := by simp [shortestDistance_self]
  symmetric x y := by simp [shortestDistance_symm a x y]

@[simp] theorem shortestTolerance_distance [Fintype V] [DecidableEq V]
    (a : Tolerance V R) (x y : V) :
    (shortestTolerance a).distance x y = shortestDistance a x y := by
  simp [Tolerance.distance, shortestTolerance]

theorem shortestTolerance_metric [Fintype V] [DecidableEq V] (a : Tolerance V R) :
    (shortestTolerance a).Metric := by
  intro x y z
  simpa [shortestTolerance_distance] using shortestDistance_triangle a x y z

theorem shortestTolerance_extends [Fintype V] [DecidableEq V] (a : Tolerance V R) :
    a.Extends (shortestTolerance a) := by
  intro x y
  have := shortestDistance_le_seed a x y
  simp [shortestTolerance, Tolerance.distance] at this ⊢
  linarith

/-- The simple-path infimum is the least metric extension of the seed. -/
theorem shortestTolerance_is_least [Fintype V] [DecidableEq V] (a : Tolerance V R) :
    LeastMetricExtension a (shortestTolerance a) := by
  refine ⟨shortestTolerance_extends a, shortestTolerance_metric a, ?_⟩
  intro other hExt hMet x y
  have hbound : other.distance x y ≤ shortestDistance a x y := by
    apply le_shortestDistance
    intro p hp
    have hps := (mem_simplePaths (x := x) (y := y)).1 hp
    exact metric_le_path hMet hExt p x y (ne_nil_of_head? hps.2.1) hps.2.1 hps.2.2.1
  simp [shortestTolerance, Tolerance.distance] at hbound ⊢
  linarith

/-- Completeness: a bound valid in every metric extension of the seed is
derivable. The witness is a min-cost simple path. -/
theorem complete [Fintype V] [DecidableEq V] (a : Tolerance V) {x y : V} {r : ℚ}
    (h : ∀ model, a.Extends model → model.Metric → model.distance x y ≤ r) :
    Derives a ⟨x, y, r⟩ := by
  have hbound :=
    h (shortestTolerance a) (shortestTolerance_extends a) (shortestTolerance_metric a)
  have hsd : shortestDistance a x y ≤ r := by
    simpa [shortestTolerance_distance] using hbound
  obtain ⟨p, hp, hpCost⟩ :=
    Finset.exists_mem_eq_inf' (simplePaths_nonempty (x := x) (y := y)) (pathCost a)
  have hps := (mem_simplePaths (x := x) (y := y)).1 hp
  have hle : pathCost a p ≤ r := by
    have : shortestDistance a x y = pathCost a p := hpCost
    linarith
  exact derives_of_path_bound a p (ne_nil_of_head? hps.2.1) hps.2.1 hps.2.2.1 hle

theorem derives_iff_metric_valid [Fintype V] [DecidableEq V]
    (a : Tolerance V) {x y : V} {r : ℚ} :
    Derives a ⟨x, y, r⟩ ↔
      ∀ model, a.Extends model → model.Metric → model.distance x y ≤ r :=
  ⟨fun derv model hExt hMet => derv.sound model hMet hExt, complete a⟩

end Mettapedia.Cybernetics.DistinctionCalculus
