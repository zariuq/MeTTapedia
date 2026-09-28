import Mathlib.Data.List.Basic

/-!
# Selecting an equation among keyed candidates

A deterministic call selects its equation by scanning the equations of its
head in order: none may match, one may, or a second may match as well, which
makes the call ambiguous (`select`).

A refutation-only index hands the scan a sublist of candidates instead, and
drops only equations that cannot match (`MatchDecisionContract` proves this
completeness for skeleton observations).  Scanning the candidates then gives
the same selection as scanning all equations, ambiguity included
(`select_filter_of_complete`): only the matching equations and their order
decide a scan (`select_filter_self`).

A first-argument key is such an index.  An equation can match only an
argument whose key equals the equation's own key, so keeping the equations
with the argument's key drops none that match.  When no two equations share
a key, at most one equation is kept (`keyed_length_le_one`), and the scan of
that one decides the call (`select_keyed`).
-/

namespace Mettapedia.GSLT.LanguageDef.KeyedEquationSelection

/-- The state of a scan: no equation matched yet, exactly one did, or two did. -/
inductive Selection (α : Type*) where
  | none
  | one (a : α)
  | ambiguous
  deriving DecidableEq

variable {α κ : Type*}

/-- One step of the scan: a matching equation is selected, unless one was
already selected, which makes the call ambiguous for good. -/
def step (m : α → Bool) : Selection α → α → Selection α
  | .ambiguous, _ => .ambiguous
  | .none, a => if m a then .one a else .none
  | .one b, a => if m a then .ambiguous else .one b

/-- The executor's scan of equations in order. -/
def select (m : α → Bool) (l : List α) : Selection α :=
  l.foldl (step m) .none

theorem step_of_not (m : α → Bool) (s : Selection α) (a : α)
    (h : m a = false) : step m s a = s := by
  cases s <;> simp [step, h]

theorem foldl_filter_self (m : α → Bool) (s : Selection α) (l : List α) :
    (l.filter m).foldl (step m) s = l.foldl (step m) s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    by_cases h : m a = true
    · simp [h, ih]
    · have hf : m a = false := by simpa using h
      simp [hf, ih, step_of_not m s a hf]

/-- Equations that do not match leave a scan unchanged: only the matching
equations, in their order, decide it. -/
theorem select_filter_self (m : α → Bool) (l : List α) :
    select m (l.filter m) = select m l :=
  foldl_filter_self m .none l

/-- Scanning the candidates of a complete filter selects what scanning every
equation selects. -/
theorem select_filter_of_complete (m p : α → Bool)
    (complete : ∀ a, m a = true → p a = true) (l : List α) :
    select m (l.filter p) = select m l := by
  have hsub : (l.filter p).filter m = l.filter m := by
    rw [List.filter_filter]
    congr 1
    funext a
    by_cases hm : m a = true
    · simp [hm, complete a hm]
    · simp [hm]
  rw [← select_filter_self m (l.filter p), hsub, select_filter_self]

/-- A scan that has selected nothing is not ambiguous after one more
equation. -/
theorem step_none_ne_ambiguous (m : α → Bool) (a : α) :
    step m .none a ≠ .ambiguous := by
  show (if m a = true then Selection.one a else Selection.none) ≠ .ambiguous
  split <;> intro h <;> cases h

/-- The equations whose key is `k`. -/
def keyed [DecidableEq κ] (key : α → κ) (k : κ) (l : List α) : List α :=
  l.filter (fun a => decide (key a = k))

/-- The keyed candidates are empty when no equation has the key. -/
theorem keyed_eq_nil [DecidableEq κ] (key : α → κ) (k : κ) :
    ∀ (l : List α), (∀ b ∈ l, key b ≠ k) → keyed key k l = []
  | [], _ => rfl
  | b :: l, h => by
    have hb : key b ≠ k := h b (List.mem_cons_self ..)
    have hcons : keyed key k (b :: l) = keyed key k l :=
      List.filter_cons_of_neg (fun e => hb (of_decide_eq_true e))
    rw [hcons]
    exact keyed_eq_nil key k l (fun c hc => h c (List.mem_cons_of_mem b hc))

/-- With no two equations sharing a key, at most one has a given key. -/
theorem keyed_length_le_one [DecidableEq κ] (key : α → κ) (k : κ)
    (l : List α) (distinct : l.Pairwise (fun a b => key a ≠ key b)) :
    (keyed key k l).length ≤ 1 := by
  induction l with
  | nil => exact Nat.zero_le 1
  | cons a l ih =>
    have hsplit := List.pairwise_cons.mp distinct
    by_cases ha : key a = k
    · have hnone : keyed key k l = [] :=
        keyed_eq_nil key k l (fun b hb e => hsplit.1 b hb (ha.trans e.symm))
      have hcons : keyed key k (a :: l) = a :: keyed key k l :=
        List.filter_cons_of_pos (decide_eq_true ha)
      rw [hcons, hnone]
      exact Nat.le_refl 1
    · have hcons : keyed key k (a :: l) = keyed key k l :=
        List.filter_cons_of_neg (fun e => ha (of_decide_eq_true e))
      rw [hcons]
      exact ih hsplit.2

/-- An argument whose key is `k`, matched only by equations with key `k`:
scanning the keyed candidates selects what scanning every equation selects. -/
theorem select_keyed [DecidableEq κ] (m : α → Bool) (key : α → κ) (k : κ)
    (keyed_match : ∀ a, m a = true → key a = k) (l : List α) :
    select m (keyed key k l) = select m l :=
  select_filter_of_complete m _ (fun a ha => by simpa using keyed_match a ha) l

/-- With distinct keys the keyed scan runs at most one equation, and it is
never ambiguous. -/
theorem select_keyed_not_ambiguous [DecidableEq κ] (m : α → Bool)
    (key : α → κ) (k : κ) (l : List α) (distinct : l.Pairwise (fun a b => key a ≠ key b)) :
    select m (keyed key k l) ≠ .ambiguous := by
  have hle := keyed_length_le_one key k l distinct
  generalize keyed key k l = c at hle ⊢
  match c, hle with
  | [], _ => intro h; cases h
  | [a], _ => exact step_none_ne_ambiguous m a

/-- Ambiguity is a property of the matching equations alone: a head whose
equations have distinct keys is never ambiguous on a keyed argument. -/
theorem select_not_ambiguous_of_keyed [DecidableEq κ] (m : α → Bool)
    (key : α → κ) (k : κ) (keyed_match : ∀ a, m a = true → key a = k)
    (l : List α) (distinct : l.Pairwise (fun a b => key a ≠ key b)) :
    select m l ≠ .ambiguous := by
  rw [← select_keyed m key k keyed_match l]
  exact select_keyed_not_ambiguous m key k l distinct

/-- A refutation that is not complete changes the selection: dropping the
one matching equation turns a selected call into one that matches nothing. -/
theorem select_filter_incomplete_differs :
    select (fun n : ℕ => n == 1) ([0, 1].filter (fun n => n == 0)) ≠
      select (fun n : ℕ => n == 1) [0, 1] := by
  decide

/-! ## Keys at several argument positions

An equation's pattern at an argument position either tests a key (a symbol,
or the head and length of an expression) or admits any argument (a variable,
or a pattern the key does not describe).  `key a p` is `some k` for a tested
key and `none` otherwise.  An equation admits an argument tuple when each key
it tests equals the argument's key there (`admits`), and two equations are
apart when some position tests different keys in both (`apart`).

When every two equations are apart, at most one admits any tuple
(`admitted_length_le_one`), and when only admitting equations can match, the
scan of the admitting ones decides the call (`select_admitted`).  The
first-argument key above is the case of one position whose every key is
tested. -/

variable {ι : Type*}

/-- A key tested at a position admits only the argument with that key; an
untested position admits any argument. -/
def admitsAt [DecidableEq κ] : Option κ → κ → Bool
  | none, _ => true
  | some k, x => decide (k = x)

/-- Equation `a` admits the arguments whose keys at the positions `ps` are
`arg`. -/
def admits [DecidableEq κ] (ps : List ι) (key : α → ι → Option κ)
    (arg : ι → κ) (a : α) : Bool :=
  ps.all (fun p => admitsAt (key a p) (arg p))

/-- Two equations test different keys at some position. -/
def apart (ps : List ι) (key : α → ι → Option κ) (a b : α) : Prop :=
  ∃ p ∈ ps, ∃ x y, key a p = some x ∧ key b p = some y ∧ x ≠ y

theorem admitsAt_some [DecidableEq κ] {k x : κ}
    (h : admitsAt (some k) x = true) : k = x :=
  of_decide_eq_true h

/-- Two equations that are apart never both admit the same arguments. -/
theorem not_admits_of_apart [DecidableEq κ] (ps : List ι)
    (key : α → ι → Option κ) (arg : ι → κ) {a b : α}
    (hab : apart ps key a b) (ha : admits ps key arg a = true) :
    admits ps key arg b = false := by
  obtain ⟨p, hp, x, y, hx, hy, hxy⟩ := hab
  cases hb : admits ps key arg b with
  | false => rfl
  | true =>
    have hax := List.all_eq_true.mp ha p hp
    have hby := List.all_eq_true.mp hb p hp
    rw [hx] at hax
    rw [hy] at hby
    exact absurd ((admitsAt_some hax).trans (admitsAt_some hby).symm) hxy

/-- The equations admitting the arguments. -/
def admitted [DecidableEq κ] (ps : List ι) (key : α → ι → Option κ)
    (arg : ι → κ) (l : List α) : List α :=
  l.filter (admits ps key arg)

/-- No equation is admitted when none admits the arguments. -/
theorem admitted_eq_nil [DecidableEq κ] (ps : List ι)
    (key : α → ι → Option κ) (arg : ι → κ) :
    ∀ (l : List α), (∀ b ∈ l, admits ps key arg b = false) →
      admitted ps key arg l = []
  | [], _ => rfl
  | b :: l, h => by
    have hb : admits ps key arg b = false := h b (List.mem_cons_self ..)
    have hcons : admitted ps key arg (b :: l) = admitted ps key arg l :=
      List.filter_cons_of_neg (fun e => Bool.false_ne_true (hb.symm.trans e))
    rw [hcons]
    exact admitted_eq_nil ps key arg l
      (fun c hc => h c (List.mem_cons_of_mem b hc))

/-- With every two equations apart, at most one admits the arguments. -/
theorem admitted_length_le_one [DecidableEq κ] (ps : List ι)
    (key : α → ι → Option κ) (arg : ι → κ) (l : List α)
    (distinct : l.Pairwise (apart ps key)) :
    (admitted ps key arg l).length ≤ 1 := by
  induction l with
  | nil => exact Nat.zero_le 1
  | cons a l ih =>
    have hsplit := List.pairwise_cons.mp distinct
    cases ha : admits ps key arg a with
    | true =>
      have hnone : admitted ps key arg l = [] :=
        admitted_eq_nil ps key arg l
          (fun b hb => not_admits_of_apart ps key arg (hsplit.1 b hb) ha)
      have hcons : admitted ps key arg (a :: l) =
          a :: admitted ps key arg l :=
        List.filter_cons_of_pos ha
      rw [hcons, hnone]
      exact Nat.le_refl 1
    | false =>
      have hcons : admitted ps key arg (a :: l) = admitted ps key arg l :=
        List.filter_cons_of_neg (fun e => Bool.false_ne_true (ha.symm.trans e))
      rw [hcons]
      exact ih hsplit.2

/-- Arguments matched only by equations admitting them: scanning the
admitting equations selects what scanning every equation selects. -/
theorem select_admitted [DecidableEq κ] (m : α → Bool) (ps : List ι)
    (key : α → ι → Option κ) (arg : ι → κ)
    (admitted_match : ∀ a, m a = true → admits ps key arg a = true)
    (l : List α) :
    select m (admitted ps key arg l) = select m l :=
  select_filter_of_complete m _ admitted_match l

/-- With every two equations apart, the scan of the admitting equations runs
at most one, and is never ambiguous. -/
theorem select_admitted_not_ambiguous [DecidableEq κ] (m : α → Bool)
    (ps : List ι) (key : α → ι → Option κ) (arg : ι → κ) (l : List α)
    (distinct : l.Pairwise (apart ps key)) :
    select m (admitted ps key arg l) ≠ .ambiguous := by
  have hle := admitted_length_le_one ps key arg l distinct
  generalize admitted ps key arg l = c at hle ⊢
  match c, hle with
  | [], _ => intro h; cases h
  | [a], _ => exact step_none_ne_ambiguous m a

/-- A head whose equations are pairwise apart is never ambiguous on
arguments with keys at the tested positions. -/
theorem select_not_ambiguous_of_apart [DecidableEq κ] (m : α → Bool)
    (ps : List ι) (key : α → ι → Option κ) (arg : ι → κ)
    (admitted_match : ∀ a, m a = true → admits ps key arg a = true)
    (l : List α) (distinct : l.Pairwise (apart ps key)) :
    select m l ≠ .ambiguous := by
  rw [← select_admitted m ps key arg admitted_match l]
  exact select_admitted_not_ambiguous m ps key arg l distinct

/-- The first-argument key is the one-position case whose key is always
tested. -/
theorem keyed_eq_admitted [DecidableEq κ] (key : α → κ) (k : κ)
    (l : List α) :
    keyed key k l =
      admitted [()] (fun a _ => some (key a)) (fun _ => k) l := by
  unfold keyed admitted admits
  congr 1
  funext a
  simp [admitsAt]

/-- A position a variable pattern leaves untested cannot tell equations apart:
`f $x` and `f a` both admit the argument `a`, so keeping the admitting
equations keeps two, and the scan must still decide between them. -/
theorem admitted_untested_keeps_both :
    (admitted [()] (fun (a : Bool) _ => if a then some 0 else none)
      (fun _ => (0 : ℕ)) [false, true]).length = 2 := by
  decide

/-- Keys at a second position tell apart equations that share their first
key, as `pack (S m) Z` and `pack (S m) (S n)` do: only one of the two admits
`(S …) Z`. -/
theorem admitted_second_position :
    admitted [0, 1]
      (fun (a : Bool) (p : ℕ) =>
        if p = 0 then some 1 else if a then some 1 else some 2)
      (fun p => if p = 0 then 1 else 2) [false, true] = [false] := by
  decide

/-- A nondeterministic call enumerates every equation's answers in order.
Equations without answers contribute nothing, so a filter that keeps each
equation with an answer keeps the enumeration, answers and order alike. -/
theorem flatMap_filter_of_complete {β : Type*} (ans : α → List β)
    (p : α → Bool) (complete : ∀ a, ans a ≠ [] → p a = true) :
    ∀ (l : List α), (l.filter p).flatMap ans = l.flatMap ans
  | [] => rfl
  | a :: l => by
    by_cases hp : p a = true
    · rw [List.filter_cons_of_pos hp, List.flatMap_cons, List.flatMap_cons,
        flatMap_filter_of_complete ans p complete l]
    · have hnil : ans a = [] := by
        by_contra h
        exact hp (complete a h)
      rw [List.filter_cons_of_neg hp, List.flatMap_cons, hnil, List.nil_append,
        flatMap_filter_of_complete ans p complete l]

/-- Arguments answered only by equations admitting them: enumerating the
admitting equations' answers gives every answer, in order. -/
theorem flatMap_admitted [DecidableEq κ] {β : Type*} (ans : α → List β)
    (ps : List ι) (key : α → ι → Option κ) (arg : ι → κ)
    (admitted_answers : ∀ a, ans a ≠ [] → admits ps key arg a = true)
    (l : List α) :
    (admitted ps key arg l).flatMap ans = l.flatMap ans :=
  flatMap_filter_of_complete ans _ admitted_answers l

/-- Testing fewer positions admits more: an index may skip a position whose
argument term is still open and stay complete. -/
theorem admits_of_sublist [DecidableEq κ] {ps qs : List ι}
    (sub : qs.Sublist ps) (key : α → ι → Option κ) (arg : ι → κ) (a : α)
    (h : admits ps key arg a = true) : admits qs key arg a = true :=
  List.all_eq_true.mpr fun p hp =>
    List.all_eq_true.mp h p (sub.subset hp)

/-- Three equations told apart by a literal at the second of three
positions keep, for an argument with that literal, the equations testing it
and those testing nothing there, in order. -/
theorem admitted_deep_position :
    admitted [0, 1, 2]
      (fun (a : Fin 3) (p : ℕ) =>
        if a = 0 then (if p = 0 then some 1 else none)
        else if a = 1 then (if p = 1 then some 1 else none)
        else none)
      (fun p => if p = 1 then 1 else 0) [0, 1, 2] = [1, 2] := by
  decide

end Mettapedia.GSLT.LanguageDef.KeyedEquationSelection
