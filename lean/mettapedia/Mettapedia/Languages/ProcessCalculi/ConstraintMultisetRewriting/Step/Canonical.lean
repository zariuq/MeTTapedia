import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Independence

/-!
# Canonical interleavings: completeness of partial-order reduction

Fix a key on firings, valued in a linear order, and an **oracle** that declares pairs of firings at
one state independent. The oracle must be sound: every pair it declares is independent
(`Transport.Independent`), as for the sound three-valued checks of `Independence` read with unknown as
dependent. The key must be kept by transport, alikeness and residuals.

* **Inversions** (`Transport.Inverted`): two adjacent firings of a run, the second alike to the residual
  of a firing whose key is smaller than the first's, which the oracle declares independent where the
  two fire. A run is **canonical** (`Transport.Canonical`) when it has none: exploration extends a run
  by a firing only when the two do not form such an inversion.
* **One swap removes one inversion** (`Inverted.swap`): an inverted run swaps, by the diamond the
  oracle's soundness provides, into a trace-equivalent run whose key word is a permutation with one
  inversion fewer. The swap moves only firings of the run itself: it never fires a firing at a state
  where it was not fired, so pairwise independence is never promoted to a joint round.
* **Completeness** (`exists_canonical`, `exists_canonical_of_check`, `exists_canonical_same_last`): every run is trace equivalent
  to a canonical run with a permutation of its key word. So exploring only canonical runs still reaches
  every trace class, and every class of end states.
* **Cliques are explored once** (`pairwise_of_canonical`, `canonical_of_pairwise`,
  `canonical_keyWord_unique`): a run whose adjacent pairs are all declared independent is canonical
  exactly when its key word is sorted, and two such canonical runs with permuted key words have the
  same key word. Of the `k!` orders of `k` firings independent at every adjacent stage, the ones kept
  are those of one key word.
* **Short runs** (`canonical_nil`, `canonical_single`, `canonical_pair_iff`): a pair is pruned exactly
  when the oracle declares it independent and its keys are inverted, so a pair the oracle does not
  declare independent is kept in every order that runs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uI uK

/-! ## Inversions of a list -/

section Inversions

variable {κ : Type uK} [LinearOrder κ]

/-- **The inversions of a list**: the pairs of positions whose later entry is smaller. -/
def inversions : List κ → ℕ
  | [] => 0
  | a :: l => l.countP (fun b => b < a) + inversions l

/-- Exchanging an adjacent inverted pair removes exactly one inversion. -/
theorem inversions_swap {a b : κ} (smaller : b < a) (l : List κ) :
    inversions (b :: a :: l) + 1 = inversions (a :: b :: l) := by
  have notLess : ¬ a < b := not_lt.mpr smaller.le
  simp only [inversions, List.countP_cons_of_pos (p := fun x => decide (x < a)) (decide_eq_true smaller),
    List.countP_cons_of_neg (p := fun x => decide (x < b)) (by simpa using notLess)]
  omega

/-- Inversions decrease under a common head when they decrease, by a permutation, below it. -/
theorem inversions_cons_lt (a : κ) {l l' : List κ} (perm : l'.Perm l) (fewer : inversions l' < inversions l) :
    inversions (a :: l') < inversions (a :: l) := by
  simp only [inversions, perm.countP_eq]
  omega

end Inversions

namespace Transport

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport P)
  {κ : Type uK} [LinearOrder κ] (key : (s : State) → Firing s → κ)

/-- **The key word of a run**: the keys of its firings, in order. -/
def keyWord {s : State} (r : P.Run s) : List κ := r.word.map fun x => key x.1 x.2

/-- **An inversion of a run**: adjacent firings, the second alike to the residual of a firing with a
smaller key than the first, declared independent of the first by the oracle where they fire. -/
inductive Inverted (indep : (s : State) → Firing s → Firing s → Prop) : {s : State} → P.Run s → Prop
  | here {s : State} {f g : Firing s} (first : P.Admits f) {g₁ : Firing (P.result f first)}
      (alike : T.Alike (T.residual f first g) g₁) (afterFirst : P.Admits g₁)
      (rest : P.Run (P.result g₁ afterFirst)) (smaller : key s g < key s f) (independent : indep s f g) :
      Inverted indep (.cons f first (.cons g₁ afterFirst rest))
  | later {s : State} (f : Firing s) (admitted : P.Admits f) {r : P.Run (P.result f admitted)} :
      Inverted indep r → Inverted indep (.cons f admitted r)

/-- **A canonical run**: a run without inversions. -/
def Canonical (indep : (s : State) → Firing s → Firing s → Prop) {s : State} (r : P.Run s) : Prop :=
  ¬ Inverted T key indep r

/-- **Every adjacent pair of a run is declared independent.** -/
inductive AdjacentIndependent (indep : (s : State) → Firing s → Firing s → Prop) :
    {s : State} → P.Run s → Prop
  | nil (s : State) : AdjacentIndependent indep (.nil s)
  | single {s : State} (f : Firing s) (admitted : P.Admits f) :
      AdjacentIndependent indep (.cons f admitted (.nil _))
  | cons {s : State} {f g : Firing s} (first : P.Admits f) {g₁ : Firing (P.result f first)}
      (alike : T.Alike (T.residual f first g) g₁) (afterFirst : P.Admits g₁)
      {rest : P.Run (P.result g₁ afterFirst)} (independent : indep s f g) :
      AdjacentIndependent indep (.cons g₁ afterFirst rest) →
      AdjacentIndependent indep (.cons f first (.cons g₁ afterFirst rest))

/-- **A key kept by transport, alikeness and residuals.** -/
structure KeyLaws : Prop where
  move : ∀ {s t : State} (i : T.Iso s t) (f : Firing s), key t (T.move i f) = key s f
  alike : ∀ {s : State} {f f' : Firing s}, T.Alike f f' → key s f = key s f'
  residual : ∀ {s : State} (g : Firing s) (admitted : P.Admits g) (f : Firing s),
    key _ (T.residual g admitted f) = key s f

variable {T key}

omit [LinearOrder κ] in
@[simp] theorem keyWord_nil (s : State) : keyWord key (.nil s : P.Run s) = [] := rfl

omit [LinearOrder κ] in
@[simp] theorem keyWord_cons {s : State} (f : Firing s) (admitted : P.Admits f)
    (rest : P.Run (P.result f admitted)) : keyWord key (.cons f admitted rest) = key s f :: keyWord key rest :=
  rfl

omit [LinearOrder κ] in
/-- **Transport keeps key words.** -/
theorem keyWord_moveRun (laws : KeyLaws T key) :
    ∀ {s t : State} (i : T.Iso s t) (r : P.Run s), keyWord key (T.moveRun i r) = keyWord key r
  | _, _, _, .nil _ => rfl
  | _, _, i, .cons f admitted rest => by
      show key _ (T.move i f) :: keyWord key (T.moveRun (T.result_move i f admitted) rest) =
        key _ f :: keyWord key rest
      rw [laws.move, keyWord_moveRun laws]

variable {indep : (s : State) → Firing s → Firing s → Prop}

/-- **One swap removes one inversion**: an inverted run swaps into a trace-equivalent run whose key
word is a permutation with fewer inversions. -/
theorem Inverted.swap (sound : ∀ s f g, indep s f g → T.Independent s f g) (laws : KeyLaws T key)
    {s : State} {r : P.Run s} (inverted : Inverted T key indep r) :
    ∃ r' : P.Run s, T.SwapStep r r' ∧ (keyWord key r').Perm (keyWord key r) ∧
      inversions (keyWord key r') < inversions (keyWord key r) := by
  induction inverted with
  | @here s f g first g₁ alike afterFirst rest smaller independent =>
      obtain ⟨_, second, afterFirst', afterSecond, ⟨close⟩⟩ := sound s f g independent
      let back : T.Iso (P.result g₁ afterFirst) (P.result (T.residual g second f) afterSecond) :=
        T.trans (T.symm (T.result_alike alike afterFirst' afterFirst)) close
      refine ⟨.cons g second (.cons (T.residual g second f) afterSecond (T.moveRun back rest)),
        .here first second alike afterFirst (Alike.refl _) afterSecond (Similar.moveRun back rest), ?_⟩
      have swapped : keyWord key (.cons g second (.cons (T.residual g second f) afterSecond
          (T.moveRun back rest))) = key s g :: key s f :: keyWord key rest := by
        simp only [keyWord_cons, laws.residual, keyWord_moveRun laws]
      have original : keyWord key (.cons f first (.cons g₁ afterFirst rest)) =
          key s f :: key s g :: keyWord key rest := by
        simp only [keyWord_cons, ← laws.alike alike, laws.residual]
      rw [swapped, original]
      exact ⟨List.Perm.swap _ _ _, by have := inversions_swap smaller (keyWord key rest); omega⟩
  | later f admitted _ ih =>
      obtain ⟨r', step, perm, fewer⟩ := ih
      refine ⟨.cons f admitted r', .later f admitted step, ?_, ?_⟩
      · simp only [keyWord_cons]
        exact perm.cons _
      · simp only [keyWord_cons]
        exact inversions_cons_lt _ perm fewer

/-- **Completeness of canonical interleavings**: every run is trace equivalent to a canonical run whose
key word is a permutation of its own. -/
theorem exists_canonical (sound : ∀ s f g, indep s f g → T.Independent s f g)
    (laws : KeyLaws T key) {s : State} (r : P.Run s) :
    ∃ r' : P.Run s, T.TraceEquiv s r r' ∧ Canonical T key indep r' ∧ (keyWord key r').Perm (keyWord key r) := by
  suffices measured : ∀ (n : ℕ) (r : P.Run s), inversions (keyWord key r) = n →
      ∃ r' : P.Run s, T.TraceEquiv s r r' ∧ Canonical T key indep r' ∧ (keyWord key r').Perm (keyWord key r) from
    measured _ r rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro r counted
      by_cases inverted : Inverted T key indep r
      · obtain ⟨r', step, perm, fewer⟩ := inverted.swap sound laws
        obtain ⟨r'', equivalent, canonical, perm'⟩ := ih _ (fewer.trans_eq counted) r' rfl
        exact ⟨r'', .trans _ _ _ (.rel _ _ (.inl step)) equivalent, canonical, perm'.trans perm⟩
      · exact ⟨r, .refl _, inverted, List.Perm.refl _⟩

/-- **A sound three-valued check is an oracle**: pruning only where the check answers independent,
reading unknown as dependent, keeps completeness. -/
theorem exists_canonical_of_check (check : ∀ s, T.Check s) (laws : KeyLaws T key) {s : State}
    (r : P.Run s) :
    ∃ r' : P.Run s, T.TraceEquiv s r r' ∧
      Canonical T key (fun s f g => (check s).verdict f g = .independent) r' ∧
      (keyWord key r').Perm (keyWord key r) :=
  exists_canonical (fun s f g answered => (check s).sound_independent f g answered) laws r

/-- **Every class of end states is reached by a canonical run.** -/
theorem exists_canonical_same_last (sound : ∀ s f g, indep s f g → T.Independent s f g)
    (laws : KeyLaws T key) {s : State} (r : P.Run s) :
    ∃ r' : P.Run s, Canonical T key indep r' ∧ T.Same r.last r'.last := by
  obtain ⟨r', equivalent, canonical, -⟩ := exists_canonical sound laws r
  exact ⟨r', canonical, TraceEquiv.same_last equivalent⟩

/-! ## Short runs -/

theorem canonical_nil (s : State) : Canonical T key indep (.nil s : P.Run s) :=
  fun inverted => nomatch inverted

theorem canonical_single {s : State} (f : Firing s) (admitted : P.Admits f) :
    Canonical T key indep (.cons f admitted (.nil _)) := by
  intro inverted
  cases inverted with
  | later _ _ inner => exact canonical_nil _ inner

/-- **A pair is pruned exactly when the oracle declares it independent with inverted keys.** -/
theorem canonical_pair_iff {s : State} {f : Firing s} (first : P.Admits f) {g₁ : Firing (P.result f first)}
    (afterFirst : P.Admits g₁) :
    Canonical T key indep (.cons f first (.cons g₁ afterFirst (.nil _))) ↔
      ¬ ∃ g : Firing s, T.Alike (T.residual f first g) g₁ ∧ key s g < key s f ∧ indep s f g := by
  constructor
  · rintro canonical ⟨g, alike, smaller, independent⟩
    exact canonical (.here first alike afterFirst _ smaller independent)
  · intro none inverted
    cases inverted with
    | here _ alike _ _ smaller independent => exact none ⟨_, alike, smaller, independent⟩
    | later _ _ inner => exact canonical_single (T := T) (key := key) _ _ inner

/-! ## Cliques are explored once -/

/-- **A canonical run whose adjacent pairs are declared independent has a sorted key word.** -/
theorem pairwise_of_canonical (laws : KeyLaws T key) {s : State} {r : P.Run s}
    (adjacent : AdjacentIndependent T indep r) (canonical : Canonical T key indep r) :
    (keyWord key r).Pairwise (· ≤ ·) := by
  induction adjacent with
  | nil => exact List.Pairwise.nil
  | single f admitted => simp
  | @cons s f g first g₁ alike afterFirst rest independent _ ih =>
      have tail : (keyWord key (.cons g₁ afterFirst rest)).Pairwise (· ≤ ·) :=
        ih fun inverted => canonical (.later f first inverted)
      have head : key s f ≤ key _ g₁ := by
        rw [← laws.alike alike, laws.residual]
        exact not_lt.mp fun smaller => canonical (.here first alike afterFirst rest smaller independent)
      rw [keyWord_cons] at tail
      rw [keyWord_cons, keyWord_cons]
      refine List.pairwise_cons.mpr ⟨fun k member => ?_, tail⟩
      rcases List.mem_cons.mp member with same | later
      · rw [same]
        exact head
      · exact head.trans ((List.pairwise_cons.mp tail).1 k later)

/-- **A run with a sorted key word is canonical.** -/
theorem canonical_of_pairwise (laws : KeyLaws T key) {s : State} {r : P.Run s}
    (sorted : (keyWord key r).Pairwise (· ≤ ·)) : Canonical T key indep r := by
  intro inverted
  induction inverted with
  | @here s f g first g₁ alike afterFirst rest smaller _ =>
      rw [keyWord_cons, keyWord_cons] at sorted
      have ordered : key s f ≤ key _ g₁ := (List.pairwise_cons.mp sorted).1 _ (by simp)
      rw [← laws.alike alike, laws.residual] at ordered
      exact absurd smaller (not_lt.mpr ordered)
  | later f admitted _ ih =>
      rw [keyWord_cons] at sorted
      exact ih (List.pairwise_cons.mp sorted).2

/-- **Cliques are explored once**: two canonical runs whose adjacent pairs are declared independent
and whose key words are permutations of each other have the same key word. -/
theorem canonical_keyWord_unique (laws : KeyLaws T key) {s : State} {r r' : P.Run s}
    (adjacent : AdjacentIndependent T indep r) (adjacent' : AdjacentIndependent T indep r')
    (canonical : Canonical T key indep r) (canonical' : Canonical T key indep r')
    (perm : (keyWord key r).Perm (keyWord key r')) : keyWord key r = keyWord key r' :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ first second => le_antisymm first second)
    (pairwise_of_canonical laws adjacent canonical) (pairwise_of_canonical laws adjacent' canonical') perm

end Transport

#print axioms inversions_swap
#print axioms inversions_cons_lt
#print axioms Transport.keyWord_moveRun
#print axioms Transport.Inverted.swap
#print axioms Transport.exists_canonical
#print axioms Transport.exists_canonical_of_check
#print axioms Transport.exists_canonical_same_last
#print axioms Transport.canonical_nil
#print axioms Transport.canonical_single
#print axioms Transport.canonical_pair_iff
#print axioms Transport.pairwise_of_canonical
#print axioms Transport.canonical_of_pairwise
#print axioms Transport.canonical_keyWord_unique

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
