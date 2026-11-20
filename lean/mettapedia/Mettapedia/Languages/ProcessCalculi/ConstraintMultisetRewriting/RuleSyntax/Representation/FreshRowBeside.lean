import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Equivariance

/-!
# No program of the step tells a store from the store beside a fresh constant row

`Representation.wholeStore_not_presented` shows that `WholeStore a b` (rewrite the store `{a}` to `{b}`, and no
other store) is the rewriting of no set of positive rules, because it is not frame-closed. This module shows
that no program of `RuleSyntax.step` at the one first-order frame over rows with unknowns presents it, whatever
its rules: unknowns, reads, tells, equation guards, none checks, count checks and collect patterns alike, of
any size. A check is read at every solution of the firing's information, and a solution that sends a pattern
to a constant that neither the program nor the state mentions can be followed by the replacement of that
constant by the row `a`; so no check sees a row whose constant nothing names.

* `replace`: the map that replaces the constant `sym N` by a term. Beyond a term's constants
  (`constantBound`, of `Representation.Equivariance`) it commutes with substitution (`replace_apply`).
* `fresh_value`: if a solution of a store sends a pattern to `sym N`, with `N` beyond every constant of the
  store and of the pattern, then the replaced solution solves the store and sends the pattern to the row `a`.
  So a check that holds at every solution and refuses, or counts, the row `a` cannot see a row `sym N`.
* `admitted_beside_fresh`: **every firing admitted at the one-row state of `a` is admitted at the state of
  `a` beside a row `sym N`** (`beside`), for `N` beyond the constants of `a`, of the firing's information, of
  its opened checks and of its collect patterns.
* `wholeStore_not_presented_any`: so no program presents `WholeStore a b`.

Control: a none check does refuse beside a row the program mentions
(`Machines.NoneReading.rewrites_but_refused`). The none query sees only rows the program can name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.FreshRowBeside

open Mettapedia.Logic.LP
open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open NamesOnTheStep (Expr)
open Presentation.Schematic
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines

/-! ## Replacing a fresh constant -/

/-- An argument of a former mentions no constant beyond the former's bound. -/
theorem constantBound_arg (f : RowFunction) (ts : Fin (rowArity f) → Tm) (i : Fin (rowArity f)) :
    constantBound (ts i) ≤ constantBound (Term.app f ts) := by
  cases f with
  | app =>
      show constantBound (ts i) ≤ max (constantBound (ts head)) (constantBound (ts tail))
      obtain ⟨k, small⟩ := i
      match k, small with
      | 0, _ => exact le_max_left _ _
      | 1, _ => exact le_max_right _ _
      | k + 2, small => exact absurd (show k + 2 < 2 from small) (by omega)
  | code =>
      show constantBound (ts i) ≤ constantBound (ts body)
      obtain ⟨k, small⟩ := i
      match k, small with
      | 0, _ => exact le_refl _
      | k + 1, small => exact absurd (show k + 1 < 1 from small) (by omega)

/-- Replace the constant `sym N` by a term. -/
def replace (N : ℕ) (u : Tm) : Tm → Tm
  | .var v => .var v
  | .const c => if c = .sym N then u else .const c
  | .app f ts => .app f fun i => replace N u (ts i)

theorem replace_of_bound (N : ℕ) (u : Tm) : ∀ t : Tm, constantBound t ≤ N → replace N u t = t
  | .var _, _ => rfl
  | .const (.sym k), bound => by
      have small : k + 1 ≤ N := bound
      have other : RowConstant.sym k ≠ RowConstant.sym N := fun same => by
        cases same
        omega
      show (if RowConstant.sym k = RowConstant.sym N then u else .const (.sym k)) = _
      rw [if_neg other]
  | .const (.name _), _ => rfl
  | .app f ts, bound => by
      show Term.app f (fun i => replace N u (ts i)) = Term.app f ts
      congr 1
      funext i
      exact replace_of_bound N u (ts i) ((constantBound_arg f ts i).trans bound)

/-- A solution followed by the replacement. -/
def replaced (N : ℕ) (u : Tm) (σ : Subst rowSig) : Subst rowSig := fun v => replace N u (σ v)

/-- **Beyond a term's constants the replacement commutes with substitution.** -/
theorem replace_apply (N : ℕ) (u : Tm) (σ : Subst rowSig) : ∀ t : Tm, constantBound t ≤ N →
    replace N u (σ.applyTerm t) = (replaced N u σ).applyTerm t
  | .var _, _ => rfl
  | .const c, bound => by
      show replace N u (.const c) = .const c
      exact replace_of_bound N u (.const c) bound
  | .app f ts, bound => by
      show Term.app f (fun i => replace N u (σ.applyTerm (ts i))) =
        Term.app f (fun i => (replaced N u σ).applyTerm (ts i))
      congr 1
      funext i
      exact replace_apply N u σ (ts i) ((constantBound_arg f ts i).trans bound)

theorem replace_fresh (N : ℕ) (u : Tm) : replace N u (.const (.sym N)) = u := by
  show (if RowConstant.sym N = RowConstant.sym N then u else _) = u
  rw [if_pos rfl]

theorem toTerm_ne_fresh {e : Expr} {N : ℕ} (bound : constantBound (toTerm e) ≤ N) :
    toTerm e ≠ .const (.sym N) := fun same => by
  rw [same] at bound
  have big : N + 1 ≤ N := bound
  omega

/-- **A solution that sends a pattern to a fresh constant gives one that sends it to the row `a`.** -/
theorem fresh_value {N : ℕ} {a : Expr} {info : EquationStore Tm}
    (infoBound : ∀ e ∈ info, constantBound e.1 ≤ N ∧ constantBound e.2 ≤ N) {p : Tm}
    (pBound : constantBound p ≤ N) {σ : Subst rowSig} (solved : A.Models σ info)
    (hits : σ.applyTerm p = .const (.sym N)) :
    A.Models (replaced N (toTerm a) σ) info ∧ (replaced N (toTerm a) σ).applyTerm p = toTerm a := by
  refine ⟨fun e member => ?_, ?_⟩
  · have same : σ.applyTerm e.1 = σ.applyTerm e.2 := solved e member
    show (replaced N (toTerm a) σ).applyTerm e.1 = (replaced N (toTerm a) σ).applyTerm e.2
    rw [← replace_apply N _ σ e.1 (infoBound e member).1, ← replace_apply N _ σ e.2 (infoBound e member).2, same]
  · rw [← replace_apply N _ σ p pBound, hits, replace_fresh]

/-! ## The state beside a fresh row -/

/-- **The state of `a` beside `sym N`**: identity `0` carries `a`, identity `M` carries `sym N`. -/
def beside (a : Expr) (N M : ℕ) : SState ℕ :=
  ⟨PUnit.unit, [], {0, M}, fun o => if o = M then toTerm (.sym N) else toTerm a⟩

theorem beside_reads (a : Expr) (N M : ℕ) :
    ReadsBag (beside a N M) (({0, M} : Finset ℕ).val.map fun o => if o = M then Expr.sym N else a) :=
  ⟨_, reads_of_ground (fun o _ => by
      show (if o = M then toTerm (.sym N) else toTerm a) = toTerm (if o = M then Expr.sym N else a)
      split_ifs <;> rfl) (fun _ member => absurd member List.not_mem_nil), rfl⟩

theorem zipWith_congr_right {α β γ : Type*} (f g : α → β → γ) :
    ∀ (l₁ : List α) (l₂ : List β), (∀ x, ∀ y ∈ l₂, f x y = g x y) → List.zipWith f l₁ l₂ = List.zipWith g l₁ l₂
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: xs, y :: ys, same => by
      rw [List.zipWith_cons_cons, List.zipWith_cons_cons, same x y List.mem_cons_self,
        zipWith_congr_right f g xs ys fun x' y' inside => same x' y' (List.mem_cons_of_mem _ inside)]

section Firing

variable {P : Program (OneFrame.Terms Tm)} {a : Expr}

/-- The terms a firing at a state asks of the store: its information, its opened checks, its collect query. -/
def askedTerms (s : SState ℕ) (g : Firing ℕ E P s.frame) : List Tm :=
  (g.information X s).flatMap (fun e => [e.1, e.2]) ++ (g.opened X).checks.flatMap checkTerms ++ g.collectOpened X

/-- A bound beyond the constants of `a` and of everything a firing at the one-row state of `a` asks. -/
def freshBound (a : Expr) (g : Firing ℕ E P (rowState a).frame) : ℕ :=
  ((toTerm a :: askedTerms (rowState a) g).map constantBound).foldr max 0

theorem le_freshBound (g : Firing ℕ E P (rowState a).frame) {t : Tm}
    (member : t ∈ toTerm a :: askedTerms (rowState a) g) : constantBound t ≤ freshBound a g :=
  le_foldr_max (List.mem_map_of_mem member)

/-- An identity beyond the made identities of a firing. -/
def freshId (g : Firing ℕ E P (rowState a).frame) : ℕ := g.selection.made.foldr max 0 + 1

theorem freshId_not_made (g : Firing ℕ E P (rowState a).frame) : freshId g ∉ g.selection.made := fun inside => by
  have small := le_foldr_max inside
  unfold freshId at small
  omega

theorem freshId_ne_zero (g : Firing ℕ E P (rowState a).frame) : freshId g ≠ 0 := Nat.succ_ne_zero _

/-- **Every firing admitted at the one-row state of `a` is admitted beside a fresh constant row.** -/
theorem admitted_beside (g : Firing ℕ E P (rowState a).frame)
    (admitted : (step X ℕ E P).Admits (s := rowState a) g) (N M : ℕ) (notZero : M ≠ 0)
    (notMade : M ∉ g.selection.made)
    (bound : ∀ t ∈ toTerm a :: askedTerms (rowState a) g, constantBound t ≤ N) :
    (step X ℕ E P).Admits (s := beside a N M) g := by
  obtain ⟨fresh, shapes, enabled, solvable, checks, collect⟩ := (admits_iff g).mp admitted
  have onlyZero : ∀ o ∈ (rowState a).present, o = 0 := fun o inside => Finset.mem_singleton.mp inside
  have rowAt : ∀ o, o = 0 → g.row X (beside a N M) o = g.row X (rowState a) o := by
    rintro o rfl
    show Subst.applyTerm (Subst.id rowSig) (if (0 : ℕ) = M then toTerm (.sym N) else toTerm a) =
      Subst.applyTerm (Subst.id rowSig) (toTerm a)
    rw [if_neg (Ne.symm notZero)]
  have rowFresh : g.row X (beside a N M) M = toTerm (.sym N) := by
    show Subst.applyTerm (Subst.id rowSig) (if M = M then toTerm (.sym N) else toTerm a) = _
    rw [if_pos rfl, Subst.applyTerm_id]
  have rowZero : g.row X (rowState a) 0 = toTerm a := Subst.applyTerm_id _
  have takenZero : ∀ o ∈ g.selection.taken, o = 0 := fun o inside =>
    onlyZero o (enabled.taken_subset (List.mem_toFinset.mpr inside))
  have readZero : ∀ o ∈ g.selection.read, o = 0 := fun o inside =>
    onlyZero o (enabled.kept_subset (List.mem_toFinset.mpr inside))
  -- the information is the same at both states
  have sameInfo : g.information X (beside a N M) = g.information X (rowState a) := by
    unfold Firing.information Firing.matching
    rw [zipWith_congr_right _ _ _ g.selection.taken fun _ o inside => by rw [rowAt o (takenZero o inside)],
      zipWith_congr_right _ _ _ g.selection.read fun _ o inside => by rw [rowAt o (readZero o inside)]]
    rfl
  have infoBound : ∀ e ∈ g.information X (rowState a), constantBound e.1 ≤ N ∧ constantBound e.2 ≤ N :=
    fun e member =>
      ⟨bound _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨e, member, List.mem_cons_self⟩)))),
        bound _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨e, member, List.mem_cons_of_mem _ List.mem_cons_self⟩))))⟩
  have checkBound : ∀ c ∈ (g.opened X).checks, ∀ t ∈ checkTerms c, constantBound t ≤ N :=
    fun c member t inside =>
      bound _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨c, member, inside⟩))))
  have collectBound : ∀ t ∈ g.collectOpened X, constantBound t ≤ N := fun t member =>
    bound _ (List.mem_cons_of_mem _ (List.mem_append_right _ member))
  have aBound : constantBound (toTerm a) ≤ N := bound _ List.mem_cons_self
  -- a pattern counted the same at every solution never meets the fresh row
  have neverFresh : ∀ (p : Tm), constantBound p ≤ N → ∀ k : ℕ,
      (∀ σ : Subst rowSig, A.Models σ (g.information X (rowState a)) →
        (matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ (g.row X (rowState a)) (rowState a).present p).card
          = k) →
      ∀ σ : Subst rowSig, A.Models σ (g.information X (rowState a)) → σ.applyTerm p ≠ .const (.sym N) := by
    intro p pBound k counted σ solved hits
    obtain ⟨solved', value⟩ := fresh_value (a := a) infoBound pBound solved hits
    have none : matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ (g.row X (rowState a)) (rowState a).present p
        = ∅ := by
      ext o
      rw [mem_matchesAt]
      simp only [Finset.notMem_empty, iff_false, not_and]
      intro inside same
      have isZero := onlyZero o inside
      subst isZero
      have same' : σ.applyTerm p = σ.applyTerm (g.row X (rowState a) 0) := same
      rw [rowZero, applyTerm_toTerm, hits] at same'
      exact toTerm_ne_fresh aBound same'.symm
    have one : matchesAt X (a := PUnit.unit) (b := PUnit.unit) (replaced N (toTerm a) σ)
        (g.row X (rowState a)) (rowState a).present p = {0} := by
      ext o
      rw [mem_matchesAt, Finset.mem_singleton]
      constructor
      · exact fun both => onlyZero o both.1
      · rintro rfl
        refine ⟨Finset.mem_singleton_self 0, ?_⟩
        show (replaced N (toTerm a) σ).applyTerm p =
          (replaced N (toTerm a) σ).applyTerm (g.row X (rowState a) 0)
        rw [value, rowZero, applyTerm_toTerm]
    have zero := counted σ solved
    have oneCount := counted _ solved'
    rw [none] at zero
    rw [one] at oneCount
    simp at zero oneCount
    omega
  -- where no solution meets the fresh row, the matches at both states agree
  have sameMatches : ∀ (p : Tm) (σ : Subst rowSig), σ.applyTerm p ≠ .const (.sym N) →
      matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ (g.row X (beside a N M)) (beside a N M).present p =
        matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ (g.row X (rowState a)) (rowState a).present p := by
    intro p σ apart
    ext o
    rw [mem_matchesAt, mem_matchesAt]
    constructor
    · rintro ⟨inside, same⟩
      rcases Finset.mem_insert.mp inside with rfl | isM
      · exact ⟨Finset.mem_singleton_self 0, by rw [← rowAt 0 rfl]; exact same⟩
      · rw [Finset.mem_singleton.mp isM] at same
        have same' : σ.applyTerm p = σ.applyTerm (g.row X (beside a N M) M) := same
        rw [rowFresh, applyTerm_toTerm] at same'
        exact absurd same' apart
    · rintro ⟨inside, same⟩
      have isZero := onlyZero o inside
      subst isZero
      exact ⟨Finset.mem_insert_self 0 _, by rw [rowAt 0 rfl]; exact same⟩
  refine (admits_iff (X := X) (s := beside a N M) g).mpr ⟨?_, shapes, ?_, ?_, ?_, ?_⟩
  · -- freshness: the new row is ground
    intro b gg h
    obtain ⟨u, -, onRule⟩ := fresh b gg h
    refine ⟨u, fun t mentioned => ?_, onRule⟩
    rcases mentioned with inKnowledge | inKnowledge | ⟨o, -, rfl⟩
    · exact absurd inKnowledge List.not_mem_nil
    · exact absurd inKnowledge List.not_mem_nil
    · show Subst.applyTerm u (Subst.applyTerm (Subst.id rowSig)
          (if o = M then toTerm (.sym N) else toTerm a)) =
        Subst.applyTerm gg (if o = M then toTerm (.sym N) else toTerm a)
      split_ifs <;> rw [applyTerm_toTerm, applyTerm_toTerm, applyTerm_toTerm]
  · -- the occurrences
    refine ⟨fun o inside => ?_, fun o inside => ?_, enabled.apart, ?_,
      fun q inside => by simp [Selection.commit] at inside⟩
    · rw [onlyZero o (enabled.taken_subset inside)]
      exact Finset.mem_insert_self 0 _
    · rw [onlyZero o (enabled.kept_subset inside)]
      exact Finset.mem_insert_self 0 _
    · refine Finset.disjoint_left.mpr fun o inMade inPresent => ?_
      rcases Finset.mem_insert.mp inPresent with rfl | isM
      · exact Finset.disjoint_left.mp enabled.fresh inMade (Finset.mem_singleton_self 0)
      · rw [Finset.mem_singleton.mp isM] at inMade
        exact notMade (List.mem_toFinset.mp inMade)
  · rw [sameInfo]
    exact solvable
  · intro c member b σ solved
    rw [sameInfo] at solved
    have old := checks c member b σ solved
    cases c with
    | equal l r => exact old
    | predicate quantifier p =>
        cases quantifier with
        | any =>
            obtain ⟨o, inside, same⟩ := old
            obtain rfl := onlyZero o inside
            have same' : σ.applyTerm p = σ.applyTerm (g.row X (beside a N M) 0) := by
              rw [rowAt 0 rfl]
              exact same
            exact ⟨0, Finset.mem_insert_self 0 _, same'⟩
        | none =>
            intro o inside same
            rcases Finset.mem_insert.mp inside with rfl | isM
            · exact old 0 (Finset.mem_singleton_self 0) (by beta_reduce; rw [← rowAt 0 rfl]; exact same)
            · rw [Finset.mem_singleton.mp isM] at same
              have same' : σ.applyTerm p = σ.applyTerm (g.row X (beside a N M) M) := same
              rw [rowFresh, applyTerm_toTerm] at same'
              have pBound : constantBound p ≤ N := checkBound _ member p (List.mem_singleton_self p)
              obtain ⟨solved', value⟩ := fresh_value (a := a) infoBound pBound solved same'
              exact checks _ member b _ solved' 0 (Finset.mem_singleton_self 0)
                (show (replaced N (toTerm a) σ).applyTerm p =
                    (replaced N (toTerm a) σ).applyTerm (g.row X (rowState a) 0) by
                  rw [value, rowZero, applyTerm_toTerm])
    | count p k =>
        have pBound : constantBound p ≤ N := checkBound _ member p (List.mem_singleton_self p)
        have apart := neverFresh p pBound k (fun σ' solved' => checks _ member PUnit.unit σ' solved') σ solved
        show (matchesAt X σ (g.row X (beside a N M)) (beside a N M).present p).card = k
        rw [sameMatches p σ apart]
        exact old
  · intro q member b σ solved
    rw [sameInfo] at solved
    have old := collect q member b σ solved
    have qBound : constantBound q.1 ≤ N := collectBound _ (List.of_mem_zip member).1
    have apart := neverFresh q.1 qBound q.2.card
      (fun σ' solved' => by rw [collect q member PUnit.unit σ' solved']) σ solved
    show matchesAt X σ (g.row X (beside a N M)) (beside a N M).present q.1 = q.2
    rw [sameMatches q.1 σ apart]
    exact old

/-- **Every firing admitted at the one-row state of `a` is admitted beside a fresh constant row.** -/
theorem admitted_beside_fresh (g : Firing ℕ E P (rowState a).frame)
    (admitted : (step X ℕ E P).Admits (s := rowState a) g) :
    (step X ℕ E P).Admits (s := beside a (freshBound a g) (freshId g)) g :=
  admitted_beside g admitted _ _ (freshId_ne_zero g) (freshId_not_made g) fun _ member => le_freshBound g member

end Firing

/-! ## The relation on whole stores -/

/-- **No program of the step presents `WholeStore a b`**, whatever its rules: a firing at the one-row state of
`a` is admitted beside a fresh constant row too, and that state reads as a bag of two rows. -/
theorem wholeStore_not_presented_any (a b : Expr) (P : Program (OneFrame.Terms Tm)) :
    ¬ Presents ℕ P (WholeStore a b) := by
  intro presents
  obtain ⟨g, admitted, -⟩ := presents.forward (rowState_reads a) (⟨rfl, rfl⟩ : WholeStore a b {a} {b})
  have notZero := freshId_ne_zero g
  obtain ⟨bag', ⟨isA, -⟩, -⟩ := presents.backward (beside_reads a (freshBound a g) (freshId g)) g
    (admitted_beside_fresh g admitted)
  have counted := congrArg Multiset.card isA
  rw [Multiset.card_map, Multiset.card_singleton, Finset.card_val,
    Finset.card_insert_of_notMem (by simpa using notZero.symm), Finset.card_singleton] at counted
  omega

#print axioms replace_apply
#print axioms fresh_value
#print axioms admitted_beside_fresh
#print axioms wholeStore_not_presented_any

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.FreshRowBeside
