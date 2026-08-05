import Mettapedia.GSLT.Dynamics.DialectTranslation
import Mathlib.Data.Multiset.Basic

/-!
# Dialect-translation boundaries under explicit observations

`DialectTranslation.lean` proves what the petta → he-extended translator can
preserve.  This module separates differences that disappear under the chosen
answer-bag observation from source constructs that require an explicit target
mechanism or a richer operational model.

## The blocker ledger

Proved in this model (clause-answer semantics):

1. **Answer order quotient** (`order_lost_in_bag`,
   `order_not_recoverable`): two
   programs with permuted clause order have EQUAL answer bags but UNEQUAL
   answer lists, so no function of the bag recovers the list.  This is not a
   translation blocker when the specified observation is
   `AnswerBagEquivalent`; tests must ignore only outer answer permutation while
   retaining multiplicity and nested structure.  Ordered source operators are
   handled explicitly rather than inferred from an unordered bag.
2. **Committed choice** (`commit_backtrack_divergence`, `chain_exact`):
   pure, finite commit-to-first-contributing-clause differs observably from
   try-all-clauses.  In this denotational fragment it is macro-expressible: the
   `chain` translation moves clause order into pure clause guards.  This does
   not model general PeTTa `cut`, effects in discarded alternatives, or
   divergence while testing an earlier alternative.
3. **Order dissolution on the committed fragment** (`chain_perm_rigid`):
   the chain image is PERMUTATION-RIGID — any reordering of its clauses
   yields the same answer list, because order now lives in guards, which
   travel with the clauses.  So for committed programs the bag-level target
   observation already determines the full ordered answer: obstruction 1
   vanishes exactly where obstruction 2's repair has been applied.
4. **Demand (first-k answers)** (`first_answer_local`, `collapse_not_local`):
   the first answer is PREFIX-LOCAL — computable from the clause prefix up to
   the first live clause, independent of everything after — while the total
   bag is NOT local: extending the finite program changes it.  This theorem
   establishes extensional non-locality only; an unbounded-cost or divergence
   result requires a coinductive/operational search model.  CeTTa
   `he-extended` already provides bounded `select`, so this row is an explicit
   policy-mapping obligation rather than evidence for a missing operator.

Outside this model (require an operational store/name model, named honestly —
the census rows from the live translator's gap ledger):

5. Non-variable `call`/`eval`/`reduce` — reflection on program text; no
   portable lowering (translator gap T0).
6. `alpha-unique-atom` — fresh-name generation needs a name-supply state
   (T1).
7. Stdlib coverage gaps (e.g. `msort`) — library provision, not semantics
   (T2).
8. Effect traces (`println`, `add-atom` order) — unlike ordinary answer order,
   these remain ordered observations unless a source component explicitly
   declares a weaker trace equivalence.
9. Space introspection / self-modification — the clause list is fixed here;
   programs that observe or grow their own clause set need the store model.

Rows 5–9 are the frontier a LeaTTa-grade operational model would formalize;
claiming them here would overreach the denotational model, so they are
census, not theorems.
-/

namespace Mettapedia.GSLT.Dynamics.DialectTranslation

variable {Goal Sub Ans : Type}

/-- Unfolding lemma: answers of a cons are the head's contribution followed by
the rest's answers. -/
theorem pettaAnswers_cons (c : Clause Goal Sub Ans)
    (cs : List (Clause Goal Sub Ans)) (g : Goal) :
    pettaAnswers (c :: cs) g = contrib c g ++ pettaAnswers cs g := by
  simp [pettaAnswers]

/-! ## Boundary 1: answer order does not survive the bag quotient -/

/-- A clause that matches everything and emits the single answer `a` —
the minimal specimen for order arguments. -/
def constClause (a : ℕ) : Clause Unit Unit ℕ where
  sel _ := [()]
  run _ := [a]

theorem pettaAnswers_constPair (a b : ℕ) :
    pettaAnswers [constClause a, constClause b] () = [a, b] := by
  simp [pettaAnswers, contrib, constClause]

/-- Two programs with EQUAL answer bags and UNEQUAL answer lists: the bag
quotient provably forgets clause order. -/
theorem order_lost_in_bag :
    ∃ cs₁ cs₂ : List (Clause Unit Unit ℕ),
      (pettaAnswers cs₁ () : Multiset ℕ) = (pettaAnswers cs₂ () : Multiset ℕ)
        ∧ pettaAnswers cs₁ () ≠ pettaAnswers cs₂ () := by
  refine ⟨[constClause 0, constClause 1], [constClause 1, constClause 0], ?_, ?_⟩
  · rw [pettaAnswers_constPair, pettaAnswers_constPair]
    decide
  · rw [pettaAnswers_constPair, pettaAnswers_constPair]
    decide

/-- **No recovery function exists**: nothing computed from the answer bag can
return the answer list for all programs.  Translation tests therefore compare
ordinary completed answers as bags; operators that observe search order need
their own explicit target mechanism. -/
theorem order_not_recoverable :
    ¬ ∃ recover : Multiset ℕ → List ℕ,
        ∀ cs : List (Clause Unit Unit ℕ),
          recover (pettaAnswers cs ()) = pettaAnswers cs () := by
  rintro ⟨f, hf⟩
  obtain ⟨cs₁, cs₂, hbag, hlist⟩ := order_lost_in_bag
  have h₁ := hf cs₁
  have h₂ := hf cs₂
  rw [hbag, h₂] at h₁
  exact hlist h₁.symm

/-! ## Obstruction 4: first-answer is prefix-local, the total bag is not -/

/-- The first answer depends only on the program prefix up to the first live
clause: everything after `c` is irrelevant once `c` contributes.  This is why
demand-1 evaluation may stop early. -/
theorem first_answer_local (c : Clause Goal Sub Ans)
    (rest rest' : List (Clause Goal Sub Ans)) (g : Goal)
    (h : contrib c g ≠ []) :
    (pettaAnswers (c :: rest) g).head? = (pettaAnswers (c :: rest') g).head? := by
  cases hc : contrib c g with
  | nil => exact absurd hc h
  | cons a t => simp [pettaAnswers_cons, hc]

/-- The total bag is NOT local: with the same live head, different tails give
different bags.  This finite theorem does not by itself establish an
operational cost or divergence result. -/
theorem collapse_not_local :
    ∃ (c : Clause Unit Unit ℕ) (rest rest' : List (Clause Unit Unit ℕ)),
      contrib c () ≠ [] ∧
        (pettaAnswers (c :: rest) () : Multiset ℕ)
          ≠ (pettaAnswers (c :: rest') () : Multiset ℕ) := by
  refine ⟨constClause 0, [], [constClause 1], ?_, ?_⟩
  · simp [contrib, constClause]
  · have h₀ : pettaAnswers [constClause 0] () = [0] := by
      simp [pettaAnswers, contrib, constClause]
    rw [pettaAnswers_constPair, h₀]
    decide

/-! ## Boundary 2: pure clause-local committed choice -/

/-- Committed-choice semantics: the first clause whose contribution is
nonempty wins outright; later clauses are never consulted. -/
def commitAnswers : List (Clause Goal Sub Ans) → Goal → List Ans
  | [], _ => []
  | c :: rest, g =>
      if (contrib c g).isEmpty then commitAnswers rest g else contrib c g

/-- Commitment observably differs from backtracking-all-clauses. -/
theorem commit_backtrack_divergence :
    ∃ cs : List (Clause Unit Unit ℕ),
      commitAnswers cs () ≠ pettaAnswers cs () := by
  refine ⟨[constClause 0, constClause 1], ?_⟩
  rw [pettaAnswers_constPair]
  simp [commitAnswers, contrib, constClause]

/-- All clauses in `pre` are dead on `g` (Boolean, so guards stay
computable). -/
def emptyAll (pre : List (Clause Goal Sub Ans)) (g : Goal) : Bool :=
  pre.all fun c => (contrib c g).isEmpty

/-- One translated clause: the head is total, and the guard — "every earlier
clause is dead" — carries the commitment.  Clause ORDER is compiled into
clause CONDITIONS; the earlier-clause prefix travels inside the clause. -/
def guardHead (pre : List (Clause Goal Sub Ans)) (c : Clause Goal Sub Ans) :
    Clause Goal Goal Ans where
  sel g := if emptyAll pre g then [g] else []
  run g := contrib c g

/-- What a translated clause contributes: its source's contribution when the
earlier prefix is dead, nothing otherwise. -/
theorem contrib_guardHead (pre : List (Clause Goal Sub Ans))
    (c : Clause Goal Sub Ans) (g : Goal) :
    contrib (guardHead pre c) g =
      if emptyAll pre g then contrib c g else [] := by
  by_cases h : emptyAll pre g <;> simp [contrib, guardHead, h]

/-- The chain translation of a committed program. -/
def chainAux : List (Clause Goal Sub Ans) → List (Clause Goal Sub Ans) →
    List (Clause Goal Goal Ans)
  | _, [] => []
  | pre, c :: rest => guardHead pre c :: chainAux (pre ++ [c]) rest

def chain (cs : List (Clause Goal Sub Ans)) : List (Clause Goal Goal Ans) :=
  chainAux [] cs

theorem emptyAll_append (pre : List (Clause Goal Sub Ans))
    (c : Clause Goal Sub Ans) (g : Goal) :
    emptyAll (pre ++ [c]) g = (emptyAll pre g && (contrib c g).isEmpty) := by
  simp [emptyAll]

theorem chainAux_spec (cs : List (Clause Goal Sub Ans))
    (pre : List (Clause Goal Sub Ans)) (g : Goal) :
    pettaAnswers (chainAux pre cs) g =
      if emptyAll pre g then commitAnswers cs g else [] := by
  induction cs generalizing pre with
  | nil => simp [chainAux, pettaAnswers, commitAnswers]
  | cons c rest ih =>
    rw [chainAux, pettaAnswers_cons, ih (pre ++ [c]), emptyAll_append]
    by_cases hpre : emptyAll pre g
    · by_cases hc : (contrib c g).isEmpty
      · have hnil : contrib c g = [] := by simpa using hc
        simp [contrib_guardHead, hpre, hnil, commitAnswers]
      · simp [contrib_guardHead, hpre, hc, commitAnswers]
    · simp [contrib_guardHead, hpre]

/-- **The pure clause-local commitment pass is exact in this model**: the
chain image, run under ordinary backtracking semantics, produces exactly the
committed source's answers.  General `cut` is outside this theorem. -/
theorem chain_exact (cs : List (Clause Goal Sub Ans)) (g : Goal) :
    pettaAnswers (chain cs) g = commitAnswers cs g := by
  have h := chainAux_spec cs [] g
  simpa [chain, emptyAll] using h

/-! ## Obstruction 3 dissolved: the chain image is permutation-rigid -/

/-- At most one clause of `l` is live on `g`. -/
def AtMostOneLive (l : List (Clause Goal Sub Ans)) (g : Goal) : Prop :=
  ∀ c₁ ∈ l, ∀ c₂ ∈ l, contrib c₁ g ≠ [] → contrib c₂ g ≠ [] → c₁ = c₂

/-- With at most one live clause, the ordered answer list is invariant under
permutation — order-sensitivity needs at least two live clauses to observe. -/
theorem perm_pettaAnswers_of_atMostOneLive {l₁ l₂ : List (Clause Goal Sub Ans)}
    (g : Goal) (hp : l₁.Perm l₂) (h : AtMostOneLive l₁ g) :
    pettaAnswers l₁ g = pettaAnswers l₂ g := by
  induction hp with
  | nil => rfl
  | cons x p ih =>
    have h' : AtMostOneLive _ g := fun c₁ h₁ c₂ h₂ =>
      h c₁ (List.mem_cons_of_mem _ h₁) c₂ (List.mem_cons_of_mem _ h₂)
    rw [pettaAnswers_cons, pettaAnswers_cons, ih h']
  | swap x y l =>
    simp only [pettaAnswers_cons]
    by_cases hy : contrib y g = []
    · simp [hy]
    · by_cases hx : contrib x g = []
      · simp [hx]
      · rw [h y (by simp) x (by simp) hy hx]
  | trans p₁ p₂ ih₁ ih₂ =>
    have h₂ : AtMostOneLive _ g := fun c₁ h₁ c₂ hc₂ hn₁ hn₂ =>
      h c₁ (p₁.mem_iff.mpr h₁) c₂ (p₁.mem_iff.mpr hc₂) hn₁ hn₂
    rw [ih₁ h, ih₂ h₂]

/-- If some earlier clause is live, every chain clause downstream is dead —
the guards see the live prefix and refuse. -/
theorem chainAux_dead_of_not_emptyAll {pre : List (Clause Goal Sub Ans)}
    {g : Goal} (h : emptyAll pre g = false)
    (cs : List (Clause Goal Sub Ans)) :
    ∀ c' ∈ chainAux pre cs, contrib c' g = [] := by
  induction cs generalizing pre with
  | nil => simp [chainAux]
  | cons c rest ih =>
    intro c' hc'
    rw [chainAux, List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · rw [contrib_guardHead, if_neg (by simp [h])]
    · exact ih (by rw [emptyAll_append, h, Bool.false_and]) c' hc'

/-- The chain image always has at most one live clause: commitment makes the
translated program semantically deterministic at the clause level. -/
theorem chainAux_atMostOneLive (cs : List (Clause Goal Sub Ans))
    (pre : List (Clause Goal Sub Ans)) (g : Goal) :
    AtMostOneLive (chainAux pre cs) g := by
  induction cs generalizing pre with
  | nil => intro c₁ h₁; simp [chainAux] at h₁
  | cons c rest ih =>
    intro c₁ h₁ c₂ h₂ hn₁ hn₂
    rw [chainAux, List.mem_cons] at h₁ h₂
    have headDead : contrib (guardHead pre c) g ≠ [] →
        ∀ c' ∈ chainAux (pre ++ [c]) rest, contrib c' g = [] := by
      intro hn
      have hguard : emptyAll pre g = true := by
        cases hpre : emptyAll pre g
        · exact absurd (by rw [contrib_guardHead, if_neg (by simp [hpre])]) hn
        · rfl
      have hlive : (contrib c g).isEmpty = false := by
        cases hemp : contrib c g with
        | nil => exact absurd (by rw [contrib_guardHead, if_pos hguard]; exact hemp) hn
        | cons a t => rfl
      exact chainAux_dead_of_not_emptyAll
        (by rw [emptyAll_append, hguard, Bool.true_and, hlive]) rest
    rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
    · rfl
    · exact absurd (headDead hn₁ c₂ h₂) hn₂
    · exact absurd (headDead hn₂ c₁ h₁) hn₁
    · exact ih (pre ++ [c]) c₁ h₁ c₂ h₂ hn₁ hn₂

/-- **Order dissolves on the committed fragment**: ANY permutation of the
chain image yields the committed source's answers — the image is
order-invariant, so a bag-level target observation already determines it. -/
theorem chain_perm_rigid (cs : List (Clause Goal Sub Ans))
    {l' : List (Clause Goal Goal Ans)} (g : Goal)
    (hp : (chain cs).Perm l') :
    pettaAnswers l' g = commitAnswers cs g := by
  rw [← perm_pettaAnswers_of_atMostOneLive g hp (chainAux_atMostOneLive cs [] g),
    chain_exact]

/-- **Bounded-selection license in this fragment**: on committed images,
demanding the first answer is order-free because every permutation has the
same sole live contribution. -/
theorem commit_first_order_free (cs : List (Clause Goal Sub Ans))
    {l' : List (Clause Goal Goal Ans)} (g : Goal)
    (hp : (chain cs).Perm l') :
    (pettaAnswers l' g).head? = (commitAnswers cs g).head? := by
  rw [chain_perm_rigid cs g hp]

end Mettapedia.GSLT.Dynamics.DialectTranslation
