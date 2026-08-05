import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic

/-!
# Dialect translation: the partiality guard, sealed

The semantic core of the petta → he-extended translator, proved before the
translator is built, so the generated rewrite passes land on anchors.

Two evaluation disciplines over the same clauses:

* **PeTTa discipline**: clauses are tried in order; a clause whose pattern
  does not match contributes nothing; a goal no clause matches FAILS —
  contributes the empty answer list.
* **HE discipline**: clauses contribute as a bag; a goal no clause matches
  is INERT — the goal itself is the one answer, as a first-class value.

The divergence is exactly partiality (`pettaAnswers` vs `heAnswers` on an
unmatched goal), and the guard translation — make every clause head total,
move the pattern into a unify-with-Empty guard — eliminates it:

* `guard_translation_exact` — the internal enumeration produced by this
  clause model is list-exact.  The language-level observation is the weaker
  `AnswerBagEquivalent` quotient: answer order is deliberately unobservable,
  while multiplicity and nested answer structure remain observable.
* `guard_translation_bag_exact` — the same pass is therefore exact for the
  public answer-bag observation used by translation tests.
* `partiality_divergence` — without the guard, the disciplines provably
  differ (the two-line `pick` specimen, formalized).
* `first_answer_sound` / `prefix_exact` — when an explicitly ordered demand
  policy is selected, demanding one (or k) internal answers yields exactly the
  source's first (or first k) answers.  This is not an ordering requirement on
  ordinary answer-bag comparison.
* `Preserves.comp` — observation-preserving passes compose, so the
  translator pipeline never re-proves the frame per feature.

Scope honesty: clauses are modeled denotationally (match yields
substitutions, bodies map substitutions to answers); recursion through the
store, effects, and the reverse direction are NOT modeled here — these are
the anchors for the generated passes, not a whole-language bisimulation.
-/

namespace Mettapedia.GSLT.Dynamics.DialectTranslation

variable {Goal Sub Ans : Type}

/-- Translation-level equivalence of completed answer collections.  The outer
enumeration order is quotiented away, but multiplicity and each answer's full
structure are retained by `Multiset`. -/
def AnswerBagEquivalent (xs ys : List Ans) : Prop :=
  (xs : Multiset Ans) = (ys : Multiset Ans)

theorem answerBagEquivalent_of_perm {xs ys : List Ans} (h : xs.Perm ys) :
    AnswerBagEquivalent xs ys := by
  exact Multiset.coe_eq_coe.mpr h

/-- Positive discriminator: an outer permutation is observationally equal. -/
example : AnswerBagEquivalent [0, 1, 0] [1, 0, 0] := by
  unfold AnswerBagEquivalent
  decide

/-- Negative discriminator: dropping or changing one duplicate is observable. -/
example : ¬ AnswerBagEquivalent [0, 0, 1] [0, 1, 1] := by
  unfold AnswerBagEquivalent
  decide

/-- Negative discriminator: answer structure is not flattened into a token
bag.  Only the outer answer enumeration is quotiented. -/
example : ¬ AnswerBagEquivalent ([[0], [1, 2]] : List (List Nat))
    [[0, 1], [2]] := by
  unfold AnswerBagEquivalent
  decide

/-- A clause: a matcher producing substitutions, and a body run under each
substitution.  Multiplicity is meaningful throughout — lists, not sets. -/
structure Clause (Goal Sub Ans : Type) where
  sel : Goal → List Sub
  run : Sub → List Ans

/-- A clause's contribution to a goal. -/
def contrib (c : Clause Goal Sub Ans) (g : Goal) : List Ans :=
  (c.sel g).flatMap c.run

/-- PeTTa discipline: ordered concatenation of clause contributions;
exhaustion is failure — the empty list. -/
def pettaAnswers (cs : List (Clause Goal Sub Ans)) (g : Goal) : List Ans :=
  cs.flatMap (fun c => contrib c g)

/-- Some clause's pattern matches the goal. -/
def matchedAny (cs : List (Clause Goal Sub Ans)) (g : Goal) : Prop :=
  ∃ c ∈ cs, c.sel g ≠ []

instance (cs : List (Clause Goal Sub Ans)) (g : Goal)
    [∀ c : Clause Goal Sub Ans, Decidable (c.sel g ≠ [])] :
    Decidable (matchedAny cs g) := by
  unfold matchedAny; infer_instance

/-- HE discipline: the same contributions, EXCEPT that a goal matched by no
clause is inert — the embedded goal itself is the single answer. -/
def heAnswers (embed : Goal → Ans) (cs : List (Clause Goal Sub Ans))
    (g : Goal) [Decidable (matchedAny cs g)] : List Ans :=
  if matchedAny cs g then cs.flatMap (fun c => contrib c g) else [embed g]

/-- The guard translation of one clause: the head becomes total (it matches
every goal with the goal itself as the trivial substitution) and the body
becomes the original guarded contribution — match inside, `Empty` on
failure.  This is exactly the `unify … Empty` scheme the concrete
translator emits. -/
def guardClause (c : Clause Goal Sub Ans) : Clause Goal Goal Ans where
  sel g := [g]
  run g := contrib c g

/-- Guarded clauses always match (given any clause exists at all). -/
theorem guardImage_matchedAny (cs : List (Clause Goal Sub Ans)) (g : Goal)
    (hne : cs ≠ []) : matchedAny (cs.map guardClause) g := by
  cases cs with
  | nil => exact absurd rfl hne
  | cons c rest =>
    exact ⟨guardClause c, List.mem_map_of_mem (List.mem_cons_self ..),
      by simp [guardClause]⟩

/-- A guarded clause contributes exactly what its source contributes. -/
theorem guarded_contrib (c : Clause Goal Sub Ans) (g : Goal) :
    contrib (guardClause c) g = contrib c g := by
  simp [guardClause, contrib]

theorem guardImage_flatMap (cs : List (Clause Goal Sub Ans)) (g : Goal) :
    (cs.map guardClause).flatMap (fun c => contrib c g) =
      cs.flatMap (fun c => contrib c g) := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map_cons, List.flatMap_cons, guarded_contrib, ih]

/-- **The partiality-guard theorem.**  For any nonempty clause list, the HE
answers of the guarded image equal the PeTTa answers of the source — as
lists: order and multiplicity exact, inert ghost gone.  This is the
correctness contract of the translator's partiality pass. -/
theorem guard_translation_exact (embed : Goal → Ans)
    (cs : List (Clause Goal Sub Ans)) (g : Goal) (hne : cs ≠ [])
    [Decidable (matchedAny (cs.map guardClause) g)] :
    heAnswers embed (cs.map guardClause) g = pettaAnswers cs g := by
  unfold heAnswers
  rw [if_pos (guardImage_matchedAny cs g hne)]
  exact guardImage_flatMap cs g

/-- The public translation contract: partiality guarding preserves the answer
bag, including duplicate derivations and complete nested answers. -/
theorem guard_translation_bag_exact (embed : Goal → Ans)
    (cs : List (Clause Goal Sub Ans)) (g : Goal) (hne : cs ≠ [])
    [Decidable (matchedAny (cs.map guardClause) g)] :
    AnswerBagEquivalent (heAnswers embed (cs.map guardClause) g)
      (pettaAnswers cs g) := by
  rw [guard_translation_exact embed cs g hne]
  unfold AnswerBagEquivalent
  rfl

/-- **The divergence, witnessed.**  On a goal no clause matches, the two
disciplines provably differ: PeTTa fails (no answers) while HE returns the
inert goal.  This is the `pick`-on-`Nil` specimen as a theorem, and the
reason the guard pass exists. -/
theorem partiality_divergence (embed : Goal → Ans)
    (cs : List (Clause Goal Sub Ans)) (g : Goal)
    (hnomatch : ∀ c ∈ cs, c.sel g = [])
    [Decidable (matchedAny cs g)] :
    pettaAnswers cs g = [] ∧ heAnswers embed cs g = [embed g] := by
  constructor
  · unfold pettaAnswers
    rw [List.flatMap_eq_nil_iff]
    intro c hc
    unfold contrib
    rw [hnomatch c hc]
    rfl
  · unfold heAnswers
    rw [if_neg]
    rintro ⟨c, hc, hm⟩
    exact hm (hnomatch c hc)

/-- **Cardinality soundness**: the first answer demanded from the image is
exactly the source's first answer — the demand-1 discipline is not merely
sound but exact. -/
theorem first_answer_sound (embed : Goal → Ans)
    (cs : List (Clause Goal Sub Ans)) (g : Goal) (hne : cs ≠ [])
    [Decidable (matchedAny (cs.map guardClause) g)] :
    (heAnswers embed (cs.map guardClause) g).head? =
      (pettaAnswers cs g).head? := by
  rw [guard_translation_exact embed cs g hne]

/-- **Prefix exactness**: demanding any k answers from the image yields the
source's first k answers — PeTTa's on-demand enumeration maps to prefix
demand on the bag, order preserved. -/
theorem prefix_exact (embed : Goal → Ans)
    (cs : List (Clause Goal Sub Ans)) (g : Goal) (hne : cs ≠ []) (k : Nat)
    [Decidable (matchedAny (cs.map guardClause) g)] :
    (heAnswers embed (cs.map guardClause) g).take k =
      (pettaAnswers cs g).take k := by
  rw [guard_translation_exact embed cs g hne]

/-! ## Pass composition -/

/-- An observation-preserving program transformation, relative to an
arbitrary observation function. -/
def Preserves {Prog Obs : Type} (obs : Prog → Obs) (T : Prog → Prog) : Prop :=
  ∀ p, obs (T p) = obs p

/-- **Preserving passes compose**: the translator pipeline inherits
correctness from its features; no per-pipeline re-proof. -/
theorem Preserves.comp {Prog Obs : Type} (obs : Prog → Obs)
    {T U : Prog → Prog} (hT : Preserves obs T) (hU : Preserves obs U) :
    Preserves obs (T ∘ U) := by
  intro p
  simp [Function.comp, hT (U p), hU p]

end Mettapedia.GSLT.Dynamics.DialectTranslation
