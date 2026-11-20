import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Every
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OneAfterAnother
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# `every` and `one` on two tokens that no row tells apart

Two rows carry the same label, a token `1`. The rule `consume` of `Examples` takes a token and makes a
`2`.

## One match and every match

* The step of the program takes **one** of the two tokens (`takeAt_admitted`,
  `one_takes_one_of_two`): after it the other token is present.
* **Every admitted firing has this shape** (`firing_shape`): one taken token, one made row.
* The bag of the two matches is admitted as `every` (`spendBoth_every`): it is jointly admitted,
  within the rule, with distinct keys, and complete. After it both tokens are gone
  (`spendBoth_result`).
* **`every` takes both or neither** (`every_takes_both_or_neither`, by `every_same_label`): no bag
  admitted as `every` leaves exactly one of the two tokens. So `every` alone cannot do what `one` does
  here.
* **`every` is not the box of `one`** (`every_not_box_one`): after every firing of the program a token
  remains; after `every` none does. **Nor its diamond** (`every_not_dia_one`): no firing of the program
  reaches a state without tokens; `every` does.

## Firings and matches

* **One match has infinitely many firings** (`firings_of_one_match`): for every identity that is not
  present, taking the first token and making that identity is an admitted firing, and all of them have
  one key. "Every firing" is no finite bag.
* **A bag may hold one match twice** (`twice_admitted`, `twice_not_distinct`, `twice_result`): the rule
  `copy` reads a token and makes a `2`; two firings that read the same token and make different
  identities are jointly admitted, and the result holds two made rows for one match. `every` asks
  distinct keys, which refuses it; the bag step without that ask commits it, as two firings of the step
  of the program one after the other do.

## Ground rules

`fresh_of_ground_bag`: a bag of rules whose terms every substitution fixes is jointly fresh at every
state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)

/-! ## Ground rules are opened freshly together -/

section Ground

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO}
  {P : Program (Terms T)}

/-- A bag of rules whose terms every substitution fixes realizes every instantiation by any
substitution. -/
theorem realized_of_ground (b : PUnit.{1}) (u : S) :
    ∀ (l : List (OneMember A O P)) {Q : S → Prop},
      (∀ m ∈ l, ∀ t ∈ m.rule.terms, ∀ σ : S, A.apply σ t = t) → Q u → Realized (frames A) b l Q
  | [], Q, _, holds => (realized_nil (frames A) Q).mpr ⟨u, holds⟩
  | m :: rest, Q, ground, holds => (realized_cons (frames A) m rest Q).mpr fun h =>
      realized_of_ground b u rest (fun r inside => ground r (List.mem_cons_of_mem _ inside))
        ⟨holds, fun t member => by
          show A.E (A.apply u (A.apply m.opening t)) (A.apply h t)
          rw [ground m List.mem_cons_self t member m.opening, ground m List.mem_cons_self t member u,
            ground m List.mem_cons_self t member h]
          exact A.equivalence.refl _⟩

/-- **A bag of ground rules is jointly fresh at every state.** -/
theorem fresh_of_ground_bag (s : State (Terms T) O) (l : List (OneMember A O P))
    (ground : ∀ m ∈ l, ∀ t ∈ m.rule.terms, ∀ σ : S, A.apply σ t = t) :
    (bagOf A l).Fresh (frames A) s := by
  intro b g
  refine realized_of_ground A b g l ground fun t _ => ?_
  show A.E (A.apply g (A.apply A.identity t)) (A.apply g t)
  rw [A.apply_identity]
  exact A.equivalence.refl _

end Ground

namespace EveryControls

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-! ## Two tokens, one rule -/

/-- **The program**: take a token `1`, make a `2`. -/
def tokens : Program Tm := {Examples.consume}

/-- Rows that all carry the same label, a token, at the given identities. -/
def tokensAt (W : Finset ℕ) : State Tm ℕ := ⟨PUnit.unit, [], W, fun _ => c 1⟩

/-- Two rows with the same label, a token. -/
def twoTokens : State Tm ℕ := tokensAt {0, 1}

/-- Take the token at `o`, make the identity `n`. -/
def takeAt (o n : ℕ) : OneMember action ℕ tokens :=
  ⟨Examples.consume, rfl, Subst.id atoms, ⟨[o], [], [n]⟩, []⟩

theorem consume_ground : ∀ t ∈ Examples.consume.terms, ∀ σ : Subst atoms, action.apply σ t = t := by
  intro t member σ
  have listed : t ∈ [c 1, c 2] := member
  rcases List.mem_cons.mp listed with rfl | rest
  · rfl
  · rw [List.mem_singleton.mp rest]
    rfl

theorem takeAt_information (W : Finset ℕ) (o n : ℕ) :
    (takeAt o n).firing.information X (tokensAt W) = [(c 1, c 1)] := rfl

/-- **Taking a present token is admitted**, whatever fresh identity is made. -/
theorem takeAt_admitted {W : Finset ℕ} {o n : ℕ} (present : o ∈ W) (fresh : n ∉ W) :
    (takeAt o n).firing.Admits X (tokensAt W) := by
  refine ⟨⟨Examples.fresh_of_ground action (tokensAt W) (takeAt o n).firing consume_ground,
    List.nodup_singleton o, List.nodup_singleton n, rfl, rfl, rfl, rfl⟩, ?_, ?_,
    fun b σ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  · refine ⟨fun x member => ?_, fun x member => ?_, ?_, ?_, fun q member => ?_⟩
    · rw [List.mem_singleton.mp (List.mem_toFinset.mp member)]
      exact present
    · exact absurd (List.mem_toFinset.mp member) List.not_mem_nil
    · exact Finset.disjoint_left.mpr fun x _ kept =>
        absurd (List.mem_toFinset.mp kept) List.not_mem_nil
    · refine Finset.disjoint_left.mpr fun x made inside => fresh ?_
      rw [← List.mem_singleton.mp (List.mem_toFinset.mp made)]
      exact inside
    · simp [Selection.commit] at member
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    have listed : e ∈ [(c 1, c 1)] := member
    rw [List.mem_singleton.mp listed]
    rfl

/-- **The shape of every admitted firing**: it takes one present token and makes one identity. -/
theorem firing_shape {W : Finset ℕ} (g : Firing ℕ E tokens PUnit.unit)
    (admitted : g.Admits X (tokensAt W)) :
    ∃ o n, o ∈ W ∧ g.rule = Examples.consume ∧ g.selection = ⟨[o], [], [n]⟩ := by
  obtain ⟨rule, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := g
  obtain ⟨⟨-, -, -, takeLength, readLength, produceLength, -⟩, enabled, -, -⟩ := admitted
  have isConsume : rule = Examples.consume := member
  subst isConsume
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp (show taken.length = 1 from takeLength.symm)
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp (show made.length = 1 from produceLength.symm)
  have noRead : read = [] := List.length_eq_zero_iff.mp (show read.length = 0 from readLength.symm)
  subst noRead
  exact ⟨o, n, enabled.taken_subset (List.mem_toFinset.mpr List.mem_cons_self), rfl, rfl⟩

/-- **After every firing of the program a token remains.** -/
theorem one_keeps_a_token (g : Firing ℕ E tokens PUnit.unit) (admitted : g.Admits X twoTokens) :
    0 ∈ (g.result X twoTokens).present ∨ 1 ∈ (g.result X twoTokens).present := by
  obtain ⟨o, n, present, -, selection⟩ := firing_shape g admitted
  have cases : o = 0 ∨ o = 1 := by
    have inside : o ∈ ({0, 1} : Finset ℕ) := present
    simpa using inside
  have unfolded : (g.result X twoTokens).present =
      fire twoTokens.present ((⟨[o], [], [n]⟩ : Selection ℕ).commit (T := Unit)) := by
    show fire twoTokens.present (g.selection.commit (T := Unit)) = _
    rw [selection]
  rw [unfolded]
  rcases cases with rfl | rfl
  · refine Or.inr (mem_fire.mpr (Or.inl ⟨by decide, fun gone => ?_⟩))
    exact absurd (List.mem_singleton.mp (List.mem_toFinset.mp gone)) (by decide)
  · refine Or.inl (mem_fire.mpr (Or.inl ⟨by decide, fun gone => ?_⟩))
    exact absurd (List.mem_singleton.mp (List.mem_toFinset.mp gone)) (by decide)

/-- **One match takes one of the two tokens**: the firing is admitted, the first token is gone and
the second is present. -/
theorem one_takes_one_of_two :
    (takeAt 0 10).firing.Admits X twoTokens ∧
      0 ∉ ((takeAt 0 10).firing.result X twoTokens).present ∧
      1 ∈ ((takeAt 0 10).firing.result X twoTokens).present :=
  ⟨takeAt_admitted (by decide) (by decide), by decide, by decide⟩

/-! ## The complete bag -/

/-- **The bag of the two matches.** -/
def spendBoth : Bag ℕ E tokens PUnit.unit := bagOf action [takeAt 0 10, takeAt 1 11]

theorem spendBoth_information :
    Bag.information X twoTokens spendBoth = [(c 1, c 1), (c 1, c 1)] := rfl

theorem spendBoth_own : Bag.AdmitsOwn X twoTokens spendBoth := by
  have members : ∀ m ∈ spendBoth.members, m = takeAt 0 10 ∨ m = takeAt 1 11 := by
    intro m inside
    have listed : m ∈ [takeAt 0 10, takeAt 1 11] := inside
    rcases List.mem_cons.mp listed with first | rest
    · exact Or.inl first
    · exact Or.inr (List.mem_singleton.mp rest)
  refine ⟨⟨fresh_of_ground_bag action twoTokens _ fun m inside => ?_, by decide, by decide,
    fun m inside => ?_⟩, ⟨by decide, by decide, by decide, by decide,
      fun q member => by simp [Selection.commit] at member⟩, ?_, fun m inside b σ _ => ?_⟩
  · rcases members m inside with rfl | rfl <;> exact consume_ground
  · rcases members m inside with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    rw [spendBoth_information] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    rw [member]
    rfl
  · rcases members m inside with rfl | rfl <;>
      exact ⟨fun check member => absurd member List.not_mem_nil,
        fun q member => absurd member List.not_mem_nil⟩

/-- **The bag of the two matches is admitted as `every`.** -/
theorem spendBoth_every : Bag.AdmitsEvery X twoTokens tokens spendBoth := by
  refine ⟨spendBoth_own, fun m inside => ?_, ?_, fun g _ admitted => ?_⟩
  · have listed : m ∈ [takeAt 0 10, takeAt 1 11] := inside
    rcases List.mem_cons.mp listed with rfl | rest
    · exact rfl
    · rw [List.mem_singleton.mp rest]
      exact rfl
  · show [(takeAt 0 10).key, (takeAt 1 11).key].Nodup
    refine List.nodup_cons.mpr ⟨fun inside => ?_, List.nodup_singleton _⟩
    have differ : ([0] : List ℕ) ≠ [1] := by decide
    exact differ (congrArg (fun k : Rule Tm × List ℕ × List ℕ => k.2.1) (List.mem_singleton.mp inside))
  · obtain ⟨o, n, present, rule, selection⟩ := firing_shape g admitted
    have key : firingKey g = (Examples.consume, [o], []) := by
      unfold firingKey
      rw [rule, selection]
    have cases : o = 0 ∨ o = 1 := by
      have inside : o ∈ ({0, 1} : Finset ℕ) := present
      simpa using inside
    rw [key]
    rcases cases with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self

/-- After it both tokens are gone. -/
theorem spendBoth_result : (Bag.result X twoTokens spendBoth).present = {10, 11} := by decide

/-- **`every` takes both tokens or neither**: no bag admitted as `every` leaves exactly one. -/
theorem every_takes_both_or_neither {f : Bag ℕ E tokens PUnit.unit}
    (every : Bag.AdmitsEvery X twoTokens tokens f) :
    0 ∈ (Bag.result X twoTokens f).present ↔ 1 ∈ (Bag.result X twoTokens f).present :=
  every_same_label (fun _ _ => ⟨Subst.id atoms⟩) every rfl (by decide) (by decide)

/-- **`every` is not the box of `one`**: after every firing of the program a token remains; after
`every` none does. -/
theorem every_not_box_one :
    ∃ φ : State Tm ℕ → Prop,
      (∀ s', Succ (step X ℕ E tokens).toStep twoTokens s' → φ s') ∧
      ∃ f : Bag ℕ E tokens PUnit.unit, Bag.AdmitsEvery X twoTokens tokens f ∧
        ¬ φ (Bag.result X twoTokens f) := by
  refine ⟨fun t => 0 ∈ t.present ∨ 1 ∈ t.present, ?_, spendBoth, spendBoth_every, ?_⟩
  · rintro s' ⟨g, admitted, rfl⟩
    exact one_keeps_a_token g admitted
  · show ¬ (0 ∈ (Bag.result X twoTokens spendBoth).present ∨
      1 ∈ (Bag.result X twoTokens spendBoth).present)
    rw [spendBoth_result]
    decide

/-- **`every` is not the diamond of `one`**: no firing of the program reaches a state without tokens;
`every` does. -/
theorem every_not_dia_one :
    ∃ ψ : State Tm ℕ → Prop,
      (¬ ∃ s', Succ (step X ℕ E tokens).toStep twoTokens s' ∧ ψ s') ∧
      ∃ f : Bag ℕ E tokens PUnit.unit, Bag.AdmitsEvery X twoTokens tokens f ∧
        ψ (Bag.result X twoTokens f) := by
  refine ⟨fun t => 0 ∉ t.present ∧ 1 ∉ t.present, ?_, spendBoth, spendBoth_every, ?_⟩
  · rintro ⟨s', ⟨g, admitted, rfl⟩, none₀, none₁⟩
    rcases one_keeps_a_token g admitted with here | here
    · exact none₀ here
    · exact none₁ here
  · show 0 ∉ (Bag.result X twoTokens spendBoth).present ∧
      1 ∉ (Bag.result X twoTokens spendBoth).present
    rw [spendBoth_result]
    decide

/-! ## Firings and matches -/

/-- **One match has infinitely many firings**: every identity that is not present gives an admitted
firing with the same key, and different identities give different firings. -/
theorem firings_of_one_match :
    (∀ n, n ∉ twoTokens.present → (takeAt 0 n).firing.Admits X twoTokens ∧
      firingKey (takeAt 0 n).firing = (Examples.consume, [0], [])) ∧
    ∀ n n', (takeAt 0 n).firing = (takeAt 0 n').firing → n = n' := by
  refine ⟨fun n fresh => ⟨takeAt_admitted (by decide) fresh, rfl⟩, fun n n' same => ?_⟩
  have made : [n] = [n'] := congrArg (fun g : Firing ℕ E tokens PUnit.unit => g.selection.made) same
  exact List.head_eq_of_cons_eq made

/-- Read a token `1`, make a `2`. -/
def copy : Rule Tm := ⟨PUnit.unit, ⟨[], [c 1], [], [], [c 2]⟩, []⟩

/-- The program of the one reading rule. -/
def copies : Program Tm := {copy}

/-- Read the token at `o`, make the identity `n`. -/
def readAt (o n : ℕ) : OneMember action ℕ copies :=
  ⟨copy, rfl, Subst.id atoms, ⟨[], [o], [n]⟩, []⟩

/-- Two firings of one match: both read the first token. -/
def twice : Bag ℕ E copies PUnit.unit := bagOf action [readAt 0 10, readAt 0 11]

theorem copy_ground : ∀ t ∈ copy.terms, ∀ σ : Subst atoms, action.apply σ t = t := by
  intro t member σ
  have listed : t ∈ [c 1, c 2] := member
  rcases List.mem_cons.mp listed with rfl | rest
  · rfl
  · rw [List.mem_singleton.mp rest]
    rfl

theorem twice_information : Bag.information X twoTokens twice = [(c 1, c 1), (c 1, c 1)] := rfl

/-- **A bag that holds one match twice is jointly admitted.** -/
theorem twice_admitted : Bag.AdmitsOwn X twoTokens twice := by
  have members : ∀ m ∈ twice.members, m = readAt 0 10 ∨ m = readAt 0 11 := by
    intro m inside
    have listed : m ∈ [readAt 0 10, readAt 0 11] := inside
    rcases List.mem_cons.mp listed with first | rest
    · exact Or.inl first
    · exact Or.inr (List.mem_singleton.mp rest)
  refine ⟨⟨fresh_of_ground_bag action twoTokens _ fun m inside => ?_, by decide, by decide,
    fun m inside => ?_⟩, ⟨by decide, by decide, by decide, by decide,
      fun q member => by simp [Selection.commit] at member⟩, ?_, fun m inside b σ _ => ?_⟩
  · rcases members m inside with rfl | rfl <;> exact copy_ground
  · rcases members m inside with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    rw [twice_information] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    rw [member]
    rfl
  · rcases members m inside with rfl | rfl <;>
      exact ⟨fun check member => absurd member List.not_mem_nil,
        fun q member => absurd member List.not_mem_nil⟩

/-- Its two members have one key, so it is not a bag of distinct matches. -/
theorem twice_not_distinct : ¬ twice.Distinct := fun distinct =>
  (List.nodup_cons.mp (show [(readAt 0 10).key, (readAt 0 11).key].Nodup from distinct)).1
    List.mem_cons_self

/-- Its result holds two made rows for the one match. -/
theorem twice_result : (Bag.result X twoTokens twice).present = {0, 1, 10, 11} := by decide

end EveryControls

#print axioms realized_of_ground
#print axioms fresh_of_ground_bag
#print axioms EveryControls.takeAt_admitted
#print axioms EveryControls.firing_shape
#print axioms EveryControls.one_keeps_a_token
#print axioms EveryControls.one_takes_one_of_two
#print axioms EveryControls.spendBoth_every
#print axioms EveryControls.spendBoth_result
#print axioms EveryControls.every_takes_both_or_neither
#print axioms EveryControls.every_not_box_one
#print axioms EveryControls.every_not_dia_one
#print axioms EveryControls.firings_of_one_match
#print axioms EveryControls.twice_admitted
#print axioms EveryControls.twice_not_distinct
#print axioms EveryControls.twice_result

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
