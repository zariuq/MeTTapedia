import Mathlib.Data.Multiset.Bind
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Outcomes of bounded search

A bounded search reports its answers together with a status: it **finished** (every alternative
was explored) or it was **cut off** (some alternative was left unexplored). This module is the
algebra of such outcomes; `SearchSpace` gives them their meaning against the unbounded semantics.

## Answers are a multiset

Alternatives of a nondeterministic choice are unordered: a space promises no order, and only a
stack or a queue does, which is a policy (`SearchPolicy`), not the semantics. Answers are
therefore a `Multiset`. Multiplicity is kept: two derivations of one answer are two answers.
On lists, commutativity of choice and left distribution of bind over choice fail
(`list_choice_not_comm`, `list_bind_not_left_distrib`); on multisets they hold.

## The algebra (`Outcome`)

* **Choice** is `+`: answers add, and the result is finished only when every alternative
  finished (`Status` is the two-element join-semilattice, `finished` its unit). Outcomes form a
  commutative monoid whose unit is `refuted`, the finished outcome with no answers.
* **Sequencing** is `bind`: a monad (`pure_bind`, `bind_pure`, `bind_assoc`) that distributes over
  choice on both sides (`add_bind`, `bind_add`) and has `refuted` as left zero (`zero_bind`).
  `refuted` is **not** a right zero: continuing a cut-off search by a failing continuation is cut
  off, not refuted (`bind_refuted`, `cutOff_bind_refuted_ne_refuted`).
* **Collect** gathers the answers of an outcome into one answer. A cut-off outcome collects to
  `unknown`: no answer, cut off (`collect_cutOff`). This is forced: it is the only monotone
  extension of collection on finished outcomes (`collect_unique`); gathering the partial answers
  as if they were the collection is not monotone (`partialCollect_not_monotone`).
* Choice is not idempotent (`choice_not_idempotent`), and `unknown` is not a unit for it
  (`unknown_not_unit`).

## The information order

`o ≤ o'` when `o'` may be what `o` becomes with more budget: equal, or `o` cut off with fewer
answers. It is a partial order with bottom `unknown` (`bot_eq_unknown`); finished outcomes are
maximal (`eq_of_finished_le`). Choice, bind and collect are monotone (`add_le_add'`, `bind_mono`,
`collect_mono`).

## Readouts

* **Existence** (`verdict`): `commit` when there is an answer, `refuted` when finished with no
  answers, `suspended` when cut off with no answers. **Incomplete is never none**: a cut-off
  outcome never reads `refuted` (`verdict_ne_refuted_of_cutOff`), and the definite readouts are
  stable along the information order (`verdict_eq_of_le`).
* **Collection** (`collect` then `verdict`): `commit` exactly when finished, `suspended` exactly
  when cut off; never `refuted` (`collect_verdict`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

universe u v w

/-! ## Status -/

/-- Whether a search explored every alternative. -/
inductive Status where
  | finished
  | cutOff
  deriving DecidableEq, Repr

namespace Status

/-- Combining the statuses of alternatives: cut off as soon as one is. -/
def join : Status → Status → Status
  | finished, t => t
  | cutOff, _ => cutOff

instance : Add Status := ⟨join⟩

instance : Zero Status := ⟨finished⟩

instance : AddCommMonoid Status where
  add_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_add := by intro a; cases a <;> rfl
  add_zero := by intro a; cases a <;> rfl
  add_comm := by intro a b; cases a <;> cases b <;> rfl
  nsmul := nsmulRec

@[simp] theorem zero_eq : (0 : Status) = finished := rfl
@[simp] theorem finished_add (t : Status) : finished + t = t := rfl
@[simp] theorem cutOff_add (t : Status) : cutOff + t = cutOff := rfl
@[simp] theorem add_finished (t : Status) : t + finished = t := by cases t <;> rfl
@[simp] theorem add_cutOff (t : Status) : t + cutOff = cutOff := by cases t <;> rfl
theorem add_self (t : Status) : t + t = t := by cases t <;> rfl

theorem add_eq_finished_iff {s t : Status} : s + t = finished ↔ s = finished ∧ t = finished := by
  cases s <;> cases t <;> decide

theorem eq_cutOff_of_ne_finished {s : Status} (h : s ≠ finished) : s = cutOff := by
  cases s
  · exact absurd rfl h
  · rfl

theorem sum_eq_finished_iff {m : Multiset Status} : m.sum = finished ↔ ∀ s ∈ m, s = finished := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp [add_eq_finished_iff, ih]

theorem sum_map_finished {ι : Type u} (m : Multiset ι) : (m.map fun _ => finished).sum = finished :=
  sum_eq_finished_iff.mpr fun s member => by
    obtain ⟨_, _, rfl⟩ := Multiset.mem_map.mp member
    rfl

end Status

/-! ## Outcomes and choice -/

/-- **A search outcome**: the answers found, and whether the search finished. -/
@[ext]
structure Outcome (α : Type u) where
  answers : Multiset α
  status : Status

namespace Outcome

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Choice: answers add, and the result is finished only if every alternative finished. -/
instance : Add (Outcome α) := ⟨fun o o' => ⟨o.answers + o'.answers, o.status + o'.status⟩⟩

/-- The empty finished choice: no answers, and nothing left to explore. -/
instance : Zero (Outcome α) := ⟨⟨0, .finished⟩⟩

@[simp] theorem add_answers (o o' : Outcome α) : (o + o').answers = o.answers + o'.answers := rfl
@[simp] theorem add_status (o o' : Outcome α) : (o + o').status = o.status + o'.status := rfl
@[simp] theorem zero_answers : (0 : Outcome α).answers = 0 := rfl
@[simp] theorem zero_status : (0 : Outcome α).status = .finished := rfl

instance : AddCommMonoid (Outcome α) where
  add_assoc a b c := by ext1 <;> simp [add_assoc]
  zero_add a := by ext1 <;> simp
  add_zero a := by ext1 <;> simp
  add_comm a b := by ext1 <;> simp [add_comm]
  nsmul := nsmulRec

/-- **Refuted**: finished with no answers. It is the unit of choice. -/
def refuted : Outcome α := 0

/-- **Unknown**: cut off with no answers. -/
def unknown : Outcome α := ⟨0, .cutOff⟩

/-- One answer, finished. -/
def pure (a : α) : Outcome α := ⟨{a}, .finished⟩

@[simp] theorem pure_answers (a : α) : (pure a).answers = {a} := rfl
@[simp] theorem pure_status (a : α) : (pure a).status = .finished := rfl
@[simp] theorem unknown_answers : (unknown : Outcome α).answers = 0 := rfl
@[simp] theorem unknown_status : (unknown : Outcome α).status = .cutOff := rfl

theorem choice_assoc (o₁ o₂ o₃ : Outcome α) : o₁ + o₂ + o₃ = o₁ + (o₂ + o₃) := add_assoc _ _ _
theorem choice_comm (o₁ o₂ : Outcome α) : o₁ + o₂ = o₂ + o₁ := add_comm _ _
theorem refuted_add (o : Outcome α) : refuted + o = o := zero_add o
theorem add_refuted (o : Outcome α) : o + refuted = o := add_zero o

/-- A choice is finished exactly when every alternative is. -/
theorem sum_status_eq_finished_iff (m : Multiset (Outcome α)) :
    m.sum.status = .finished ↔ ∀ o ∈ m, o.status = .finished := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp [Status.add_eq_finished_iff, ih]

theorem sum_answers (m : Multiset (Outcome α)) : m.sum.answers = (m.map answers).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp [ih]

theorem list_sum_answers (l : List (Outcome α)) : l.sum.answers = (l.map answers).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem list_sum_status_eq_finished_iff (l : List (Outcome α)) :
    l.sum.status = .finished ↔ ∀ o ∈ l, o.status = .finished := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Status.add_eq_finished_iff, ih]

/-- The answers of an outcome joined by choice with a cut-off one are cut off. -/
theorem add_unknown_status (o : Outcome α) : (o + unknown).status = .cutOff := by simp

/-- **Choice is not idempotent**: answers keep their multiplicity. -/
theorem choice_not_idempotent (a : α) : pure a + pure a ≠ pure a := by
  intro same
  have := congrArg (fun o : Outcome α => Multiset.card o.answers) same
  simp at this

/-- **`unknown` is not a unit of choice**: a cut-off alternative cannot be dropped. -/
theorem unknown_not_unit (a : α) : pure a + unknown ≠ pure a := by
  intro same
  have := congrArg Outcome.status same
  simp at this

/-! ## Answers in a list: what order breaks -/

/-- On lists, choice (append) is not commutative. -/
theorem list_choice_not_comm : ([0] ++ [1] : List ℕ) ≠ [1] ++ [0] := by decide

/-- On lists, bind (`flatMap`) does not distribute over choice on the left; the two sides are the
same multiset in two orders. -/
theorem list_bind_not_left_distrib :
    ([1, 2] : List ℕ).flatMap (fun a => [a] ++ [10 * a]) ≠
      ([1, 2] : List ℕ).flatMap (fun a => [a]) ++ ([1, 2] : List ℕ).flatMap (fun a => [10 * a]) := by
  decide

/-! ## Sequencing -/

/-- **Sequencing**: every answer is continued; the result is finished when the first search and
every continuation of its answers finished. -/
def bind (o : Outcome α) (f : α → Outcome β) : Outcome β :=
  ⟨o.answers.bind fun a => (f a).answers, o.status + (o.answers.map fun a => (f a).status).sum⟩

/-- Transport of answers. -/
def map (f : α → β) (o : Outcome α) : Outcome β := ⟨o.answers.map f, o.status⟩

@[simp] theorem bind_answers (o : Outcome α) (f : α → Outcome β) :
    (o.bind f).answers = o.answers.bind fun a => (f a).answers := rfl
@[simp] theorem map_answers (f : α → β) (o : Outcome α) : (o.map f).answers = o.answers.map f := rfl
@[simp] theorem map_status (f : α → β) (o : Outcome α) : (o.map f).status = o.status := rfl

theorem bind_status_eq_finished_iff (o : Outcome α) (f : α → Outcome β) :
    (o.bind f).status = .finished ↔
      o.status = .finished ∧ ∀ a ∈ o.answers, (f a).status = .finished := by
  simp only [bind, Status.add_eq_finished_iff, Status.sum_eq_finished_iff, Multiset.mem_map]
  constructor
  · rintro ⟨first, rest⟩
    exact ⟨first, fun a member => rest _ ⟨a, member, rfl⟩⟩
  · rintro ⟨first, rest⟩
    refine ⟨first, ?_⟩
    rintro _ ⟨a, member, rfl⟩
    exact rest a member

theorem pure_bind (a : α) (f : α → Outcome β) : (pure a).bind f = f a := by
  ext1 <;> simp [bind]

theorem bind_pure (o : Outcome α) : o.bind pure = o := by
  ext1
  · exact (Multiset.bind_singleton (s := o.answers) id).trans (Multiset.map_id _)
  · simp only [bind, pure_status]
    rw [Status.sum_map_finished, Status.add_finished]

theorem bind_assoc (o : Outcome α) (f : α → Outcome β) (g : β → Outcome γ) :
    (o.bind f).bind g = o.bind fun a => (f a).bind g := by
  ext1
  · simp [bind, Multiset.bind_assoc]
  · simp only [bind, Multiset.map_bind, Multiset.sum_bind, Multiset.sum_map_add, add_assoc]

/-- Choice, then a continuation: each alternative is continued. -/
theorem add_bind (o o' : Outcome α) (f : α → Outcome β) :
    (o + o').bind f = o.bind f + o'.bind f := by
  ext1
  · simp [bind, Multiset.add_bind]
  · simp only [bind, add_answers, add_status, Multiset.map_add, Multiset.sum_add]
    rw [add_add_add_comm]

/-- A choice of continuations: the continued searches are a choice. -/
theorem bind_add (o : Outcome α) (f g : α → Outcome β) :
    o.bind (fun a => f a + g a) = o.bind f + o.bind g := by
  ext1
  · simp [bind, Multiset.bind_add]
  · simp only [bind, add_status, Multiset.sum_map_add, add_answers]
    rw [add_add_add_comm o.status, Status.add_self]

/-- **Refuted is a left zero**: nothing to continue, nothing left to explore. -/
theorem zero_bind (f : α → Outcome β) : (0 : Outcome α).bind f = 0 := by
  ext1 <;> simp [bind]

/-- **Unknown is left absorbing**: continuing an unknown outcome stays unknown. -/
theorem unknown_bind (f : α → Outcome β) : (unknown : Outcome α).bind f = unknown := by
  ext1 <;> simp [bind]

/-- Continuing by a failing continuation keeps only the status of the first search. -/
theorem bind_refuted (o : Outcome α) : o.bind (fun _ => (0 : Outcome β)) = ⟨0, o.status⟩ := by
  ext1
  · simp [bind]
  · simp only [bind, zero_status]
    rw [Status.sum_map_finished, Status.add_finished]

/-- **Refuted is not a right zero**: a cut-off search whose found answers all fail downstream is
cut off, not refuted. -/
theorem cutOff_bind_refuted_ne_refuted (a : α) :
    (⟨{a}, .cutOff⟩ : Outcome α).bind (fun _ => (0 : Outcome β)) ≠ refuted := by
  rw [bind_refuted]
  intro same
  have := congrArg Outcome.status same
  simp [refuted] at this

theorem map_add (f : α → β) (o o' : Outcome α) : (o + o').map f = o.map f + o'.map f := by
  ext1 <;> simp [map]

theorem map_list_sum (f : α → β) (l : List (Outcome α)) :
    l.sum.map f = (l.map (map f)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [map_add, ih]

theorem map_pure (f : α → β) (a : α) : (pure a).map f = pure (f a) := by
  ext1 <;> simp [map]

theorem map_unknown (f : α → β) : (unknown : Outcome α).map f = unknown := by
  ext1 <;> simp [map]

theorem map_eq_bind (f : α → β) (o : Outcome α) : o.map f = o.bind (fun a => pure (f a)) := by
  ext1
  · simp [map, bind, Multiset.bind_singleton]
  · simp only [map, bind, pure_status]
    rw [Status.sum_map_finished, Status.add_finished]

/-! ## Collect -/

/-- **Collect**: the answers of a finished outcome become one answer; a cut-off outcome has no
collection yet. -/
def collect : Outcome α → Outcome (Multiset α)
  | ⟨answers, .finished⟩ => pure answers
  | ⟨_, .cutOff⟩ => unknown

@[simp] theorem collect_finished (answers : Multiset α) :
    collect ⟨answers, .finished⟩ = pure answers := rfl

@[simp] theorem collect_cutOff (answers : Multiset α) :
    collect ⟨answers, .cutOff⟩ = unknown := rfl

theorem collect_status (o : Outcome α) : (collect o).status = o.status := by
  obtain ⟨_, _ | _⟩ := o <;> rfl

/-- **Collect over a choice with a cut-off alternative is unknown.** -/
theorem collect_add_cutOff (o o' : Outcome α) (cut : o'.status = .cutOff) :
    collect (o + o') = unknown := by
  obtain ⟨A, s⟩ := o
  obtain ⟨B, t⟩ := o'
  simp only at cut
  subst cut
  change collect ⟨A + B, s + .cutOff⟩ = unknown
  rw [Status.add_cutOff]
  rfl

/-- Collect is not additive: a finished choice collects to one answer, not two. -/
theorem collect_not_additive (a : α) :
    collect (pure a + pure a) ≠ collect (pure a) + collect (pure a) := by
  intro same
  have := congrArg (fun o : Outcome (Multiset α) => Multiset.card o.answers) same
  change Multiset.card (collect ⟨{a} + {a}, .finished⟩).answers =
    Multiset.card (collect ⟨{a}, .finished⟩ + collect ⟨{a}, .finished⟩).answers at this
  simp at this

/-! ## The information order -/

/-- **The information order**: `o'` is `o`, or `o` was cut off and `o'` has at least its
answers. -/
instance : PartialOrder (Outcome α) where
  le o o' := o = o' ∨ (o.status = .cutOff ∧ o.answers ≤ o'.answers)
  le_refl _ := .inl rfl
  le_trans a b c := by
    rintro (rfl | ⟨cut, small⟩) (rfl | ⟨cut', small'⟩)
    · exact .inl rfl
    · exact .inr ⟨cut', small'⟩
    · exact .inr ⟨cut, small⟩
    · exact .inr ⟨cut, small.trans small'⟩
  le_antisymm a b := by
    rintro (same | ⟨cut, small⟩) (same' | ⟨cut', small'⟩)
    · exact same
    · exact same
    · exact same'.symm
    · exact Outcome.ext (le_antisymm small small') (cut.trans cut'.symm)

theorem le_def {o o' : Outcome α} :
    o ≤ o' ↔ o = o' ∨ (o.status = .cutOff ∧ o.answers ≤ o'.answers) := Iff.rfl

theorem answers_le_of_le {o o' : Outcome α} (h : o ≤ o') : o.answers ≤ o'.answers := by
  rcases h with rfl | ⟨_, small⟩
  · exact le_rfl
  · exact small

/-- **`unknown` is the bottom**: it may become any outcome. -/
instance : OrderBot (Outcome α) where
  bot := unknown
  bot_le _ := .inr ⟨rfl, Multiset.zero_le _⟩

theorem bot_eq_unknown : (⊥ : Outcome α) = unknown := rfl

/-- **Finished outcomes are maximal**: more budget changes nothing. -/
theorem eq_of_finished_le {o o' : Outcome α} (finished : o.status = .finished) (h : o ≤ o') :
    o' = o := by
  rcases h with rfl | ⟨cut, _⟩
  · rfl
  · rw [finished] at cut
    exact Status.noConfusion cut

theorem le_iff_eq_of_finished {o o' : Outcome α} (finished : o.status = .finished) :
    o ≤ o' ↔ o' = o :=
  ⟨eq_of_finished_le finished, fun same => same ▸ le_rfl⟩

/-- **Incomplete is never none, in the order**: `unknown` lies below every outcome, `refuted` below
none but itself. -/
theorem refuted_le_iff (o : Outcome α) : refuted ≤ o ↔ o = refuted :=
  le_iff_eq_of_finished rfl

theorem unknown_ne_refuted : (unknown : Outcome α) ≠ refuted := by
  intro same
  have := congrArg Outcome.status same
  simp [refuted] at this

/-- **Choice is monotone.** -/
theorem add_le_add' {o₁ o₁' o₂ o₂' : Outcome α} (h₁ : o₁ ≤ o₁') (h₂ : o₂ ≤ o₂') :
    o₁ + o₂ ≤ o₁' + o₂' := by
  rcases h₁ with rfl | ⟨cut₁, small₁⟩
  · rcases h₂ with rfl | ⟨cut₂, small₂⟩
    · exact le_rfl
    · exact .inr ⟨by simp [cut₂], add_le_add le_rfl small₂⟩
  · exact .inr ⟨by simp [cut₁], add_le_add small₁ (answers_le_of_le h₂)⟩

/-- A choice over a list is monotone in each alternative. -/
theorem list_sum_le_list_sum {ι : Type w} (l : List ι) {f g : ι → Outcome α}
    (h : ∀ i ∈ l, f i ≤ g i) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add' (h a (by simp)) (ih fun i member => h i (by simp [member]))

theorem bind_le_bind_of_le {F G : α → Multiset β} (A : Multiset α) (h : ∀ a, F a ≤ G a) :
    A.bind F ≤ A.bind G := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih => simpa [Multiset.cons_bind] using add_le_add (h a) ih

theorem bind_le_bind_left {o o' : Outcome α} (h : o ≤ o') (f : α → Outcome β) :
    o.bind f ≤ o'.bind f := by
  rcases h with rfl | ⟨cut, small⟩
  · exact le_rfl
  · refine .inr ⟨by simp [bind, cut], ?_⟩
    obtain ⟨extra, same⟩ := Multiset.le_iff_exists_add.mp small
    simp only [bind_answers, same, Multiset.add_bind]
    exact Multiset.le_add_right _ _

theorem bind_le_bind_right (o : Outcome α) {f g : α → Outcome β} (h : ∀ a, f a ≤ g a) :
    o.bind f ≤ o.bind g := by
  by_cases same : ∀ a ∈ o.answers, f a = g a
  · have : o.bind f = o.bind g := by
      ext1
      · exact Multiset.bind_congr fun a member => by rw [same a member]
      · simp only [bind]
        rw [Multiset.map_congr rfl fun a member => by rw [same a member]]
    exact this ▸ le_rfl
  · push Not at same
    obtain ⟨a, member, differ⟩ := same
    have cut : (f a).status = .cutOff := by
      rcases h a with equal | ⟨cut, _⟩
      · exact absurd equal differ
      · exact cut
    refine .inr ⟨?_, ?_⟩
    · apply Status.eq_cutOff_of_ne_finished
      intro finished
      have := ((bind_status_eq_finished_iff o f).mp finished).2 a member
      rw [cut] at this
      exact Status.noConfusion this
    · simp only [bind_answers]
      exact bind_le_bind_of_le o.answers fun b => answers_le_of_le (h b)

/-- **Bind is monotone** in both arguments. -/
theorem bind_mono {o o' : Outcome α} {f g : α → Outcome β} (h : o ≤ o') (h' : ∀ a, f a ≤ g a) :
    o.bind f ≤ o'.bind g :=
  (bind_le_bind_left h f).trans (bind_le_bind_right o' h')

theorem map_mono (f : α → β) {o o' : Outcome α} (h : o ≤ o') : o.map f ≤ o'.map f := by
  rcases h with rfl | ⟨cut, small⟩
  · exact le_rfl
  · exact .inr ⟨cut, Multiset.map_le_map small⟩

/-- **Collect is monotone.** -/
theorem collect_mono : Monotone (collect : Outcome α → Outcome (Multiset α)) := by
  intro o o' h
  obtain ⟨A, _ | _⟩ := o
  · rw [eq_of_finished_le rfl h]
  · exact bot_le

/-- **Collect is forced**: on an inhabited type it is the only monotone map that collects finished
outcomes. -/
theorem collect_unique [Nonempty α] (c : Outcome α → Outcome (Multiset α)) (monotone : Monotone c)
    (onFinished : ∀ A : Multiset α, c ⟨A, .finished⟩ = pure A) : c = collect := by
  obtain ⟨a⟩ := ‹Nonempty α›
  funext o
  obtain ⟨A, _ | _⟩ := o
  · exact onFinished A
  · have below : ∀ B : Multiset α, c ⟨A, .cutOff⟩ ≤ pure (A + B) := fun B => by
      rw [← onFinished]
      exact monotone (.inr ⟨rfl, Multiset.le_add_right A B⟩)
    have differ : (A : Multiset α) ≠ A + {a} := by
      intro same
      have := congrArg Multiset.card same
      simp at this
    rcases below 0 with same | ⟨cut, small⟩
    · rcases below {a} with same' | ⟨cut', _⟩
      · rw [add_zero] at same
        have := congrArg Outcome.answers (same.symm.trans same')
        simp only [pure_answers, Multiset.singleton_inj] at this
        exact absurd this differ
      · rw [same] at cut'
        exact Status.noConfusion cut'
    · rcases below {a} with same' | ⟨_, small'⟩
      · rw [same'] at cut
        exact Status.noConfusion cut
      · rw [add_zero, pure_answers, Multiset.le_singleton] at small
        rw [pure_answers, Multiset.le_singleton] at small'
        apply Outcome.ext _ cut
        rcases small with empty | whole
        · exact empty
        · rcases small' with empty' | whole'
          · exact empty'
          · rw [whole] at whole'
            exact absurd (Multiset.singleton_inj.mp whole') differ

/-- Gathering the partial answers as if they were the collection. -/
def partialCollect (o : Outcome α) : Outcome (Multiset α) := ⟨{o.answers}, o.status⟩

/-- **Partial collection is not monotone**: an empty cut-off outcome would collect to the empty
collection, which more budget contradicts. -/
theorem partialCollect_not_monotone (a : α) :
    ¬ Monotone (partialCollect : Outcome α → Outcome (Multiset α)) := by
  intro monotone
  have h := monotone (bot_le : (⊥ : Outcome α) ≤ pure a)
  rcases h with same | ⟨_, small⟩
  · have := congrArg Outcome.status same
    simp [partialCollect, bot_eq_unknown] at this
  · simp [partialCollect, bot_eq_unknown] at small

/-! ## Readouts -/

/-- The three outcomes of a search for a certificate. -/
inductive Verdict where
  /-- a certificate was found -/
  | commit
  /-- the search finished without one -/
  | refuted
  /-- the search was cut off without one -/
  | suspended
  deriving DecidableEq, Repr

/-- **The existence readout.** -/
def verdict (o : Outcome α) : Verdict :=
  if Multiset.card o.answers = 0 then
    match o.status with
    | .finished => .refuted
    | .cutOff => .suspended
  else .commit

theorem verdict_eq_commit_iff (o : Outcome α) : o.verdict = .commit ↔ o.answers ≠ 0 := by
  obtain ⟨A, s⟩ := o
  by_cases h : A = 0
  · subst h
    cases s <;> simp [verdict]
  · have card : Multiset.card A ≠ 0 := fun c => h (Multiset.card_eq_zero.mp c)
    simp [verdict, card, h]

theorem verdict_eq_refuted_iff (o : Outcome α) : o.verdict = .refuted ↔ o = refuted := by
  obtain ⟨A, s⟩ := o
  by_cases h : A = 0
  · subst h
    cases s <;> simp [verdict, refuted, Outcome.ext_iff]
  · have card : Multiset.card A ≠ 0 := fun c => h (Multiset.card_eq_zero.mp c)
    simp [verdict, card, h, refuted, Outcome.ext_iff]

theorem verdict_eq_suspended_iff (o : Outcome α) : o.verdict = .suspended ↔ o = unknown := by
  obtain ⟨A, s⟩ := o
  by_cases h : A = 0
  · subst h
    cases s <;> simp [verdict, unknown, Outcome.ext_iff]
  · have card : Multiset.card A ≠ 0 := fun c => h (Multiset.card_eq_zero.mp c)
    simp [verdict, card, h, unknown, Outcome.ext_iff]

/-- **Incomplete is never none**: a cut-off outcome never reads refuted. -/
theorem verdict_ne_refuted_of_cutOff {o : Outcome α} (cut : o.status = .cutOff) :
    o.verdict ≠ .refuted := by
  rw [Ne, verdict_eq_refuted_iff]
  intro same
  rw [same] at cut
  exact Status.noConfusion cut

/-- A finished outcome never reads suspended. -/
theorem verdict_ne_suspended_of_finished {o : Outcome α} (finished : o.status = .finished) :
    o.verdict ≠ .suspended := by
  rw [Ne, verdict_eq_suspended_iff]
  intro same
  rw [same] at finished
  exact Status.noConfusion finished

/-- **Definite readouts are stable**: more budget never changes a commit or a refutation. -/
theorem verdict_eq_of_le {o o' : Outcome α} (h : o ≤ o') (definite : o.verdict ≠ .suspended) :
    o'.verdict = o.verdict := by
  rcases h with rfl | ⟨cut, small⟩
  · rfl
  · have found : o.verdict = .commit := by
      cases hv : o.verdict
      · rfl
      · exact absurd hv (verdict_ne_refuted_of_cutOff cut)
      · exact absurd hv definite
    rw [found, verdict_eq_commit_iff]
    rw [verdict_eq_commit_iff] at found
    intro empty
    exact found (Multiset.le_zero.mp (empty ▸ small))

/-- **The collection readout**: commit exactly when finished, suspended exactly when cut off. -/
theorem collect_verdict (o : Outcome α) :
    (collect o).verdict = match o.status with
      | .finished => .commit
      | .cutOff => .suspended := by
  obtain ⟨A, _ | _⟩ := o <;> rfl

theorem collect_verdict_ne_refuted (o : Outcome α) : (collect o).verdict ≠ .refuted := by
  rw [collect_verdict]
  cases o.status <;> simp

end Outcome

#print axioms Status.sum_eq_finished_iff
#print axioms Outcome.choice_not_idempotent
#print axioms Outcome.unknown_not_unit
#print axioms Outcome.list_choice_not_comm
#print axioms Outcome.list_bind_not_left_distrib
#print axioms Outcome.pure_bind
#print axioms Outcome.bind_pure
#print axioms Outcome.bind_assoc
#print axioms Outcome.add_bind
#print axioms Outcome.bind_add
#print axioms Outcome.zero_bind
#print axioms Outcome.unknown_bind
#print axioms Outcome.bind_refuted
#print axioms Outcome.cutOff_bind_refuted_ne_refuted
#print axioms Outcome.collect_add_cutOff
#print axioms Outcome.collect_not_additive
#print axioms Outcome.eq_of_finished_le
#print axioms Outcome.refuted_le_iff
#print axioms Outcome.unknown_ne_refuted
#print axioms Outcome.add_le_add'
#print axioms Outcome.bind_mono
#print axioms Outcome.collect_mono
#print axioms Outcome.collect_unique
#print axioms Outcome.partialCollect_not_monotone
#print axioms Outcome.verdict_eq_commit_iff
#print axioms Outcome.verdict_eq_refuted_iff
#print axioms Outcome.verdict_eq_suspended_iff
#print axioms Outcome.verdict_ne_refuted_of_cutOff
#print axioms Outcome.verdict_eq_of_le
#print axioms Outcome.collect_verdict_ne_refuted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search
