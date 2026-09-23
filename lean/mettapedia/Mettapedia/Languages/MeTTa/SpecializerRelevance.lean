import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic

/-!
# Relevance of a relation to higher-order specialization

A relation is relevant to specialization when some chain of forwards through
equation-backed callees ends at a dynamic-head application.  Reading an
equation reports a direct dynamic-head application, a body that could not be
read, or the callees the body forwards to.  A body that could not be read may
or may not hold such an application, so the program only bounds relevance:
`Certain` from below, `Possible` from above.

The specializer reads a relation's equations in order and stops at the first
direct application or unreadable body.  It records what it saw before
stopping, and the forwards it met until then, which may be only a prefix of
the relation's forwards.  It explores the relations reachable from a source
and marks two properties by propagation along recorded forwards: `certain`,
seeded by the direct applications it saw, and `possible`, seeded also by the
unreadable bodies it saw.  A relation classified before is not read again; its
stored classification, `certain` or `irrelevant`, stands in for everything
below it.  The propagation repeats until a sweep changes nothing.

* `stable_marking_iff`: a marking in which every mark is justified by a seed
  or a marked recorded forward, and which a further sweep would not change,
  is exactly the least fixed point `Marked`.
* `marked_iff_reaches`: that least fixed point is reachability of a seed along
  recorded forwards.
* `explored_possible_iff`: on explored relations the `possible` marking is
  exactly `Possible`, whichever source the exploration started from.
* `explored_certain_sound`: a relation marked certain is `Certain`.
* `next_store_sound`: classifications computed from sound stored ones are
  sound, so the store stays sound.
* `hidden_not_marked_certain`: the `certain` marking is not complete; a direct
  application behind an unreadable body goes unseen.

The soundness theorems assume only what reading guarantees: what it saw and
recorded is true of the program, it sees a direct application or an unreadable
body whenever the relation has one, and a relation read to the end had all its
forwards recorded.
-/

namespace Mettapedia.Languages.MeTTa.SpecializerRelevance

universe u

variable {Rel : Type u}

/-! ## The program's relevance -/

/-- What reading all of each relation's equations would report. -/
structure Program (Rel : Type u) where
  direct : Rel → Prop
  unreadable : Rel → Prop
  forwards : Rel → List Rel

/-- `r` reaches `s` along forwards. -/
def Program.Reaches (program : Program Rel) : Rel → Rel → Prop :=
  Relation.ReflTransGen fun a b => b ∈ program.forwards a

/-- Relevant for certain: a chain of forwards ends at a direct application. -/
def Program.Certain (program : Program Rel) (r : Rel) : Prop :=
  ∃ s, program.Reaches r s ∧ program.direct s

/-- Possibly relevant: a chain ends at a direct application or at a body that
could not be read. -/
def Program.Possible (program : Program Rel) (r : Rel) : Prop :=
  ∃ s, program.Reaches r s ∧ (program.direct s ∨ program.unreadable s)

theorem Program.certain_possible {program : Program Rel} {r : Rel}
    (certain : program.Certain r) : program.Possible r := by
  obtain ⟨s, reach, direct⟩ := certain
  exact ⟨s, reach, Or.inl direct⟩

/-! ## Propagation over recorded forwards -/

/-- The least fixed point of `marked n ↔ seed n ∨ ∃ t ∈ edges n, marked t`. -/
inductive Marked (seed : Rel → Prop) (edges : Rel → List Rel) : Rel → Prop
  | seed {n : Rel} : seed n → Marked seed edges n
  | forward {n t : Rel} : t ∈ edges n → Marked seed edges t →
      Marked seed edges n

theorem marked_iff_reaches (seed : Rel → Prop) (edges : Rel → List Rel)
    (n : Rel) :
    Marked seed edges n ↔
      ∃ s, Relation.ReflTransGen (fun a b => b ∈ edges a) n s ∧ seed s := by
  constructor
  · intro marked
    induction marked with
    | seed hs => exact ⟨_, Relation.ReflTransGen.refl, hs⟩
    | forward edge _ ih =>
        obtain ⟨s, reach, hs⟩ := ih
        exact ⟨s, Relation.ReflTransGen.head edge reach, hs⟩
  · rintro ⟨s, reach, hs⟩
    induction reach using Relation.ReflTransGen.head_induction_on with
    | refl => exact .seed hs
    | head edge _ ih => exact .forward edge ih

/-- A marking a further sweep would not change: seeds are marked, and a
relation with a marked recorded forward is marked. -/
def Stable (seed : Rel → Prop) (edges : Rel → List Rel)
    (marking : Rel → Prop) : Prop :=
  (∀ n, seed n → marking n) ∧
    ∀ n t, t ∈ edges n → marking t → marking n

/-- Every mark is justified by a seed or by a marked recorded forward. -/
def Justified (seed : Rel → Prop) (edges : Rel → List Rel)
    (marking : Rel → Prop) : Prop :=
  ∀ n, marking n → Marked seed edges n

theorem marked_of_stable {seed : Rel → Prop} {edges : Rel → List Rel}
    {marking : Rel → Prop} (stable : Stable seed edges marking)
    {n : Rel} (marked : Marked seed edges n) : marking n := by
  induction marked with
  | seed hs => exact stable.1 _ hs
  | forward edge _ ih => exact stable.2 _ _ edge ih

/-- The propagation stops at the least fixed point: a justified marking that
a further sweep would not change is exactly `Marked`. -/
theorem stable_marking_iff {seed : Rel → Prop} {edges : Rel → List Rel}
    {marking : Rel → Prop} (justified : Justified seed edges marking)
    (stable : Stable seed edges marking) (n : Rel) :
    marking n ↔ Marked seed edges n :=
  ⟨justified n, marked_of_stable stable⟩

/-! ## Soundness of the explored classification -/

/-- Stored classifications true of the program: `certain` only for certainly
relevant relations, `irrelevant` only for relations not possibly relevant. -/
structure SoundStore (program : Program Rel)
    (certain irrelevant : Rel → Prop) : Prop where
  certain_sound : ∀ n, certain n → program.Certain n
  irrelevant_sound : ∀ n, irrelevant n → ¬ program.Possible n

/-- The specializer's exploration of a program.  For each relation it read,
it records whether it saw a direct application or an unreadable body before
it stopped, and the recorded forwards it propagates along; a relation
explored but not read carries a stored classification. -/
structure Exploration (program : Program Rel) where
  explored : Rel → Prop
  read : Rel → Prop
  sawDirect : Rel → Prop
  sawUnreadable : Rel → Prop
  edges : Rel → List Rel
  storedCertain : Rel → Prop
  storedIrrelevant : Rel → Prop
  read_explored : ∀ n, read n → explored n
  saw_direct_sound : ∀ n, read n → sawDirect n → program.direct n
  saw_unreadable_sound : ∀ n, read n → sawUnreadable n →
    program.unreadable n
  saw_complete : ∀ n, read n → program.direct n ∨ program.unreadable n →
    sawDirect n ∨ sawUnreadable n
  edges_sound : ∀ n, read n → ∀ t ∈ edges n, t ∈ program.forwards n
  edges_complete : ∀ n, read n → ¬ sawDirect n → ¬ sawUnreadable n →
    ∀ t ∈ program.forwards n, t ∈ edges n
  edges_unread : ∀ n, ¬ read n → edges n = []
  edges_explored : ∀ n, read n → ∀ t ∈ edges n, explored t
  unread_stored : ∀ n, explored n → ¬ read n →
    storedCertain n ∨ storedIrrelevant n
  store : SoundStore program storedCertain storedIrrelevant

variable {program : Program Rel}

/-- Seeds of the `certain` marking: direct applications seen here, and stored
`certain` classifications. -/
def Exploration.certainSeed (e : Exploration program) (n : Rel) : Prop :=
  (e.read n ∧ e.sawDirect n) ∨ (¬ e.read n ∧ e.storedCertain n)

/-- Seeds of the `possible` marking add the unreadable bodies seen here. -/
def Exploration.possibleSeed (e : Exploration program) (n : Rel) : Prop :=
  (e.read n ∧ (e.sawDirect n ∨ e.sawUnreadable n)) ∨
    (¬ e.read n ∧ e.storedCertain n)

/-- Every recorded forward is a forward of the program. -/
theorem Exploration.forward_of_edge (e : Exploration program) {n t : Rel}
    (edge : t ∈ e.edges n) : t ∈ program.forwards n := by
  by_cases hread : e.read n
  · exact e.edges_sound n hread t edge
  · rw [e.edges_unread n hread] at edge
    exact absurd edge List.not_mem_nil

/-- A relation marked certain has a chain of forwards to a direct
application. -/
theorem explored_certain_sound (e : Exploration program) (n : Rel)
    (marked : Marked e.certainSeed e.edges n) : program.Certain n := by
  induction marked with
  | seed hs =>
      rcases hs with ⟨hread, saw⟩ | ⟨_, stored⟩
      · exact ⟨_, Relation.ReflTransGen.refl,
          e.saw_direct_sound _ hread saw⟩
      · exact e.store.certain_sound _ stored
  | forward edge _ ih =>
      obtain ⟨s, reach, direct⟩ := ih
      exact ⟨s, Relation.ReflTransGen.head (e.forward_of_edge edge) reach,
        direct⟩

/-- A relation marked possible has a chain of forwards to a direct
application or an unreadable body. -/
theorem explored_possible_sound (e : Exploration program) (n : Rel)
    (marked : Marked e.possibleSeed e.edges n) : program.Possible n := by
  induction marked with
  | seed hs =>
      rcases hs with ⟨hread, saw | saw⟩ | ⟨_, stored⟩
      · exact ⟨_, Relation.ReflTransGen.refl,
          Or.inl (e.saw_direct_sound _ hread saw)⟩
      · exact ⟨_, Relation.ReflTransGen.refl,
          Or.inr (e.saw_unreadable_sound _ hread saw)⟩
      · exact Program.certain_possible (e.store.certain_sound _ stored)
  | forward edge _ ih =>
      obtain ⟨s, reach, target⟩ := ih
      exact ⟨s, Relation.ReflTransGen.head (e.forward_of_edge edge) reach,
        target⟩

/-- An explored relation with a chain to a direct application or an unreadable
body is marked possible. -/
theorem explored_possible_complete (e : Exploration program) (n : Rel)
    (explored : e.explored n) (possible : program.Possible n) :
    Marked e.possibleSeed e.edges n := by
  obtain ⟨s, reach, target⟩ := possible
  induction reach using Relation.ReflTransGen.head_induction_on with
  | refl =>
      by_cases hread : e.read s
      · exact .seed (Or.inl ⟨hread, e.saw_complete s hread target⟩)
      · rcases e.unread_stored s explored hread with stored | stored
        · exact .seed (Or.inr ⟨hread, stored⟩)
        · exact absurd ⟨s, Relation.ReflTransGen.refl, target⟩
            (e.store.irrelevant_sound s stored)
  | @head x y edge rest ih =>
      by_cases hread : e.read x
      · by_cases hseed : e.sawDirect x ∨ e.sawUnreadable x
        · exact .seed (Or.inl ⟨hread, hseed⟩)
        · rcases not_or.mp hseed with ⟨hdirect, hunread⟩
          have recorded :=
            e.edges_complete x hread hdirect hunread y edge
          exact .forward recorded
            (ih (e.edges_explored x hread y recorded))
      · rcases e.unread_stored x explored hread with stored | stored
        · exact .seed (Or.inr ⟨hread, stored⟩)
        · exact absurd ⟨s, Relation.ReflTransGen.head edge rest, target⟩
            (e.store.irrelevant_sound x stored)

/-- On explored relations the `possible` marking is exactly `Possible`, so
whether a relation is left irrelevant does not depend on the source the
exploration started from. -/
theorem explored_possible_iff (e : Exploration program) (n : Rel)
    (explored : e.explored n) :
    Marked e.possibleSeed e.edges n ↔ program.Possible n :=
  ⟨explored_possible_sound e n, explored_possible_complete e n explored⟩

/-- An explored relation left unmarked by `possible` has no chain to a direct
application or an unreadable body. -/
theorem explored_irrelevant_sound (e : Exploration program) (n : Rel)
    (explored : e.explored n)
    (unmarked : ¬ Marked e.possibleSeed e.edges n) :
    ¬ program.Possible n :=
  fun possible => unmarked (explored_possible_complete e n explored possible)

/-- After the exploration a relation read is stored `certain` when marked
certain; the earlier classifications are kept. -/
def Exploration.nextCertain (e : Exploration program) (n : Rel) : Prop :=
  e.storedCertain n ∨ (e.read n ∧ Marked e.certainSeed e.edges n)

/-- After the exploration a relation read is stored `irrelevant` when left
unmarked by `possible`; a relation marked possible but not certain is not
stored. -/
def Exploration.nextIrrelevant (e : Exploration program) (n : Rel) : Prop :=
  e.storedIrrelevant n ∨ (e.read n ∧ ¬ Marked e.possibleSeed e.edges n)

/-- Classifications computed from sound stored classifications are sound. -/
theorem Exploration.next_store_sound (e : Exploration program) :
    SoundStore program e.nextCertain e.nextIrrelevant where
  certain_sound n := by
    rintro (stored | ⟨_, marked⟩)
    · exact e.store.certain_sound n stored
    · exact explored_certain_sound e n marked
  irrelevant_sound n := by
    rintro (stored | ⟨hread, unmarked⟩)
    · exact e.store.irrelevant_sound n stored
    · exact explored_irrelevant_sound e n (e.read_explored n hread) unmarked

/-! ## Examples -/

section Examples

inductive Node | a | b | c | d | e
  deriving DecidableEq

/-- `a` forwards to `b` and `c`; `b` is direct; `c` forwards to `d`, whose body
could not be read; `e` forwards only to itself. -/
def example_program : Program Node where
  direct n := n = .b
  unreadable n := n = .d
  forwards
    | .a => [.b, .c]
    | .c => [.d]
    | .e => [.e]
    | _ => []

example : example_program.Certain .a :=
  ⟨.b, Relation.ReflTransGen.single (by decide), rfl⟩

/-- `c` reaches only an unreadable body: possibly relevant. -/
example : example_program.Possible .c :=
  ⟨.d, Relation.ReflTransGen.single (by decide), Or.inr rfl⟩

/-- From `c` only `c` and its unreadable callee `d` are reachable. -/
theorem reach_from_c {y : Node} (reach : example_program.Reaches .c y) :
    y = .c ∨ y = .d := by
  induction reach with
  | refl => exact Or.inl rfl
  | tail _ edge ih =>
      rcases ih with rfl | rfl
      · simp [example_program] at edge
        exact Or.inr edge
      · simp [example_program] at edge

/-- An unreadable body is never certified: `c` is not certainly relevant. -/
theorem c_not_certain : ¬ example_program.Certain .c := by
  rintro ⟨s, reach, direct⟩
  change s = .b at direct
  subst direct
  rcases reach_from_c reach with h | h <;> cases h

/-- From `e` only `e` is reachable. -/
theorem reach_from_e {y : Node} (reach : example_program.Reaches .e y) :
    y = .e := by
  induction reach with
  | refl => rfl
  | tail _ edge ih =>
      subst ih
      simpa [example_program] using edge

/-- `e` forwards only to itself: irrelevant. -/
theorem e_irrelevant : ¬ example_program.Possible .e := by
  rintro ⟨s, reach, target⟩
  have := reach_from_e reach
  subst this
  rcases target with h | h <;> cases h

/-- `a`'s first equation could not be read; its second forwards to the direct
relation `b`. -/
def hidden_program : Program Node where
  direct n := n = .b
  unreadable n := n = .a
  forwards
    | .a => [.b]
    | _ => []

/-- Exploring from `a`: reading stops at the unreadable first equation, before
the forward to `b` is recorded. -/
def hidden_exploration : Exploration hidden_program where
  explored n := n = .a
  read n := n = .a
  sawDirect _ := False
  sawUnreadable n := n = .a
  edges _ := []
  storedCertain _ := False
  storedIrrelevant _ := False
  read_explored _ hread := hread
  saw_direct_sound _ _ saw := saw.elim
  saw_unreadable_sound _ hread _ := hread
  saw_complete _ hread _ := Or.inr hread
  edges_sound _ _ _ edge := absurd edge List.not_mem_nil
  edges_complete _ hread _ unseen := (unseen hread).elim
  edges_unread _ _ := rfl
  edges_explored _ _ _ edge := absurd edge List.not_mem_nil
  unread_stored _ explored unread := (unread explored).elim
  store := ⟨fun _ stored => stored.elim, fun _ stored => stored.elim⟩

example : hidden_program.Certain .a :=
  ⟨.b, Relation.ReflTransGen.single (by decide), rfl⟩

/-- A direct application behind an unreadable body goes unseen: `a` is
certainly relevant but not marked certain, so nothing is stored for it. -/
theorem hidden_not_marked_certain :
    ¬ Marked hidden_exploration.certainSeed hidden_exploration.edges .a := by
  intro marked
  refine marked_of_stable (marking := fun _ => False) ⟨?_, ?_⟩ marked
  · rintro _ (⟨_, saw⟩ | ⟨_, stored⟩)
    · exact saw
    · exact stored
  · intro _ _ edge
    exact absurd edge List.not_mem_nil

/-- `a` is still marked possible, so it is not stored irrelevant either. -/
example : Marked hidden_exploration.possibleSeed hidden_exploration.edges .a :=
  .seed (Or.inl ⟨rfl, Or.inr rfl⟩)

end Examples

end Mettapedia.Languages.MeTTa.SpecializerRelevance
