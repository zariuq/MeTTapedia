import Mathlib.Data.Multiset.Bind

/-!
# Observational quotients: when a program cannot tell equated values apart

A **machine** is a nondeterministic program over values `T`: operations
`step i`, each sending a value to the bag of its results, and observers
`observe o` (`Machine`). A **context** is a word of operations; running it
sends a value to a bag of values (`Machine.run`), and each observer reads
that bag as a bag of observations (`Machine.answers`). Two values are
**contextually equivalent** when every context and observer gives them one
bag of observations (`Machine.Equiv`). Bags, not lists: the order in which a
nondeterministic program produces its answers is not observed.

Storing a value as a quotient by an equivalence `E` means storing a
canonical representative of its class (`Normalizer`).

* **Exactness.** Storing representatives is sound for every context exactly
  when `E` is contained in contextual equivalence (`store_sound_iff`). Then
  the runtime may also normalize every intermediate result
  (`runNf_answers`).
* **The proof method.** A relation is *compatible* when related values step
  to bags that are related elementwise under a bijection (`Compatible`), and
  *refines* observation when related values are observed alike (`Refines`).
  Any compatible relation that refines observation is contained in
  contextual equivalence (`Compatible.le_equiv`), so finding one that contains
  `E` proves storage sound (`store_sound_of_compatible`). This is the
  checker's certificate: a relation, closed under the program's own
  operations, that no observer can see through.
* **Refutation.** A single observer that separates two equated values is a
  context that separates them (`not_store_sound_of_observer`).
* **Deterministic programs.** When every operation has exactly one result,
  contextual equivalence is itself compatible (`equiv_compatible`), so the
  method is complete: storage is sound exactly when some compatible relation
  refining observation contains `E` (`store_sound_iff_compatible`).
* **Nondeterministic programs.** There the method is sound but not complete:
  two values can have equal bags of observations for every context while no
  compatible relation relates them
  (`Controls.equivalent_without_compatible_relation`). Each step's results
  must be paired one by one, and the pairing that serves one continuation can
  differ from the pairing that serves another.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.ObservationalQuotient

universe u v w x

/-- A nondeterministic program: operations indexed by `ι` sending a value to
the bag of its results, and observers indexed by `ω`. -/
structure Machine (ι : Type u) (ω : Type v) (T : Type w) (O : Type x) where
  step : ι → T → Multiset T
  observe : ω → T → O

namespace Machine

variable {ι : Type u} {ω : Type v} {T : Type w} {O : Type x} (M : Machine ι ω T O)

/-- Run a context, a word of operations applied in order. -/
def run (M : Machine ι ω T O) : List ι → T → Multiset T
  | [], a => {a}
  | i :: w, a => (M.step i a).bind (run M w)

@[simp] theorem run_nil (a : T) : M.run [] a = {a} := rfl

@[simp] theorem run_cons (i : ι) (w : List ι) (a : T) :
    M.run (i :: w) a = (M.step i a).bind (M.run w) := rfl

/-- The bag of observations of a context. -/
def answers (w : List ι) (o : ω) (a : T) : Multiset O := (M.run w a).map (M.observe o)

theorem answers_cons (i : ι) (w : List ι) (o : ω) (a : T) :
    M.answers (i :: w) o a = (M.step i a).bind (M.answers w o) := by
  simp only [answers, run_cons, Multiset.map_bind]
  rfl

/-- **Contextual equivalence.** -/
def Equiv (a b : T) : Prop := ∀ w o, M.answers w o a = M.answers w o b

theorem equiv_equivalence : Equivalence M.Equiv where
  refl _ _ _ := rfl
  symm h w o := (h w o).symm
  trans h₁ h₂ w o := (h₁ w o).trans (h₂ w o)

/-- Related values step to bags related elementwise, under a bijection. -/
def Compatible (R : T → T → Prop) : Prop :=
  ∀ i a b, R a b → Multiset.Rel R (M.step i a) (M.step i b)

/-- Related values are observed alike. -/
def Refines (R : T → T → Prop) : Prop := ∀ o a b, R a b → M.observe o a = M.observe o b

theorem rel_run {R : T → T → Prop} (compatible : M.Compatible R) (w : List ι) :
    ∀ {a b : T}, R a b → Multiset.Rel R (M.run w a) (M.run w b) := by
  induction w with
  | nil => intro a b h; simpa using Multiset.Rel.cons h Multiset.Rel.zero
  | cons i w ih =>
      intro a b h
      rw [run_cons, run_cons]
      exact Multiset.rel_bind (fun _ _ h' => ih h') (compatible i a b h)

/-- Bags related by a relation that refines an observer are observed alike. -/
theorem map_eq_of_rel {R : T → T → Prop} {f : T → O} (refines : ∀ a b, R a b → f a = f b)
    {s t : Multiset T} (h : Multiset.Rel R s t) : s.map f = t.map f :=
  Multiset.rel_eq.mp (Multiset.rel_map.mpr (h.mono fun a _ b _ hab => refines a b hab))

/-- **A compatible relation that refines observation is contained in
contextual equivalence.** -/
theorem Compatible.le_equiv {R : T → T → Prop} (compatible : M.Compatible R)
    (refines : M.Refines R) {a b : T} (h : R a b) : M.Equiv a b := fun w o =>
  map_eq_of_rel (refines o) (M.rel_run compatible w h)

/-- Contextual equivalence refines every observer: the empty context. -/
theorem equiv_refines : M.Refines M.Equiv := fun o a b h => by
  simpa [answers] using h [] o

/-- After one operation, contextually equivalent values give one bag of
observations for every continuation. -/
theorem Equiv.step {a b : T} (h : M.Equiv a b) (i : ι) (w : List ι) (o : ω) :
    (M.step i a).bind (M.answers w o) = (M.step i b).bind (M.answers w o) := by
  rw [← answers_cons, ← answers_cons]
  exact h (i :: w) o

/-! ## Storing representatives -/

/-- A canonical representative for each class of `E`. -/
structure Normalizer (E : T → T → Prop) where
  nf : T → T
  rel_nf : ∀ a, E a (nf a)
  nf_eq : ∀ a b, E a b → nf a = nf b

/-- **Storing representatives is sound exactly when `E` is contained in
contextual equivalence.** -/
theorem store_sound_iff {E : T → T → Prop} (N : Normalizer E) :
    (∀ w o a, M.answers w o (N.nf a) = M.answers w o a) ↔ ∀ a b, E a b → M.Equiv a b := by
  constructor
  · intro sound a b h w o
    rw [← sound w o a, ← sound w o b, N.nf_eq a b h]
  · intro contained w o a
    exact (contained a (N.nf a) (N.rel_nf a) w o).symm

/-- Running a context while normalizing every intermediate result. -/
def runNf (M : Machine ι ω T O) (nf : T → T) : List ι → T → Multiset T
  | [], a => {nf a}
  | i :: w, a => (M.step i (nf a)).bind (runNf M nf w)

/-- **Normalizing every intermediate result** is sound once `E` is contained
in contextual equivalence. -/
theorem runNf_answers {E : T → T → Prop} (N : Normalizer E)
    (contained : ∀ a b, E a b → M.Equiv a b) (w : List ι) (o : ω) :
    ∀ a : T, (M.runNf N.nf w a).map (M.observe o) = M.answers w o a := by
  induction w with
  | nil =>
      intro a
      have same := M.equiv_refines o _ _ (contained a (N.nf a) (N.rel_nf a))
      simp [runNf, answers, same]
  | cons i w ih =>
      intro a
      have step : (M.runNf N.nf (i :: w) a).map (M.observe o) =
          (M.step i (N.nf a)).bind (M.answers w o) := by
        simp only [runNf, Multiset.map_bind, ih]
      rw [step, ← answers_cons]
      exact (contained a (N.nf a) (N.rel_nf a) (i :: w) o).symm

/-- **The checker's certificate.** A compatible relation that refines
observation and contains `E` makes storing representatives sound. -/
theorem store_sound_of_compatible {E R : T → T → Prop} (N : Normalizer E)
    (contains : ∀ a b, E a b → R a b) (compatible : M.Compatible R) (refines : M.Refines R)
    (w : List ι) (o : ω) (a : T) : M.answers w o (N.nf a) = M.answers w o a :=
  (M.store_sound_iff N).mpr (fun a b h => compatible.le_equiv M refines (contains a b h)) w o a

/-- **Refutation.** An observer that separates two equated values refutes
storing representatives. -/
theorem not_store_sound_of_observer {E : T → T → Prop} (N : Normalizer E) {a b : T}
    (equated : E a b) (o : ω) (separated : M.observe o a ≠ M.observe o b) :
    ¬ ∀ w o a, M.answers w o (N.nf a) = M.answers w o a := by
  intro sound
  exact separated (M.equiv_refines o a b ((M.store_sound_iff N).mp sound a b equated))

/-! ## Deterministic programs -/

/-- Every operation has exactly one result. -/
def Deterministic : Prop := ∀ i a, ∃ b, M.step i a = {b}

/-- For a deterministic program, contextual equivalence is compatible. -/
theorem equiv_compatible (deterministic : M.Deterministic) : M.Compatible M.Equiv := by
  intro i a b h
  obtain ⟨a', ha⟩ := deterministic i a
  obtain ⟨b', hb⟩ := deterministic i b
  rw [ha, hb]
  refine Multiset.Rel.cons ?_ Multiset.Rel.zero
  intro w o
  have := h.step M i w o
  rwa [ha, hb, Multiset.singleton_bind, Multiset.singleton_bind] at this

/-- **For deterministic programs the method is complete.** -/
theorem store_sound_iff_compatible (deterministic : M.Deterministic) {E : T → T → Prop}
    (N : Normalizer E) :
    (∀ w o a, M.answers w o (N.nf a) = M.answers w o a) ↔
      ∃ R : T → T → Prop, (∀ a b, E a b → R a b) ∧ M.Compatible R ∧ M.Refines R := by
  rw [M.store_sound_iff N]
  constructor
  · intro contained
    exact ⟨M.Equiv, contained, M.equiv_compatible deterministic, M.equiv_refines⟩
  · rintro ⟨R, contains, compatible, refines⟩ a b h
    exact compatible.le_equiv M refines (contains a b h)

end Machine

/-! ## Controls -/

namespace Controls

open Machine

/-- States of a machine with two equivalent starts `p` and `q`. -/
inductive State
  | p | q | p₁ | p₂ | q₁ | q₂ | x | y
  deriving DecidableEq

/-- Three operations: `s` branches, `t` and `u` probe a branch. -/
inductive Op
  | s | t | u
  deriving DecidableEq

open State Op

/-- `p` branches to `p₁`, which answers both probes, and `p₂`, which answers
neither; `q` branches to `q₁` and `q₂`, which answer one probe each. -/
def machine : Machine Op Unit State Unit where
  step
    | s, p => {p₁, p₂}
    | s, q => {q₁, q₂}
    | t, p₁ => {x}
    | u, p₁ => {y}
    | t, q₁ => {x}
    | u, q₂ => {y}
    | _, _ => 0
  observe _ _ := ()

/-- After two operations every run from `p` or `q` is over. -/
theorem run_long (a : State) (start : a = p ∨ a = q) (i j k : Op) (w : List Op) :
    machine.run (i :: j :: k :: w) a = 0 := by
  rcases start with rfl | rfl <;> cases i <;> cases j <;> cases k <;>
    simp [Machine.run, machine, Multiset.insert_eq_cons]

/-- **Equal bags of observations for every context.** -/
theorem p_equiv_q : machine.Equiv p q := by
  intro w o
  cases o
  match w with
  | [] => rfl
  | [i] => cases i <;> simp [Machine.answers, Machine.run, machine, Multiset.insert_eq_cons]
  | [i, j] =>
      cases i <;> cases j <;> simp [Machine.answers, Machine.run, machine, Multiset.insert_eq_cons]
  | i :: j :: k :: w =>
      simp only [Machine.answers, run_long p (.inl rfl), run_long q (.inr rfl)]

/-- **No compatible relation relates them.** Pairing `p₁` with `q₁` fails
on the probe `u`, pairing it with `q₂` fails on `t`. -/
theorem equivalent_without_compatible_relation :
    machine.Equiv p q ∧
      ∀ R : State → State → Prop, machine.Compatible R → ¬ R p q := by
  refine ⟨p_equiv_q, fun R compatible related => ?_⟩
  have branches := compatible s p q related
  change Multiset.Rel R {p₁, p₂} {q₁, q₂} at branches
  have first : R p₁ q₁ ∨ R p₁ q₂ := by
    rw [Multiset.insert_eq_cons, Multiset.rel_cons_left] at branches
    obtain ⟨b, bs, hb, -, hbs⟩ := branches
    have : b ∈ ({q₁, q₂} : Multiset State) := by rw [hbs]; exact Multiset.mem_cons_self b bs
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at this
    rcases this with rfl | rfl
    · exact .inl hb
    · exact .inr hb
  rcases first with h | h
  · have := Multiset.card_eq_card_of_rel (compatible u p₁ q₁ h)
    exact absurd this (by decide)
  · have := Multiset.card_eq_card_of_rel (compatible t p₁ q₂ h)
    exact absurd this (by decide)

end Controls

end Mettapedia.Algebra.Collections.ObservationalQuotient
