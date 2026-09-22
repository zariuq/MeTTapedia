import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Basic

/-!
# Separation: the constructor-free combinators cannot reach a fresh subject

The constructor-free combinators produce no name absent from the redex
(`noNameCreation`).  This file turns that into an observational separation.

## The observer class, stated explicitly

`MessageAt c` holds of a term when that term offers a message whose subject is
name-equivalent to `c`.  The observers of interest are the contexts that fire
exactly when such a message becomes available at a chosen subject: place the
term in parallel with a consumer at `c` and watch whether the consumer ever
runs.  In the source note's argument the consumer is a duplicator at the
subject being tested, and the label it would emit is what a separating
bisimulation must match.

Freshness is taken **up to name equivalence** (`PresentUpTo`), not up to
syntactic equality, because subjects are matched up to congruence.  Taking it
up to equality would give a weaker statement wearing the same name.

## The engine

`no_messageAt_of_absent` is the content: if a subject is absent from a term up
to name equivalence, then *no* reduct of that term ever offers a message
there, so an observer keyed on activity at that subject can never fire.  This
is what separates the constructor-free combinators from reflective rho, where
substituting under a quotation manufactures a subject present in neither
participant.

`names_finite` records that the names of a term form a finite set, which is
what licenses choosing a subject absent from a given term.

## The separation itself

`selfPairWitness` is a concrete term of the full calculus which, given a
message at its input subject carrying `v`, makes the assembled subject
`⌜v ∣ v⌝` **active**: it duplicates the received name, assembles the
self-parallel composition with a constructor, and binds the assembled name
into subject position.  `selfPairWitness_reaches` exhibits that derivation in
three steps.

`separation` puts the two halves together.  The constructors reach activity at
an assembled subject; no constructor-free term whose names omit that subject
ever does.  One observer, keyed on activity at the assembled subject,
distinguishes them.

This is the content of the source note's separation result without routing
through the translation: what separates the calculi is not the particular
source term but the ability to bring a *constructed* subject into play.

## References

- L. G. Meredith and M. Radestock, *A reflective higher-order calculus*,
  ENTCS 141(5):49–67, 2005.
- S. Lybech, *Encodability and separation for a reflective higher-order
  calculus*, EXPRESS/SOS 2022, EPTCS 368, 95–112.
- F1R3FLY.io research note, *Name-Free Combinators for the Rho Calculus*,
  draft 3, 2026.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-- Reachability in the constructor-free calculus. -/
inductive Reaches : Comb → Comb → Prop where
  | refl (p : Comb) : Reaches p p
  | tail {p q r : Comb} : Reaches p q → StepMinus Cong q r → Reaches p r
  | congruent {p q : Comb} : Cong p q → Reaches p q
  | trans {p q r : Comb} : Reaches p q → Reaches q r → Reaches p r

/-- Names do not grow along reachability. -/
theorem names_reaches {p q : Comb} (h : Reaches p q) : names q ⊆ names p := by
  induction h with
  | refl => exact subset_rfl
  | tail _ step ih => exact (noNameCreation step).trans ih
  | congruent hc => exact (cong_names hc).symm.subset
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁

/-- A name is present up to name equivalence when some name of the term is
congruent to it.  Subjects are matched up to congruence, so this is the form
freshness must take. -/
def PresentUpTo (c : Comb) (t : Comb) : Prop :=
  ∃ c', Cong c c' ∧ c' ∈ names t

theorem presentUpTo_of_subset {c p q : Comb} (sub : names q ⊆ names p)
    (h : PresentUpTo c q) : PresentUpTo c p := by
  obtain ⟨c', hc, hmem⟩ := h
  exact ⟨c', hc, sub hmem⟩

/-- The observer class: a context fires only when a message becomes available
at its chosen subject, up to name equivalence. -/
inductive MessageAt (c : Comb) : Comb → Prop where
  | here {c' : Comb} (v : Comb) : Cong c c' → MessageAt c (mm c' v)
  | parLeft {p : Comb} (q : Comb) : MessageAt c p → MessageAt c (par p q)
  | parRight (p : Comb) {q : Comb} : MessageAt c q → MessageAt c (par p q)

/-- A message at a subject witnesses that subject's presence. -/
theorem presentUpTo_of_messageAt {c t : Comb} (h : MessageAt c t) :
    PresentUpTo c t := by
  induction h with
  | here v hc => exact ⟨_, hc, by simp [names]⟩
  | parLeft q _ ih =>
      obtain ⟨c', hc, hmem⟩ := ih
      exact ⟨c', hc, by simp [names]; exact Or.inl hmem⟩
  | parRight p _ ih =>
      obtain ⟨c', hc, hmem⟩ := ih
      exact ⟨c', hc, by simp [names]; exact Or.inr hmem⟩

/-- **The blindness engine.**  If a subject is absent from a term, up to name
equivalence, then no reduct of that term ever offers a message there.  An
observer keyed on activity at such a subject can never fire. -/
theorem no_messageAt_of_absent {c t t' : Comb}
    (absent : ¬ PresentUpTo c t) (reach : Reaches t t') :
    ¬ MessageAt c t' := by
  intro h
  exact absent (presentUpTo_of_subset (names_reaches reach)
    (presentUpTo_of_messageAt h))

/-- Names of a term form a finite set, which is what licenses choosing a
subject absent from it. -/
theorem names_finite (t : Comb) : (names t).Finite := by
  induction t <;> simp only [names] <;>
    repeat' first
      | exact Set.finite_empty
      | assumption
      | apply Set.Finite.union
      | apply Set.finite_insert
      | exact Set.finite_singleton _

/-! ## Activity, the witness, and the separation -/

/-- A subject is active in a term when some atom of the term is listening or
speaking at a subject name-equivalent to it. -/
inductive ActiveAt (c : Comb) : Comb → Prop where
  | msg {c' : Comb} (v : Comb) : Cong c c' → ActiveAt c (mm c' v)
  | dup {c' : Comb} (b e : Comb) : Cong c c' → ActiveAt c (dd c' b e)
  | discard {c' : Comb} : Cong c c' → ActiveAt c (kk c')
  | fwd {c' : Comb} (b : Comb) : Cong c c' → ActiveAt c (fw c' b)
  | bindIn {c' : Comb} (b : Comb) : Cong c c' → ActiveAt c (bl c' b)
  | bindOut {c' : Comb} (b : Comb) : Cong c c' → ActiveAt c (br c' b)
  | syn {c' : Comb} (b e : Comb) : Cong c c' → ActiveAt c (sy c' b e)
  | opening {c' : Comb} : Cong c c' → ActiveAt c (ev c')
  | store {c' : Comb} (p : Comb) : Cong c c' → ActiveAt c (qq c' p)
  | parLeft {p : Comb} (q : Comb) : ActiveAt c p → ActiveAt c (par p q)
  | parRight (p : Comb) {q : Comb} : ActiveAt c q → ActiveAt c (par p q)

/-- Activity at a subject witnesses that subject's presence. -/
theorem presentUpTo_of_activeAt {c t : Comb} (h : ActiveAt c t) :
    PresentUpTo c t := by
  induction h with
  | msg v hc => exact ⟨_, hc, by simp [names]⟩
  | dup b e hc => exact ⟨_, hc, by simp [names]⟩
  | discard hc => exact ⟨_, hc, by simp [names]⟩
  | fwd b hc => exact ⟨_, hc, by simp [names]⟩
  | bindIn b hc => exact ⟨_, hc, by simp [names]⟩
  | bindOut b hc => exact ⟨_, hc, by simp [names]⟩
  | syn b e hc => exact ⟨_, hc, by simp [names]⟩
  | opening hc => exact ⟨_, hc, by simp [names]⟩
  | store p hc => exact ⟨_, hc, by simp [names]⟩
  | parLeft q _ ih =>
      obtain ⟨c', hc, hmem⟩ := ih
      exact ⟨c', hc, by simp [names]; exact Or.inl hmem⟩
  | parRight p _ ih =>
      obtain ⟨c', hc, hmem⟩ := ih
      exact ⟨c', hc, by simp [names]; exact Or.inr hmem⟩

/-- **No constructor-free term makes an absent subject active.** -/
theorem no_activeAt_of_absent {c t t' : Comb}
    (absent : ¬ PresentUpTo c t) (reach : Reaches t t') : ¬ ActiveAt c t' := by
  intro h
  exact absent (presentUpTo_of_subset (names_reaches reach)
    (presentUpTo_of_activeAt h))

/-! ## Reachability in the full calculus -/

inductive ReachesFull : Comb → Comb → Prop where
  | refl (p : Comb) : ReachesFull p p
  | tail {p q r : Comb} : ReachesFull p q → Step Cong q r → ReachesFull p r
  | congruent {p q : Comb} : Cong p q → ReachesFull p q
  | trans {p q r : Comb} : ReachesFull p q → ReachesFull q r → ReachesFull p r

theorem ReachesFull.single {p q : Comb} (h : Step Cong p q) : ReachesFull p q :=
  ReachesFull.tail (ReachesFull.refl p) h

/-- Constructor-free reduction is in particular full reduction. -/
theorem ReachesFull.ofReaches {p q : Comb} (h : Reaches p q) : ReachesFull p q := by
  induction h with
  | refl => exact ReachesFull.refl _
  | tail _ step ih => exact ReachesFull.tail ih (Step.ofMinus step)
  | congruent hc => exact ReachesFull.congruent hc
  | trans _ _ ih₁ ih₂ => exact ReachesFull.trans ih₁ ih₂

/-- Full reduction under the left of a parallel composition. -/
theorem ReachesFull.parLeft {p p' : Comb} (r : Comb) (h : ReachesFull p p') :
    ReachesFull (par p r) (par p' r) := by
  induction h with
  | refl => exact ReachesFull.refl _
  | tail _ step ih => exact ReachesFull.tail ih (Step.parLeft _ step)
  | congruent hc => exact ReachesFull.congruent (Cong.parLeft _ hc)
  | trans _ _ ih₁ ih₂ => exact ReachesFull.trans ih₁ ih₂

/-! ## The witness -/

/-- Rotation of a three-way parallel composition. -/
theorem par_rotate (x y z : Comb) : Cong (par (par x y) z) (par (par x z) y) :=
  Cong.trans (Cong.parAssoc x y z)
    (Cong.trans (Cong.parRight x (Cong.parComm y z))
      (Cong.symm (Cong.parAssoc x z y)))

/-- The witness: duplicate the received name, assemble its self-parallel
composition with a constructor, and bind the assembled name into subject
position so that it becomes active. -/
def selfPairWitness (a b₁ b₂ c d : Comb) : Comb :=
  par (par (dd a b₁ b₂) (consPar b₁ b₂ c)) (bl c d)

/-- **The constructors reach the assembled subject.**  Given a message at `a`
carrying `v`, the witness makes the assembled name `⌜v ∣ v⌝` active. -/
theorem selfPairWitness_reaches {a b₁ b₂ c d v : Comb} :
    ∃ t, ReachesFull (par (selfPairWitness a b₁ b₂ c d) (mm a v)) t
      ∧ ActiveAt (par v v) t := by
  refine ⟨fw (par v v) d, ?_, ActiveAt.fwd d (Cong.refl _)⟩
  have first :
      Step Cong (par (selfPairWitness a b₁ b₂ c d) (mm a v))
        (par (par (par (mm b₁ v) (mm b₂ v)) (consPar b₁ b₂ c)) (bl c d)) := by
    refine Step.congruent
      (p' := par (par (par (dd a b₁ b₂) (mm a v)) (consPar b₁ b₂ c)) (bl c d))
      (q' := par (par (par (mm b₁ v) (mm b₂ v)) (consPar b₁ b₂ c)) (bl c d))
      ?_ ?_ (Cong.refl _)
    · exact Cong.trans (par_rotate (par (dd a b₁ b₂) (consPar b₁ b₂ c)) (bl c d) (mm a v))
        (Cong.parLeft _ (par_rotate (dd a b₁ b₂) (consPar b₁ b₂ c) (mm a v)))
    · exact Step.parLeft _ (Step.parLeft _
        (Step.ofMinus (StepMinus.duplicate b₁ b₂ v (Cong.refl a))))
  have second :
      Step Cong (par (par (par (mm b₁ v) (mm b₂ v)) (consPar b₁ b₂ c)) (bl c d))
        (par (mm c (par v v)) (bl c d)) := by
    refine Step.congruent
      (p' := par (par (consPar b₁ b₂ c) (par (mm b₁ v) (mm b₂ v))) (bl c d))
      (q' := par (mm c (par v v)) (bl c d))
      ?_ ?_ (Cong.refl _)
    · exact Cong.parLeft _ (Cong.parComm _ _)
    · exact Step.parLeft _ (Step.buildPar c v v (Cong.refl b₁) (Cong.refl b₂))
  have third :
      Step Cong (par (mm c (par v v)) (bl c d)) (fw (par v v) d) := by
    refine Step.congruent
      (p' := par (bl c d) (mm c (par v v)))
      (q' := fw (par v v) d)
      (Cong.parComm _ _) ?_ (Cong.refl _)
    exact Step.ofMinus (StepMinus.bindIn d (par v v) (Cong.refl c))
  exact ReachesFull.tail (ReachesFull.tail (ReachesFull.single first) second) third

/-- **Separation.**  The constructors make an assembled subject active; no
constructor-free term whose names omit that subject ever does.  So the two
calculi are distinguished by an observer keyed on activity at the assembled
subject. -/
theorem separation {a b₁ b₂ c d v : Comb} (T : Comb)
    (absent : ¬ PresentUpTo (par v v) T) :
    (∃ t, ReachesFull (par (selfPairWitness a b₁ b₂ c d) (mm a v)) t
        ∧ ActiveAt (par v v) t)
      ∧ (∀ t', Reaches T t' → ¬ ActiveAt (par v v) t') :=
  ⟨selfPairWitness_reaches, fun _ reach => no_activeAt_of_absent absent reach⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.names_reaches
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.presentUpTo_of_messageAt
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.no_messageAt_of_absent
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.names_finite
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.presentUpTo_of_activeAt
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.no_activeAt_of_absent
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.selfPairWitness_reaches
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.separation
