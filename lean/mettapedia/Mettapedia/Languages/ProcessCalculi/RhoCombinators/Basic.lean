import Mathlib

/-!
# Name-free combinators for the rho calculus

The rho calculus has no name restriction: names are quoted processes, and
freshness comes from quotation.  It nonetheless has one binder, the input
prefix.  Eliminating that binder in favour of combinators should therefore
give a concurrency calculus with no bound names at all.  This file formalizes
the resulting calculus and the two facts that govern it.

Every name is a quotation, so a name position carries the process that is
quoted: `mm a b` denotes the message `mm(⌜a⌝, ⌜b⌝)`.  This is not an
abbreviation but the actual grammar — there is no separate sort of names.

## The defect

The published combinators inherited, from a presentation in which quote and
drop are mutually inverse, an identification of the opening of a quotation
with the quoted process.  In the combinator setting the opening is a *guard*
on a communication rule, not a process former, and since every name is a
quotation the identification makes an arbitrary running process match that
guard.  In the representation used here the inherited clause reads `ev q ≃ q`,
and `defect` shows the consequence: for all `p` and `q`,

    q ∣ mm(⌜q⌝, ⌜p⌝)  ⟶  p

so any process beside a message addressed to its own quotation is consumed and
replaced by that message's payload.  `DefectCong` carries the clause and
`Cong` does not; the repair is to work with the latter, leaving the decoding
to substitution.

This is retained as a negative control.  Any presentation or generated
equation theory in this development that reintroduces the clause makes
`defect` available, and `defect` is therefore the test such a theory must
fail.

## What reflection needs

`noNameCreation` proves that a step of the constructor-free calculus produces
no name absent from the redex, hereditarily.  The rho calculus has no such
property: substituting under a quotation turns `⌜(drop y) ∣ R⌝` into
`⌜Q ∣ R⌝`, a name in neither participant.  That difference is the expressive
content of substitution under a quotation.

The four name constructors supply exactly the missing operation.  Each
assembles the quotation of one node from the quotations of its children and
delivers the result as an ordinary message, so chains of them build a name of
any shape.  `constructor_creates_name` shows the no-name-creation lemma is
sharp: it fails as soon as one constructor is available, and the name produced
is in neither participant.

Taken together the two results are a characterisation rather than an
obstruction: the constructor-free combinators can quote code but cannot
compute names, and the constructors are precisely that one operation.

## Scope

Structural congruence here is the monoid laws for parallel composition closed
under parallel composition and equivalence.  There is no clause for alpha
equivalence, there being no binders.  The results below use no more of the
congruence than that, so they are insensitive to extending it to the remaining
term formers; `defect` in particular is proved with the smaller relation and
so holds for any extension of it.

Subjects are matched up to the supplied congruence, which for this calculus is
name equivalence: two names are equivalent exactly when the processes they
quote are congruent.

Reduction is nondeterministic by design.  Two consumers may compete for one
message and two producers may offer at one consumer; both are the familiar
sides of the race a communication rule has always had.

## References

- L. G. Meredith and M. Radestock, *A reflective higher-order calculus*,
  ENTCS 141(5):49–67, 2005.
- N. Yoshida, *Minimality and separation results on asynchronous mobile
  processes*, TCS 274(1–2):231–276, 2002.
- F1R3FLY.io research note, *Name-Free Combinators for the Rho Calculus*,
  draft 3, 2026, whose findings this file mechanizes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

/-- Combinator processes.  Every name is a quotation, so a name position
carries the process that is quoted: `mm a b` denotes `mm(⌜a⌝, ⌜b⌝)`. -/
inductive Comb where
  | nil : Comb
  | par : Comb → Comb → Comb
  | mm : Comb → Comb → Comb
  | dd : Comb → Comb → Comb → Comb
  | kk : Comb → Comb
  | fw : Comb → Comb → Comb
  | bl : Comb → Comb → Comb
  | br : Comb → Comb → Comb
  | sy : Comb → Comb → Comb → Comb
  | ev : Comb → Comb
  | qq : Comb → Comb → Comb
  | consPar : Comb → Comb → Comb → Comb
  | consMsg : Comb → Comb → Comb → Comb
  | consDup : Comb → Comb → Comb → Comb → Comb
  | consSyn : Comb → Comb → Comb → Comb → Comb
  deriving Repr, DecidableEq

open Comb

/-- Structural congruence: the monoid laws for parallel composition, closed
under parallel composition and under equivalence.  There is no clause for
alpha equivalence, there being no binders, and no clause identifying the
opening of a quotation with the quoted process. -/
inductive Cong : Comb → Comb → Prop where
  | refl (p : Comb) : Cong p p
  | symm {p q : Comb} : Cong p q → Cong q p
  | trans {p q r : Comb} : Cong p q → Cong q r → Cong p r
  | parNil (p : Comb) : Cong (par p nil) p
  | parComm (p q : Comb) : Cong (par p q) (par q p)
  | parAssoc (p q r : Comb) : Cong (par (par p q) r) (par p (par q r))
  | parLeft {p p' : Comb} (q : Comb) : Cong p p' → Cong (par p q) (par p' q)
  | parRight (p : Comb) {q q' : Comb} : Cong q q' → Cong (par p q) (par p q')

/-- The defective congruence: structural congruence together with the
inherited identification of the opening of a quotation with the quoted
process.  In this presentation the opening is a guard, not a former, so the
clause reads `ev q ≃ q`. -/
inductive DefectCong : Comb → Comb → Prop where
  | ofCong {p q : Comb} : Cong p q → DefectCong p q
  | dropQuote (q : Comb) : DefectCong (ev q) q
  | symm {p q : Comb} : DefectCong p q → DefectCong q p
  | trans {p q r : Comb} : DefectCong p q → DefectCong q r → DefectCong p r
  | parLeft {p p' : Comb} (q : Comb) :
      DefectCong p p' → DefectCong (par p q) (par p' q)
  | parRight (p : Comb) {q q' : Comb} :
      DefectCong q q' → DefectCong (par p q) (par p q')

/-- Reduction of the constructor-free calculus, with subjects matched up to a
supplied congruence. -/
inductive StepMinus (C : Comb → Comb → Prop) : Comb → Comb → Prop where
  | duplicate {a a' : Comb} (b c v : Comb) :
      C a a' → StepMinus C (par (dd a b c) (mm a' v)) (par (mm b v) (mm c v))
  | discard {a a' : Comb} (v : Comb) :
      C a a' → StepMinus C (par (kk a) (mm a' v)) nil
  | forward {a a' : Comb} (b v : Comb) :
      C a a' → StepMinus C (par (fw a b) (mm a' v)) (mm b v)
  | bindOut {a a' : Comb} (b v : Comb) :
      C a a' → StepMinus C (par (br a b) (mm a' v)) (fw b v)
  | bindIn {a a' : Comb} (b v : Comb) :
      C a a' → StepMinus C (par (bl a b) (mm a' v)) (fw v b)
  | synchronise {a a' : Comb} (b c v : Comb) :
      C a a' → StepMinus C (par (sy a b c) (mm a' v)) (fw b c)
  | opening {a a' : Comb} (p : Comb) :
      C a a' → StepMinus C (par (ev a) (mm a' p)) p
  | release {a a' : Comb} (b p : Comb) :
      C a a' → StepMinus C (par (fw a b) (qq a' p)) (mm b p)
  | parLeft {p p' : Comb} (r : Comb) :
      StepMinus C p p' → StepMinus C (par p r) (par p' r)
  | congruent {p p' q' q : Comb} :
      C p p' → StepMinus C p' q' → C q' q → StepMinus C p q

/-! ## The defect -/

/-- **The defect.**  With the inherited identification in force, every process
sitting beside a message addressed to its own quotation is consumed and
replaced by that message's payload.  The guard matches an arbitrary running
process. -/
theorem defect (p q : Comb) : StepMinus DefectCong (par q (mm q p)) p :=
  StepMinus.congruent
    (DefectCong.parLeft _ (DefectCong.symm (DefectCong.dropQuote q)))
    (StepMinus.opening p (DefectCong.ofCong (Cong.refl q)))
    (DefectCong.ofCong (Cong.refl p))


open Comb

/-! ## Names -/

/-- The names occurring in a term, hereditarily.  A name position contributes
the name it carries together with the names inside it.  The storage combinator
contributes the quotation of what it stores, which is the name a forwarder
releases. -/
def names : Comb → Set Comb
  | nil => ∅
  | par p q => names p ∪ names q
  | mm a b => {a, b} ∪ names a ∪ names b
  | dd a b c => {a, b, c} ∪ names a ∪ names b ∪ names c
  | kk a => {a} ∪ names a
  | fw a b => {a, b} ∪ names a ∪ names b
  | bl a b => {a, b} ∪ names a ∪ names b
  | br a b => {a, b} ∪ names a ∪ names b
  | sy a b c => {a, b, c} ∪ names a ∪ names b ∪ names c
  | ev a => {a} ∪ names a
  | qq a p => {a, p} ∪ names a ∪ names p
  | consPar a b c => {a, b, c} ∪ names a ∪ names b ∪ names c
  | consMsg a b c => {a, b, c} ∪ names a ∪ names b ∪ names c
  | consDup a b c e => {a, b, c, e} ∪ names a ∪ names b ∪ names c ∪ names e
  | consSyn a b c e => {a, b, c, e} ∪ names a ∪ names b ∪ names c ∪ names e

/-- Structural congruence neither creates nor destroys names. -/
theorem cong_names {p q : Comb} (h : Cong p q) : names p = names q := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | parNil p => simp [names]
  | parComm p q => simp [names, Set.union_comm]
  | parAssoc p q r => simp [names, Set.union_assoc]
  | parLeft q _ ih => simp [names, ih]
  | parRight p _ ih => simp [names, ih]

/-- **No name creation.**  A step of the constructor-free calculus produces no
name that was not already present in the redex, hereditarily. -/
theorem noNameCreation {p q : Comb} (h : StepMinus Cong p q) :
    names q ⊆ names p := by
  induction h with
  | duplicate b c v _ => intro x hx; simp [names] at hx ⊢; tauto
  | discard v _ => intro x hx; simp [names] at hx
  | forward b v _ => intro x hx; simp [names] at hx ⊢; tauto
  | bindOut b v _ => intro x hx; simp [names] at hx ⊢; tauto
  | bindIn b v _ => intro x hx; simp [names] at hx ⊢; tauto
  | synchronise b c v _ => intro x hx; simp [names] at hx ⊢; tauto
  | opening p _ => intro x hx; simp [names] at hx ⊢; tauto
  | release b p _ => intro x hx; simp [names] at hx ⊢; tauto
  | parLeft r _ ih => intro x hx; simp [names] at hx ⊢; tauto
  | congruent hc₁ _ hc₂ ih =>
      rw [cong_names hc₁, ← cong_names hc₂]
      exact ih


open Comb

/-- Reduction of the full calculus: the constructor-free rules together with
the four name constructors.  Each constructor assembles the quotation of one
node from the quotations of its children and delivers it as a message. -/
inductive Step (C : Comb → Comb → Prop) : Comb → Comb → Prop where
  | ofMinus {p q : Comb} : StepMinus C p q → Step C p q
  | buildPar {a a' b b' : Comb} (c p q : Comb) : C a a' → C b b' →
      Step C (par (consPar a b c) (par (mm a' p) (mm b' q))) (mm c (par p q))
  | buildMsg {a a' b b' : Comb} (c u v : Comb) : C a a' → C b b' →
      Step C (par (consMsg a b c) (par (mm a' u) (mm b' v))) (mm c (mm u v))
  | buildDup {a a' b b' c c' : Comb} (e p q r : Comb) :
      C a a' → C b b' → C c c' →
      Step C (par (consDup a b c e) (par (mm a' p) (par (mm b' q) (mm c' r))))
        (mm e (dd p q r))
  | buildSyn {a a' b b' c c' : Comb} (e p q r : Comb) :
      C a a' → C b b' → C c c' →
      Step C (par (consSyn a b c e) (par (mm a' p) (par (mm b' q) (mm c' r))))
        (mm e (sy p q r))
  | parLeft {p p' : Comb} (r : Comb) : Step C p p' → Step C (par p r) (par p' r)
  | congruent {p p' q' q : Comb} :
      C p p' → Step C p' q' → C q' q → Step C p q

/-- **The constructors are exactly the missing power.**  A constructor step
produces a name that is in neither participant: the quotation of the assembled
node.  So the no-name-creation lemma is sharp — it fails as soon as a
constructor is available. -/
theorem constructor_creates_name :
    ∃ p q : Comb, Step Cong p q ∧ ¬ names q ⊆ names p := by
  refine ⟨par (consPar nil (kk nil) nil) (par (mm nil nil) (mm (kk nil) (kk nil))),
    mm nil (par nil (kk nil)), ?_, ?_⟩
  · exact Step.buildPar nil nil (kk nil) (Cong.refl nil) (Cong.refl (kk nil))
  · intro below
    have mem : par nil (kk nil) ∈ names (mm nil (par nil (kk nil))) := by
      simp [names]
    have bad := below mem
    simp [names] at bad

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.defect
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.cong_names
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.noNameCreation
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.constructor_creates_name
