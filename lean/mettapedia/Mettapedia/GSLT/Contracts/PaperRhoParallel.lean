import Mettapedia.GSLT.Contracts.PaperRho
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Parallel replacement for the literal-slot rho profile

The outer parallel monoid admits a multiset presentation. Its elements
are classes of *processes*, not classes of subject names. A communication
tests the latter explicitly. Keeping these two comparisons separate
allows a bag implementation without promoting a name equation to a
process equation.
This is the finer process observer of PaperRho. The forwarding
obstruction below is specific to that observer: the paper-facing
Congruence relates the two forwarded results.

The result is extensional: it describes every one-step successor.
The component classes below are quotients, not executable key codes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.PaperRho

abbrev ProcessClass := Quotient processEquations

def ofProcess (p : Process) : ProcessClass := Quotient.mk _ p

private def classAdd (p q : ProcessClass) : ProcessClass :=
  Quotient.liftOn₂ p q (fun a b => ofProcess (.par a b))
    (fun _ _ _ _ left right => Quotient.sound (.par left right))

instance : AddCommMonoid ProcessClass where
  zero := ofProcess .zero
  add := classAdd
  add_zero a := Quotient.inductionOn a fun p => Quotient.sound (.unit p)
  zero_add a := Quotient.inductionOn a fun p =>
    Quotient.sound (.trans (.swap .zero p) (.unit p))
  add_assoc a b c := Quotient.inductionOn₃ a b c fun p q r =>
    Quotient.sound (.assoc p q r)
  add_comm a b := Quotient.inductionOn₂ a b fun p q => Quotient.sound (.swap p q)
  nsmul n a := Nat.rec (ofProcess .zero) (fun _ b => classAdd b a) n
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

@[simp] theorem ofProcess_zero : ofProcess .zero = 0 := rfl

@[simp] theorem ofProcess_par (p q : Process) :
    ofProcess (.par p q) = ofProcess p + ofProcess q := rfl

/-- Flatten just the unguarded parallel layer; do not open quotes or
move anything out of a suspended continuation. -/
def components (p : Process) : Multiset ProcessClass :=
  match p with
  | .zero => 0
  | .par p q => components p + components q
  | .send .. | .receive .. | .drop .. => {ofProcess p}
termination_by structural p

theorem components_sum (p : Process) : (components p).sum = ofProcess p := by
  cases p with
  | zero => simp [components]
  | par p q => simp [components, components_sum p, components_sum q]
  | send _ _ | receive _ _ | drop _ => simp [components]
termination_by structural p

theorem ProcEq.components_eq {p q : Process} (eq : ProcEq p q) :
    components p = components q := by
  induction eq with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | unit _ => simp [components]
  | swap _ _ => simp [components, add_comm]
  | assoc _ _ _ => simp [components, add_assoc]
  | par _ _ first second => simp only [components, first, second]
  | send name inner _ =>
      simp only [components]
      exact congrArg (fun c : ProcessClass => ({c} : Multiset ProcessClass))
        (Quotient.sound (s := processEquations) (.send name inner))
  | receive name inner _ =>
      simp only [components]
      exact congrArg (fun c : ProcessClass => ({c} : Multiset ProcessClass))
        (Quotient.sound (s := processEquations) (.receive name inner))

theorem procEq_iff_components {p q : Process} : ProcEq p q ↔ components p = components q := by
  refine ⟨ProcEq.components_eq, fun h => Quotient.exact (s := processEquations) ?_⟩
  change ofProcess p = ofProcess q
  simpa only [components_sum] using congrArg Multiset.sum h

structure Communication where
  offered : Name
  waiting : Name
  payload : Process
  body : Process
  result : Process
  offeredScoped : ScopedName 0 offered
  waitingScoped : ScopedName 0 waiting
  payloadScoped : ScopedProcess 0 payload
  bodyScoped : ScopedProcess 1 body
  subjectsAgree : NameEq offered waiting
  substitution : Subst payload 0 body result

def Communication.source (r : Communication) : Process :=
  .par (.send r.offered r.payload) (.receive r.waiting r.body)

theorem Communication.fires (r : Communication) : Reduces r.source r.result :=
  .comm r.offeredScoped r.waitingScoped r.payloadScoped r.bodyScoped r.subjectsAgree r.substitution

/-- Bag extension retains the same frame on both sides. The redex is
two occurrences even if their classes also occur elsewhere in the bag. -/
def BagStep (before after : Multiset ProcessClass) : Prop :=
  ∃ (r : Communication) (frame : Multiset ProcessClass),
    before = components r.source + frame ∧ after = components r.result + frame

theorem Reduces.bagStep {p q : Process} (step : Reduces p q) :
    BagStep (components p) (components q) := by
  induction step with
  | comm ho hw hp hb eq subst =>
      exact ⟨⟨_, _, _, _, _, ho, hw, hp, hb, eq, subst⟩, 0,
        by simp [Communication.source], by simp⟩
  | par frame _ ih =>
      obtain ⟨r, kept, start, finish⟩ := ih
      exact ⟨r, kept + components frame,
        by simp only [components, start, add_assoc],
        by simp only [components, finish, add_assoc]⟩
  | equiv before _ after ih =>
      simpa only [before.components_eq, ← after.components_eq] using ih

theorem reduces_iff_bagStep (p q : Process) :
    Reduces p q ↔ BagStep (components p) (components q) := by
  refine ⟨Reduces.bagStep, ?_⟩
  rintro ⟨rule, frame, start, finish⟩
  obtain ⟨kept, sameFrame⟩ := Quotient.exists_rep frame.sum
  change ofProcess kept = frame.sum at sameFrame
  have beforeEq : ProcEq p (.par rule.source kept) := Quotient.exact (s := processEquations) (by
    change ofProcess p = ofProcess (.par rule.source kept)
    have sums := congrArg Multiset.sum start
    simpa only [Multiset.sum_add, components_sum, ofProcess_par, sameFrame] using sums)
  have afterEq : ProcEq (.par rule.result kept) q := Quotient.exact (s := processEquations) (by
    change ofProcess (.par rule.result kept) = ofProcess q
    have sums := congrArg Multiset.sum finish
    simpa only [Multiset.sum_add, components_sum, ofProcess_par, sameFrame] using sums.symm)
  exact .equiv beforeEq (.par kept rule.fires) afterEq

namespace ParallelControls

open Separation

/-- Two competing outputs retain different continuations in the bag,
even when the competing communications share their receiver. -/
theorem competing_successors :
    let input := Process.receive base (.drop (.bound 0))
    let out₁ := Process.send base .zero
    let out₂ := Process.send wrapped .zero
    let before := Process.par out₁ (.par out₂ input)
    BagStep (components before) (components out₁) ∧
      BagStep (components before) (components out₂) ∧
      components out₁ ≠ components out₂ := by
  dsimp only
  have baseScoped : ScopedName 0 base := .literal .zero
  have aliasScoped : ScopedName 0 wrapped := .literal (.drop baseScoped)
  have bodyScoped : ScopedProcess 1 (.drop (.bound 0)) := .drop (.bound (by decide))
  let first : Communication :=
    ⟨base, base, .zero, _, .zero, baseScoped, baseScoped, .zero, bodyScoped, .refl _, .drop_hit (.refl _)⟩
  let second : Communication :=
    ⟨wrapped, base, .zero, _, .zero, aliasScoped, baseScoped, .zero, bodyScoped,
      alias_separation.1, .drop_hit (.refl _)⟩
  refine ⟨⟨second, components (.send base .zero), ?_, ?_⟩,
    ⟨first, components (.send wrapped .zero), ?_, ?_⟩, ?_⟩
  · simp only [Communication.source, second, components]; ac_rfl
  · simp [second, components]
  · simp only [Communication.source, first, components]; ac_rfl
  · simp [first, components]
  · exact fun same => alias_separation.2.1 (.symm ((procEq_iff_components).mpr same))

private def payload : Process := .drop base
private def insertion : Process := .par payload .zero
private def forwards : Process := .send (.bound 0) .zero
private def forwarded (p : Process) : Process := .send (.quote p) .zero
private def withOffer (p : Process) : Process :=
  .par (.send base p) (.receive base forwards)

private theorem payloadScoped : ScopedProcess 0 payload := .drop (.literal .zero)
private theorem insertionScoped : ScopedProcess 0 insertion := .par payloadScoped .zero

private theorem forwardsSubstitutes (p : Process) : Subst p 0 forwards (forwarded p) :=
  .send (.hit (.refl _)) .zero

private theorem forwardsInComm {p : Process} (closed : ScopedProcess 0 p) :
    Reduces (withOffer p) (forwarded p) :=
  .comm (.literal .zero) (.literal .zero) closed (.send (.bound (by decide)) .zero)
    (.refl _) (forwardsSubstitutes p)

private theorem forwarded_distinct : ¬ ProcEq (forwarded payload) (forwarded insertion) := by
  intro eq
  have reads := procEq_preserves_read eq
  exact (by decide : ({Mark.output true} : Multiset Mark) ≠ {Mark.output false}) reads

/-- A *single offer* has two observable successors in the scoped
profile. Replacing the offered payload by an equivalent process before
COMM can change the literal name that is constructed as data. Simply
selecting a canonical payload in the raw substitution is not justified
by canonicalizing the enclosing parallel bag. -/
theorem forwarding_observes_payload_representative :
    ProcEq payload insertion ∧
      Reduces (withOffer payload) (forwarded payload) ∧
      Reduces (withOffer payload) (forwarded insertion) ∧
      ¬ ProcEq (forwarded payload) (forwarded insertion) := by
  have eq : ProcEq payload insertion := .symm (.unit payload)
  refine ⟨eq, forwardsInComm payloadScoped, ?_, forwarded_distinct⟩
  exact .equiv (.par (.send base eq) (.refl _)) (forwardsInComm insertionScoped) (.refl _)

/-- Even on closed payloads, this continuation's *literal* result
cannot be a function on process classes. An endpoint observer coarser
than these source classes is a new choice, not an adequacy lemma. -/
theorem literal_forwarder_does_not_descend :
    ¬ ∃ forward : ProcessClass → ProcessClass,
      ∀ p target, ScopedProcess 0 p → Subst p 0 forwards target →
        forward (ofProcess p) = ofProcess target := by
  rintro ⟨forward, computes⟩
  have beforeSame : ofProcess payload = ofProcess insertion :=
    Quotient.sound (s := processEquations) (.symm (.unit payload))
  have first := computes _ _ payloadScoped (forwardsSubstitutes payload)
  have second := computes _ _ insertionScoped (forwardsSubstitutes insertion)
  exact forwarded_distinct (Quotient.exact (s := processEquations)
    (first.symm.trans ((congrArg forward beforeSame).trans second)))

end ParallelControls

#print axioms procEq_iff_components
#print axioms reduces_iff_bagStep
#print axioms ParallelControls.competing_successors
#print axioms ParallelControls.forwarding_observes_payload_representative
#print axioms ParallelControls.literal_forwarder_does_not_descend

end Mettapedia.GSLT.Contracts.PaperRho
