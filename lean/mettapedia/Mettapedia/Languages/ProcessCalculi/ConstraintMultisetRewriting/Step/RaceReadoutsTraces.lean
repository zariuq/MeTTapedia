import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceReadouts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Canonical

/-!
# Multiplicities, trace classes and partial-order reduction

## What `collect` counts (`count_eq_runs`)

At a finished budget of an enumeration, the multiplicity of a final state in the search's answers is
the number of complete runs ending there (`Enumeration.multiplicity_space`). `collect` counts
**runs**, not trace classes.

## Trace classes (`TraceClass`, `endClass`)

Runs from one start up to trace equivalence (`Transport.TraceEquiv`: swaps and similarity) are trace
classes. A classifier that respects the state classes (`Respects`) reads one class at the end of a
whole trace class (`endClass`), and completeness is a property of the trace class. Hence the complete
runs ending in a class are a union of whole trace classes (`mem_runsTo_iff`): each trace class is
counted by `collect` with its size.

**Counted by trace classes, multiplicities are invariants of the state class**
(`tracesTo_encard_eq_of_same`): transport along an isomorphism of the start is a bijection of trace
classes (`moveTrace`, `moveTrace_comp`) that keeps completeness and the end class.

## Partial-order reduction (`Transport.Canonical`, R63)

Exploring only canonical runs, with a sound oracle and a key kept by transport:

* **keeps the set of answer classes** (`canonical_classes_eq`);
* **rescales the multiplicities**: for every class, the number of trace classes ending there is at
  most the number of canonical complete runs ending there, which is at most the number of complete
  runs ending there (`tracesTo_le_canonicalTo`, `canonicalTo_le_runsTo`). When each trace class has
  one canonical run, the reduced count is exactly the number of trace classes
  (`canonicalTo_eq_tracesTo_of_unique`).

## The program's transport (`Race.restrictTransport`)

A transport of a step restricts to a program whose kept firings are closed under transport and
residuals. The one-frame transport restricts to every program (`Race.programTransport`), since it
moves and residuates firings as themselves. The control with differing raw multiplicities is in
`RaceReadoutsTracesControls`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

open Interface

universe uO uT uH uOcc uS uF uI uK v

section Traces

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS}
  {Firing : State → Type uF} {P : Interface.Step X O State Firing}
  (T : Interface.Transport.{uO, uT, uH, uOcc, uS, uF, uI} P) {β : Type v}

/-- **A classifier respects the state classes**: isomorphic states have one class. -/
def Respects (cls : State → β) : Prop := ∀ {a b : State}, T.Same a b → cls a = cls b

theorem respects_mk : Respects T (Transport.StateClass.mk T) :=
  fun same => (Transport.StateClass.mk_eq_mk_iff T).mpr same

/-- Trace equivalence of runs from one start, as a setoid. -/
def traceSetoid (s : State) : Setoid (P.Run s) :=
  ⟨T.TraceEquiv s, Relation.EqvGen.is_equivalence _⟩

/-- **A trace class**: a run up to trace equivalence. -/
abbrev TraceClass (s : State) : Type _ := Quotient (traceSetoid T s)

variable {T}

/-- **The end class of a trace class**: trace-equivalent runs end in one class. -/
def endClass {cls : State → β} (respects : Respects T cls) {s : State} : TraceClass T s → β :=
  Quotient.lift (fun r : P.Run s => cls r.last) fun _ _ equivalent =>
    respects (Transport.TraceEquiv.same_last equivalent)

theorem endClass_mk {cls : State → β} (respects : Respects T cls) {s : State} (r : P.Run s) :
    endClass respects (Quotient.mk (traceSetoid T s) r) = cls r.last := rfl

/-- **Completeness is a property of the trace class.** -/
theorem halted_of_traceEquiv {s : State} {r r' : P.Run s} (equivalent : T.TraceEquiv s r r')
    (halted : Halted P r.last) : Halted P r'.last :=
  halted_of_same (Transport.TraceEquiv.same_last equivalent) halted

variable (P) in
/-- The complete runs from `s` ending in class `c`. -/
def runsTo (cls : State → β) (s : State) (c : β) : Set (P.Run s) :=
  {r | Halted P r.last ∧ cls r.last = c}

variable (T) in
/-- The trace classes of complete runs from `s` ending in class `c`. -/
def tracesTo (cls : State → β) (s : State) (c : β) : Set (TraceClass T s) :=
  Quotient.mk (traceSetoid T s) '' runsTo P cls s c

/-- **Complete runs ending in a class are a union of whole trace classes**: `collect` counts each
trace class with its size. -/
theorem mem_runsTo_iff {cls : State → β} (respects : Respects T cls) {s : State} {c : β}
    (r : P.Run s) : r ∈ runsTo P cls s c ↔ Quotient.mk (traceSetoid T s) r ∈ tracesTo T cls s c := by
  constructor
  · intro member
    exact ⟨r, member, rfl⟩
  · rintro ⟨r', ⟨halted, ends⟩, same⟩
    have equivalent : T.TraceEquiv s r' r := Quotient.exact same
    exact ⟨halted_of_traceEquiv equivalent halted,
      (respects (Transport.TraceEquiv.same_last equivalent)).symm.trans ends⟩

/-- **What `collect` counts**: at a finished budget of an enumeration, the multiplicity of a final
state is the number of complete runs ending there. -/
theorem count_eq_runs [DecidableEq State] (E : Enumeration P) {n : ℕ} {s : State}
    (finished : (E.space.run n (.inr s)).status = .finished) (t : State) :
    ((E.space.approx n (.inr s)).answers.count t : ℕ∞) = (runsTo P id s t).encard := by
  rw [E.space.count_approx_eq_of_finished finished, E.multiplicity_space]
  rfl

/-- Trace classes transported along an isomorphism of their start. -/
def moveTrace {s t : State} (i : T.Iso s t) : TraceClass T s → TraceClass T t :=
  Quotient.map (T.moveRun i) fun _ _ equivalent => Transport.TraceEquiv.moveRun i equivalent

/-- Transporting there and back gives the trace class back. -/
theorem moveTrace_comp {s t : State} (i : T.Iso s t) (j : T.Iso t s) (q : TraceClass T s) :
    moveTrace j (moveTrace i q) = q := by
  refine Quotient.inductionOn q fun r => ?_
  show Quotient.mk (traceSetoid T s) (T.moveRun j (T.moveRun i r)) = Quotient.mk (traceSetoid T s) r
  exact Quotient.sound (.rel _ _ (.inr (Transport.Similar.symm
    (Transport.Similar.trans (Transport.Similar.moveRun i r) (Transport.Similar.moveRun j _)))))

/-- **Counted by trace classes, multiplicities are invariants of the state class**: from isomorphic
starts, every class is reached by equally many trace classes of complete runs. -/
theorem tracesTo_encard_eq_of_same {cls : State → β} (respects : Respects T cls) {s t : State}
    (same : T.Same s t) (c : β) : (tracesTo T cls s c).encard = (tracesTo T cls t c).encard := by
  obtain ⟨i⟩ := same
  have image : moveTrace i '' tracesTo T cls s c = tracesTo T cls t c := by
    ext q
    constructor
    · rintro ⟨_, ⟨r, ⟨halted, ends⟩, rfl⟩, rfl⟩
      have ends' := Transport.Similar.same_last (Transport.Similar.moveRun i r)
      exact ⟨T.moveRun i r, ⟨halted_of_same ends' halted, (respects ends').symm.trans ends⟩, rfl⟩
    · rintro ⟨r, ⟨halted, ends⟩, rfl⟩
      have ends' := Transport.Similar.same_last (Transport.Similar.moveRun (T.symm i) r)
      exact ⟨Quotient.mk _ (T.moveRun (T.symm i) r),
        ⟨_, ⟨halted_of_same ends' halted, (respects ends').symm.trans ends⟩, rfl⟩,
        moveTrace_comp (T.symm i) i (Quotient.mk (traceSetoid T t) r)⟩
  rw [← image]
  exact ((Function.LeftInverse.injective (moveTrace_comp i (T.symm i))).injOn).encard_image.symm

section Reduction

variable {κ : Type uK} [LinearOrder κ] {key : (s : State) → Firing s → κ}
  {indep : (s : State) → Firing s → Firing s → Prop}

variable (T key indep) in
/-- The canonical complete runs from `s` ending in class `c`: those partial-order reduction keeps. -/
def canonicalTo (cls : State → β) (s : State) (c : β) : Set (P.Run s) :=
  {r | Halted P r.last ∧ cls r.last = c ∧ Transport.Canonical T key indep r}

/-- **Partial-order reduction keeps the set of answer classes.** -/
theorem canonical_classes_eq (sound : ∀ s f g, indep s f g → T.Independent s f g)
    (laws : Transport.KeyLaws T key) {cls : State → β} (respects : Respects T cls) (s : State) :
    {c | ∃ r : P.Run s, Halted P r.last ∧ Transport.Canonical T key indep r ∧ cls r.last = c} =
      {c | ∃ r : P.Run s, Halted P r.last ∧ cls r.last = c} := by
  ext c
  constructor
  · rintro ⟨r, halted, _, ends⟩
    exact ⟨r, halted, ends⟩
  · rintro ⟨r, halted, rfl⟩
    obtain ⟨r', canonical, same⟩ := Transport.exists_canonical_same_last sound laws r
    exact ⟨r', halted_of_same same halted, canonical, (respects same).symm⟩

/-- **Every trace class of complete runs has a canonical member.** -/
theorem tracesTo_eq_image (sound : ∀ s f g, indep s f g → T.Independent s f g)
    (laws : Transport.KeyLaws T key) {cls : State → β} (respects : Respects T cls) (s : State)
    (c : β) :
    tracesTo T cls s c = Quotient.mk (traceSetoid T s) '' canonicalTo T key indep cls s c := by
  ext q
  constructor
  · rintro ⟨r, ⟨halted, ends⟩, rfl⟩
    obtain ⟨r', equivalent, canonical, -⟩ := Transport.exists_canonical sound laws r
    refine ⟨r', ⟨halted_of_traceEquiv equivalent halted,
      (respects (Transport.TraceEquiv.same_last equivalent)).symm.trans ends, canonical⟩, ?_⟩
    exact Quotient.sound (Relation.EqvGen.symm _ _ equivalent)
  · rintro ⟨r, ⟨halted, ends, _⟩, rfl⟩
    exact ⟨r, ⟨halted, ends⟩, rfl⟩

/-- **The reduced count is at least the number of trace classes.** -/
theorem tracesTo_le_canonicalTo (sound : ∀ s f g, indep s f g → T.Independent s f g)
    (laws : Transport.KeyLaws T key) {cls : State → β} (respects : Respects T cls) (s : State)
    (c : β) : (tracesTo T cls s c).encard ≤ (canonicalTo T key indep cls s c).encard := by
  rw [tracesTo_eq_image sound laws respects s c]
  exact Set.encard_image_le _ _

/-- **The reduced count is at most the number of runs.** -/
theorem canonicalTo_le_runsTo (cls : State → β) (s : State) (c : β) :
    (canonicalTo T key indep cls s c).encard ≤ (runsTo P cls s c).encard :=
  Set.encard_le_encard fun _ member => ⟨member.1, member.2.1⟩

/-- **With one canonical run per trace class, partial-order reduction counts trace classes.** -/
theorem canonicalTo_eq_tracesTo_of_unique (sound : ∀ s f g, indep s f g → T.Independent s f g)
    (laws : Transport.KeyLaws T key) {cls : State → β} (respects : Respects T cls) (s : State)
    (unique : ∀ r r' : P.Run s, Transport.Canonical T key indep r →
      Transport.Canonical T key indep r' → T.TraceEquiv s r r' → r = r') (c : β) :
    (canonicalTo T key indep cls s c).encard = (tracesTo T cls s c).encard := by
  rw [tracesTo_eq_image sound laws respects s c]
  refine (Set.InjOn.encard_image fun r member r' member' same => ?_).symm
  exact unique r r' member.2.2 member'.2.2 (Quotient.exact same)

end Reduction

end Traces

#print axioms respects_mk
#print axioms mem_runsTo_iff
#print axioms count_eq_runs
#print axioms tracesTo_encard_eq_of_same
#print axioms canonical_classes_eq
#print axioms tracesTo_eq_image
#print axioms tracesTo_le_canonicalTo
#print axioms canonicalTo_le_runsTo
#print axioms canonicalTo_eq_tracesTo_of_unique

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open Interface

universe uOb uTm uHm uOc uSt uFi uIs

section Restrict

variable {Obj : Type uOb} {Tm : Obj → Type uTm} {Hom : Obj → Obj → Type uHm}
  {X : Interface.Frames Tm Hom} {O : Type uOc} [DecidableEq O] {State : Type uSt}
  {Fir : State → Type uFi} {P : Interface.Step X O State Fir}

/-- **A transport restricts to a program** whose kept firings are closed under transport and
residuals. -/
def restrictTransport (T : Interface.Transport.{uOb, uTm, uHm, uOc, uSt, uFi, uIs} P)
    (keep : ∀ s, Fir s → Prop)
    (move_keep : ∀ {s t : State} (i : T.Iso s t) (f : Fir s), keep s f → keep t (T.move i f))
    (residual_keep : ∀ {s : State} (g : Fir s) (admitted : P.Admits g) (f : Fir s), keep s f →
      keep _ (T.residual g admitted f)) :
    Interface.Transport (restrict P keep) where
  Iso := T.Iso
  toStateIso i := ⟨(T.toStateIso i).frame, (T.toStateIso i).knowledge, (T.toStateIso i).rename,
    (T.toStateIso i).present⟩
  refl := T.refl
  symm := T.symm
  trans := T.trans
  Alike f f' := T.Alike f.1 f'.1
  alike_equivalence s := ⟨fun f => (T.alike_equivalence s).refl f.1,
    fun alike => (T.alike_equivalence s).symm alike,
    fun first second => (T.alike_equivalence s).trans first second⟩
  selection_alike alike := T.selection_alike alike
  admits_alike alike := T.admits_alike alike
  result_alike alike admitted admitted' := T.result_alike alike admitted admitted'
  move i f := ⟨T.move i f.1, move_keep i f.1 f.2⟩
  move_alike i _ _ alike := T.move_alike i alike
  move_refl f := T.move_refl f.1
  move_trans i j f := T.move_trans i j f.1
  move_symm i f := T.move_symm i f.1
  selection_move i f := T.selection_move i f.1
  admits_move i f := T.admits_move i f.1
  result_move i f admitted := T.result_move i f.1 admitted
  residual g admitted f := ⟨T.residual g.1 admitted f.1, residual_keep g.1 admitted f.1 f.2⟩
  selection_residual g admitted f := T.selection_residual g.1 admitted f.1
  move_residual i g admitted f := T.move_residual i g.1 admitted f.1

end Restrict

variable {T : Type*} {S : Type*} {O : Type*} [DecidableEq O]

/-- **The one-frame transport of a program**: configurations with the same solutions and occurrences
are isomorphic, and firings move and residuate as themselves. -/
def programTransport (A : SubstitutionAction T S) (label : O → T) (alphabet : List (AnnotatedRuns.Firing T S O)) :
    Interface.Transport (program A label alphabet) :=
  restrictTransport (AnnotatedRuns.firstOrderTransport A label) (fun _ f => f ∈ alphabet)
    (fun _ _ member => member) (fun _ _ _ member => member)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
