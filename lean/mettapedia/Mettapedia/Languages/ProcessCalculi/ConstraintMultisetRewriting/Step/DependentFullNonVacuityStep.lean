import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# The frame-local equation step over any frames instance

The fibre join (`fibre_admission_transfer_of_full`) speaks about any candidate step over the
second-order list frames whose guards are equation guards. To apply it to a concrete firing, this
file gives the plainest such step, over an arbitrary frames instance `X`:

* **states** (`State`): a frame, its knowledge, the present occurrences, and their labels, terms at
  the frame;
* **firings** (`Firing`): takes and reads with their patterns, made rows, told equations and equation
  guards, all at the state's frame; a firing stays at its frame and moves along the identity;
* **information** (`Firing.information`): the knowledge carried along the identity, each take and
  read pattern equated with the label of its row, and the told equations;
* **admission** (`step`, `admits_iff`): distinct takes and made occurrences, one row per pattern, the
  physical enabling of the selection, solvability of the information, and the guards at every
  solution of it. Its guards are equation guards by definition (`holds_iff`).

Admission has content: a take whose pattern no solution equates with its row is refused, and so is a
guard that some solution of the information breaks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace EquationStep

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH

variable {Obj : Type uO} (Tm : Obj → Type uT) {Hom : Obj → Obj → Type uH}

/-- **A state of the frame-local equation step.** -/
structure State (O : Type) where
  frame : Obj
  knowledge : EquationStore (Tm frame)
  present : Finset O
  label : O → Tm frame

/-- **A firing of the frame-local equation step**, at the state's frame. -/
structure Firing {O : Type} (s : State Tm O) where
  taken : List O
  read : List O
  takes : List (Tm s.frame)
  reads : List (Tm s.frame)
  makes : List (O × Tm s.frame)
  tells : EquationStore (Tm s.frame)
  guards : EquationStore (Tm s.frame)

variable {Tm}

/-- Relabel the made occurrences by their made rows; the first made row of an occurrence wins. -/
def relabelRows {T : Type uT} {O : Type} [DecidableEq O] (label : O → T) : List (O × T) → O → T
  | [], o => label o
  | m :: rest, o => if o = m.1 then m.2 else relabelRows label rest o

/-- The equations of patterns with the labels of their rows. -/
def State.matching {O : Type} (s : State Tm O) (patterns : List (Tm s.frame)) (selected : List O) :
    EquationStore (Tm s.frame) :=
  (patterns.zip selected).map fun x => (x.1, s.label x.2)

namespace Firing

variable {O : Type} {s : State Tm O} (f : Firing Tm s)

/-- The occurrences it makes. -/
def made : List O := f.makes.map Prod.fst

/-- Its selection: takes, reads and made occurrences, in pattern order. -/
def selection : Selection O := ⟨f.taken, f.read, f.made⟩

variable (X : Frames Tm Hom)

/-- **Its information**: the knowledge along the identity, the take and read equations, and the
told equations. -/
def information : EquationStore (Tm s.frame) :=
  X.applyStore (X.id s.frame) s.knowledge ++ s.matching f.takes f.taken ++ s.matching f.reads f.read ++
    f.tells

/-- **Its shapes**: distinct takes and made occurrences, and one row per pattern. -/
def Shapes : Prop :=
  f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length

variable [DecidableEq O]

/-- **Admission.** -/
def Admits : Prop :=
  f.Shapes ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    X.Solvable (f.information X) ∧ X.Entails (f.information X) (fun _ g => X.Models g f.guards)

/-- The label of a row after the firing: a made row's term, else the old label. -/
def relabel (o : O) : Tm s.frame := relabelRows s.label f.makes o

/-- The state after the firing: the information carried along the identity as knowledge, the fired
occurrences, and the made rows relabelled. -/
def after : State Tm O :=
  ⟨s.frame, X.applyStore (X.id s.frame) (f.information X), fire s.present (f.selection.commit (T := Unit)),
    f.relabel⟩

end Firing

variable (X : Frames Tm Hom) (O : Type) [DecidableEq O]

/-- **The frame-local equation step** over the frames instance `X`. -/
def step : Step.Standard X O (State Tm O) (fun s => Firing Tm s) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target {s} _ := s.frame
  extension {s} _ := X.id s.frame
  information f := f.information X
  transported := by
    intro s f e member
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨e, member, rfl⟩)))
  Shapes f := f.Shapes
  Holds f _ g := X.Models g f.guards
  Admits f := f.Admits X
  admits_iff _ := Iff.rfl
  preparedResult f _ := f.after X
  present_preparedResult _ _ := rfl
  preparedSettle {s} _ _ := X.id s.frame
  knowledge_preparedResult _ _ := rfl

variable {X O}

/-- **Its guards are equation guards.** -/
theorem holds_iff {s : State Tm O} (f : Firing Tm s) (b : Obj) (g : Hom ((step X O).target f) b) :
    (step X O).Holds f b g ↔ X.Models g f.guards :=
  Iff.rfl

theorem information_eq {s : State Tm O} (f : Firing Tm s) :
    (step X O).information f = f.information X :=
  rfl

/-- **Admission of a frame-local firing.** -/
theorem admits_iff {s : State Tm O} (f : Firing Tm s) :
    (step X O).Admits f ↔ f.Shapes ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
      X.Solvable (f.information X) ∧ X.Entails (f.information X) (fun _ g => X.Models g f.guards) :=
  Iff.rfl

/-- **The physical enabling**: takes and reads present, takes not read, made occurrences fresh. -/
theorem enabled_iff {s : State Tm O} (f : Firing Tm s) :
    Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ↔
      (∀ o ∈ f.taken, o ∈ s.present) ∧ (∀ o ∈ f.read, o ∈ s.present) ∧
        (∀ o ∈ f.taken, o ∉ f.read) ∧ ∀ o ∈ f.made, o ∉ s.present := by
  constructor
  · intro enabled
    refine ⟨fun o member => enabled.taken_subset (by simpa [Firing.selection, Selection.commit] using member),
      fun o member => enabled.kept_subset (by simpa [Firing.selection, Selection.commit] using member),
      fun o member readToo => Finset.disjoint_left.mp enabled.apart
        (by simpa [Firing.selection, Selection.commit] using member)
        (by simpa [Firing.selection, Selection.commit] using readToo),
      fun o member present' => Finset.disjoint_left.mp enabled.fresh
        (by simpa [Firing.selection, Selection.commit] using member) present'⟩
  · rintro ⟨taken, read, apart, fresh⟩
    refine ⟨fun o member => taken o (by simpa [Firing.selection, Selection.commit] using member),
      fun o member => read o (by simpa [Firing.selection, Selection.commit] using member),
      Finset.disjoint_left.mpr fun {o} member readToo => apart o
        (by simpa [Firing.selection, Selection.commit] using member)
        (by simpa [Firing.selection, Selection.commit] using readToo),
      Finset.disjoint_left.mpr fun {o} member present' => fresh o
        (by simpa [Firing.selection, Selection.commit] using member) present',
      fun q member => by simp [Firing.selection, Selection.commit] at member⟩

omit [DecidableEq O] in
/-- **A take constrains**: every solution of the information equates each take pattern with the
label of its row. -/
theorem take_solved {s : State Tm O} (f : Firing Tm s) {b : Obj} {g : Hom s.frame b}
    (solved : X.Models g (f.information X)) {p : Tm s.frame} {o : O} (inside : (p, o) ∈ f.takes.zip f.taken) :
    X.E (X.act g p) (X.act g (s.label o)) :=
  solved _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨(p, o), inside, rfl⟩))))

end EquationStep

#print axioms EquationStep.step
#print axioms EquationStep.holds_iff
#print axioms EquationStep.admits_iff
#print axioms EquationStep.enabled_iff
#print axioms EquationStep.take_solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
