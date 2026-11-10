import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEta

/-!
# The dependent full step: takes, reads, makes, tells, guards and predicate queries

An instance of the candidate step over the typed βη frames of the dependent unifier
(`ContextualDependentEta.frames`), with every part of a firing a conflict-bearing step has.

**States** (`State`): a formed frame `Γ`, its knowledge (an equation store of typed terms over `Γ`),
the present occurrences, and their labels, **typed terms over `Γ`**.

**Firings** (`Firing`) at a state with frame `Γ`:
* a telescope of fresh helpers over `Γ` (`Helpers`); the firing's patterns live at the frame it
  extends `Γ` to, and the state's labels are read there along the weakening;
* take and read patterns, typed terms over that frame, matched against the taken and read rows;
* made rows: an occurrence, a formed type and a raw term, checked against the type;
* told equations and guards, equations of typed terms;
* predicate queries (`Query`): a region of rows at each solution, which **reads through
  solutions** (terms a solution equates are in the region together), and an answer on the region of
  present rows. Absence (`Query.absent`) and counting (`Query.count`) of a pattern are queries.

**The information** of a firing is the knowledge read along the weakening, the equations of each
take and read pattern with the label of its row, and the told equations (`Firing.information`). An
equation of typed terms compares both their types and their terms: a told equation between terms of
different types is heterogeneous, and holds where a solution makes the types equal and then the
terms (`ContextualDependentTwins.solves_iff`).

**Admission** (`admits_iff`): the shapes (distinct takes and made occurrences, pattern counts, and
made terms typed at their types), the physical enabling of the selection, solvability of the
information, and the guards and queries asked at every solution of the information.

**Takes constrain** (`take_solved`, `read_solved`): every solution of the information equates each
take pattern with its row's label, in the dependent unifier's equality.

**Results and subject reduction** (`label_after_of_not_mem`, `label_after_of_mem`,
`subject_reduction`). The result lives at the extended frame, keeps the information as its
knowledge, and relabels the made occurrences by their checked made rows; every other row is the old
label read along the weakening. Every row of every state is a typed term of its frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {Head : Type} {rules : Rules Head}

/-! ## Telescopes of fresh helpers -/

/-- **A telescope of fresh helpers** over a frame: each helper's type is formed over the frame
extended by the helpers before it. -/
inductive Helpers : Context rules → Type
  | nil (Γ : Context rules) : Helpers Γ
  | cons {Γ : Context rules} (type : TypeOver Γ) (rest : Helpers (extend Γ type)) : Helpers Γ

namespace Helpers

/-- The frame a telescope extends its frame to. -/
def frame : {Γ : Context rules} → Helpers Γ → Context rules
  | Γ, .nil _ => Γ
  | _, .cons _ rest => rest.frame

/-- The weakening from the extended frame back to the frame. -/
def weaken : {Γ : Context rules} → (helpers : Helpers Γ) → helpers.frame ⟶ Γ
  | Γ, .nil _ => 𝟙 Γ
  | Γ, .cons type rest => rest.weaken ≫ projectionHom Γ type

/-- The number of helpers. -/
def length : {Γ : Context rules} → Helpers Γ → Nat
  | _, .nil _ => 0
  | _, .cons _ rest => rest.length + 1

theorem frame_nil (Γ : Context rules) : (Helpers.nil Γ).frame = Γ := rfl

theorem weaken_nil (Γ : Context rules) : (Helpers.nil Γ).weaken = 𝟙 Γ := rfl

end Helpers

/-! ## Made rows -/

/-- **A made row**: a formed type and a raw term, checked against the type at admission. -/
structure Make (Δ : Context rules) where
  type : TypeOver Δ
  code : Tm Head Δ.arity

namespace Make

variable {Δ : Context rules}

/-- The made term is typed at its type. -/
def WellTyped (m : Make Δ) : Prop := Typed rules Δ.raw m.code m.type.code

/-- The typed term of a checked made row. -/
def row (m : Make Δ) (typed : m.WellTyped) : TotalTerm Δ := ⟨m.type, ⟨m.code, typed⟩⟩

/-- A typed term, as a made row. -/
def ofRow (t : TotalTerm Δ) : Make Δ := ⟨t.1, t.2.code⟩

theorem ofRow_wellTyped (t : TotalTerm Δ) : (ofRow t).WellTyped := t.2.typed

theorem row_ofRow (t : TotalTerm Δ) : (ofRow t).row (ofRow_wellTyped t) = t := rfl

end Make

/-! ## Predicate queries that read through solutions -/

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L) (O : Type)

/-- **A predicate query** at a frame: a region of rows at each solution, which reads through
solutions, and an answer on the region of present rows. -/
structure Query (Δ : Context rules) where
  region : {Θ : Context rules} → (Θ ⟶ Δ) → TotalTerm Δ → Prop
  /-- **The region reads through solutions**: terms a solution equates are in it together. -/
  reads : ∀ {Θ : Context rules} (τ : Θ ⟶ Δ) {s t : TotalTerm Δ},
    (frames levels).E ((frames levels).act τ s) ((frames levels).act τ t) → (region τ s ↔ region τ t)
  answer : Finset O → Prop

variable {levels O}

namespace Query

variable {Δ : Context rules}

/-- A query holds at a solution when the region of the present rows has an accepted answer. -/
def Holds (q : Query levels O Δ) (present : Finset O) (row : O → TotalTerm Δ) {Θ : Context rules}
    (τ : Θ ⟶ Δ) : Prop :=
  ∃ seen : Finset O, (∀ o, o ∈ seen ↔ o ∈ present ∧ q.region τ (row o)) ∧ q.answer seen

variable (levels O)

/-- The rows a solution equates with a pattern. -/
def matching (pattern : TotalTerm Δ) {Θ : Context rules} (τ : Θ ⟶ Δ) (t : TotalTerm Δ) : Prop :=
  (frames levels).E ((frames levels).act τ pattern) ((frames levels).act τ t)

theorem matching_reads (pattern : TotalTerm Δ) {Θ : Context rules} (τ : Θ ⟶ Δ)
    {s t : TotalTerm Δ} (same : (frames levels).E ((frames levels).act τ s) ((frames levels).act τ t)) :
    matching levels pattern τ s ↔ matching levels pattern τ t :=
  ⟨fun h => ((frames levels).equivalence Θ).trans h same,
    fun h => ((frames levels).equivalence Θ).trans h (((frames levels).equivalence Θ).symm same)⟩

/-- **The absence query of a pattern**: no present row is equated with the pattern. -/
def absent (pattern : TotalTerm Δ) : Query levels O Δ where
  region τ t := matching levels pattern τ t
  reads := fun {_} τ {_ _} same => matching_reads levels pattern τ same
  answer seen := seen = ∅

/-- **The counting query of a pattern**: exactly `number` present rows are equated with it. -/
def count (pattern : TotalTerm Δ) (number : Nat) : Query levels O Δ where
  region τ t := matching levels pattern τ t
  reads := fun {_} τ {_ _} same => matching_reads levels pattern τ same
  answer seen := seen.card = number

variable {levels O}

theorem absent_holds_iff (pattern : TotalTerm Δ) (present : Finset O) (row : O → TotalTerm Δ)
    {Θ : Context rules} (τ : Θ ⟶ Δ) :
    (absent levels O pattern).Holds present row τ ↔
      ∀ o ∈ present, ¬ (frames levels).E ((frames levels).act τ pattern) ((frames levels).act τ (row o)) := by
  constructor
  · rintro ⟨seen, members, empty⟩ o present' equated
    have inside : o ∈ seen := (members o).mpr ⟨present', equated⟩
    rw [show seen = ∅ from empty] at inside
    exact absurd inside (Finset.notMem_empty o)
  · intro none
    refine ⟨∅, fun o => ⟨fun inside => absurd inside (Finset.notMem_empty o), ?_⟩, rfl⟩
    rintro ⟨present', equated⟩
    exact absurd equated (none o present')

end Query

/-! ## States and firings -/

variable (rules O) in
/-- **A state of the dependent full step**: a formed frame, its knowledge, the present occurrences,
and their labels, typed terms over the frame. -/
structure State where
  frame : Context rules
  knowledge : EquationStore (TotalTerm frame)
  present : Finset O
  label : O → TotalTerm frame

variable (levels) in
/-- **A firing of the dependent full step.** Its patterns, made rows, tells, guards and queries live
at the frame its helper telescope extends the state's frame to. -/
structure Firing (s : State rules O) where
  helpers : Helpers s.frame
  taken : List O
  read : List O
  takes : List (TotalTerm helpers.frame)
  reads : List (TotalTerm helpers.frame)
  makes : List (O × Make helpers.frame)
  tells : EquationStore (TotalTerm helpers.frame)
  guards : EquationStore (TotalTerm helpers.frame)
  queries : List (Query levels O helpers.frame)

namespace Firing

variable {s : State rules O} (f : Firing levels s)

/-- The occurrences it makes. -/
def made : List O := f.makes.map Prod.fst

/-- Its selection: takes, reads and made occurrences, in pattern order. -/
def selection : Selection O := ⟨f.taken, f.read, f.made⟩

/-- The label of a row, read at the firing's frame along the weakening. -/
def row (o : O) : TotalTerm f.helpers.frame := (frames levels).act f.helpers.weaken (s.label o)

/-- The equations of patterns with the labels of their rows. -/
def matching (patterns : List (TotalTerm f.helpers.frame)) (selected : List O) :
    EquationStore (TotalTerm f.helpers.frame) :=
  (patterns.zip selected).map fun x => (x.1, f.row x.2)

/-- **Its information**: the knowledge read along the weakening, the take and read equations, and
the told equations. -/
def information : EquationStore (TotalTerm f.helpers.frame) :=
  (frames levels).applyStore f.helpers.weaken s.knowledge ++ f.matching f.takes f.taken ++
    f.matching f.reads f.read ++ f.tells

/-- **Its shapes**: distinct takes and made occurrences, one row per pattern, and made terms typed
at their types. -/
def Shapes : Prop :=
  f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧
    f.reads.length = f.read.length ∧ ∀ m ∈ f.makes, m.2.WellTyped

/-- Its guards and queries at one solution of its information; queries see the present rows. -/
def Holds {Θ : Context rules} (τ : Θ ⟶ f.helpers.frame) : Prop :=
  (frames levels).Models τ f.guards ∧ ∀ q ∈ f.queries, q.Holds s.present f.row τ

variable [DecidableEq O]

/-- **Admission**. -/
def Admits : Prop :=
  f.Shapes ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    (frames levels).Solvable f.information ∧
    (frames levels).Entails f.information (fun _ τ => f.Holds τ)

end Firing

variable [DecidableEq O]

/-- Relabel the made occurrences by their checked made rows. -/
def relabel {Δ : Context rules} (row : O → TotalTerm Δ) :
    (makes : List (O × Make Δ)) → (∀ m ∈ makes, m.2.WellTyped) → O → TotalTerm Δ
  | [], _, o => row o
  | m :: rest, typed, o =>
      if o = m.1 then m.2.row (typed m (List.mem_cons.mpr (Or.inl rfl)))
      else relabel row rest (fun m' h => typed m' (List.mem_cons.mpr (Or.inr h))) o

theorem relabel_of_not_mem {Δ : Context rules} (row : O → TotalTerm Δ) :
    ∀ (makes : List (O × Make Δ)) (typed : ∀ m ∈ makes, m.2.WellTyped) {o : O},
      o ∉ makes.map Prod.fst → relabel row makes typed o = row o
  | [], _, _, _ => rfl
  | m :: rest, typed, o, absent => by
      have other : o ≠ m.1 := fun same => absent (List.mem_cons.mpr (Or.inl same))
      have later : o ∉ rest.map Prod.fst := fun inside => absent (List.mem_cons.mpr (Or.inr inside))
      simp only [relabel, if_neg other]
      exact relabel_of_not_mem row rest _ later

theorem relabel_of_mem {Δ : Context rules} (row : O → TotalTerm Δ) :
    ∀ (makes : List (O × Make Δ)) (typed : ∀ m ∈ makes, m.2.WellTyped) {o : O},
      o ∈ makes.map Prod.fst → ∃ (m : O × Make Δ) (member : m ∈ makes),
        m.1 = o ∧ relabel row makes typed o = m.2.row (typed m member)
  | [], _, _, inside => absurd inside (List.not_mem_nil)
  | m :: rest, typed, o, inside => by
      by_cases same : o = m.1
      · refine ⟨m, List.mem_cons.mpr (Or.inl rfl), same.symm, ?_⟩
        simp only [relabel, if_pos same]
      · have later : o ∈ rest.map Prod.fst := by
          rcases List.mem_cons.mp inside with first | later
          · exact absurd first same
          · exact later
        obtain ⟨m', member, named, eq⟩ := relabel_of_mem row rest _ later
        refine ⟨m', List.mem_cons.mpr (Or.inr member), named, ?_⟩
        simp only [relabel, if_neg same]
        exact eq

namespace Firing

variable {s : State rules O} (f : Firing levels s)

/-- The state after an admitted firing: the extended frame, the information as knowledge, the
fired occurrences, and the made occurrences relabelled by their made rows. -/
def after (admitted : f.Admits) : State rules O :=
  ⟨f.helpers.frame, f.information, fire s.present (f.selection.commit (T := Unit)),
    relabel f.row f.makes admitted.1.2.2.2.2⟩

end Firing

variable (levels O) in
/-- **The dependent full step**: firings with fresh helper telescopes, takes, reads, made rows,
tells, guards and predicate queries, over the typed βη frames of the dependent unifier. -/
def step : Interface.Step.Standard (frames levels) O (State rules O) (Firing levels) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := f.helpers.frame
  extension f := f.helpers.weaken
  information f := f.information
  transported := by
    intro s f e member
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨e, member, rfl⟩)))
  Shapes f := f.Shapes
  Holds f _ τ := f.Holds τ
  Admits f := f.Admits
  admits_iff _ := Iff.rfl
  preparedResult {s} f p := ⟨f.helpers.frame, f.information, fire s.present (f.selection.commit (T := Unit)),
    relabel f.row f.makes p.1.2.2.2.2⟩
  present_preparedResult _ _ := rfl
  preparedSettle f _ := (frames levels).id f.helpers.frame
  knowledge_preparedResult f _ := (Frames.applyStore_id (X := frames levels) f.information).symm

/-! ## Admission -/

section Admission

variable {s : State rules O} (f : Firing levels s)

theorem enabled_iff :
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

/-- **Admission of a dependent full firing**: its shapes; takes and reads present, takes not read,
made occurrences fresh; solvable information; and its guards and each of its queries asked at every
solution of the information. -/
theorem admits_iff :
    (step levels O).Admits f ↔ f.Shapes ∧
      ((∀ o ∈ f.taken, o ∈ s.present) ∧ (∀ o ∈ f.read, o ∈ s.present) ∧
        (∀ o ∈ f.taken, o ∉ f.read) ∧ ∀ o ∈ f.made, o ∉ s.present) ∧
      (frames levels).Solvable f.information ∧
      (frames levels).Entails f.information (fun _ τ => (frames levels).Models τ f.guards) ∧
      ∀ q ∈ f.queries, (frames levels).Entails f.information (fun _ τ => q.Holds s.present f.row τ) := by
  show f.Admits ↔ _
  unfold Firing.Admits Firing.Holds
  rw [enabled_iff, Frames.entails_and]
  constructor
  · rintro ⟨shapes, enabled, solvable, guards, queries⟩
    exact ⟨shapes, enabled, solvable, guards, fun q member b τ solved => queries b τ solved q member⟩
  · rintro ⟨shapes, enabled, solvable, guards, queries⟩
    exact ⟨shapes, enabled, solvable, guards, fun b τ solved q member => queries q member b τ solved⟩

namespace Firing

/-! ## Takes and reads constrain -/

omit [DecidableEq O] in
theorem matching_mem {patterns : List (TotalTerm f.helpers.frame)} {selected : List O}
    {p : TotalTerm f.helpers.frame} {o : O} (inside : (p, o) ∈ patterns.zip selected) :
    (p, f.row o) ∈ f.matching patterns selected :=
  List.mem_map.mpr ⟨(p, o), inside, rfl⟩

omit [DecidableEq O] in
/-- Every take equation is in the information. -/
theorem take_mem {p : TotalTerm f.helpers.frame} {o : O} (inside : (p, o) ∈ f.takes.zip f.taken) :
    (p, f.row o) ∈ f.information :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (f.matching_mem inside)))

omit [DecidableEq O] in
/-- Every read equation is in the information. -/
theorem read_mem {p : TotalTerm f.helpers.frame} {o : O} (inside : (p, o) ∈ f.reads.zip f.read) :
    (p, f.row o) ∈ f.information :=
  List.mem_append_left _ (List.mem_append_right _ (f.matching_mem inside))

omit [DecidableEq O] in
/-- **A take constrains**: every solution of the information equates each take pattern with the
label of its taken row. -/
theorem take_solved {Θ : Context rules} {τ : Θ ⟶ f.helpers.frame}
    (solved : (frames levels).Models τ f.information) {p : TotalTerm f.helpers.frame} {o : O}
    (inside : (p, o) ∈ f.takes.zip f.taken) :
    (frames levels).E ((frames levels).act τ p) ((frames levels).act τ (f.row o)) :=
  solved _ (f.take_mem inside)

omit [DecidableEq O] in
/-- **A read constrains** in the same way. -/
theorem read_solved {Θ : Context rules} {τ : Θ ⟶ f.helpers.frame}
    (solved : (frames levels).Models τ f.information) {p : TotalTerm f.helpers.frame} {o : O}
    (inside : (p, o) ∈ f.reads.zip f.read) :
    (frames levels).E ((frames levels).act τ p) ((frames levels).act τ (f.row o)) :=
  solved _ (f.read_mem inside)

/-- An admitted firing's take patterns unify with their rows. -/
theorem admitted_take_unifies (admitted : f.Admits) {p : TotalTerm f.helpers.frame} {o : O}
    (inside : (p, o) ∈ f.takes.zip f.taken) :
    (frames levels).Solvable [(p, f.row o)] := by
  obtain ⟨Θ, τ, solved⟩ := admitted.2.2.1
  exact ⟨Θ, τ, fun e member => by
    obtain rfl := List.mem_singleton.mp member
    exact f.take_solved solved inside⟩

/-! ## Results and subject reduction -/

theorem label_after_of_not_mem (admitted : f.Admits) {o : O} (absent : o ∉ f.made) :
    (f.after admitted).label o = f.row o :=
  relabel_of_not_mem f.row f.makes _ absent

theorem label_after_of_mem (admitted : f.Admits) {o : O} (inside : o ∈ f.made) :
    ∃ (m : O × Make f.helpers.frame) (member : m ∈ f.makes),
      m.1 = o ∧ (f.after admitted).label o = m.2.row (admitted.1.2.2.2.2 m member) :=
  relabel_of_mem f.row f.makes _ inside

/-- **Subject reduction.** After an admitted firing every row is a typed term of the new frame: a
made row is its checked made term at its type, and every other row is the old label substituted
along the weakening, at the substituted type. -/
theorem subject_reduction (admitted : f.Admits) (o : O) :
    Typed rules (f.after admitted).frame.raw ((f.after admitted).label o).2.code
        ((f.after admitted).label o).1.code ∧
      (o ∉ f.made → ((f.after admitted).label o).2.code =
          subst f.helpers.weaken.substitution (s.label o).2.code ∧
        ((f.after admitted).label o).1.code = subst f.helpers.weaken.substitution (s.label o).1.code) ∧
      (o ∈ f.made → ∃ m ∈ f.makes, m.1 = o ∧ ((f.after admitted).label o).1 = m.2.type ∧
        ((f.after admitted).label o).2.code = m.2.code) := by
  refine ⟨((f.after admitted).label o).2.typed, fun absent => ?_, fun inside => ?_⟩
  · rw [f.label_after_of_not_mem admitted absent]
    exact ⟨rfl, rfl⟩
  · obtain ⟨m, member, named, eq⟩ := f.label_after_of_mem admitted inside
    exact ⟨m, member, named, by rw [eq]; rfl, by rw [eq]; rfl⟩

theorem after_frame (admitted : f.Admits) : (f.after admitted).frame = f.helpers.frame := rfl

theorem after_knowledge (admitted : f.Admits) : (f.after admitted).knowledge = f.information := rfl

theorem after_present (admitted : f.Admits) :
    (f.after admitted).present = fire s.present (f.selection.commit (T := Unit)) := rfl

end Firing

end Admission

end DependentFull

#print axioms DependentFull.Query.absent_holds_iff
#print axioms DependentFull.step
#print axioms DependentFull.enabled_iff
#print axioms DependentFull.admits_iff
#print axioms DependentFull.Firing.take_solved
#print axioms DependentFull.Firing.read_solved
#print axioms DependentFull.Firing.admitted_take_unifies
#print axioms DependentFull.Firing.label_after_of_not_mem
#print axioms DependentFull.Firing.label_after_of_mem
#print axioms DependentFull.Firing.subject_reduction

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
