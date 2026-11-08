import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFull
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Transport

/-!
# Independence at dependent frames: the diamond of firings without helpers

**At a generic frame.** A firing without helpers (`Plain Δ`) has its takes, reads, made rows, tells,
guards and predicate queries at one frame `Δ`, and a state at that frame (`Local Δ`) is knowledge,
present occurrences and labels there. Its information, admission and result (`Plain.information`,
`Plain.Admits`, `Plain.after`) never leave `Δ`, so a second firing is read after the first with the
same data, and every comparison is an equation at `Δ`.

**Independence** (`Independent`) is a condition on the two firings at the state where both fire:
* their takes are disjoint, and neither takes a row the other reads;
* their made occurrences are distinct;
* their joint information (`joint`: the knowledge, then each firing's take, read and told equations)
  is solvable;
* neither firing **writes** a region of the other's predicate queries (`Plain.Writes`: it takes a row
  in the region, or makes a row in it) at any solution of the joint information.

Guards need no clause: they are equations, and every solution of the joint information solves each
firing's own information (`guards_unaffected`).

**The diamond** (`local_diamond`): two admitted, independent firings are each admitted after the
other, and the two composites have the same present occurrences, the same labels, and knowledge with
the same solutions. **The clauses are necessary** except the query clause (`clauses_of_residuals`):
when both orders are admitted, the takes are disjoint, no take meets the other's read, the made
occurrences are distinct and the joint information is solvable. So for firings without predicate
queries, independence is exactly the admission of both orders (`independent_iff_residuals`).

**In the dependent full step** (`toFiring`, `diamond`): a firing without helpers is a firing of
`DependentFull.step` with the empty telescope; its admission and result are the generic ones
(`admits_toFiring`, `after_toFiring`), so the diamond holds for the step itself, with composites that
agree (`State.Agree`): one frame, the same present occurrences and labels, and equivalent knowledge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
  {O : Type}

/-! ## Rows, equations of patterns, relabelling -/

/-- The equations of patterns with the labels of their rows. -/
def pairs {Δ : Context rules} (label : O → TotalTerm Δ) (patterns : List (TotalTerm Δ))
    (selected : List O) : EquationStore (TotalTerm Δ) :=
  (patterns.zip selected).map fun x => (x.1, label x.2)

theorem pairs_congr {Δ : Context rules} {label label' : O → TotalTerm Δ}
    (patterns : List (TotalTerm Δ)) (selected : List O) (agree : ∀ o ∈ selected, label o = label' o) :
    pairs label patterns selected = pairs label' patterns selected := by
  unfold pairs
  refine List.map_congr_left fun x member => ?_
  rw [agree x.2 (List.of_mem_zip member).2]

theorem relabel_irrelevant [DecidableEq O] {Δ : Context rules} (row row' : O → TotalTerm Δ) :
    ∀ (makes : List (O × Make Δ)) (typed typed' : ∀ m ∈ makes, m.2.WellTyped) {o : O},
      o ∈ makes.map Prod.fst → relabel row makes typed o = relabel row' makes typed' o
  | [], _, _, _, inside => absurd inside List.not_mem_nil
  | m :: rest, typed, typed', o, inside => by
      by_cases same : o = m.1
      · simp only [relabel, if_pos same]
      · have later : o ∈ rest.map Prod.fst := by
          rcases List.mem_cons.mp inside with first | later
          · exact absurd first same
          · exact later
        simp only [relabel, if_neg same]
        exact relabel_irrelevant row row' rest _ _ later

/-- **Relabellings by disjoint made rows commute.** -/
theorem relabel_comm [DecidableEq O] {Δ : Context rules} (row : O → TotalTerm Δ)
    (one two : List (O × Make Δ)) (typedOne : ∀ m ∈ one, m.2.WellTyped)
    (typedTwo : ∀ m ∈ two, m.2.WellTyped) (apart : ∀ o ∈ one.map Prod.fst, o ∉ two.map Prod.fst) :
    relabel (relabel row one typedOne) two typedTwo = relabel (relabel row two typedTwo) one typedOne := by
  funext o
  by_cases inTwo : o ∈ two.map Prod.fst
  · have notOne : o ∉ one.map Prod.fst := fun inOne => apart o inOne inTwo
    rw [relabel_of_not_mem _ one typedOne notOne]
    exact relabel_irrelevant _ _ two typedTwo typedTwo inTwo
  · rw [relabel_of_not_mem _ two typedTwo inTwo]
    by_cases inOne : o ∈ one.map Prod.fst
    · exact relabel_irrelevant _ _ one typedOne typedOne inOne
    · rw [relabel_of_not_mem _ one typedOne inOne, relabel_of_not_mem _ one typedOne inOne,
        relabel_of_not_mem _ two typedTwo inTwo]

/-! ## States at a fixed frame, and firings without helpers -/

variable (rules O) in
/-- **A state at the frame `Δ`**: knowledge, present occurrences and labels there. -/
structure Local (Δ : Context rules) where
  knowledge : EquationStore (TotalTerm Δ)
  present : Finset O
  label : O → TotalTerm Δ

/-- A state at a fixed frame, as a state of the dependent full step. -/
def Local.toState {Δ : Context rules} (c : Local rules O Δ) : State rules O :=
  ⟨Δ, c.knowledge, c.present, c.label⟩

/-- A state of the dependent full step, at its own frame. -/
def State.toLocal (s : State rules O) : Local rules O s.frame := ⟨s.knowledge, s.present, s.label⟩

variable (levels O) in
/-- **A firing without helpers** at the frame `Δ`: every part of it lives at `Δ`. -/
structure Plain (Δ : Context rules) where
  taken : List O
  read : List O
  takes : List (TotalTerm Δ)
  reads : List (TotalTerm Δ)
  makes : List (O × Make Δ)
  tells : EquationStore (TotalTerm Δ)
  guards : EquationStore (TotalTerm Δ)
  queries : List (Query levels O Δ)

namespace Plain

variable {Δ : Context rules} (f : Plain levels O Δ)

/-- The occurrences it makes. -/
def made : List O := f.makes.map Prod.fst

/-- Its selection. -/
def selection : Selection O := ⟨f.taken, f.read, f.made⟩

/-- Its own equations: its takes and reads with their rows' labels, and its tells. -/
def own (label : O → TotalTerm Δ) : EquationStore (TotalTerm Δ) :=
  pairs label f.takes f.taken ++ pairs label f.reads f.read ++ f.tells

/-- Its information at a state: the knowledge and its own equations. -/
def information (c : Local rules O Δ) : EquationStore (TotalTerm Δ) := c.knowledge ++ f.own c.label

/-- Its shapes, as for every firing of the step. -/
def Shapes : Prop :=
  f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧
    f.reads.length = f.read.length ∧ ∀ m ∈ f.makes, m.2.WellTyped

/-- Its guards and queries at one solution; the queries see the present rows. -/
def Holds (c : Local rules O Δ) {Θ : Context rules} (τ : Θ ⟶ Δ) : Prop :=
  (frames levels).Models τ f.guards ∧ ∀ q ∈ f.queries, q.Holds c.present c.label τ

variable [DecidableEq O]

/-- **Admission at a state at `Δ`**. -/
def Admits (c : Local rules O Δ) : Prop :=
  f.Shapes ∧ Enabled (fun _ : O => ()) c.present (f.selection.commit (T := Unit)) ∧
    (frames levels).Solvable (f.information c) ∧
    (frames levels).Entails (f.information c) (fun _ τ => f.Holds c τ)

/-- **The state after it**: the information as knowledge, the fired occurrences, and the made
occurrences relabelled by their checked made rows. -/
def after (c : Local rules O Δ) (typed : ∀ m ∈ f.makes, m.2.WellTyped) : Local rules O Δ :=
  ⟨f.information c, fire c.present (f.selection.commit (T := Unit)), relabel c.label f.makes typed⟩

omit [DecidableEq O] in
theorem own_congr {label label' : O → TotalTerm Δ}
    (agree : ∀ o, o ∈ f.taken ∨ o ∈ f.read → label o = label' o) : f.own label = f.own label' := by
  unfold own
  rw [pairs_congr f.takes f.taken fun o inside => agree o (.inl inside),
    pairs_congr f.reads f.read fun o inside => agree o (.inr inside)]

theorem enabled_iff (c : Local rules O Δ) :
    Enabled (fun _ : O => ()) c.present (f.selection.commit (T := Unit)) ↔
      (∀ o ∈ f.taken, o ∈ c.present) ∧ (∀ o ∈ f.read, o ∈ c.present) ∧
        (∀ o ∈ f.taken, o ∉ f.read) ∧ ∀ o ∈ f.made, o ∉ c.present := by
  constructor
  · intro enabled
    refine ⟨fun o member => enabled.taken_subset (by simpa [selection, Selection.commit] using member),
      fun o member => enabled.kept_subset (by simpa [selection, Selection.commit] using member),
      fun o member readToo => Finset.disjoint_left.mp enabled.apart
        (by simpa [selection, Selection.commit] using member)
        (by simpa [selection, Selection.commit] using readToo),
      fun o member present' => Finset.disjoint_left.mp enabled.fresh
        (by simpa [selection, Selection.commit] using member) present'⟩
  · rintro ⟨taken, read, apart, fresh⟩
    refine ⟨fun o member => taken o (by simpa [selection, Selection.commit] using member),
      fun o member => read o (by simpa [selection, Selection.commit] using member),
      Finset.disjoint_left.mpr fun {o} member readToo => apart o
        (by simpa [selection, Selection.commit] using member)
        (by simpa [selection, Selection.commit] using readToo),
      Finset.disjoint_left.mpr fun {o} member present' => fresh o
        (by simpa [selection, Selection.commit] using member) present',
      fun q member => by simp [selection, Selection.commit] at member⟩

theorem mem_fire_iff (c : Local rules O Δ) (o : O) :
    o ∈ fire c.present (f.selection.commit (T := Unit)) ↔
      (o ∈ c.present ∧ o ∉ f.taken) ∨ o ∈ f.made := by
  rw [mem_fire]
  simp only [selection, Selection.commit, List.mem_toFinset]

end Plain

/-! ## Independence -/

namespace Plain

variable {Δ : Context rules}

/-- **A firing writes a region of a query** at a solution: it takes a row inside the region, or
makes a row inside it. -/
def Writes (f : Plain levels O Δ) (label : O → TotalTerm Δ) (q : Query levels O Δ)
    {Θ : Context rules} (τ : Θ ⟶ Δ) : Prop :=
  (∃ o ∈ f.taken, q.region τ (label o)) ∨
    ∃ m ∈ f.makes, ∃ typed : m.2.WellTyped, q.region τ (m.2.row typed)

end Plain

/-- **The joint information** of two firings at a state: the knowledge, then each firing's own
equations. -/
def joint {Δ : Context rules} (c : Local rules O Δ) (f g : Plain levels O Δ) :
    EquationStore (TotalTerm Δ) :=
  c.knowledge ++ f.own c.label ++ g.own c.label

/-- **Independence of two firings without helpers** at a state. -/
structure Independent {Δ : Context rules} (c : Local rules O Δ) (f g : Plain levels O Δ) : Prop where
  takes_apart : ∀ o ∈ f.taken, o ∉ g.taken
  left_keeps_reads : ∀ o ∈ f.taken, o ∉ g.read
  right_keeps_reads : ∀ o ∈ g.taken, o ∉ f.read
  made_apart : ∀ o ∈ f.made, o ∉ g.made
  joint_solvable : (frames levels).Solvable (joint c f g)
  left_unwritten : ∀ q ∈ g.queries,
    (frames levels).Entails (joint c f g) (fun _ τ => ¬ f.Writes c.label q τ)
  right_unwritten : ∀ q ∈ f.queries,
    (frames levels).Entails (joint c f g) (fun _ τ => ¬ g.Writes c.label q τ)

section Diamond

variable {Δ : Context rules} {c : Local rules O Δ}

theorem mem_joint_iff (f g : Plain levels O Δ) (e : Equation (TotalTerm Δ)) :
    e ∈ joint c f g ↔ e ∈ c.knowledge ∨ e ∈ f.own c.label ∨ e ∈ g.own c.label := by
  simp only [joint, List.mem_append, or_assoc]

theorem joint_comm (f g : Plain levels O Δ) : (frames levels).Equivalent (joint c f g) (joint c g f) :=
  Frames.equivalent_of_mem_iff fun e => by
    rw [mem_joint_iff, mem_joint_iff]
    tauto

theorem information_subset_joint (f g : Plain levels O Δ) :
    ∀ e ∈ g.information c, e ∈ joint c f g := by
  intro e member
  rw [mem_joint_iff]
  rcases List.mem_append.mp member with known | own
  · exact .inl known
  · exact .inr (.inr own)

variable [DecidableEq O]

/-- **The rows a second firing selects keep their labels** after an admitted first firing: they were
present, and the first firing's made occurrences were not. -/
theorem label_after_selected {f g : Plain levels O Δ} (first : f.Admits c) (second : g.Admits c)
    (typed : ∀ m ∈ f.makes, m.2.WellTyped) :
    ∀ o, o ∈ g.taken ∨ o ∈ g.read → relabel c.label f.makes typed o = c.label o := by
  intro o inside
  obtain ⟨-, -, -, fresh⟩ := (f.enabled_iff c).mp first.2.1
  obtain ⟨gTaken, gRead, -, -⟩ := (g.enabled_iff c).mp second.2.1
  refine relabel_of_not_mem _ _ _ fun made => fresh o made ?_
  exact inside.elim (gTaken o) (gRead o)

/-- **The information of a residual is the joint information.** -/
theorem information_after {f g : Plain levels O Δ} (first : f.Admits c) (second : g.Admits c)
    (typed : ∀ m ∈ f.makes, m.2.WellTyped) :
    g.information (f.after c typed) = joint c f g := by
  show f.information c ++ g.own (relabel c.label f.makes typed) = _
  rw [g.own_congr (label_after_selected first second typed)]
  rfl

/-- **Guards are unaffected**: every solution of the joint information solves the guards of each
firing, since it solves that firing's own information. -/
theorem guards_unaffected {f g : Plain levels O Δ} (second : g.Admits c) :
    (frames levels).Entails (joint c f g) (fun _ τ => (frames levels).Models τ g.guards) :=
  Frames.Entails.of_subset (information_subset_joint f g)
    (Frames.Entails.mono second.2.2.2 fun _ _ holds => holds.1)

/-- **A query the first firing does not write keeps its answer** after it. -/
theorem query_after {f : Plain levels O Δ} (first : f.Admits c) (typed : ∀ m ∈ f.makes, m.2.WellTyped)
    (q : Query levels O Δ) {Θ : Context rules} (τ : Θ ⟶ Δ) (unwritten : ¬ f.Writes c.label q τ)
    (before : q.Holds c.present c.label τ) :
    q.Holds (fire c.present (f.selection.commit (T := Unit))) (relabel c.label f.makes typed) τ := by
  obtain ⟨-, -, -, fresh⟩ := (f.enabled_iff c).mp first.2.1
  obtain ⟨seen, members, answer⟩ := before
  refine ⟨seen, fun o => ?_, answer⟩
  rw [members o, f.mem_fire_iff c o]
  by_cases made : o ∈ f.made
  · obtain ⟨m, member, named, eq⟩ := relabel_of_mem c.label f.makes typed made
    rw [eq]
    have outside : ¬ q.region τ (m.2.row (typed m member)) :=
      fun inside => unwritten (.inr ⟨m, member, typed m member, inside⟩)
    constructor
    · rintro ⟨present, -⟩
      exact absurd present (fresh o made)
    · rintro ⟨-, inside⟩
      exact absurd inside outside
  · rw [relabel_of_not_mem c.label f.makes typed made]
    by_cases taken : o ∈ f.taken
    · have outside : ¬ q.region τ (c.label o) := fun inside => unwritten (.inl ⟨o, taken, inside⟩)
      constructor
      · rintro ⟨-, inside⟩
        exact absurd inside outside
      · rintro ⟨⟨-, notTaken⟩ | made', -⟩
        · exact absurd taken notTaken
        · exact absurd made' made
    · constructor
      · rintro ⟨present, inside⟩
        exact ⟨.inl ⟨present, taken⟩, inside⟩
      · rintro ⟨⟨present, -⟩ | made', inside⟩
        · exact ⟨present, inside⟩
        · exact absurd made' made

/-- **One side of the diamond**: after an admitted first firing, an admitted second firing is
admitted, provided they are independent. -/
theorem residual_admits {f g : Plain levels O Δ} (first : f.Admits c) (second : g.Admits c)
    (typed : ∀ m ∈ f.makes, m.2.WellTyped)
    (takesApart : ∀ o ∈ g.taken, o ∉ f.taken) (readsKept : ∀ o ∈ g.read, o ∉ f.taken)
    (madeApart : ∀ o ∈ g.made, o ∉ f.made) (solvable : (frames levels).Solvable (joint c f g))
    (unwritten : ∀ q ∈ g.queries,
      (frames levels).Entails (joint c f g) (fun _ τ => ¬ f.Writes c.label q τ)) :
    g.Admits (f.after c typed) := by
  obtain ⟨-, -, -, fFresh⟩ := (f.enabled_iff c).mp first.2.1
  obtain ⟨gTaken, gRead, gApart, gFresh⟩ := (g.enabled_iff c).mp second.2.1
  have information := information_after first second typed
  refine ⟨second.1, (g.enabled_iff _).mpr ⟨fun o inside => ?_, fun o inside => ?_, gApart, fun o made => ?_⟩,
    by rw [information]; exact solvable, ?_⟩
  · exact (f.mem_fire_iff c o).mpr (.inl ⟨gTaken o inside, takesApart o inside⟩)
  · exact (f.mem_fire_iff c o).mpr (.inl ⟨gRead o inside, readsKept o inside⟩)
  · intro inside
    rcases (f.mem_fire_iff c o).mp inside with ⟨present, -⟩ | fMade
    · exact gFresh o made present
    · exact madeApart o made fMade
  · rw [information]
    intro b τ solved
    have own : (frames levels).Models τ (g.information c) :=
      Frames.models_of_subset (information_subset_joint f g) solved
    obtain ⟨guards, queries⟩ := second.2.2.2 b τ own
    exact ⟨guards, fun q member =>
      query_after first typed q τ (unwritten q member b τ solved) (queries q member)⟩

omit [DecidableEq O] in
theorem fire_comm_prop {A Tf Tg Mf Mg : Prop} (tf : Tf → A) (tg : Tg → A) (mf : Mf → ¬ A)
    (mg : Mg → ¬ A) :
    ((((A ∧ ¬ Tf) ∨ Mf) ∧ ¬ Tg) ∨ Mg) ↔ ((((A ∧ ¬ Tg) ∨ Mg) ∧ ¬ Tf) ∨ Mf) := by
  constructor
  · rintro (⟨⟨a, ntf⟩ | m, ntg⟩ | m)
    · exact .inl ⟨.inl ⟨a, ntg⟩, ntf⟩
    · exact .inr m
    · exact .inl ⟨.inr m, fun t => mg m (tf t)⟩
  · rintro (⟨⟨a, ntg⟩ | m, ntf⟩ | m)
    · exact .inl ⟨.inl ⟨a, ntf⟩, ntg⟩
    · exact .inr m
    · exact .inl ⟨.inr m, fun t => mf m (tg t)⟩

/-- **Firing two selections in either order** leaves the same occurrences, when each takes only
present rows and makes only fresh ones. -/
theorem fire_fire_comm (c : Local rules O Δ) (f g : Plain levels O Δ) (o : O)
    (tf : o ∈ f.taken → o ∈ c.present) (tg : o ∈ g.taken → o ∈ c.present)
    (mf : o ∈ f.made → o ∉ c.present) (mg : o ∈ g.made → o ∉ c.present) :
    o ∈ fire (fire c.present (f.selection.commit (T := Unit))) (g.selection.commit (T := Unit)) ↔
      o ∈ fire (fire c.present (g.selection.commit (T := Unit))) (f.selection.commit (T := Unit)) := by
  rw [mem_fire, mem_fire, mem_fire, mem_fire]
  simp only [Plain.selection, Selection.commit, List.mem_toFinset]
  exact fire_comm_prop tf tg mf mg

/-- **The diamond of independent firings without helpers, at a generic frame.** Both orders are
admitted, and the composites have the same present occurrences and labels, and knowledge with the
same solutions. -/
theorem local_diamond {f g : Plain levels O Δ} (first : f.Admits c) (second : g.Admits c)
    (independent : Independent c f g) :
    g.Admits (f.after c first.1.2.2.2.2) ∧ f.Admits (g.after c second.1.2.2.2.2) ∧
      (frames levels).Equivalent (g.after (f.after c first.1.2.2.2.2) second.1.2.2.2.2).knowledge
        (f.after (g.after c second.1.2.2.2.2) first.1.2.2.2.2).knowledge ∧
      (g.after (f.after c first.1.2.2.2.2) second.1.2.2.2.2).present =
        (f.after (g.after c second.1.2.2.2.2) first.1.2.2.2.2).present ∧
      (g.after (f.after c first.1.2.2.2.2) second.1.2.2.2.2).label =
        (f.after (g.after c second.1.2.2.2.2) first.1.2.2.2.2).label := by
  obtain ⟨apart, leftReads, rightReads, madeApart, solvable, leftQueries, rightQueries⟩ := independent
  have symmetric := joint_comm (c := c) f g
  refine ⟨residual_admits first second _ (fun o inside taken => apart o taken inside)
      (fun o inside taken => leftReads o taken inside) (fun o inside made => madeApart o made inside)
      solvable leftQueries,
    residual_admits second first _ (fun o inside taken => apart o inside taken)
      (fun o inside taken => rightReads o taken inside) madeApart (symmetric.solvable_iff.mp solvable)
      (fun q member => (symmetric.entails_iff _).mp (rightQueries q member)), ?_, ?_, ?_⟩
  · show (frames levels).Equivalent (g.information (f.after c _)) (f.information (g.after c _))
    rw [information_after first second, information_after second first]
    exact symmetric
  · ext o
    obtain ⟨fTaken, -, -, fFresh⟩ := (f.enabled_iff c).mp first.2.1
    obtain ⟨gTaken, -, -, gFresh⟩ := (g.enabled_iff c).mp second.2.1
    exact fire_fire_comm c f g o (fTaken o) (gTaken o) (fFresh o) (gFresh o)
  · exact relabel_comm c.label f.makes g.makes _ _ madeApart

/-! ## The clauses are necessary, except the query clause -/

/-- **What one order's admission forces**: after an admitted first firing, an admitted second firing
takes and reads no row the first took, makes no occurrence the first made, and the joint
information is solvable. -/
theorem residual_clauses {f g : Plain levels O Δ} (first : f.Admits c) (second : g.Admits c)
    (typed : ∀ m ∈ f.makes, m.2.WellTyped) (afterFirst : g.Admits (f.after c typed)) :
    (∀ o ∈ g.taken, o ∉ f.taken) ∧ (∀ o ∈ g.read, o ∉ f.taken) ∧ (∀ o ∈ g.made, o ∉ f.made) ∧
      (frames levels).Solvable (joint c f g) := by
  obtain ⟨fTaken, -, -, fFresh⟩ := (f.enabled_iff c).mp first.2.1
  obtain ⟨gTaken', gRead', -, gFresh'⟩ := (g.enabled_iff _).mp afterFirst.2.1
  refine ⟨fun o gT fT => ?_, fun o gR fT => ?_, fun o gM fM => ?_, ?_⟩
  · rcases (f.mem_fire_iff c o).mp (gTaken' o gT) with ⟨-, notTaken⟩ | made
    · exact notTaken fT
    · exact fFresh o made (fTaken o fT)
  · rcases (f.mem_fire_iff c o).mp (gRead' o gR) with ⟨-, notTaken⟩ | made
    · exact notTaken fT
    · exact fFresh o made (fTaken o fT)
  · exact gFresh' o gM ((f.mem_fire_iff c o).mpr (.inr fM))
  · rw [← information_after first second typed]
    exact afterFirst.2.2.1

/-- **When both orders are admitted**, the takes are disjoint, neither takes the other's read, the
made occurrences are distinct, and the joint information is solvable. -/
theorem clauses_of_residuals {f g : Plain levels O Δ} (first : f.Admits c) (second : g.Admits c)
    (afterFirst : g.Admits (f.after c first.1.2.2.2.2))
    (afterSecond : f.Admits (g.after c second.1.2.2.2.2)) :
    (∀ o ∈ f.taken, o ∉ g.taken) ∧ (∀ o ∈ f.taken, o ∉ g.read) ∧ (∀ o ∈ g.taken, o ∉ f.read) ∧
      (∀ o ∈ f.made, o ∉ g.made) ∧ (frames levels).Solvable (joint c f g) := by
  obtain ⟨fTaken, fRead, -, fFresh⟩ := (f.enabled_iff c).mp first.2.1
  obtain ⟨gTaken, -, -, -⟩ := (g.enabled_iff c).mp second.2.1
  obtain ⟨gTaken', gRead', -, gFresh'⟩ := (g.enabled_iff _).mp afterFirst.2.1
  obtain ⟨-, fRead', -, -⟩ := (f.enabled_iff _).mp afterSecond.2.1
  refine ⟨fun o fT gT => ?_, fun o fT gR => ?_, fun o gT fR => ?_, fun o fM gM => ?_, ?_⟩
  · rcases (f.mem_fire_iff c o).mp (gTaken' o gT) with ⟨-, notTaken⟩ | made
    · exact notTaken fT
    · exact fFresh o made (fTaken o fT)
  · rcases (f.mem_fire_iff c o).mp (gRead' o gR) with ⟨-, notTaken⟩ | made
    · exact notTaken fT
    · exact fFresh o made (fTaken o fT)
  · rcases (g.mem_fire_iff c o).mp (fRead' o fR) with ⟨-, notTaken⟩ | made
    · exact notTaken gT
    · obtain ⟨-, -, -, gFresh⟩ := (g.enabled_iff c).mp second.2.1
      exact gFresh o made (gTaken o gT)
  · exact gFresh' o gM ((f.mem_fire_iff c o).mpr (.inr fM))
  · rw [← information_after first second first.1.2.2.2.2]
    exact afterFirst.2.2.1

/-- **For firings without predicate queries, independence is exactly the admission of both
orders.** -/
theorem independent_iff_residuals {f g : Plain levels O Δ} (first : f.Admits c) (second : g.Admits c)
    (noQueries : f.queries = [] ∧ g.queries = []) :
    Independent c f g ↔
      g.Admits (f.after c first.1.2.2.2.2) ∧ f.Admits (g.after c second.1.2.2.2.2) := by
  constructor
  · intro independent
    obtain ⟨one, two, -⟩ := local_diamond first second independent
    exact ⟨one, two⟩
  · rintro ⟨afterFirst, afterSecond⟩
    obtain ⟨apart, leftReads, rightReads, madeApart, solvable⟩ :=
      clauses_of_residuals first second afterFirst afterSecond
    refine ⟨apart, leftReads, rightReads, madeApart, solvable, fun q member => ?_, fun q member => ?_⟩
    · rw [noQueries.2] at member
      cases member
    · rw [noQueries.1] at member
      cases member

end Diamond

/-! ## In the dependent full step -/

/-- States of the dependent full step that agree: one frame, knowledge with the same solutions,
and the same present occurrences and labels. -/
def State.Agree (s t : State rules O) : Prop :=
  ∃ (Δ : Context rules) (K K' : EquationStore (TotalTerm Δ)) (present : Finset O)
    (label : O → TotalTerm Δ),
    s = ⟨Δ, K, present, label⟩ ∧ t = ⟨Δ, K', present, label⟩ ∧ (frames levels).Equivalent K K'

namespace Plain

variable {s : State rules O}

/-- **A firing without helpers is a firing of the dependent full step** with the empty telescope. -/
abbrev toFiring (f : Plain levels O s.frame) : Firing levels s :=
  ⟨.nil _, f.taken, f.read, f.takes, f.reads, f.makes, f.tells, f.guards, f.queries⟩

theorem act_one {Δ : Context rules} (t : TotalTerm Δ) : (frames levels).act (𝟙 Δ) t = t :=
  (frames levels).act_id t

theorem applyStore_one {Δ : Context rules} (K : EquationStore (TotalTerm Δ)) :
    (frames levels).applyStore (𝟙 Δ) K = K :=
  Frames.applyStore_id (X := frames levels) K

theorem row_toFiring (f : Plain levels O s.frame) : (toFiring f).row = s.label :=
  funext fun o => (frames levels).act_id (s.label o)

theorem information_toFiring (f : Plain levels O s.frame) :
    (toFiring f).information = f.information s.toLocal := by
  show (frames levels).applyStore (𝟙 s.frame) s.knowledge ++
      pairs (fun o => (frames levels).act (𝟙 s.frame) (s.label o)) f.takes f.taken ++
      pairs (fun o => (frames levels).act (𝟙 s.frame) (s.label o)) f.reads f.read ++ f.tells =
    s.knowledge ++ (pairs (fun o => s.label o) f.takes f.taken ++ pairs (fun o => s.label o) f.reads f.read ++
      f.tells)
  simp only [applyStore_one, act_one, List.append_assoc]

variable [DecidableEq O]

/-- The second firing, read after the first: the same data, at the first's result, whose frame is
the state's frame by definition. -/
abbrev residual (f g : Plain levels O s.frame) (first : (toFiring f).Admits) :
    Plain levels O ((toFiring f).after first).frame :=
  g

/-- **Admission of a firing without helpers is its admission at the state's frame.** -/
theorem admits_toFiring (f : Plain levels O s.frame) :
    (toFiring f).Admits ↔ f.Admits s.toLocal := by
  have information := information_toFiring f
  have row := row_toFiring f
  unfold Firing.Admits Firing.Holds
  rw [information, row]
  rfl

theorem relabel_row_congr {Δ : Context rules} {row row' : O → TotalTerm Δ} (same : row = row')
    (makes : List (O × Make Δ)) (typed : ∀ m ∈ makes, m.2.WellTyped) :
    relabel row makes typed = relabel row' makes typed := by
  subst same
  rfl

omit [DecidableEq O] in
theorem local_mk_congr {Δ : Context rules} {K K' : EquationStore (TotalTerm Δ)} (present : Finset O)
    {label label' : O → TotalTerm Δ} (knowledge : K = K') (labels : label = label') :
    (⟨K, present, label⟩ : Local rules O Δ) = ⟨K', present, label'⟩ := by
  subst knowledge
  subst labels
  rfl

theorem toLocal_after (f : Plain levels O s.frame) (first : (toFiring f).Admits) :
    ((toFiring f).after first).toLocal = f.after s.toLocal first.1.2.2.2.2 :=
  local_mk_congr (Δ := s.frame) _ (information_toFiring f)
    (relabel_row_congr (Δ := s.frame) (row_toFiring f) f.makes first.1.2.2.2.2)

/-- **A residual is admitted by the step exactly when it is admitted after the first firing at the
state's frame.** -/
theorem admits_residual_iff (f g : Plain levels O s.frame) (first : (toFiring f).Admits) :
    (toFiring (residual f g first)).Admits ↔ g.Admits (f.after s.toLocal first.1.2.2.2.2) :=
  (admits_toFiring (residual f g first)).trans
    (iff_of_eq (congrArg (fun c => Plain.Admits (residual f g first) c) (toLocal_after f first)))

/-- **The result of a firing without helpers is its result at the state's frame.** -/
theorem after_toFiring (f : Plain levels O s.frame) (first : (toFiring f).Admits) :
    (toFiring f).after first = (f.after s.toLocal first.1.2.2.2.2).toState :=
  congrArg Local.toState (toLocal_after f first)

end Plain

/-- **The diamond of independent firings without helpers in the dependent full step.** Two
admitted firings without helpers that are independent at the state are each admitted after the
other, and the two composite states agree. -/
theorem diamond [DecidableEq O] {s : State rules O} {f g : Plain levels O s.frame} (first : (Plain.toFiring f).Admits)
    (second : (Plain.toFiring g).Admits) (independent : Independent s.toLocal f g) :
    ∃ (afterFirst : (Plain.toFiring (Plain.residual f g first)).Admits)
      (afterSecond : (Plain.toFiring (Plain.residual g f second)).Admits),
      State.Agree (levels := levels) ((Plain.toFiring (Plain.residual f g first)).after afterFirst)
        ((Plain.toFiring (Plain.residual g f second)).after afterSecond) := by
  have localFirst := (Plain.admits_toFiring f).mp first
  have localSecond := (Plain.admits_toFiring g).mp second
  obtain ⟨one, two, knowledge, present, label⟩ := local_diamond localFirst localSecond independent
  have afterFirst : (Plain.toFiring (Plain.residual f g first)).Admits := by
    refine (Plain.admits_toFiring (Plain.residual f g first)).mpr ?_
    rw [Plain.toLocal_after f first]
    exact one
  have afterSecond : (Plain.toFiring (Plain.residual g f second)).Admits := by
    refine (Plain.admits_toFiring (Plain.residual g f second)).mpr ?_
    rw [Plain.toLocal_after g second]
    exact two
  refine ⟨afterFirst, afterSecond, s.frame,
    (g.after (f.after s.toLocal localFirst.1.2.2.2.2) localSecond.1.2.2.2.2).knowledge,
    (f.after (g.after s.toLocal localSecond.1.2.2.2.2) localFirst.1.2.2.2.2).knowledge,
    (g.after (f.after s.toLocal localFirst.1.2.2.2.2) localSecond.1.2.2.2.2).present,
    (g.after (f.after s.toLocal localFirst.1.2.2.2.2) localSecond.1.2.2.2.2).label, ?_, ?_, knowledge⟩
  · rw [Plain.after_toFiring (Plain.residual f g first) afterFirst]
    have same := Plain.toLocal_after f first
    show Local.toState (Plain.after g ((Plain.toFiring f).after first).toLocal _) = _
    rw [same]
    rfl
  · rw [Plain.after_toFiring (Plain.residual g f second) afterSecond]
    have same := Plain.toLocal_after g second
    show Local.toState (Plain.after f ((Plain.toFiring g).after second).toLocal _) = _
    rw [same, present, label]
    rfl

end DependentFull

#print axioms DependentFull.relabel_comm
#print axioms DependentFull.Plain.enabled_iff
#print axioms DependentFull.information_after
#print axioms DependentFull.guards_unaffected
#print axioms DependentFull.query_after
#print axioms DependentFull.residual_admits
#print axioms DependentFull.local_diamond
#print axioms DependentFull.residual_clauses
#print axioms DependentFull.clauses_of_residuals
#print axioms DependentFull.independent_iff_residuals
#print axioms DependentFull.Plain.admits_toFiring
#print axioms DependentFull.Plain.admits_residual_iff
#print axioms DependentFull.Plain.after_toFiring
#print axioms DependentFull.diamond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
