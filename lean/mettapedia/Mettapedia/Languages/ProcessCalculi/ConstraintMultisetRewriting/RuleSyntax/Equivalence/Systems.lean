import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core

/-!
# Systems, contexts and barbs on the step of a program

## Systems

A **system** (`System`) is a program with a state. It **reduces** (`Reduces`) by a step of its
program, `RuleSyntax.step`; the program does not change.

## Contexts

A **basic context** (`Basic`) is one of four kinds:

* `rows ids label`: the identities `ids` become present with the given labels;
* `rules Q`: the rules of `Q` join the program;
* `tell equations`: the equations join the knowledge;
* `extend x`: the frame is extended along an extension of the frame action, and the knowledge and the
  labels are carried along its weakening.

Labels, equations and extensions are given at every frame, so that one context applies to every
system, at whatever frame its state is. At the one-frame instance they are plain values.

A context **applies** to a system (`Basic.Applies`) when the identities it adds are absent from it; no
other side condition is asked. In particular a tell may make the knowledge unsolvable: the system is
then inert, which the barbs see.

**Composite contexts** are words of basic contexts (`applyAll`, `AppliesAll`), applied from left to
right; they compose by concatenation (`applyAll_append`, `appliesAll_append`). **Running beside
another system** (`beside`) is the composite that tells its knowledge, adds its rows and adds its
rules (`applyAll_beside`): the union of programs and of states, with disjoint identities.

A context's added identities can be **renamed** (`Basic.rename`): the same labels at other identities.
Renamings compose (`rename_rename`) and the identity renaming changes nothing (`rename_one`).

## Barbs

A **pattern** (`Pattern`) is a term with its own unknowns.

* **May-barb** (`MayBarb`): some present row and the pattern have a common instance at some solution
  of the knowledge, that is, some row can be read against the pattern. It is the admission of the
  **observer** of the pattern, the rule that reads one row against it (`mayBarb_of_observed`, and
  `observed_of_mayBarb` given a fresh opening). It says whether a row can be read, not how many: one
  row `7` and two rows `7` show the same may-barbs (`AtOneFrame.sevens_barbs`), while a user's `match`
  against the store returns one answer per matching row. Counting is observed by the contexts that add
  rules (`AtOneFrame.count_separates`).
* **Must-barb** (`MustBarb`): some present row is an instance of the pattern at every solution. It
  implies the may-barb when the knowledge is solvable (`mayBarb_of_mustBarb`); at unsolvable knowledge
  every must-barb holds and no may-barb does (`mustBarb_of_unsolvable`, `not_mayBarb_of_unsolvable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## Systems and reductions -/

/-- **A system**: a program with a state. -/
structure System (Tm : Obj → Type uT) (O : Type uOcc) where
  program : Program Tm
  state : State Tm O

section Reductions

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)

/-- **A reduction of a system**: a step of its program; the program stays. -/
def Reduces (S T : System Tm O) : Prop :=
  T.program = S.program ∧ Succ (step X O E S.program).toStep S.state T.state

variable {X O E}

/-- A reduction, spelled out: an admitted firing of the program whose result is the new state. -/
theorem reduces_iff {S T : System Tm O} :
    Reduces X O E S T ↔ T.program = S.program ∧
      ∃ f : Firing O E S.program S.state.frame, f.Admits X S.state ∧ f.result X S.state = T.state := by
  constructor
  · rintro ⟨same, f, admitted, reached⟩
    exact ⟨same, f, admitted, reached⟩
  · rintro ⟨same, f, admitted, reached⟩
    exact ⟨same, f, admitted, reached⟩

/-- An admitted firing of the program is a reduction. -/
theorem reduces_of_admits {P : Program Tm} {s : State Tm O} (f : Firing O E P s.frame)
    (admitted : f.Admits X s) : Reduces X O E ⟨P, s⟩ ⟨P, f.result X s⟩ :=
  ⟨rfl, f, admitted, rfl⟩

end Reductions

/-! ## Operations on states -/

section Operations

variable {O : Type uOcc}

/-- **Add rows**: the identities become present with the given labels; the other labels stay. -/
def addRows [DecidableEq O] (s : State Tm O) (ids : Finset O) (label : O → Tm s.frame) :
    State Tm O :=
  ⟨s.frame, s.knowledge, s.present ∪ ids, fun o => if o ∈ ids then label o else s.label o⟩

/-- **Tell equations**: they join the knowledge. -/
def tellState (s : State Tm O) (equations : EquationStore (Tm s.frame)) : State Tm O :=
  ⟨s.frame, s.knowledge ++ equations, s.present, s.label⟩

/-- **Extend the frame** along an extension: the knowledge and the labels are carried along its
weakening. -/
def extendState (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom) (s : State Tm O)
    (x : E.Ext s.frame) : State Tm O :=
  ⟨E.target x, X.applyStore (E.weaken x) s.knowledge, s.present,
    fun o => X.act (E.weaken x) (s.label o)⟩

end Operations

/-! ## Contexts -/

/-- **A basic context**: add rows, add rules, tell equations, or extend the frame. Labels,
equations and extensions are given at every frame. -/
inductive Basic (Tm : Obj → Type uT) (O : Type uOcc) (E : Extensions.{uO, uH, uE} Hom) :
    Type (max uO uT uOcc uE) where
  | rows (ids : Finset O) (label : (a : Obj) → O → Tm a)
  | rules (added : Program Tm)
  | tell (equations : (a : Obj) → EquationStore (Tm a))
  | extend (extension : (a : Obj) → E.Ext a)

namespace Basic

variable {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}

/-- The identities a context adds. -/
def ids : Basic Tm O E → Finset O
  | .rows ids _ => ids
  | _ => ∅

/-- **A context applies** to a system when the identities it adds are absent from the system. -/
def Applies (c : Basic Tm O E) (S : System Tm O) : Prop := Disjoint c.ids S.state.present

/-- **The same context with its added identities renamed**: the same labels at the renamed
identities. Contexts of the other kinds add no identities and are unchanged. -/
def rename (π : Equiv.Perm O) : Basic Tm O E → Basic Tm O E
  | .rows ids label => .rows (ids.map π.toEmbedding) (fun a o => label a (π.symm o))
  | .rules added => .rules added
  | .tell equations => .tell equations
  | .extend extension => .extend extension

/-- The identity renaming changes nothing. -/
theorem rename_one (c : Basic Tm O E) : c.rename 1 = c := by
  cases c with
  | rows ids label =>
      have same : ids.map (1 : Equiv.Perm O).toEmbedding = ids := by
        ext o
        rw [Finset.mem_map_equiv]
        exact Iff.rfl
      simp only [rename, same]
      rfl
  | rules added => rfl
  | tell equations => rfl
  | extend extension => rfl

/-- Renamings compose. -/
theorem rename_rename (c : Basic Tm O E) (π ρ : Equiv.Perm O) :
    (c.rename π).rename ρ = c.rename (ρ * π) := by
  cases c with
  | rows ids label =>
      have same : (ids.map π.toEmbedding).map ρ.toEmbedding = ids.map (ρ * π).toEmbedding := by
        ext o
        rw [Finset.mem_map_equiv, Finset.mem_map_equiv, Finset.mem_map_equiv]
        exact Iff.rfl
      simp only [rename, same]
      congr 1
  | rules added => rfl
  | tell equations => rfl
  | extend extension => rfl

/-- The identities of a renamed context are the renamed identities. -/
theorem ids_rename (c : Basic Tm O E) (π : Equiv.Perm O) :
    (c.rename π).ids = c.ids.map π.toEmbedding := by
  cases c <;> simp [rename, ids]

/-- A context without added identities applies to every system. -/
theorem applies_of_ids_empty {c : Basic Tm O E} (empty : c.ids = ∅) (S : System Tm O) :
    c.Applies S := by
  unfold Applies
  rw [empty]
  exact Finset.disjoint_empty_left _

variable (X : Frames Tm Hom) [DecidableEq O]

/-- **Applying a basic context.** -/
def apply : Basic Tm O E → System Tm O → System Tm O
  | .rows ids label, S => ⟨S.program, addRows S.state ids (label S.state.frame)⟩
  | .rules added, S => ⟨S.program ∪ added, S.state⟩
  | .tell equations, S => ⟨S.program, tellState S.state (equations S.state.frame)⟩
  | .extend extension, S => ⟨S.program, extendState X E S.state (extension S.state.frame)⟩

end Basic

section Composite

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}

/-- **A composite context**, a word of basic contexts, applied from left to right. -/
def applyAll : List (Basic Tm O E) → System Tm O → System Tm O
  | [], S => S
  | c :: C, S => applyAll C (c.apply X S)

/-- **A composite context applies** when each basic context applies to the system it meets. -/
inductive AppliesAll : List (Basic Tm O E) → System Tm O → Prop
  | nil (S : System Tm O) : AppliesAll [] S
  | cons {c : Basic Tm O E} {C : List (Basic Tm O E)} {S : System Tm O} :
      c.Applies S → AppliesAll C (c.apply X S) → AppliesAll (c :: C) S

/-- **Composite contexts compose by concatenation.** -/
theorem applyAll_append (C D : List (Basic Tm O E)) (S : System Tm O) :
    applyAll X (C ++ D) S = applyAll X D (applyAll X C S) := by
  induction C generalizing S with
  | nil => rfl
  | cons c C ih => exact ih (c.apply X S)

theorem appliesAll_append {C D : List (Basic Tm O E)} {S : System Tm O} :
    AppliesAll X (C ++ D) S ↔ AppliesAll X C S ∧ AppliesAll X D (applyAll X C S) := by
  induction C generalizing S with
  | nil =>
      constructor
      · intro applies
        exact ⟨.nil S, applies⟩
      · rintro ⟨-, applies⟩
        exact applies
  | cons c C ih =>
      constructor
      · intro applies
        cases applies with
        | cons first rest =>
            obtain ⟨left, right⟩ := ih.mp rest
            exact ⟨.cons first left, right⟩
      · rintro ⟨left, right⟩
        cases left with
        | cons first rest => exact .cons first (ih.mpr ⟨rest, right⟩)

/-- **Renaming a composite context**: each basic context renamed, each by its own permutation. -/
def RenamesAll (C' C : List (Basic Tm O E)) : Prop :=
  List.Forall₂ (fun c' c => ∃ π : Equiv.Perm O, c' = c.rename π) C' C

omit [DecidableEq O] in
theorem renamesAll_refl (C : List (Basic Tm O E)) : RenamesAll C C := by
  induction C with
  | nil => exact .nil
  | cons c C ih => exact .cons ⟨1, (Basic.rename_one c).symm⟩ ih

/-- **Running beside another system**: tell its knowledge, add its rows, add its rules. -/
def beside (added : Program Tm) (ids : Finset O) (label : (a : Obj) → O → Tm a)
    (knowledge : (a : Obj) → EquationStore (Tm a)) : List (Basic Tm O E) :=
  [.tell knowledge, .rows ids label, .rules added]

/-- **Beside another system**: the union of the programs, of the knowledges, and of the stores. -/
theorem applyAll_beside (added : Program Tm) (ids : Finset O) (label : (a : Obj) → O → Tm a)
    (knowledge : (a : Obj) → EquationStore (Tm a)) (S : System Tm O) :
    applyAll X (beside (E := E) added ids label knowledge) S =
      ⟨S.program ∪ added, ⟨S.state.frame, S.state.knowledge ++ knowledge S.state.frame,
        S.state.present ∪ ids, fun o => if o ∈ ids then label S.state.frame o else S.state.label o⟩⟩ :=
  rfl

/-- **Beside another system applies exactly when the identities are disjoint.** -/
theorem appliesAll_beside_iff (added : Program Tm) (ids : Finset O) (label : (a : Obj) → O → Tm a)
    (knowledge : (a : Obj) → EquationStore (Tm a)) (S : System Tm O) :
    AppliesAll X (beside (E := E) added ids label knowledge) S ↔ Disjoint ids S.state.present := by
  constructor
  · intro applies
    cases applies with
    | cons _ rest =>
        cases rest with
        | cons rows _ => exact rows
  · intro apart
    exact .cons (Basic.applies_of_ids_empty rfl _) (.cons apart
      (.cons (Basic.applies_of_ids_empty rfl _) (.nil _)))

end Composite

/-! ## Barbs -/

/-- **A pattern**: a term with its own unknowns. -/
structure Pattern (Tm : Obj → Type uT) where
  locals : Obj
  term : Tm locals

section Barbs

variable (X : Frames Tm Hom) {O : Type uOcc}

/-- **May-barb**: some present row and the pattern have a common instance at some solution of the
knowledge. -/
def MayBarb (p : Pattern Tm) (s : State Tm O) : Prop :=
  ∃ o ∈ s.present, ∃ (b : Obj) (σ : Hom s.frame b) (h : Hom p.locals b),
    X.Models σ s.knowledge ∧ X.E (X.act σ (s.label o)) (X.act h p.term)

/-- **Must-barb**: some present row is an instance of the pattern at every solution of the
knowledge. -/
def MustBarb (p : Pattern Tm) (s : State Tm O) : Prop :=
  ∃ o ∈ s.present, ∀ (b : Obj) (σ : Hom s.frame b), X.Models σ s.knowledge →
    ∃ h : Hom p.locals b, X.E (X.act σ (s.label o)) (X.act h p.term)

variable {X}

/-- At solvable knowledge a must-barb is a may-barb. -/
theorem mayBarb_of_mustBarb {p : Pattern Tm} {s : State Tm O} (solvable : X.Solvable s.knowledge)
    (must : MustBarb X p s) : MayBarb X p s := by
  obtain ⟨o, present, every⟩ := must
  obtain ⟨b, σ, known⟩ := solvable
  obtain ⟨h, equated⟩ := every b σ known
  exact ⟨o, present, b, σ, h, known, equated⟩

/-- **At unsolvable knowledge every must-barb of a present row holds.** -/
theorem mustBarb_of_unsolvable {p : Pattern Tm} {s : State Tm O}
    (unsolvable : ¬ X.Solvable s.knowledge) {o : O} (present : o ∈ s.present) : MustBarb X p s :=
  ⟨o, present, fun b σ known => absurd ⟨b, σ, known⟩ unsolvable⟩

/-- **At unsolvable knowledge no may-barb holds.** -/
theorem not_mayBarb_of_unsolvable {p : Pattern Tm} {s : State Tm O}
    (unsolvable : ¬ X.Solvable s.knowledge) : ¬ MayBarb X p s := by
  rintro ⟨o, -, b, σ, h, known, -⟩
  exact unsolvable ⟨b, σ, known⟩

end Barbs

/-! ## The may-barb is what the observer of a pattern sees -/

section Observer

variable {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom}

/-- **The observer of a pattern**: one rule that reads one row against the pattern and does nothing
else. -/
abbrev observer (p : Pattern Tm) : Rule Tm := ⟨p.locals, ⟨[], [p.term], [], [], []⟩, []⟩

/-- The observer opened along an extension, reading the row `o`. -/
def observerFiring {a : Obj} (p : Pattern Tm) (x : E.Ext a) (ι : Hom p.locals (E.target x)) (o : O) :
    Firing O E ({observer p} : Program Tm) a :=
  ⟨observer p, Set.mem_singleton _, x, ι, ⟨[], [o], []⟩, []⟩

variable (X : Frames Tm Hom) [DecidableEq O]

/-- **A firing of the observer is a may-barb**: it reads a present row, and its information equates
the row with the opened pattern. -/
theorem mayBarb_of_observed {s : State Tm O} {p : Pattern Tm}
    {f : Firing O E ({observer p} : Program Tm) s.frame}
    (admitted : (step X O E ({observer p} : Program Tm)).Admits (s := s) f) : MayBarb X p s := by
  obtain ⟨r, member, x, ι, ⟨taken, read, made⟩, seen⟩ := f
  have same : r = observer p := member
  subst same
  obtain ⟨-, ⟨-, -, -, readLength, -, -⟩, enabled, ⟨b, u, solved⟩, -, -⟩ := (admits_iff _).mp admitted
  obtain ⟨o, rfl⟩ := List.length_eq_one_iff.mp readLength.symm
  have present : o ∈ s.present := enabled.kept_subset (by simp [Selection.commit])
  have equated := Firing.read_solved _ solved (p := X.act ι p.term) (o := o) List.mem_cons_self
  have known := Firing.knowledge_solved _ solved
  refine ⟨o, present, b, X.comp u (E.weaken x), X.comp u ι, known, ?_⟩
  have key : X.E (X.act u (X.act (E.weaken x) (s.label o))) (X.act u (X.act ι p.term)) :=
    (X.equivalence b).symm equated
  have first := X.act_comp u (E.weaken x) (s.label o)
  have second := X.act_comp u ι p.term
  exact (congrArg₂ (@Frames.E _ _ _ X b) first second).mpr key

/-- **A may-barb is seen by the observer**, given a fresh opening of it: the observer reading the row
of the barb is admitted. -/
theorem observed_of_mayBarb {s : State Tm O} {p : Pattern Tm} (x : E.Ext s.frame)
    (ι : Hom p.locals (E.target x)) (fresh : ∀ o, (observerFiring (O := O) p x ι o).Fresh X s)
    (barb : MayBarb X p s) :
    ∃ o, (step X O E ({observer p} : Program Tm)).Admits (s := s) (observerFiring p x ι o) := by
  obtain ⟨o, present, b, σ, h, known, equated⟩ := barb
  have symm := fun {y z : Tm b} (same : X.E y z) => (X.equivalence b).symm same
  have trans := fun {y z w : Tm b} (one : X.E y z) (two : X.E z w) => (X.equivalence b).trans one two
  refine ⟨o, (admits_iff _).mpr ⟨fresh o, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩,
    ?_, ?_, ?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [observerFiring, Selection.commit, present]
  · obtain ⟨u, state, rule⟩ := fresh o b σ h
    refine ⟨b, u, fun e member => ?_⟩
    have unfolded : e ∈ (X.applyStore (E.weaken x) s.knowledge ++ []) ++
        [(X.act ι p.term, X.act (E.weaken x) (s.label o))] ++ [] := member
    rcases List.mem_append.mp unfolded with front | back
    · rcases List.mem_append.mp front with front' | matched
      · rcases List.mem_append.mp front' with old | none
        · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp old
          have left := state original.1 (Or.inl (List.mem_map_of_mem inside))
          have right := state original.2 (Or.inr (Or.inl (List.mem_map_of_mem inside)))
          exact trans left (trans (known original inside) (symm right))
        · exact absurd none List.not_mem_nil
      · obtain rfl := List.mem_singleton.mp matched
        have opened := rule p.term (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ List.mem_cons_self))))))
        have row := state (s.label o) (Or.inr (Or.inr ⟨o, present, rfl⟩))
        exact trans opened (trans (symm equated) (symm row))
    · exact absurd back List.not_mem_nil
  · intro c member
    exact absurd member List.not_mem_nil
  · intro q member
    exact absurd member List.not_mem_nil

end Observer

#print axioms reduces_iff
#print axioms Basic.rename_one
#print axioms Basic.rename_rename
#print axioms applyAll_append
#print axioms appliesAll_append
#print axioms applyAll_beside
#print axioms appliesAll_beside_iff
#print axioms mayBarb_of_mustBarb
#print axioms mustBarb_of_unsolvable
#print axioms not_mayBarb_of_unsolvable
#print axioms mayBarb_of_observed
#print axioms observed_of_mayBarb

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
