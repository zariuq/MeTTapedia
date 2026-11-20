import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core

/-!
# A firing that commits a bag of matches

`RuleSyntax.Core` defines a firing as one rule, one opening and one selection: one match. This module
defines, over the same `Rule`, `State` and `Firing`, a firing that commits a finite bag of matches at one
state, so that the choices that a one-match firing fixes become statements that can be compared.

## The joint firing

* **A member** (`Member`) is what a firing of the program is, without its extension: a rule of the
  program, an opening into the extended frame, a selection, and the seen sets. `Member.firing` is the
  firing of the program it stands for. `Member.key` is what identifies a match: the rule and the rows
  selected for its take and read patterns. Two firings with one key differ only by their opening and by
  the identities of their made rows.
* **A bag** (`Bag`) is one extension of the frame and a list of members along it.

From these alone:

* the **joint selection** (`Bag.selection`): the selections of the members, one after another;
* the **joint information** (`Bag.information`): the knowledge along the extension, then for every member
  its own equations (`Member.own`: the equations of its takes and reads with their rows, and its tells).
  The information of a member alone is the knowledge and its own equations (`Member.information_eq`);
* **joint freshness** (`Bag.Fresh`, by `Realized`): any instantiation of the state's frame and any
  instantiations of the unknowns of the members' rules, one for each member, are realized together. For one
  member this is `Firing.Fresh` word for word;
* **the fit** (`Bag.Fits`): joint freshness, the taken rows of all members distinct, the made identities
  of all members distinct, and for every member one row per pattern;
* the **guard predicate** (`Bag.Holds`): the guard predicate of every member, at one solution. The none query,
  counts and collect query read the entry state, as they do for one firing;
* the **result** (`Bag.result`): the extended frame, the joint information as knowledge, the store after
  the joint commit, and every made identity labelled by its opened made row.

## Readings of joint admission

Three readings are defined; they differ in what the members owe each other.

* `Bag.Admits`: the fit, the joint selection enabled as one commit (so no member reads or takes a row that
  a member takes), the joint information solvable, and the guards of every member at every solution of
  the **joint** information.
* `Bag.AdmitsOwn`: the same, with the guards of every member at every solution of **its own**
  information. It implies `Bag.Admits` (`Bag.admits_of_admitsOwn`): a solution of the joint information
  solves the information of each member (`Bag.models_member`).
* `Bag.AdmitsSnapshot`: as `Bag.Admits`, with every member enabled on its own instead of the joint
  selection enabled, so that a member may read a row that another member takes; both see the entry state.
  `Bag.Admits` implies it (`Bag.admitsSnapshot_of_admits`).

## The step

`bagStep` is an `Interface.Step.Standard` whose firings are bags and whose admission is `Bag.Admits` of a
bag that has a member. Its selection, information and guard predicate are the joint ones, so the general
theory of the interface applies to it as it does to `step`. A bag without members is left out of the step:
it is jointly admissible exactly when the state's terms can be carried along its extension and the
knowledge along it is solvable (`Bag.admits_nil_iff`), and it selects no row; were it a step, a state where
nothing can fire would have one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## Members and bags -/

/-- **A member of a joint firing** along an extension `x` of the frame: a rule of the program, an opening
of its unknowns into the extended frame, a selection of occurrences, and the set of rows each collect query
pattern claims to see. -/
structure Member (O : Type uOcc) (E : Extensions.{uO, uH, uE} Hom) (P : Program Tm) {a : Obj}
    (x : E.Ext a) where
  rule : Rule Tm
  member : rule ∈ P
  opening : Hom rule.locals (E.target x)
  selection : Selection O
  seen : List (Finset O)

namespace Member

variable {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm} {a : Obj} {x : E.Ext a}

/-- The firing of the program a member stands for. -/
abbrev firing (m : Member O E P x) : Firing O E P a :=
  ⟨m.rule, m.member, x, m.opening, m.selection, m.seen⟩

/-- A firing of the program, as a member along its own extension. -/
def ofFiring (g : Firing O E P a) : Member O E P g.ext :=
  ⟨g.rule, g.member, g.opening, g.selection, g.seen⟩

theorem firing_ofFiring (g : Firing O E P a) : (ofFiring g).firing = g := rfl

/-- **What identifies a match**: the rule and the rows selected for its take and read patterns. -/
def key (m : Member O E P x) : Rule Tm × List O × List O :=
  (m.rule, m.selection.taken, m.selection.read)

end Member

/-- **A bag of matches at one frame**: one extension of the frame and the members along it. -/
structure Bag (O : Type uOcc) (E : Extensions.{uO, uH, uE} Hom) (P : Program Tm) (a : Obj) where
  ext : E.Ext a
  members : List (Member O E P ext)

/-! ## What a member adds, and joint realization -/

section Own

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
  (s : State Tm O) {x : E.Ext s.frame} (m : Member O E P x)

/-- **The equations a member adds**: its take and read patterns with their rows, and its tells. -/
def Member.own : EquationStore (Tm (E.target x)) :=
  m.firing.matching X s (m.firing.opened X).take m.firing.selection.taken ++
    m.firing.matching X s (m.firing.opened X).read m.firing.selection.read ++ (m.firing.opened X).tell

/-- **The information of a member alone** is the knowledge along the extension and its own equations. -/
theorem Member.information_eq :
    m.firing.information X s = X.applyStore (E.weaken m.firing.ext) s.knowledge ++ m.own X s := by
  unfold Firing.information Member.own
  simp only [List.append_assoc]

end Own

/-- **Joint realization**: for every choice of an instantiation of the unknowns of each member's rule,
some instantiation of the extended frame satisfies `Q` and realizes each of them on the terms of its
rule along its opening. -/
def Realized (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
    {a : Obj} {x : E.Ext a} (b : Obj) :
    List (Member O E P x) → (Hom (E.target x) b → Prop) → Prop
  | [], Q => ∃ u, Q u
  | m :: rest, Q => ∀ h : Hom m.rule.locals b,
      Realized X b rest fun u => Q u ∧ ∀ t ∈ m.rule.terms, X.E (X.act u (X.act m.opening t)) (X.act h t)

section Realization

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
  {a : Obj} {x : E.Ext a} {b : Obj}

theorem realized_nil (Q : Hom (E.target x) b → Prop) :
    Realized X b ([] : List (Member O E P x)) Q ↔ ∃ u, Q u := Iff.rfl

theorem realized_cons (m : Member O E P x) (rest : List (Member O E P x))
    (Q : Hom (E.target x) b → Prop) :
    Realized X b (m :: rest) Q ↔ ∀ h : Hom m.rule.locals b,
      Realized X b rest fun u =>
        Q u ∧ ∀ t ∈ m.rule.terms, X.E (X.act u (X.act m.opening t)) (X.act h t) := Iff.rfl

/-- Joint realization is monotone in what is asked of the instantiation. -/
theorem Realized.mono (l : List (Member O E P x)) :
    ∀ {Q Q' : Hom (E.target x) b → Prop}, (∀ u, Q u → Q' u) → Realized X b l Q → Realized X b l Q' := by
  induction l with
  | nil =>
      intro Q Q' implies realized
      obtain ⟨u, holds⟩ := (realized_nil X Q).mp realized
      exact (realized_nil X Q').mpr ⟨u, implies u holds⟩
  | cons m rest ih =>
      intro Q Q' implies realized
      refine (realized_cons X m rest Q').mpr fun h => ?_
      refine ih ?_ ((realized_cons X m rest Q).mp realized h)
      exact fun u both => ⟨implies u both.1, both.2⟩

end Realization

/-! ## What a bag determines -/

namespace Bag

variable {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **The joint selection**: the rows the members select, member after member. -/
def selection {a : Obj} (f : Bag O E P a) : Selection O :=
  ⟨f.members.flatMap fun m => m.selection.taken, f.members.flatMap fun m => m.selection.read,
    f.members.flatMap fun m => m.selection.made⟩

/-- The opened made rows of the members, member after member. -/
def produce (X : Frames Tm Hom) {a : Obj} (f : Bag O E P a) : List (Tm (E.target f.ext)) :=
  f.members.flatMap fun m => (m.firing.opened X).produce

section Derived

variable (X : Frames Tm Hom) (s : State Tm O) (f : Bag O E P s.frame)

/-- **The joint information**: the knowledge along the extension, and the equations every member adds. -/
def information : EquationStore (Tm (E.target f.ext)) :=
  X.applyStore (E.weaken f.ext) s.knowledge ++ f.members.flatMap fun m => m.own X s

/-- **Joint freshness**: every instantiation of the state's frame and every choice of an instantiation of
the unknowns of each member's rule are realized by one instantiation of the extended frame. -/
def Fresh : Prop :=
  ∀ (b : Obj) (g : Hom s.frame b), Realized X b f.members fun u =>
    ∀ t, s.Mentions t → X.E (X.act u (X.act (E.weaken f.ext) t)) (X.act g t)

/-- **The fit**: joint freshness, all taken rows distinct, all made identities distinct, and for every
member one row per pattern, one made row per made identity, one seen set per collect pattern. -/
def Fits : Prop :=
  f.Fresh X s ∧ f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
    ∀ m ∈ f.members, m.rule.body.take.length = m.selection.taken.length ∧
      m.rule.body.read.length = m.selection.read.length ∧
      m.rule.body.produce.length = m.selection.made.length ∧
      m.rule.collect.length = m.seen.length

/-- **The joint guard predicate at a solution**: the guard predicate of every member. -/
def Holds {b : Obj} (σ : Hom (E.target f.ext) b) : Prop :=
  ∀ m ∈ f.members, m.firing.Holds X s σ

variable [DecidableEq O]

/-- **Joint admission, guards at the joint information**: the fit, the joint selection enabled as one
commit, solvable joint information, and the guards of every member at every solution of the joint
information. -/
def Admits : Prop :=
  f.Fits X s ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    X.Solvable (f.information X s) ∧ X.Entails (f.information X s) (fun _ σ => f.Holds X s σ)

/-- **Joint admission, guards at each member's own information.** -/
def AdmitsOwn : Prop :=
  f.Fits X s ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    X.Solvable (f.information X s) ∧
    ∀ m ∈ f.members, X.Entails (m.firing.information X s) (fun _ σ => m.firing.Holds X s σ)

/-- **Joint admission at the entry state, member by member**: every member is enabled on its own, so a
member may read a row another member takes. -/
def AdmitsSnapshot : Prop :=
  f.Fits X s ∧
    (∀ m ∈ f.members, Enabled (fun _ : O => ()) s.present (m.selection.commit (T := Unit))) ∧
    X.Solvable (f.information X s) ∧ X.Entails (f.information X s) (fun _ σ => f.Holds X s σ)

/-- **The result of a bag**: the extended frame, the joint information as knowledge, the store after the
joint commit, and the made identities labelled by the opened made rows. -/
def result : State Tm O :=
  ⟨E.target f.ext, f.information X s, fire s.present (f.selection.commit (T := Unit)),
    relabel (fun o => X.act (E.weaken f.ext) (s.label o)) f.selection.made (f.produce X)⟩

end Derived

/-! ## The readings compared -/

section Readings

variable (X : Frames Tm Hom) {s : State Tm O} {f : Bag O E P s.frame}

/-- **A solution of the joint information solves the information of each member.** -/
theorem models_member {m : Member O E P f.ext} (inside : m ∈ f.members) {b : Obj}
    {σ : Hom (E.target f.ext) b} (solved : X.Models σ (f.information X s)) :
    X.Models σ (m.firing.information X s) := by
  have split : X.Models σ (X.applyStore (E.weaken f.ext) s.knowledge) ∧
      X.Models σ (f.members.flatMap fun m => m.own X s) :=
    (Frames.models_append σ _ _).mp solved
  rw [Member.information_eq X s m]
  exact (Frames.models_append σ _ _).mpr
    ⟨split.1, fun e member => split.2 e (List.mem_flatMap.mpr ⟨m, inside, member⟩)⟩

/-- **The joint information is solvable only if the information of each member is.** -/
theorem solvable_member {m : Member O E P f.ext} (inside : m ∈ f.members)
    (solvable : X.Solvable (f.information X s)) : X.Solvable (m.firing.information X s) := by
  obtain ⟨b, σ, solved⟩ := solvable
  exact ⟨b, σ, models_member X inside solved⟩

variable [DecidableEq O]

/-- **Guards at each member's own information are guards at the joint information.** -/
theorem admits_of_admitsOwn (own : f.AdmitsOwn X s) : f.Admits X s :=
  ⟨own.1, own.2.1, own.2.2.1, fun b σ solved m inside =>
    own.2.2.2 m inside b σ (models_member X inside solved)⟩

/-- A member of a bag whose joint selection is enabled is enabled on its own. -/
theorem enabled_member {a : Obj} {g : Bag O E P a} {W : Finset O}
    (enabled : Enabled (fun _ : O => ()) W (g.selection.commit (T := Unit))) {m : Member O E P g.ext}
    (inside : m ∈ g.members) : Enabled (fun _ : O => ()) W (m.selection.commit (T := Unit)) := by
  refine ⟨fun o member => ?_, fun o member => ?_, ?_, ?_, fun q member => ?_⟩
  · exact enabled.taken_subset
      (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨m, inside, List.mem_toFinset.mp member⟩))
  · exact enabled.kept_subset
      (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨m, inside, List.mem_toFinset.mp member⟩))
  · exact Finset.disjoint_left.mpr fun o taken kept => Finset.disjoint_left.mp enabled.apart
      (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨m, inside, List.mem_toFinset.mp taken⟩))
      (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨m, inside, List.mem_toFinset.mp kept⟩))
  · exact Finset.disjoint_left.mpr fun o made present => Finset.disjoint_left.mp enabled.fresh
      (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨m, inside, List.mem_toFinset.mp made⟩)) present
  · simp [Selection.commit] at member

/-- **The joint selection enabled as one commit is every member enabled on its own.** -/
theorem admitsSnapshot_of_admits (admitted : f.Admits X s) : f.AdmitsSnapshot X s :=
  ⟨admitted.1, fun _ inside => enabled_member admitted.2.1 inside, admitted.2.2.1, admitted.2.2.2⟩

/-- **A bag without members** is jointly admissible exactly when the state's terms can be carried along the
extension and the knowledge along it is solvable. It commits nothing. -/
theorem admits_nil_iff (x : E.Ext s.frame) :
    (⟨x, []⟩ : Bag O E P s.frame).Admits X s ↔
      (∀ (b : Obj) (g : Hom s.frame b), ∃ u : Hom (E.target x) b,
        ∀ t, s.Mentions t → X.E (X.act u (X.act (E.weaken x) t)) (X.act g t)) ∧
      X.Solvable (X.applyStore (E.weaken x) s.knowledge) := by
  have known : (⟨x, []⟩ : Bag O E P s.frame).information X s =
      X.applyStore (E.weaken x) s.knowledge := List.append_nil _
  constructor
  · rintro ⟨⟨fresh, -⟩, -, solvable, -⟩
    refine ⟨fun b g => (realized_nil X _).mp (fresh b g), ?_⟩
    rw [← known]
    exact solvable
  · rintro ⟨carried, solvable⟩
    refine ⟨⟨fun b g => (realized_nil X _).mpr (carried b g), List.nodup_nil, List.nodup_nil,
      fun m inside => absurd inside List.not_mem_nil⟩, enabled_nil s.present, ?_,
      fun b σ _ m inside => absurd inside List.not_mem_nil⟩
    rw [known]
    exact solvable

end Readings

end Bag

/-! ## The step -/

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)
  (P : Program Tm)

/-- **The step whose firing is a bag of matches.** Its admission is `Bag.Admits` of a bag that has a
member; its selection, information and guard predicate are the joint ones. -/
def bagStep : Interface.Step.Standard X O (State Tm O) (fun s => Bag O E P s.frame) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.selection
  target f := E.target f.ext
  extension f := E.weaken f.ext
  information {s} f := f.information X s
  transported := by
    intro s f e member
    exact List.mem_append_left _ (List.mem_map.mpr ⟨e, member, rfl⟩)
  Shapes {s} f := f.members ≠ [] ∧ f.Fits X s
  Holds {s} f _ σ := f.Holds X s σ
  Admits {s} f := f.members ≠ [] ∧ f.Admits X s
  admits_iff _ := ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  preparedResult {s} f _ := f.result X s
  present_preparedResult _ _ := rfl
  preparedSettle f _ := X.id (E.target f.ext)
  knowledge_preparedResult {s} f _ := (Frames.applyStore_id (X := X) (f.information X s)).symm

variable {X O E P}

theorem bagStep_admits_iff {s : State Tm O} (f : Bag O E P s.frame) :
    (bagStep X O E P).Admits f ↔ f.members ≠ [] ∧ f.Admits X s := Iff.rfl

theorem bagStep_result {s : State Tm O} (f : Bag O E P s.frame)
    (admitted : (bagStep X O E P).Admits f) :
    (bagStep X O E P).result f admitted = f.result X s := rfl

#print axioms Member.information_eq
#print axioms Realized.mono
#print axioms Bag.models_member
#print axioms Bag.solvable_member
#print axioms Bag.admits_of_admitsOwn
#print axioms Bag.enabled_member
#print axioms Bag.admitsSnapshot_of_admits
#print axioms Bag.admits_nil_iff
#print axioms bagStep
#print axioms bagStep_admits_iff
#print axioms bagStep_result

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
