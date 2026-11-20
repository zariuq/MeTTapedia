import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core

/-!
# A candidate state: worlds, and a shared space whose rows are rules

A **candidate** for a state of the step in which alternatives are worlds that share a space:

* `WState`: a list of **worlds**, each a state of the present step with its own knowledge, and a
  **shared space**, a list of rules.
* **A row of a shared space is a rule** (`snapshot`): the adding world's frame as its unknowns, the
  adding world's knowledge as its told equations, the atom as its made row. A world reads the row by
  firing it, and every firing opens a rule's unknowns fresh: the row and its store are renamed apart
  at every use (the role of the source's `rowUse`), and a world's knowledge never meets another
  world's.
* `WStep`: a world fires a rule of the program or of the space (`fire`); a world is copied (`fork`);
  a world moves one of its rows to the space as a snapshot (`publish`).
* **Worlds share only what the space holds** (`fire_others`, `fire_space`, `publish_others`): a firing
  changes its own world and nothing else; only `publish` changes the space. **Firings in two distinct
  worlds commute** (`fire_commute`): two histories that differ by swapping such firings reach one
  state.

**The present step is the one-world instance** (`one_world_steps`): from one world and an empty
space, the steps to one world and an empty space are exactly the steps of the present step, with the
same results (`liftW_admits_iff`, `liftW_result`, `firing_of_empty`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Worlds

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open RuleSyntax

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **A state of worlds (a candidate state)**: the worlds, each a state of the present step, and the
rows of a shared space, each a rule. -/
structure WState (Tm : Obj → Type uT) (O : Type uOcc) where
  worlds : List (State Tm O)
  space : List (Rule Tm)

/-- The program a world runs: the program and the space's rows. -/
def withSpace (P : Program Tm) (space : List (Rule Tm)) : Program Tm := {r | r ∈ P ∨ r ∈ space}

variable {O : Type uOcc}

/-- **The snapshot of an atom**: a row of the shared space made from a world, with the world's frame as
its unknowns, the world's knowledge as its told equations and the atom as its made row. -/
def snapshot (s : State Tm O) (atom : Tm s.frame) : Rule Tm :=
  ⟨s.frame, { take := [], read := [], tell := s.knowledge, checks := [], produce := [atom] }, []⟩

variable [DecidableEq O]

section Steps

variable (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom) (P : Program Tm)

/-- **A step of worlds (a candidate step)**: a world fires a rule of the program or of the space; a
world is copied; a world publishes one of its rows to the space as a snapshot. -/
inductive WStep : WState Tm O → WState Tm O → Prop
  | fire (ws : List (State Tm O)) (space : List (Rule Tm)) (i : ℕ) (hi : i < ws.length)
      (f : Firing O E (withSpace P space) ws[i].frame) (admitted : f.Admits X ws[i]) :
      WStep ⟨ws, space⟩ ⟨ws.set i (f.result X ws[i]), space⟩
  | fork (ws : List (State Tm O)) (space : List (Rule Tm)) (i : ℕ) (hi : i < ws.length) :
      WStep ⟨ws, space⟩ ⟨ws[i] :: ws, space⟩
  | publish (ws : List (State Tm O)) (space : List (Rule Tm)) (i : ℕ) (hi : i < ws.length) (o : O)
      (present : o ∈ ws[i].present) :
      WStep ⟨ws, space⟩ ⟨ws.set i ⟨ws[i].frame, ws[i].knowledge, ws[i].present.erase o, ws[i].label⟩,
        snapshot ws[i] (ws[i].label o) :: space⟩

end Steps

/-! ## Worlds share only what the space holds -/

omit [DecidableEq O] in
/-- A firing changes no other world. -/
theorem fire_others {ws : List (State Tm O)} {i : ℕ} (s' : State Tm O) {j : ℕ} (other : i ≠ j)
    (hj : j < (ws.set i s').length) : (ws.set i s')[j] = ws[j]'(by simpa using hj) :=
  List.getElem_set_ne other _

/-- Only a publication changes the space. -/
theorem fire_space {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
    {w w' : WState Tm O} (step : WStep X E P w w') (notPublish : w'.space.length = w.space.length) :
    w'.space = w.space := by
  cases step with
  | fire => rfl
  | fork => rfl
  | publish => simp at notPublish

/-- A firing at a world given by an equation. -/
theorem WStep.fire_eq {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
    (ws : List (State Tm O)) (space : List (Rule Tm)) (i : ℕ) (hi : i < ws.length) {s : State Tm O}
    (hs : ws[i] = s) (f : Firing O E (withSpace P space) s.frame) (admitted : f.Admits X s) :
    WStep X E P ⟨ws, space⟩ ⟨ws.set i (f.result X s), space⟩ := by
  subst hs
  exact .fire ws space i hi f admitted

/-- **Firings in two distinct worlds commute**: firing world `i` then world `j`, and firing world `j`
then world `i`, reach one state of worlds. -/
theorem fire_commute {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}
    (ws : List (State Tm O)) (space : List (Rule Tm)) {i j : ℕ} (hi : i < ws.length) (hj : j < ws.length)
    (other : i ≠ j) (f : Firing O E (withSpace P space) ws[i].frame) (admittedF : f.Admits X ws[i])
    (g : Firing O E (withSpace P space) ws[j].frame) (admittedG : g.Admits X ws[j]) :
    WStep X E P ⟨ws, space⟩ ⟨ws.set i (f.result X ws[i]), space⟩ ∧
      WStep X E P ⟨ws.set i (f.result X ws[i]), space⟩
        ⟨(ws.set i (f.result X ws[i])).set j (g.result X ws[j]), space⟩ ∧
      WStep X E P ⟨ws, space⟩ ⟨ws.set j (g.result X ws[j]), space⟩ ∧
      WStep X E P ⟨ws.set j (g.result X ws[j]), space⟩
        ⟨(ws.set i (f.result X ws[i])).set j (g.result X ws[j]), space⟩ := by
  refine ⟨.fire ws space i hi f admittedF,
    WStep.fire_eq _ space j (by simpa using hj) (List.getElem_set_ne other _) g admittedG,
    .fire ws space j hj g admittedG, ?_⟩
  rw [List.set_comm _ _ other]
  exact WStep.fire_eq _ space i (by simpa using hi) (List.getElem_set_ne (Ne.symm other) _) f admittedF

omit [DecidableEq O] in
/-- A publication changes no other world. -/
theorem publish_others {ws : List (State Tm O)} {i : ℕ} (s' : State Tm O) {j : ℕ} (other : i ≠ j)
    (hj : j < (ws.set i s').length) : (ws.set i s')[j] = ws[j]'(by simpa using hj) :=
  List.getElem_set_ne other _

/-! ## The present step is the one-world instance -/

section OneWorld

variable (X : Frames Tm Hom) {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- A firing of the program as a firing of the program with a space. -/
def liftW (space : List (Rule Tm)) {a : Obj} (f : Firing O E P a) : Firing O E (withSpace P space) a :=
  ⟨f.rule, Or.inl f.member, f.ext, f.opening, f.selection, f.seen⟩

omit [DecidableEq O] in
/-- With an empty space, every firing is a firing of the program. -/
theorem firing_of_empty {a : Obj} (g : Firing O E (withSpace P []) a) : ∃ f : Firing O E P a, g = liftW [] f := by
  obtain ⟨rule, member, ext, opening, selection, seen⟩ := g
  rcases member with inP | inSpace
  · exact ⟨⟨rule, inP, ext, opening, selection, seen⟩, rfl⟩
  · cases inSpace

/-- **Admission does not see the space**: a lifted firing is admitted exactly when the firing is. -/
theorem liftW_admits_iff (space : List (Rule Tm)) (s : State Tm O) (f : Firing O E P s.frame) :
    (liftW space f).Admits X s ↔ f.Admits X s :=
  Iff.rfl

/-- The lifted firing has the firing's result. -/
theorem liftW_result (space : List (Rule Tm)) (s : State Tm O) (f : Firing O E P s.frame) :
    (liftW space f).result X s = f.result X s :=
  rfl

/-- **The present step is the one-world instance of the step of worlds**: from one world and an empty
space, the steps to one world and an empty space are exactly the steps of the present step. -/
theorem one_world_steps (s s' : State Tm O) :
    WStep X E P ⟨[s], []⟩ ⟨[s'], []⟩ ↔ ∃ f : Firing O E P s.frame, f.Admits X s ∧ f.result X s = s' := by
  constructor
  · intro step
    generalize hw : (⟨[s], []⟩ : WState Tm O) = w at step
    generalize hw' : (⟨[s'], []⟩ : WState Tm O) = w' at step
    cases step with
    | fire ws space i hi g admitted =>
        injection hw with hws hspace
        injection hw' with hws' _
        subst hws hspace
        have zero : i = 0 := by simp at hi; omega
        subst zero
        obtain ⟨f, rfl⟩ := firing_of_empty g
        refine ⟨f, admitted, ?_⟩
        simp only [List.set_cons_zero, List.cons.injEq, and_true] at hws'
        exact hws'.symm
    | fork ws space i hi =>
        injection hw with hws _
        injection hw' with hws' _
        subst hws
        simp at hws'
    | publish ws space i hi o present =>
        injection hw' with _ hspace'
        simp at hspace'
  · rintro ⟨f, admitted, rfl⟩
    exact WStep.fire (X := X) (E := E) (P := P) [s] [] 0 (by simp) (liftW [] f) admitted

end OneWorld

#print axioms fire_others
#print axioms fire_commute
#print axioms fire_space
#print axioms firing_of_empty
#print axioms liftW_admits_iff
#print axioms one_world_steps

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Worlds
