import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core

/-!
# A candidate state: knowledge located per alternative

A **candidate** for a state of the step in which alternatives share rows: one frame, one bag of rows,
and **a store of equations at each location**. Every row has a location, or none: a row with no
location belongs to a shared space and every location sees it.

* `LState`: the frame, the stores by location, the live locations, the present rows, their labels
  and their locations.
* `LState.view`: **what a location sees is a state of the present step**: the frame, the location's
  store, the rows at the location and the shared rows.
* `LFiring`: a firing at a location is a firing of the program at the location's view, with where its
  made rows go (the location, a location it creates, or the shared space), the locations it creates
  (each starting from a copy of the location's new store) and whether the location retires.
  `LFiring.Admits`: admitted at the view, the location live, the made identities fresh among all
  rows, the created locations fresh. `LFiring.result`: the firing's information becomes the store of
  the location and of every location it creates; every other location keeps its store, carried along
  the extension.

**The present step is the one-location instance** (`one_location_admits_iff`, `one_location_result`,
`one_location_firing`, `one_location_steps`): with one location, every row at it, nothing created,
shared or retired, the located firings are the firings of the present step, admitted exactly when
they are, with the same results. A choice that forks a location copies a store and renames nothing,
since locations are read separately; a firing never reads another location's store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Located

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open RuleSyntax

universe uO uT uH uE uOcc uL

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **A located state (a candidate state)**: one frame, a store at each location, the live locations,
the present rows with their labels, and each row's location (`none`: a row of a shared space). -/
structure LState (Tm : Obj → Type uT) (O : Type uOcc) (L : Type uL) where
  frame : Obj
  stores : L → EquationStore (Tm frame)
  live : Finset L
  present : Finset O
  label : O → Tm frame
  place : O → Option L

variable {O : Type uOcc} [DecidableEq O] {L : Type uL} [DecidableEq L]

/-- The rows a location sees: the rows at it and the shared rows. -/
def LState.visible (s : LState Tm O L) (ℓ : L) : Finset O :=
  s.present.filter fun o => s.place o = some ℓ ∨ s.place o = none

/-- **The view of a location**: the state of the present step that the location sees. -/
def LState.view (s : LState Tm O L) (ℓ : L) : State Tm O :=
  ⟨s.frame, s.stores ℓ, s.visible ℓ, s.label⟩

/-- **A located firing (a candidate firing)**: a location, a firing of the program at the location's
view, the place of each made row, the locations it creates, and whether the location retires. -/
structure LFiring (O : Type uOcc) (L : Type uL) (E : Extensions.{uO, uH, uE} Hom) (P : Program Tm) (a : Obj) where
  loc : L
  firing : Firing O E P a
  places : List (Option L)
  born : List L
  retire : Bool

/-- The places after a firing: each made row at its given place, every other row where it was. -/
def placeMade (old : O → Option L) : List O → List (Option L) → O → Option L
  | o' :: rest, p :: ps, o => if o = o' then p else placeMade old rest ps o
  | _, _, o => old o

section Step

variable (X : Frames Tm Hom) {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **Admission of a located firing**: the location is live; the firing is admitted at its view; the
made identities are fresh among all present rows; the created locations are distinct and not live;
each made row goes to the location, to a created location, or to the shared space. -/
def LFiring.Admits (s : LState Tm O L) (f : LFiring O L E P s.frame) : Prop :=
  f.loc ∈ s.live ∧ f.firing.Admits X (s.view f.loc) ∧
    (∀ o ∈ f.firing.selection.made, o ∉ s.present) ∧
    f.born.Nodup ∧ (∀ ℓ ∈ f.born, ℓ ∉ s.live) ∧
    f.places.length = f.firing.selection.made.length ∧
    ∀ p ∈ f.places, p = none ∨ p = some f.loc ∨ ∃ ℓ ∈ f.born, p = some ℓ

/-- **The result of a located firing**: the information becomes the store of the location and of
every location it creates; every other location keeps its store, carried along the extension. -/
def LFiring.result (s : LState Tm O L) (f : LFiring O L E P s.frame) : LState Tm O L where
  frame := E.target f.firing.ext
  stores ℓ := if ℓ = f.loc ∨ ℓ ∈ f.born then f.firing.information X (s.view f.loc)
    else X.applyStore (E.weaken f.firing.ext) (s.stores ℓ)
  live := (if f.retire then s.live.erase f.loc else s.live) ∪ f.born.toFinset
  present := fire s.present (f.firing.selection.commit (T := Unit))
  label := relabel (f.firing.row X (s.view f.loc)) f.firing.selection.made (f.firing.opened X).produce
  place := placeMade s.place f.firing.selection.made f.places

end Step

/-! ## The present step is the one-location instance -/

section OneLocation

variable (X : Frames Tm Hom) {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- A state of the present step as a located state with one location, every row at it. -/
def embed (s : State Tm O) : LState Tm O PUnit.{1} :=
  ⟨s.frame, fun _ => s.knowledge, {PUnit.unit}, s.present, s.label, fun _ => some PUnit.unit⟩

/-- A firing of the present step as a located firing at the one location. -/
def lift {s : State Tm O} (f : Firing O E P s.frame) : LFiring O PUnit.{1} E P (embed s).frame :=
  ⟨PUnit.unit, f, f.selection.made.map fun _ => some PUnit.unit, [], false⟩

omit [DecidableEq O] in
theorem embed_injective {s₁ s₂ : State Tm O} (same : embed s₁ = embed s₂) : s₁ = s₂ := by
  obtain ⟨f₁, k₁, p₁, l₁⟩ := s₁
  obtain ⟨f₂, k₂, p₂, l₂⟩ := s₂
  have frames : f₁ = f₂ := congrArg LState.frame same
  subst frames
  unfold embed at same
  injection same with _ stores _ present label _
  have knowledge : k₁ = k₂ := congrFun stores PUnit.unit
  subst knowledge present label
  rfl

omit [DecidableEq O] in
theorem visible_embed (s : State Tm O) : (embed s).visible PUnit.unit = s.present :=
  Finset.filter_true_of_mem fun _ _ => Or.inl rfl

/-- The view of the one location is the state, for admission. -/
theorem admits_view_embed (s : State Tm O) (f : Firing O E P s.frame) :
    f.Admits X ((embed s).view PUnit.unit) ↔ f.Admits X s := by
  obtain ⟨frame, knowledge, present, label⟩ := s
  change f.Admits X ⟨frame, knowledge, (embed (⟨frame, knowledge, present, label⟩ : State Tm O)).visible PUnit.unit,
    label⟩ ↔ _
  rw [visible_embed]

theorem placeMade_home : ∀ (made : List O) (o : O),
    placeMade (fun _ => some PUnit.unit) made (made.map fun _ => some PUnit.unit) o = some PUnit.unit
  | [], _ => rfl
  | o' :: rest, o => by
      simp only [placeMade, List.map_cons]
      split
      · rfl
      · exact placeMade_home rest o

/-- **One location, admission**: the lifted firing is admitted exactly when the firing is. -/
theorem one_location_admits_iff (s : State Tm O) (f : Firing O E P s.frame) :
    (lift f).Admits X (embed s) ↔ f.Admits X s := by
  constructor
  · rintro ⟨_, admitted, _⟩
    exact (admits_view_embed X s f).mp admitted
  · intro admitted
    refine ⟨Finset.mem_singleton_self _, (admits_view_embed X s f).mpr admitted, ?_, List.nodup_nil,
      fun _ member => (by cases member), by simp [lift], ?_⟩
    · intro o made inside
      exact Finset.disjoint_left.mp admitted.2.1.fresh (by simpa [Selection.commit, lift] using made) inside
    · intro p member
      simp only [lift, List.mem_map] at member
      obtain ⟨_, _, rfl⟩ := member
      exact .inr (.inl rfl)

/-- **One location, results**: the lifted firing's result is the firing's result. -/
theorem one_location_result (s : State Tm O) (f : Firing O E P s.frame) :
    (lift f).result X (embed s) = embed (f.result X s) := by
  simp only [LFiring.result, embed, lift, Firing.result]
  congr 1
  funext o
  exact placeMade_home _ o

omit [DecidableEq O] in
/-- **One location, firings**: a located firing at a one-location state that places every made row at
the location, creates no location and does not retire is the lift of its firing. -/
theorem one_location_firing {s : State Tm O} (f : LFiring O PUnit.{1} E P (embed s).frame)
    (lengths : f.places.length = f.firing.selection.made.length) (home : ∀ p ∈ f.places, p = some PUnit.unit)
    (noBorn : f.born = []) (stays : f.retire = false) : f = lift f.firing := by
  obtain ⟨loc, firing, places, born, retire⟩ := f
  simp only at lengths home noBorn stays
  subst noBorn stays
  have samePlaces : places = firing.selection.made.map fun _ => some PUnit.unit := by
    apply List.ext_getElem (by simpa using lengths)
    intro k small _
    simp only [List.getElem_map]
    exact home _ (List.getElem_mem small)
  subst samePlaces
  cases loc
  rfl

/-- **The present step is the one-location instance of the located step**: from a one-location state,
the located steps that keep every made row at the location and create, share and retire nothing are
exactly the steps of the present step, with the same results. -/
theorem one_location_steps (s s' : State Tm O) :
    (∃ f : LFiring O PUnit.{1} E P (embed s).frame, f.Admits X (embed s) ∧ f.born = [] ∧ f.retire = false ∧
        (∀ p ∈ f.places, p = some PUnit.unit) ∧ f.result X (embed s) = embed s') ↔
      ∃ g : Firing O E P s.frame, g.Admits X s ∧ g.result X s = s' := by
  constructor
  · rintro ⟨f, admitted, noBorn, stays, home, result⟩
    have same := one_location_firing f admitted.2.2.2.2.2.1 home noBorn stays
    rw [same] at admitted result
    exact ⟨f.firing, (one_location_admits_iff X s f.firing).mp admitted,
      embed_injective ((one_location_result X s f.firing).symm.trans result)⟩
  · rintro ⟨g, admitted, rfl⟩
    refine ⟨lift g, (one_location_admits_iff X s g).mpr admitted, rfl, rfl, ?_, one_location_result X s g⟩
    intro p member
    simp only [lift, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl

end OneLocation

#print axioms one_location_admits_iff
#print axioms one_location_result
#print axioms one_location_firing
#print axioms one_location_steps

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Located
