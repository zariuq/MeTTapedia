import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceSteps

/-!
# The races layer over the generic step

The labelled step, its multi-firing steps and its histories, for every instance of the candidate
step's interface (`Interface.Step`), with any frames. `RaceSpectrum` and `RaceSteps` are the
one-frame case; `RaceGenericFirstOrder` proves that they are the restriction of these definitions.

## The labelled step (`Moves`, `Bisimilar`)

A program says which firings it offers at each state, under which label (`offers ℓ s f`). `Moves s ℓ
t` holds when an offered firing labelled `ℓ` is admitted at `s` and `t` is its result. A program's
labels are **invariant under transport** (`Invariant`) when moving an offered firing along an
isomorphism of states offers it under the same label.

* **Transport-equivalent states are bisimilar** (`bisimilar_of_same`), for every transport whose
  isomorphisms keep the labels: `Transport.Same` is a bisimulation. They satisfy the same
  Hennessy–Milner formulas (`sat_iff_of_same`), which characterize bisimilarity when each label offers
  finitely many firings at each state (`bisimilar_iff_sat`).

## Multi-firing steps (`Concurrent`, `StepMoves`, `StepBisimilar`)

The interface's independence is semantic and local to a state (`Transport.Independent`, the
diamond up to state classes). A step fires a word of firings at one state, **each independent, at the
state it fires from, of every later firing of the word, the later ones read as residuals after it**
(`Concurrent`). Its label is the multiset of the firings' labels. A step of one firing is a move
(`stepMoves_singleton_iff`), so step bisimilarity implies bisimilarity (`bisimilar_of_stepBisimilar`).

* **Independence is transported** (`independent_move`): along an isomorphism of states, by
  naturality of residuals, for every transport.
* **Steps are transported** (`concurrent_move`) for strict transports (alike firings are equal), and
  **transport-equivalent states are step bisimilar** (`stepBisimilar_of_same`).

## Histories (`HMoves`, `HPBisimilar`)

An event is a firing at the state it fired at (`Event`). The interface's independence relates two
firings at one state; the events of a history fire at different states, so a history needs an
independence of events, which the program supplies (`indep`). The causal past of a new firing is its
dependences on earlier events closed under their recorded pasts (`past`), as in `RaceSteps`. Two
events are **of one class** (`EventSame`) when an isomorphism of their states moves one to a firing
alike to the other.

* **Transport-equivalent states are history-preserving bisimilar** (`hpBisimilar_of_same`) when the
  independence of events is a property of event classes (`IndepInvariant`): histories related event by
  event have the same causal pasts (`past_congr`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Generic

open Interface (Frames Transport)
open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.HennessyMilner (Formula System)

universe uOb uTm uHm uO uSt uF uI uL

variable {Obj : Type uOb} {Tm : Obj → Type uTm} {Hom : Obj → Obj → Type uHm}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uSt} {Fir : State → Type uF}
  {L : Type uL}

/-! ## The labelled step -/

section Labelled

variable (P : Interface.Step X O State Fir) (offers : L → (s : State) → Fir s → Prop)

/-- **A labelled move**: an offered firing with label `ℓ` is admitted at `s`, and `t` is its
result. -/
def Moves (s : State) (ℓ : L) (t : State) : Prop :=
  ∃ (f : Fir s) (admitted : P.Admits f), offers ℓ s f ∧ t = P.result f admitted

/-- The step under a program, as a GSLT on states with discrete equations. -/
def gslt : GSLT where
  Term := State
  equations := ⟨Eq, eq_equivalence⟩
  rewrites s t := ∃ ℓ, Moves P offers s ℓ t
  rewrites_resp_left := by
    intro s s' t same step
    exact ⟨t, (same : s = s') ▸ step, rfl⟩
  rewrites_resp_right := by
    intro s t t' step same
    exact (same : t = t') ▸ step

/-- **The labelled step as a Hennessy–Milner system**, without atomic observations. -/
def system : System (gslt P offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := L
  act ℓ s t := Moves P offers s ℓ t
  act_resp_left := by
    intro ℓ s s' t same step
    exact ⟨t, (same : s = s') ▸ step, rfl⟩
  act_resp_right := by
    intro ℓ s t t' step same
    exact (same : t = t') ▸ step

/-- **Bisimilarity of the generic step.** -/
def Bisimilar (s t : State) : Prop := (system P offers).Bisimilar s t

/-- Hennessy–Milner satisfaction in the generic step. -/
def Sat (φ : Formula PEmpty.{1} L) (s : State) : Prop := (system P offers).sat φ s

/-- **Labels invariant under transport**: moving an offered firing along an isomorphism of states
offers it under the same label. -/
def Invariant (T : Transport P) : Prop :=
  ∀ ⦃s t : State⦄ (i : T.Iso s t) (ℓ : L) (f : Fir s), offers ℓ s f → offers ℓ t (T.move i f)

variable {P offers}

/-- **Transport-equivalent states are bisimilar.** -/
theorem bisimilar_of_same (T : Transport.{uOb, uTm, uHm, uO, uSt, uF, uI} P)
    (invariant : Invariant P offers T) {s t : State} (same : T.Same s t) : Bisimilar P offers s t := by
  refine ⟨T.Same, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, same⟩
  · rintro s t ⟨i⟩ ℓ s' ⟨f, admitted, offered, rfl⟩
    exact ⟨_, ⟨T.move i f, (T.admits_move i f).mpr admitted, invariant i ℓ f offered, rfl⟩,
      ⟨T.result_move i f admitted⟩⟩
  · rintro s t ⟨i⟩ ℓ t' ⟨g, admitted, offered, rfl⟩
    exact ⟨_, ⟨T.move (T.symm i) g, (T.admits_move (T.symm i) g).mpr admitted,
      invariant (T.symm i) ℓ g offered, rfl⟩, ⟨T.symm (T.result_move (T.symm i) g admitted)⟩⟩

/-- **Transport-equivalent states satisfy the same formulas.** -/
theorem sat_iff_of_same (T : Transport.{uOb, uTm, uHm, uO, uSt, uF, uI} P)
    (invariant : Invariant P offers T) {s t : State} (same : T.Same s t) (φ : Formula PEmpty.{1} L) :
    Sat P offers φ s ↔ Sat P offers φ t :=
  (system P offers).logicallyEquivalent_of_bisimilar (bisimilar_of_same T invariant same) φ

variable (P offers) in
/-- **Hennessy–Milner for the generic step**: when each label offers finitely many firings at each
state, bisimilarity is agreement on every formula. -/
theorem bisimilar_iff_sat (finite : ∀ ℓ s, {f : Fir s | offers ℓ s f}.Finite) (s t : State) :
    Bisimilar P offers s t ↔ ∀ φ : Formula PEmpty.{1} L, (Sat P offers φ s ↔ Sat P offers φ t) := by
  refine ((system P offers).logicallyEquivalent_iff_bisimilar ?_ s t).symm
  intro ℓ s
  classical
  refine ⟨(fun f : {f : Fir s // offers ℓ s f ∧ P.Admits f} => P.result f.1 f.2.2) '' Set.univ, ?_, ?_⟩
  · have : Finite {f : Fir s // offers ℓ s f ∧ P.Admits f} :=
      ((finite ℓ s).subset fun f member => member.1).to_subtype
    exact Set.finite_univ.image _
  · rintro t ⟨f, admitted, offered, rfl⟩
    exact ⟨_, ⟨⟨f, offered, admitted⟩, Set.mem_univ _, rfl⟩, rfl⟩

end Labelled

/-! ## Multi-firing steps -/

section Steps

variable (P : Interface.Step X O State Fir) (T : Transport.{uOb, uTm, uHm, uO, uSt, uF, uI} P)

/-- **A concurrent word at a state**: the first firing is admitted and independent of every later
one; the later ones, read as residuals after it, form a concurrent word at its result. `t` is the
state the word ends in. -/
inductive Concurrent : (s : State) → List (Fir s) → State → Prop
  | nil (s : State) : Concurrent s [] s
  | cons {s : State} (f : Fir s) (rest : List (Fir s)) (admitted : P.Admits f) {t : State}
      (independent : ∀ g ∈ rest, T.Independent s f g)
      (later : Concurrent (P.result f admitted) (rest.map (T.residual f admitted)) t) :
      Concurrent s (f :: rest) t

variable (offers : L → (s : State) → Fir s → Prop)

/-- **A multi-firing step**: a nonempty concurrent word of offered firings, labelled by the
multiset of their labels. -/
def StepMoves (s : State) (M : Multiset L) (t : State) : Prop :=
  ∃ w : List (L × Fir s), w ≠ [] ∧ (∀ x ∈ w, offers x.1 s x.2) ∧
    Concurrent P T s (w.map Prod.snd) t ∧ M = (↑(w.map Prod.fst) : Multiset L)

/-- The step moves as a Hennessy–Milner system. -/
def stepSystem : System (gslt P offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Multiset L
  act M s t := StepMoves P T offers s M t
  act_resp_left := by
    intro M s s' t same step
    exact ⟨t, (same : s = s') ▸ step, rfl⟩
  act_resp_right := by
    intro M s t t' step same
    exact (same : t = t') ▸ step

/-- **Step bisimilarity of the generic step.** -/
def StepBisimilar (s t : State) : Prop := (stepSystem P T offers).Bisimilar s t

variable {P T offers}

theorem concurrent_singleton_iff {s t : State} {f : Fir s} :
    Concurrent P T s [f] t ↔ ∃ admitted : P.Admits f, t = P.result f admitted := by
  constructor
  · intro concurrent
    cases concurrent with
    | cons _ _ admitted _ later =>
        cases later
        exact ⟨admitted, rfl⟩
  · rintro ⟨admitted, rfl⟩
    exact .cons f [] admitted (fun _ member => absurd member List.not_mem_nil) (.nil _)

theorem concurrent_nil_iff {s t : State} : Concurrent P T s [] t ↔ t = s := by
  constructor
  · intro concurrent
    cases concurrent
    rfl
  · rintro rfl
    exact .nil _

theorem concurrent_cons_iff {s t : State} {f : Fir s} {rest : List (Fir s)} :
    Concurrent P T s (f :: rest) t ↔ ∃ admitted : P.Admits f, (∀ g ∈ rest, T.Independent s f g) ∧
      Concurrent P T (P.result f admitted) (rest.map (T.residual f admitted)) t := by
  constructor
  · intro concurrent
    cases concurrent with
    | cons _ _ admitted independent later => exact ⟨admitted, independent, later⟩
  · rintro ⟨admitted, independent, later⟩
    exact .cons f rest admitted independent later

/-- **A step of one firing is a move.** -/
theorem stepMoves_singleton_iff {s t : State} {ℓ : L} :
    StepMoves P T offers s {ℓ} t ↔ Moves P offers s ℓ t := by
  constructor
  · rintro ⟨w, _, offered, concurrent, labels⟩
    have length : (w.map Prod.fst).length = 1 := by
      have := congrArg Multiset.card labels
      simpa using this.symm
    rw [List.length_map] at length
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp length
    have same : ℓ = x.1 := by simpa using labels
    subst same
    obtain ⟨admitted, rfl⟩ := concurrent_singleton_iff.mp concurrent
    exact ⟨x.2, admitted, offered x (List.mem_singleton_self _), rfl⟩
  · rintro ⟨f, admitted, offered, rfl⟩
    refine ⟨[(ℓ, f)], List.cons_ne_nil _ _, ?_, concurrent_singleton_iff.mpr ⟨admitted, rfl⟩,
      (Multiset.coe_singleton ℓ).symm⟩
    intro x member
    rw [List.mem_singleton.mp member]
    exact offered

/-- **Step bisimilarity implies bisimilarity.** -/
theorem bisimilar_of_stepBisimilar {s t : State} (bisimilar : StepBisimilar P T offers s t) :
    Bisimilar P offers s t := by
  obtain ⟨R, ⟨forward, backward, _⟩, related⟩ := bisimilar
  refine ⟨R, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related⟩
  · intro s t related ℓ s' moved
    obtain ⟨t', stepped, related'⟩ := forward related ({ℓ} : Multiset L)
      (stepMoves_singleton_iff.mpr moved)
    exact ⟨t', stepMoves_singleton_iff.mp stepped, related'⟩
  · intro s t related ℓ t' moved
    obtain ⟨s', stepped, related'⟩ := backward related ({ℓ} : Multiset L)
      (stepMoves_singleton_iff.mpr moved)
    exact ⟨s', stepMoves_singleton_iff.mp stepped, related'⟩

variable (T) in
/-- **Independence is transported along isomorphisms of states**, by naturality of residuals. -/
theorem independent_move {s s' : State} (i : T.Iso s s') {f g : Fir s}
    (independent : T.Independent s f g) : T.Independent s' (T.move i f) (T.move i g) := by
  obtain ⟨af, ag, afg, agf, ⟨close⟩⟩ := independent
  have af' : P.Admits (T.move i f) := (T.admits_move i f).mpr af
  have ag' : P.Admits (T.move i g) := (T.admits_move i g).mpr ag
  have alikeFG := T.move_residual i f af g
  have alikeGF := T.move_residual i g ag f
  have movedFG := (T.admits_move (T.result_move i f af) (T.residual f af g)).mpr afg
  have movedGF := (T.admits_move (T.result_move i g ag) (T.residual g ag f)).mpr agf
  have afg' : P.Admits (T.residual (T.move i f) af' (T.move i g)) :=
    (T.admits_alike alikeFG).mp movedFG
  have agf' : P.Admits (T.residual (T.move i g) ag' (T.move i f)) :=
    (T.admits_alike alikeGF).mp movedGF
  exact ⟨af', ag', afg', agf', ⟨T.trans (T.result_alike alikeFG.symm afg' movedFG)
    (T.trans (T.symm (T.result_move (T.result_move i f af) (T.residual f af g) afg))
      (T.trans close (T.trans (T.result_move (T.result_move i g ag) (T.residual g ag f) agf)
        (T.result_alike alikeGF movedGF agf'))))⟩⟩

/-- **Concurrent words are transported** along isomorphisms of their start, for strict
transports. -/
theorem concurrent_move (strict : ∀ {s : State} {f f' : Fir s}, T.Alike f f' ↔ f = f')
    {s : State} {fs : List (Fir s)} {t : State} (concurrent : Concurrent P T s fs t) :
    ∀ {s' : State} (i : T.Iso s s'), ∃ t', Concurrent P T s' (fs.map (T.move i)) t' ∧ T.Same t t' := by
  induction concurrent with
  | nil s =>
      intro s' i
      exact ⟨s', .nil s', ⟨i⟩⟩
  | cons f rest admitted independent later ih =>
      intro s' i
      have admitted' : P.Admits (T.move i f) := (T.admits_move i f).mpr admitted
      obtain ⟨t', later', same⟩ := ih (T.result_move i f admitted)
      refine ⟨t', .cons (T.move i f) (rest.map (T.move i)) admitted' ?_ ?_, same⟩
      · intro g' member
        obtain ⟨g, inRest, rfl⟩ := List.mem_map.mp member
        exact independent_move T i (independent g inRest)
      · have residuals : (rest.map (T.residual f admitted)).map (T.move (T.result_move i f admitted)) =
            (rest.map (T.move i)).map (T.residual (T.move i f) admitted') := by
          rw [List.map_map, List.map_map]
          exact List.map_congr_left fun g _ => strict.mp (T.move_residual i f admitted g)
        rw [residuals] at later'
        exact later'

/-- A labelled word moved along an isomorphism. -/
def moveWord {s s' : State} (i : T.Iso s s') (w : List (L × Fir s)) : List (L × Fir s') :=
  w.map fun x => (x.1, T.move i x.2)

theorem moveWord_snd {s s' : State} (i : T.Iso s s') (w : List (L × Fir s)) :
    (moveWord i w).map Prod.snd = (w.map Prod.snd).map (T.move i) := by
  unfold moveWord
  rw [List.map_map, List.map_map]
  rfl

theorem moveWord_fst {s s' : State} (i : T.Iso s s') (w : List (L × Fir s)) :
    (moveWord i w).map Prod.fst = w.map Prod.fst := by
  unfold moveWord
  rw [List.map_map]
  rfl

theorem step_move (strict : ∀ {s : State} {f f' : Fir s}, T.Alike f f' ↔ f = f')
    (invariant : Invariant P offers T) {s s' t : State} (i : T.Iso s s') {M : Multiset L}
    (stepped : StepMoves P T offers s M t) :
    ∃ t', StepMoves P T offers s' M t' ∧ T.Same t t' := by
  obtain ⟨w, nonempty, offered, concurrent, rfl⟩ := stepped
  obtain ⟨t', concurrent', same⟩ := concurrent_move strict concurrent i
  refine ⟨t', ⟨moveWord i w, ?_, ?_, ?_, ?_⟩, same⟩
  · intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  · intro x member
    obtain ⟨y, inW, rfl⟩ := List.mem_map.mp member
    exact invariant i y.1 y.2 (offered y inW)
  · rw [moveWord_snd]
    exact concurrent'
  · rw [moveWord_fst]

/-- **Transport-equivalent states are step bisimilar**, for strict transports. -/
theorem stepBisimilar_of_same (strict : ∀ {s : State} {f f' : Fir s}, T.Alike f f' ↔ f = f')
    (invariant : Invariant P offers T) {s t : State} (same : T.Same s t) :
    StepBisimilar P T offers s t := by
  refine ⟨T.Same, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, same⟩
  · rintro s t ⟨i⟩ M s' stepped
    exact step_move strict invariant i stepped
  · rintro s t ⟨i⟩ M t' stepped
    obtain ⟨s', stepped', same'⟩ := step_move strict invariant (T.symm i) stepped
    exact ⟨s', stepped', same'.symm⟩

end Steps

/-! ## Histories -/

section Histories

variable (State Fir) in
/-- An event: a firing at the state it fired at. -/
abbrev Event := (s : State) × Fir s

variable (State Fir) in
/-- The events of a run so far, each with the positions of its causal past. -/
abbrev History := List (Event State Fir × Finset ℕ)

variable (indep : Event State Fir → Event State Fir → Prop)

/-- **Direct dependence**: the positions of earlier events not independent of `e`. -/
noncomputable def directPast (h : History State Fir) (e : Event State Fir) : Finset ℕ := by
  classical
  exact (Finset.range h.length).filter fun i => ∃ x, h[i]? = some x ∧ ¬ indep x.1 e

/-- **The causal past**: direct dependences, closed under their recorded pasts. -/
noncomputable def past (h : History State Fir) (e : Event State Fir) : Finset ℕ :=
  directPast indep h e ∪ (directPast indep h e).biUnion fun i => (h[i]?.map Prod.snd).getD ∅

theorem mem_directPast {h : History State Fir} {e : Event State Fir} {i : ℕ} :
    i ∈ directPast indep h e ↔ i < h.length ∧ ∃ x, h[i]? = some x ∧ ¬ indep x.1 e := by
  classical
  unfold directPast
  rw [Finset.mem_filter, Finset.mem_range]

variable (P : Interface.Step X O State Fir) (offers : L → (s : State) → Fir s → Prop)

/-- **A history move**: an offered firing admitted at the state, labelled by its label and its
causal past, appended to the history as an event. -/
def HMoves (x : State × History State Fir) (lab : L × Finset ℕ) (y : State × History State Fir) :
    Prop :=
  ∃ (f : Fir x.1) (admitted : P.Admits f), offers lab.1 x.1 f ∧ lab.2 = past indep x.2 ⟨x.1, f⟩ ∧
    y = (P.result f admitted, x.2 ++ [(⟨x.1, f⟩, lab.2)])

/-- States with histories, with discrete equations. -/
def histGslt : GSLT where
  Term := State × History State Fir
  equations := ⟨Eq, eq_equivalence⟩
  rewrites x y := ∃ lab, HMoves indep P offers x lab y
  rewrites_resp_left := by
    intro x x' y same step
    exact ⟨y, (same : x = x') ▸ step, rfl⟩
  rewrites_resp_right := by
    intro x y y' step same
    exact (same : y = y') ▸ step

/-- History moves as a Hennessy–Milner system. -/
def histSystem : System (histGslt indep P offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := L × Finset ℕ
  act lab x y := HMoves indep P offers x lab y
  act_resp_left := by
    intro lab x x' y same step
    exact ⟨y, (same : x = x') ▸ step, rfl⟩
  act_resp_right := by
    intro lab x y y' step same
    exact (same : y = y') ▸ step

/-- **History-preserving bisimilarity of the generic step**: the empty histories are bisimilar for
history moves. -/
def HPBisimilar (s t : State) : Prop := (histSystem indep P offers).Bisimilar (s, []) (t, [])

variable {P}
variable (T : Transport.{uOb, uTm, uHm, uO, uSt, uF, uI} P)

/-- **Events of one class**: an isomorphism of their states moves the first to a firing alike to the
second. -/
def EventSame (a b : Event State Fir) : Prop := ∃ i : T.Iso a.1 b.1, T.Alike (T.move i a.2) b.2

/-- **An independence of events that is a property of event classes.** -/
def IndepInvariant : Prop :=
  ∀ ⦃a a' b b' : Event State Fir⦄, EventSame T a a' → EventSame T b b' → (indep a b ↔ indep a' b')

variable {T}

theorem EventSame.symm {a b : Event State Fir} (same : EventSame T a b) : EventSame T b a := by
  obtain ⟨i, alike⟩ := same
  exact ⟨T.symm i, (T.move_alike (T.symm i) alike.symm).trans (T.move_symm i a.2)⟩

theorem EventSame.move {s s' : State} (i : T.Iso s s') (f : Fir s) :
    EventSame T ⟨s, f⟩ ⟨s', T.move i f⟩ :=
  ⟨i, Transport.Alike.refl _⟩

/-- Histories related event by event: events of one class with the same recorded pasts. -/
def HistorySame (h h' : History State Fir) : Prop :=
  List.Forall₂ (fun a b => EventSame T a.1 b.1 ∧ a.2 = b.2) h h'

theorem forall₂_getElem? {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i : ℕ, Option.Rel R l₁[i]? l₂[i]?
  | _, _, .nil, i => by
      rw [List.getElem?_nil, List.getElem?_nil]
      exact .none
  | _, _, .cons related _, 0 => by
      rw [List.getElem?_cons_zero, List.getElem?_cons_zero]
      exact .some related
  | _, _, .cons _ rest, i + 1 => by
      rw [List.getElem?_cons_succ, List.getElem?_cons_succ]
      exact forall₂_getElem? rest i

variable {indep}

/-- **Related histories give the same causal pasts** to firings of one class. -/
theorem past_congr (invariant : IndepInvariant indep T) {h h' : History State Fir}
    (related : HistorySame (T := T) h h') {e e' : Event State Fir} (same : EventSame T e e') :
    past indep h e = past indep h' e' := by
  have length : h.length = h'.length := related.length_eq
  have direct : directPast indep h e = directPast indep h' e' := by
    ext i
    rw [mem_directPast, mem_directPast, length]
    have rel := forall₂_getElem? related i
    constructor
    · rintro ⟨lt, x, get, dependent⟩
      rw [get] at rel
      rcases get' : h'[i]? with _ | y
      · rw [get'] at rel
        cases rel
      · rw [get'] at rel
        cases rel with
        | some r => exact ⟨lt, y, rfl, fun ind => dependent ((invariant r.1 same).mpr ind)⟩
    · rintro ⟨lt, y, get', dependent⟩
      rw [get'] at rel
      rcases get : h[i]? with _ | x
      · rw [get] at rel
        cases rel
      · rw [get] at rel
        cases rel with
        | some r => exact ⟨lt, x, rfl, fun ind => dependent ((invariant r.1 same).mp ind)⟩
  unfold past
  rw [direct]
  congr 1
  refine Finset.biUnion_congr rfl fun i _ => ?_
  have rel := forall₂_getElem? related i
  rcases get : h[i]? with _ | x <;> rcases get' : h'[i]? with _ | y <;> rw [get, get'] at rel <;>
    first
    | rfl
    | (cases rel with | some r => simp [r.2])
    | cases rel

variable {offers}

theorem hist_forward (invariant : Invariant P offers T) (indepInvariant : IndepInvariant indep T)
    {x y : State × History State Fir} (rel : T.Same x.1 y.1 ∧ HistorySame (T := T) x.2 y.2)
    {lab : L × Finset ℕ} {x' : State × History State Fir} (moved : HMoves indep P offers x lab x')
    (i : T.Iso x.1 y.1) :
    ∃ y', HMoves indep P offers y lab y' ∧ T.Same x'.1 y'.1 ∧ HistorySame (T := T) x'.2 y'.2 := by
  obtain ⟨f, admitted, offered, labelled, rfl⟩ := moved
  have samePast : past indep y.2 ⟨y.1, T.move i f⟩ = lab.2 :=
    labelled ▸ (past_congr indepInvariant rel.2 (EventSame.move i f)).symm
  refine ⟨(P.result (T.move i f) ((T.admits_move i f).mpr admitted),
      y.2 ++ [(⟨y.1, T.move i f⟩, lab.2)]),
    ⟨T.move i f, (T.admits_move i f).mpr admitted, invariant i lab.1 f offered, samePast.symm, rfl⟩,
    ⟨T.result_move i f admitted⟩, ?_⟩
  exact List.rel_append rel.2 (.cons ⟨EventSame.move i f, rfl⟩ .nil)

/-- **Transport-equivalent states are history-preserving bisimilar** when the program's labels and
its independence of events are invariant under transport. -/
theorem hpBisimilar_of_same (invariant : Invariant P offers T) (indepInvariant : IndepInvariant indep T)
    {s t : State} (same : T.Same s t) : HPBisimilar indep P offers s t := by
  refine ⟨fun x y => T.Same x.1 y.1 ∧ HistorySame (T := T) x.2 y.2, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩,
    same, .nil⟩
  · rintro x y rel lab x' moved
    obtain ⟨i⟩ := rel.1
    exact hist_forward invariant indepInvariant rel moved i
  · rintro x y rel lab y' moved
    obtain ⟨i⟩ := rel.1
    have flipped : T.Same y.1 x.1 ∧ HistorySame (T := T) y.2 x.2 :=
      ⟨rel.1.symm, List.Forall₂.flip (rel.2.imp fun _ _ r => ⟨r.1.symm, r.2.symm⟩)⟩
    obtain ⟨x', moved', same', hist'⟩ := hist_forward invariant indepInvariant flipped moved (T.symm i)
    exact ⟨x', moved', same'.symm, List.Forall₂.flip (hist'.imp fun _ _ r => ⟨r.1.symm, r.2.symm⟩)⟩

end Histories

#print axioms bisimilar_of_same
#print axioms sat_iff_of_same
#print axioms bisimilar_iff_sat
#print axioms stepMoves_singleton_iff
#print axioms bisimilar_of_stepBisimilar
#print axioms independent_move
#print axioms concurrent_move
#print axioms stepBisimilar_of_same
#print axioms past_congr
#print axioms hpBisimilar_of_same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Generic
