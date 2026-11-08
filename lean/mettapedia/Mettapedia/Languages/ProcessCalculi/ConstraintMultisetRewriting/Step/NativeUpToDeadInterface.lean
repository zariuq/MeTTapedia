import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceGeneric
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulTransport

/-!
# Transport up to dead names: the interface

The interface's `Transport` moves firings along isomorphisms of states (`Step.StateIso`), and its
`move` is total. Native diamonds close only up to **dead names**: the two composite states are one
state seen through two inclusions that miss names nothing mentions, and a firing at the larger state
that mentions a missed name is the carrying of no firing at the smaller (`Step/NativeUpToDeadObstruction`,
`carrying_not_surjective`). So a total `move` up to dead names is impossible. This module gives the
interface's notions up to dead names, without editing the existing ones.

## Inclusions and transport

* **An inclusion of states** (`Step.StateIncl`): a morphism of frames, with no inverse, carrying the
  knowledge to knowledge with the same solutions, and a renaming of occurrences carrying the present
  occurrences. Every isomorphism of states is one (`Step.StateIso.toIncl`); the smaller state's
  knowledge is solvable when the larger's is (`StateIncl.solvable_of`).
* **Transport up to dead names** (`DeadTransport`): chosen inclusions, closed under identity and
  composition, with an amalgamation of every two inclusions of one state, and a relation `Carries e f
  g`: `g` at the larger state is `f` carried along `e`. Carried firings select the renamed
  occurrences, are admitted together, and have results that agree up to dead names.
* **Agreement up to dead names** (`DeadTransport.Same`): two states included in one state. It is an
  equivalence relation (`Same.refl`, `Same.symm`, `Same.trans`, by amalgamation).
* **The partial move** (`DeadTransport.Moves`): along agreement `s ↪ u ↩ t`, a firing `f` at `s` moves
  to `g` at `t` when both carry to one firing at `u`. It is defined exactly on the firings whose
  carrying is **over the core** of `t` (`DeadTransport.Over`): carried from `t`.
* **Every transport is one** (`Transport.toDead`): isomorphisms are inclusions, `Carries` is moving up
  to alikeness, and agreement is isomorphism (`Transport.toDead_same_iff`).

## The races layer up to dead names

* **Agreeing states are bisimilar** (`DeadTransport.bisimilar_of_same`) for every program that offers
  exactly the carried firings along every inclusion (`DeadTransport.Invariant`), and satisfy the same
  Hennessy–Milner formulas (`DeadTransport.sat_iff_of_same`).
* **Residuals and independence up to dead names** (`DeadTransport.Residuals`, `Independent`): the
  diamond closes up to agreement.
* **Multi-firing steps** (`Concurrent`, `StepMoves`, `StepBisimilar`): a concurrent word fires its
  first firing, independent of every later one, and the residuals of the rest. A step of one firing
  is a move (`stepMoves_singleton_iff`), so step bisimilarity implies bisimilarity.
* **Agreeing states are step bisimilar** (`stepBisimilar_of_same`), for every invariant program, when
  concurrent words carry along inclusions in both directions (`CarriesWords`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.GSLT.HennessyMilner (Formula System)

universe uOb uTm uHm uO uSt uF uI uL

variable {Obj : Type uOb} {Tm : Obj → Type uTm} {Hom : Obj → Obj → Type uHm}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uSt} {Fir : State → Type uF}

namespace Step

variable (P : Step X O State Fir)

/-- **An inclusion of states, as the interface sees it**: a morphism of their frames that carries the
knowledge of the first to knowledge with the same solutions as the second's, and a renaming of
occurrence identities that carries the present occurrences of the first to those of the second. It
has no inverse: the names it misses are the larger state's dead names. -/
structure StateIncl (s u : State) where
  frame : Hom (P.frame s) (P.frame u)
  knowledge : X.Equivalent (X.applyStore frame (P.knowledge s)) (P.knowledge u)
  rename : O ≃ O
  present : (P.present s).map rename.toEmbedding = P.present u

variable {P}

/-- **Every isomorphism of states is an inclusion.** -/
def StateIso.toIncl {s t : State} (i : P.StateIso s t) : P.StateIncl s t :=
  ⟨i.frame.hom, i.knowledge, i.rename, i.present⟩

/-- The identity inclusion. -/
def StateIncl.refl (s : State) : P.StateIncl s s := (StateIso.refl s).toIncl

/-- The smaller state's knowledge is solvable when the larger's is. -/
theorem StateIncl.solvable_of {s u : State} (i : P.StateIncl s u) (solvable : X.Solvable (P.knowledge u)) :
    X.Solvable (P.knowledge s) :=
  Frames.solvable_of_applyStore i.frame ((Frames.Equivalent.solvable_iff i.knowledge).mpr solvable)

/-- Inclusions carry membership of present occurrences. -/
theorem StateIncl.mem_present_iff {s u : State} (i : P.StateIncl s u) (o : O) :
    i.rename o ∈ P.present u ↔ o ∈ P.present s := by
  rw [← i.present, Finset.mem_map_equiv, Equiv.symm_apply_apply]

end Step

/-- **Transport up to dead names.** An instance chooses its inclusions of states over the interface's,
closed under identity and composition, with an amalgamation of every two inclusions of one state. It
chooses which firing at the larger state is a given firing **carried** along an inclusion. Carried
firings select the renamed occurrences, are admitted together, and have results that agree up to dead
names: both included in one state. -/
structure DeadTransport (P : Step X O State Fir) where
  Incl : State → State → Type uI
  toStateIncl : {s u : State} → Incl s u → P.StateIncl s u
  refl : (s : State) → Incl s s
  comp : {s u w : State} → Incl s u → Incl u w → Incl s w
  /-- Two inclusions of one state amalgamate. -/
  amalgamate : ∀ {t u v : State}, Incl t u → Incl t v → ∃ w, Nonempty (Incl u w) ∧ Nonempty (Incl v w)
  /-- `Carries e f g`: the firing `g` at the larger state is `f` carried along `e`. -/
  Carries : {s u : State} → Incl s u → Fir s → Fir u → Prop
  carries_comp : ∀ {s u w : State} {e : Incl s u} {e' : Incl u w} {f : Fir s} {g : Fir u} {h : Fir w},
    Carries e f g → Carries e' g h → Carries (comp e e') f h
  selection_carries : ∀ {s u : State} {e : Incl s u} {f : Fir s} {g : Fir u}, Carries e f g →
    P.selection g = AnnotatedRuns.renameSelection (toStateIncl e).rename (P.selection f)
  admits_carries : ∀ {s u : State} {e : Incl s u} {f : Fir s} {g : Fir u}, Carries e f g →
    (P.Admits f ↔ P.Admits g)
  result_carries : ∀ {s u : State} {e : Incl s u} {f : Fir s} {g : Fir u}, Carries e f g →
    (admitted : P.Admits f) → (admitted' : P.Admits g) →
      ∃ w, Nonempty (Incl (P.result f admitted) w) ∧ Nonempty (Incl (P.result g admitted') w)

namespace DeadTransport

variable {P : Step X O State Fir} (T : DeadTransport.{uOb, uTm, uHm, uO, uSt, uF, uI} P)

/-! ## Agreement up to dead names -/

/-- **Two states agree up to dead names**: both are included in one state. -/
def Same (s t : State) : Prop := ∃ u, Nonempty (T.Incl s u) ∧ Nonempty (T.Incl t u)

variable {T}

theorem Same.refl (s : State) : T.Same s s := ⟨s, ⟨T.refl s⟩, ⟨T.refl s⟩⟩

theorem Same.symm {s t : State} (same : T.Same s t) : T.Same t s := by
  obtain ⟨u, first, second⟩ := same
  exact ⟨u, second, first⟩

theorem Same.of_incl {s u : State} (e : T.Incl s u) : T.Same s u := ⟨u, ⟨e⟩, ⟨T.refl u⟩⟩

/-- **Agreement up to dead names is transitive**: the two common states amalgamate. -/
theorem Same.trans {s t w : State} (first : T.Same s t) (second : T.Same t w) : T.Same s w := by
  obtain ⟨u, ⟨su⟩, ⟨tu⟩⟩ := first
  obtain ⟨v, ⟨tv⟩, ⟨wv⟩⟩ := second
  obtain ⟨p, ⟨up⟩, ⟨vp⟩⟩ := T.amalgamate tu tv
  exact ⟨p, ⟨T.comp su up⟩, ⟨T.comp wv vp⟩⟩

variable (T) in
/-- Agreement up to dead names, as a setoid. -/
def setoid : Setoid State := ⟨T.Same, ⟨Same.refl, Same.symm, Same.trans⟩⟩

/-- Carried firings have results that agree up to dead names. -/
theorem same_result {s u : State} {e : T.Incl s u} {f : Fir s} {g : Fir u} (carries : T.Carries e f g)
    (admitted : P.Admits f) (admitted' : P.Admits g) : T.Same (P.result f admitted) (P.result g admitted') :=
  T.result_carries carries admitted admitted'

/-! ## The partial move -/

variable (T) in
/-- **A firing at the larger state is over the core** of the smaller state: it is the carrying of a
firing there. -/
def Over {s u : State} (e : T.Incl s u) (g : Fir u) : Prop := ∃ f, T.Carries e f g

variable (T) in
/-- **The partial move along agreement** `s ↪ u ↩ t`: `f` at `s` moves to `g` at `t` when both carry
to one firing at `u`. -/
def Moves {s t u : State} (e : T.Incl s u) (e' : T.Incl t u) (f : Fir s) (g : Fir t) : Prop :=
  ∃ h, T.Carries e f h ∧ T.Carries e' g h

/-- **The partial move is defined exactly on firings whose carrying is over the core** of the other
state. -/
theorem moves_iff_over {s t u : State} (e : T.Incl s u) (e' : T.Incl t u) (f : Fir s) :
    (∃ g, T.Moves e e' f g) ↔ ∃ h, T.Carries e f h ∧ T.Over e' h :=
  ⟨fun ⟨g, h, carried, carried'⟩ => ⟨h, carried, g, carried'⟩,
    fun ⟨h, carried, g, carried'⟩ => ⟨g, h, carried, carried'⟩⟩

/-- **A moved firing is admitted exactly when the firing is, and their results agree up to dead
names.** -/
theorem Moves.admits {s t u : State} {e : T.Incl s u} {e' : T.Incl t u} {f : Fir s} {g : Fir t}
    (moved : T.Moves e e' f g) :
    (P.Admits f ↔ P.Admits g) ∧ ∀ (admitted : P.Admits f) (admitted' : P.Admits g),
      T.Same (P.result f admitted) (P.result g admitted') := by
  obtain ⟨h, carried, carried'⟩ := moved
  refine ⟨(T.admits_carries carried).trans (T.admits_carries carried').symm, fun admitted admitted' => ?_⟩
  have middle := (T.admits_carries carried).mp admitted
  exact (same_result carried admitted middle).trans (same_result carried' admitted' middle).symm

/-! ## Every transport is a transport up to dead names -/

end DeadTransport

namespace Transport

variable {P : Step X O State Fir} (T : Transport.{uOb, uTm, uHm, uO, uSt, uF, uI} P)

/-- **Every transport is a transport up to dead names**: its isomorphisms are inclusions, a firing is
carried to every firing alike to its move, and two inclusions of one state amalgamate at the second
state. -/
def toDead : DeadTransport.{uOb, uTm, uHm, uO, uSt, uF, uI} P where
  Incl := T.Iso
  toStateIncl i := (T.toStateIso i).toIncl
  refl := T.refl
  comp := T.trans
  amalgamate tu tv := ⟨_, ⟨T.trans (T.symm tu) tv⟩, ⟨T.refl _⟩⟩
  Carries i f g := T.Alike (T.move i f) g
  carries_comp {_ _ _ i j f _ _} first second := (T.move_trans i j f).trans ((T.move_alike j first).trans second)
  selection_carries {_ _ i f _} alike := (T.selection_alike alike).symm.trans (T.selection_move i f)
  admits_carries {_ _ i f _} alike := (T.admits_move i f).symm.trans (T.admits_alike alike)
  result_carries {_ _ i f _} alike admitted admitted' :=
    ⟨_, ⟨T.trans (T.result_move i f admitted) (T.result_alike alike _ admitted')⟩, ⟨T.refl _⟩⟩

/-- **Up to dead names, a transport's agreement is its isomorphism of states.** -/
theorem toDead_same_iff {s t : State} : T.toDead.Same s t ↔ T.Same s t := by
  constructor
  · rintro ⟨u, ⟨i⟩, ⟨j⟩⟩
    exact ⟨T.trans i (T.symm j)⟩
  · rintro ⟨i⟩
    exact ⟨t, ⟨i⟩, ⟨T.refl t⟩⟩

end Transport

/-! ## The races layer up to dead names -/

namespace DeadTransport

variable {L : Type uL} {P : Step X O State Fir} (T : DeadTransport.{uOb, uTm, uHm, uO, uSt, uF, uI} P)
  (offers : L → (s : State) → Fir s → Prop)

/-- **A program that does not see dead names**: along every inclusion it offers the carryings of
its firings, and every firing it offers at the larger state is the carrying of one it offers at the
smaller. -/
def Invariant : Prop :=
  ∀ ⦃s u : State⦄ (e : T.Incl s u) (ℓ : L),
    (∀ f, offers ℓ s f → ∃ g, T.Carries e f g ∧ offers ℓ u g) ∧
      ∀ g, offers ℓ u g → ∃ f, offers ℓ s f ∧ T.Carries e f g

variable {T offers}

/-- One direction of the bisimulation: a move of `s` is matched by `t`. -/
theorem match_move (invariant : T.Invariant offers) {s t u : State} (e : T.Incl s u) (e' : T.Incl t u)
    {ℓ : L} {s' : State} (moved : Race.Generic.Moves P offers s ℓ s') :
    ∃ t', Race.Generic.Moves P offers t ℓ t' ∧ T.Same s' t' := by
  obtain ⟨f, admitted, offered, rfl⟩ := moved
  obtain ⟨h, carried, offeredH⟩ := (invariant e ℓ).1 f offered
  obtain ⟨g, offeredG, carried'⟩ := (invariant e' ℓ).2 h offeredH
  obtain ⟨admits, results⟩ := Moves.admits (T := T) ⟨h, carried, carried'⟩
  exact ⟨_, ⟨g, admits.mp admitted, offeredG, rfl⟩, results admitted (admits.mp admitted)⟩

/-- **States that agree up to dead names are bisimilar**, for every program that does not see dead
names. -/
theorem bisimilar_of_same (invariant : T.Invariant offers) {s t : State} (same : T.Same s t) :
    Race.Generic.Bisimilar P offers s t := by
  refine ⟨T.Same, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, same⟩
  · rintro s t ⟨u, ⟨e⟩, ⟨e'⟩⟩ ℓ s' moved
    exact match_move invariant e e' moved
  · rintro s t ⟨u, ⟨e⟩, ⟨e'⟩⟩ ℓ t' moved
    obtain ⟨s', moved', related⟩ := match_move invariant e' e moved
    exact ⟨s', moved', related.symm⟩

/-- **States that agree up to dead names satisfy the same Hennessy–Milner formulas.** -/
theorem sat_iff_of_same (invariant : T.Invariant offers) {s t : State} (same : T.Same s t)
    (φ : Formula PEmpty.{1} L) : Race.Generic.Sat P offers φ s ↔ Race.Generic.Sat P offers φ t :=
  (Race.Generic.system P offers).logicallyEquivalent_of_bisimilar (bisimilar_of_same invariant same) φ

end DeadTransport

/-! ## Residuals, independence and multi-firing steps up to dead names -/

namespace DeadTransport

variable {L : Type uL} {P : Step X O State Fir}

/-- **Residuals up to dead names**: which firing at an admitted firing's result is the residual of a
firing at the state. A residual keeps its selection. -/
structure Residuals (T : DeadTransport.{uOb, uTm, uHm, uO, uSt, uF, uI} P) where
  Residual : {s : State} → (g : Fir s) → (admitted : P.Admits g) → Fir s → Fir (P.result g admitted) → Prop
  selection_residual : ∀ {s : State} {g : Fir s} {admitted : P.Admits g} {f : Fir s}
    {r : Fir (P.result g admitted)}, Residual g admitted f r → P.selection r = P.selection f

variable {T : DeadTransport.{uOb, uTm, uHm, uO, uSt, uF, uI} P}

/-- **Independence up to dead names**: both firings are admitted, each has a residual after the other
that is admitted, and the two composites agree up to dead names. -/
def Independent (R : T.Residuals) {s : State} (f g : Fir s) : Prop :=
  ∃ (first : P.Admits f) (second : P.Admits g) (g' : Fir (P.result f first)) (f' : Fir (P.result g second)),
    R.Residual f first g g' ∧ R.Residual g second f f' ∧
      ∃ (afterFirst : P.Admits g') (afterSecond : P.Admits f'),
        T.Same (P.result g' afterFirst) (P.result f' afterSecond)

theorem Independent.symm {R : T.Residuals} {s : State} {f g : Fir s} (independent : Independent R f g) :
    Independent R g f := by
  obtain ⟨first, second, g', f', residualG, residualF, afterFirst, afterSecond, same⟩ := independent
  exact ⟨second, first, f', g', residualF, residualG, afterSecond, afterFirst, same.symm⟩

/-- **A concurrent word up to dead names**: the first firing is admitted and independent of every
later one; residuals of the later ones form a concurrent word at its result. -/
inductive Concurrent (R : T.Residuals) : (s : State) → List (Fir s) → State → Prop
  | nil (s : State) : Concurrent R s [] s
  | cons {s : State} (f : Fir s) (rest : List (Fir s)) (admitted : P.Admits f)
      (residuals : List (Fir (P.result f admitted))) (residual : List.Forall₂ (R.Residual f admitted) rest residuals)
      (independent : ∀ g ∈ rest, Independent R f g) {t : State}
      (later : Concurrent R (P.result f admitted) residuals t) : Concurrent R s (f :: rest) t

/-- **A multi-firing step up to dead names**: a nonempty concurrent word of offered firings, labelled
by the multiset of their labels. -/
def StepMoves (R : T.Residuals) (offers : L → (s : State) → Fir s → Prop) (s : State) (M : Multiset L)
    (t : State) : Prop :=
  ∃ w : List (L × Fir s), w ≠ [] ∧ (∀ x ∈ w, offers x.1 s x.2) ∧ Concurrent R s (w.map Prod.snd) t ∧
    M = (↑(w.map Prod.fst) : Multiset L)

/-- The multi-firing steps as a Hennessy–Milner system. -/
def stepSystem (R : T.Residuals) (offers : L → (s : State) → Fir s → Prop) :
    System (Race.Generic.gslt P offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Multiset L
  act M s t := StepMoves R offers s M t
  act_resp_left := by
    intro M s s' t same step
    exact ⟨t, (same : s = s') ▸ step, rfl⟩
  act_resp_right := by
    intro M s t t' step same
    exact (same : t = t') ▸ step

/-- **Step bisimilarity up to dead names.** -/
def StepBisimilar (R : T.Residuals) (offers : L → (s : State) → Fir s → Prop) (s t : State) : Prop :=
  (stepSystem R offers).Bisimilar s t

variable {R : T.Residuals} {offers : L → (s : State) → Fir s → Prop}

theorem concurrent_singleton_iff {s t : State} {f : Fir s} :
    Concurrent R s [f] t ↔ ∃ admitted : P.Admits f, t = P.result f admitted := by
  constructor
  · intro concurrent
    cases concurrent with
    | cons _ _ admitted residuals residual _ later =>
        cases residual
        cases later
        exact ⟨admitted, rfl⟩
  · rintro ⟨admitted, rfl⟩
    exact .cons f [] admitted [] .nil (fun _ member => absurd member List.not_mem_nil) (.nil _)

/-- **A step of one firing is a move.** -/
theorem stepMoves_singleton_iff {s t : State} {ℓ : L} :
    StepMoves R offers s {ℓ} t ↔ Race.Generic.Moves P offers s ℓ t := by
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

/-- **Step bisimilarity up to dead names implies bisimilarity.** -/
theorem bisimilar_of_stepBisimilar {s t : State} (bisimilar : StepBisimilar R offers s t) :
    Race.Generic.Bisimilar P offers s t := by
  obtain ⟨Rel, ⟨forward, backward, _⟩, related⟩ := bisimilar
  refine ⟨Rel, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related⟩
  · intro s t related ℓ s' moved
    obtain ⟨t', stepped, related'⟩ := forward related ({ℓ} : Multiset L) (stepMoves_singleton_iff.mpr moved)
    exact ⟨t', stepMoves_singleton_iff.mp stepped, related'⟩
  · intro s t related ℓ t' moved
    obtain ⟨s', stepped, related'⟩ := backward related ({ℓ} : Multiset L) (stepMoves_singleton_iff.mpr moved)
    exact ⟨s', stepMoves_singleton_iff.mp stepped, related'⟩

/-- **Concurrent words carry along inclusions**, in both directions: a concurrent word carries to a
concurrent word at the larger state, and a concurrent word at the larger state that is carried from a
word at the smaller state comes from a concurrent word there; the final states agree up to dead
names. -/
def CarriesWords (R : T.Residuals) : Prop :=
  ∀ ⦃s u : State⦄ (e : T.Incl s u) (fs : List (Fir s)) (gs : List (Fir u)), List.Forall₂ (T.Carries e) fs gs →
    (∀ {t : State}, Concurrent R s fs t → ∃ t', Concurrent R u gs t' ∧ T.Same t t') ∧
      ∀ {t' : State}, Concurrent R u gs t' → ∃ t, Concurrent R s fs t ∧ T.Same t t'

/-- An offered word carries along an inclusion to an offered word with the same labels. -/
theorem carry_word (invariant : T.Invariant offers) {s u : State} (e : T.Incl s u) :
    ∀ (w : List (L × Fir s)), (∀ x ∈ w, offers x.1 s x.2) →
      ∃ w' : List (L × Fir u), (∀ x ∈ w', offers x.1 u x.2) ∧ w'.map Prod.fst = w.map Prod.fst ∧
        List.Forall₂ (T.Carries e) (w.map Prod.snd) (w'.map Prod.snd)
  | [], _ => ⟨[], fun _ member => absurd member List.not_mem_nil, rfl, .nil⟩
  | x :: rest, offered => by
      obtain ⟨g, carried, offeredG⟩ := (invariant e x.1).1 x.2 (offered x List.mem_cons_self)
      obtain ⟨w', offered', labels, carries⟩ :=
        carry_word invariant e rest fun y member => offered y (List.mem_cons_of_mem _ member)
      refine ⟨(x.1, g) :: w', ?_, by rw [List.map_cons, List.map_cons, labels], .cons carried carries⟩
      intro y member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact offeredG
      · exact offered' y inRest

/-- An offered word at the larger state is carried from an offered word at the smaller state with the
same labels. -/
theorem pull_word (invariant : T.Invariant offers) {s u : State} (e : T.Incl s u) :
    ∀ (w' : List (L × Fir u)), (∀ x ∈ w', offers x.1 u x.2) →
      ∃ w : List (L × Fir s), (∀ x ∈ w, offers x.1 s x.2) ∧ w.map Prod.fst = w'.map Prod.fst ∧
        List.Forall₂ (T.Carries e) (w.map Prod.snd) (w'.map Prod.snd)
  | [], _ => ⟨[], fun _ member => absurd member List.not_mem_nil, rfl, .nil⟩
  | x :: rest, offered => by
      obtain ⟨f, offeredF, carried⟩ := (invariant e x.1).2 x.2 (offered x List.mem_cons_self)
      obtain ⟨w, offered', labels, carries⟩ :=
        pull_word invariant e rest fun y member => offered y (List.mem_cons_of_mem _ member)
      refine ⟨(x.1, f) :: w, ?_, by rw [List.map_cons, List.map_cons, labels], .cons carried carries⟩
      intro y member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact offeredF
      · exact offered' y inRest

/-- One direction of the step bisimulation: a step of `s` is matched by `t`. -/
theorem match_step (invariant : T.Invariant offers) (words : CarriesWords R) {s t u : State} (e : T.Incl s u)
    (e' : T.Incl t u) {M : Multiset L} {s' : State} (stepped : StepMoves R offers s M s') :
    ∃ t', StepMoves R offers t M t' ∧ T.Same s' t' := by
  obtain ⟨w, nonempty, offered, concurrent, rfl⟩ := stepped
  obtain ⟨w₁, offered₁, labels₁, carries₁⟩ := carry_word invariant e w offered
  obtain ⟨w₂, offered₂, labels₂, carries₂⟩ := pull_word invariant e' w₁ offered₁
  obtain ⟨u', concurrent₁, same₁⟩ := (words e _ _ carries₁).1 concurrent
  obtain ⟨t', concurrent₂, same₂⟩ := (words e' _ _ carries₂).2 concurrent₁
  refine ⟨t', ⟨w₂, fun empty => nonempty ?_, offered₂, concurrent₂, by rw [labels₂, labels₁]⟩,
    same₁.trans same₂.symm⟩
  have this : (w₂.map Prod.fst).length = 0 := by rw [empty]; rfl
  rw [labels₂, labels₁, List.length_map] at this
  exact List.length_eq_zero_iff.mp this

/-- **States that agree up to dead names are step bisimilar**, for every program that does not see
dead names, when concurrent words carry along inclusions. -/
theorem stepBisimilar_of_same (invariant : T.Invariant offers) (words : CarriesWords R) {s t : State}
    (same : T.Same s t) : StepBisimilar R offers s t := by
  refine ⟨T.Same, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, same⟩
  · rintro s t ⟨u, ⟨e⟩, ⟨e'⟩⟩ M s' stepped
    exact match_step invariant words e e' stepped
  · rintro s t ⟨u, ⟨e⟩, ⟨e'⟩⟩ M t' stepped
    obtain ⟨s', stepped', same'⟩ := match_step invariant words e' e stepped
    exact ⟨s', stepped', same'.symm⟩

end DeadTransport

#print axioms Step.StateIncl.solvable_of
#print axioms DeadTransport.Same.trans
#print axioms DeadTransport.Moves.admits
#print axioms DeadTransport.moves_iff_over
#print axioms Transport.toDead_same_iff
#print axioms DeadTransport.bisimilar_of_same
#print axioms DeadTransport.sat_iff_of_same
#print axioms DeadTransport.stepMoves_singleton_iff
#print axioms DeadTransport.bisimilar_of_stepBisimilar
#print axioms DeadTransport.stepBisimilar_of_same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
