import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Independence

/-!
# Cells: jointly admitted rounds, with faces given by residuals

Pairwise independence does not give a parallel step: three tells can be pairwise independent and
jointly inconsistent. The higher-dimensional reading keeps every cube: a cell of dimension `n` is a
round of `n` firings admitted jointly, and its faces are residuals.

* **Cells** (`Transport.Cell`): a round is a cell when each of its members is admitted, and after
  it the residuals of the other members again form a cell. The upper faces of a cell are therefore
  cells by construction; a cell runs in its listed order (`Cell.jointly`), each firing read after its
  predecessors (`Transport.Jointly`).
* **Low dimensions.** The empty round is the 0-cell of every state (`Cell.nil`); a single firing is a
  1-cell exactly when it is admitted (`cell_singleton_iff`); two firings form a 2-cell exactly when
  both orders are admitted (`cell_pair_iff`). An independent pair is a 2-cell (`Independent.cell`),
  and where diamonds close the 2-cells are exactly the independent pairs (`cell_pair_iff_independent`).
* **The cube law** (`Transport.CubeLaw`), relative to a choice of closing isomorphisms of squares
  (`Transport.Closing`): a third firing's residual after two firings, carried along the closing
  isomorphism of their square, is its residual after them in the other order. These are the face
  identities of the precubical set of cells.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing}

namespace Transport

variable (T : Transport P)

/-- **A word of firings that runs in its order**, each firing read after its predecessors. -/
inductive Jointly : (s : State) → List (Firing s) → Prop
  | nil (s : State) : Jointly s []
  | cons {s : State} (f : Firing s) (admitted : P.Admits f) {rest : List (Firing s)} :
      Jointly (P.result f admitted) (rest.map (T.residual f admitted)) → Jointly s (f :: rest)

/-- **A cell**: a round each of whose members is admitted, and after which the residuals of the
other members form a cell. Its dimension is the length of the round; its upper faces are the
residual rounds. -/
inductive Cell : (s : State) → List (Firing s) → Prop
  | intro {s : State} (round : List (Firing s)) (admitted : ∀ i : Fin round.length, P.Admits round[i])
      (faces : ∀ i : Fin round.length,
        Cell (P.result round[i] (admitted i)) ((round.eraseIdx i).map (T.residual round[i] (admitted i)))) :
      Cell s round

variable {T}

/-- The first firing of a jointly run word is admitted, and the residuals of the rest run after it. -/
theorem Jointly.uncons {s : State} {f : Firing s} {rest : List (Firing s)} (run : T.Jointly s (f :: rest)) :
    ∃ admitted : P.Admits f, T.Jointly (P.result f admitted) (rest.map (T.residual f admitted)) := by
  cases run with
  | cons _ admitted later => exact ⟨admitted, later⟩

/-- The empty round is a cell at every state. -/
theorem Cell.nil (s : State) : T.Cell s [] :=
  .intro [] (fun i => i.elim0) (fun i => i.elim0)

/-- **A cell runs in its listed order.** -/
theorem Cell.jointly {s : State} {round : List (Firing s)} (cell : T.Cell s round) :
    T.Jointly s round := by
  induction cell with
  | intro round admitted _ ih =>
      cases round with
      | nil => exact .nil _
      | cons f rest => exact .cons f (admitted ⟨0, by simp⟩) (ih ⟨0, by simp⟩)

/-- **A single firing is a 1-cell exactly when it is admitted.** -/
theorem cell_singleton_iff {s : State} {f : Firing s} : T.Cell s [f] ↔ P.Admits f := by
  constructor
  · rintro ⟨_, admitted, _⟩
    exact admitted ⟨0, by simp⟩
  · intro admitted
    refine .intro [f] (fun i => ?_) (fun i => ?_)
    · fin_cases i
      exact admitted
    · fin_cases i
      exact Cell.nil _

/-- **Two firings form a 2-cell exactly when both orders are admitted.** -/
theorem cell_pair_iff {s : State} {f g : Firing s} :
    T.Cell s [f, g] ↔ ∃ (first : P.Admits f) (second : P.Admits g),
      P.Admits (T.residual f first g) ∧ P.Admits (T.residual g second f) := by
  constructor
  · rintro ⟨_, admitted, faces⟩
    exact ⟨admitted ⟨0, by simp⟩, admitted ⟨1, by simp⟩,
      cell_singleton_iff.mp (faces ⟨0, by simp⟩), cell_singleton_iff.mp (faces ⟨1, by simp⟩)⟩
  · rintro ⟨first, second, afterFirst, afterSecond⟩
    refine .intro [f, g] (fun i => ?_) (fun i => ?_)
    · fin_cases i
      · exact first
      · exact second
    · fin_cases i
      · exact cell_singleton_iff.mpr afterFirst
      · exact cell_singleton_iff.mpr afterSecond

/-- **An independent pair is a 2-cell.** -/
theorem Independent.cell {s : State} {f g : Firing s} (independent : T.Independent s f g) :
    T.Cell s [f, g] := by
  obtain ⟨first, second, afterFirst, afterSecond, _⟩ := independent
  exact cell_pair_iff.mpr ⟨first, second, afterFirst, afterSecond⟩

/-- **Where diamonds close, the 2-cells are exactly the independent pairs.** -/
theorem cell_pair_iff_independent (closes : T.Closes) {s : State} {f g : Firing s} :
    T.Cell s [f, g] ↔ T.Independent s f g :=
  cell_pair_iff.trans (independent_iff_admits closes).symm

variable (T)

/-- **A choice of closing isomorphisms**: for every square admitted in both orders, an isomorphism of
its two composite results. -/
def Closing :=
  ∀ {s : State} {f g : Firing s} (first : P.Admits f) (second : P.Admits g)
    (afterFirst : P.Admits (T.residual f first g)) (afterSecond : P.Admits (T.residual g second f)),
    T.Iso (P.result (T.residual f first g) afterFirst) (P.result (T.residual g second f) afterSecond)

/-- **The cube law**, relative to a choice of closing isomorphisms: a third firing's residual after
`f` and then `g`, carried along the closing isomorphism of their square, is its residual after `g`
and then `f`. -/
def CubeLaw (close : T.Closing) : Prop :=
  ∀ {s : State} {f g : Firing s} (h : Firing s) (first : P.Admits f) (second : P.Admits g)
    (afterFirst : P.Admits (T.residual f first g)) (afterSecond : P.Admits (T.residual g second f)),
    T.move (close first second afterFirst afterSecond)
        (T.residual (T.residual f first g) afterFirst (T.residual f first h)) =
      T.residual (T.residual g second f) afterSecond (T.residual g second h)

end Transport

#print axioms Transport.Jointly.uncons
#print axioms Transport.Cell.nil
#print axioms Transport.Cell.jointly
#print axioms Transport.cell_singleton_iff
#print axioms Transport.cell_pair_iff
#print axioms Transport.Independent.cell
#print axioms Transport.cell_pair_iff_independent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
