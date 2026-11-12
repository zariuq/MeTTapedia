import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeCoexistence
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Lattice

/-!
# The knowledge zone of the step is a meet semilattice of solution sets

The step keeps knowledge as a store of equations over the frame of the state. The logical reading
needs a meet semilattice that only refines. Stores are that only up to their solutions: the
knowledge of a store is the set of its solutions in every later frame, ordered by inclusion.

* `solutions_append`: telling is the meet.
* `solutions_applyStore`, `pull`: transport along a frame map is the inverse image of solutions
  under composition; it preserves meets (`pull_inf`). On the knowledge of a store it is
  functorial (`pull_id_solutions`, `pull_comp_solutions`), although frame maps satisfy only the
  action laws.
* `entails_iff_subset`, `Entails.of_solutions_subset`: an ask is a property of the solution set,
  and it is kept by every refinement. Guards are down-closed.
* `solvable_iff_nonempty`: consistency is inhabitation, so it is inherited upward.
* `information_solutions_subset`, `run_solutions_subset`: a firing and a run only refine.
* `pair_solutions`: the knowledge of two coexisting states is the meet of their transported
  knowledges.
* `solutions_append_self`: knowledge is not counted: telling twice is telling once.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)

/-- The knowledge of a store: the set of its solutions in every later frame. -/
def solutions {a : Obj} (store : EquationStore (Tm a)) : Set (Frames.Solution Hom a) :=
  {solution | X.Models solution.2 store}

/-- Transport of knowledge along a frame map: the later solutions that are solutions after the
map. -/
def pull {a b : Obj} (f : Hom a b) (known : Set (Frames.Solution Hom a)) :
    Set (Frames.Solution Hom b) :=
  {solution | (⟨solution.1, X.comp solution.2 f⟩ : Frames.Solution Hom a) ∈ known}

variable {X}

/-- **Telling is the meet.** -/
theorem solutions_append {a : Obj} (one two : EquationStore (Tm a)) :
    solutions X (one ++ two) = solutions X one ⊓ solutions X two := by
  ext solution
  exact Frames.models_append solution.2 one two

/-- **Knowledge is not counted**: telling twice is telling once. -/
theorem solutions_append_self {a : Obj} (store : EquationStore (Tm a)) :
    solutions X (store ++ store) = solutions X store := by
  rw [solutions_append]
  exact inf_idem _

/-- **Transport of a store is the inverse image of its solutions.** -/
theorem solutions_applyStore {a b : Obj} (f : Hom a b) (store : EquationStore (Tm a)) :
    solutions X (X.applyStore f store) = pull X f (solutions X store) := by
  ext solution
  exact Frames.models_applyStore f solution.2 store

/-- Transport preserves meets. -/
theorem pull_inf {a b : Obj} (f : Hom a b) (one two : Set (Frames.Solution Hom a)) :
    pull X f (one ⊓ two) = pull X f one ⊓ pull X f two :=
  rfl

/-- Transport is monotone. -/
theorem pull_mono {a b : Obj} (f : Hom a b) {stronger weaker : Set (Frames.Solution Hom a)}
    (refines : stronger ⊆ weaker) : pull X f stronger ⊆ pull X f weaker :=
  fun _ member => refines member

/-- Transport along the identity keeps the knowledge of a store. -/
theorem pull_id_solutions {a : Obj} (store : EquationStore (Tm a)) :
    pull X (X.id a) (solutions X store) = solutions X store := by
  ext solution
  exact (Frames.models_congr (fun t => Frames.act_comp_id solution.2 t) store).symm

/-- Transport along a composite is transport along the parts, on the knowledge of a store. -/
theorem pull_comp_solutions {a b c : Obj} (f : Hom a b) (g : Hom b c)
    (store : EquationStore (Tm a)) :
    pull X (X.comp g f) (solutions X store) = pull X g (pull X f (solutions X store)) := by
  ext solution
  exact (Frames.models_congr (fun t => Frames.act_comp_assoc f g solution.2 t) store).symm

/-- **An ask is a property of the solution set.** -/
theorem entails_iff_subset {a : Obj} (store : EquationStore (Tm a))
    (observation : (b : Obj) → Hom a b → Prop) :
    X.Entails store observation ↔
      solutions X store ⊆ {solution | observation solution.1 solution.2} :=
  ⟨fun asked solution solved => asked solution.1 solution.2 solved,
    fun inside b f solved => inside (a := ⟨b, f⟩) solved⟩

/-- **Guards are down-closed**: an ask entailed by knowledge is entailed by every refinement. -/
theorem Entails.of_solutions_subset {a : Obj} {stronger weaker : EquationStore (Tm a)}
    {observation : (b : Obj) → Hom a b → Prop}
    (refines : solutions X stronger ⊆ solutions X weaker) (asked : X.Entails weaker observation) :
    X.Entails stronger observation :=
  (entails_iff_subset stronger observation).mpr
    (refines.trans ((entails_iff_subset weaker observation).mp asked))

/-- Consistency is inhabitation of the solution set. -/
theorem solvable_iff_nonempty {a : Obj} (store : EquationStore (Tm a)) :
    X.Solvable store ↔ (solutions X store).Nonempty :=
  ⟨fun ⟨b, f, solved⟩ => ⟨⟨b, f⟩, solved⟩, fun ⟨solution, solved⟩ => ⟨solution.1, solution.2, solved⟩⟩

/-- Consistency is inherited by weaker knowledge, so only the last knowledge needs it. -/
theorem solvable_of_solutions_subset {a : Obj} {stronger weaker : EquationStore (Tm a)}
    (refines : solutions X stronger ⊆ solutions X weaker) (solvable : X.Solvable stronger) :
    X.Solvable weaker :=
  (solvable_iff_nonempty weaker).mpr (((solvable_iff_nonempty stronger).mp solvable).mono refines)

section Step

variable {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **The information of a firing only refines the knowledge it starts from.** -/
theorem information_solutions_subset (E : EffectCore X O State Firing) {s : State} (f : Firing s) :
    solutions X (E.information f) ⊆ pull X (E.extension f) (solutions X (E.knowledge s)) :=
  fun solution solved => E.information_refines f solution.2 solved

/-- **A prepared result only refines the information.** -/
theorem result_solutions_subset (E : EffectCore X O State Firing) {s : State} (f : Firing s)
    (prepared : E.Prepares f) :
    solutions X (E.knowledge (E.preparedResult f prepared)) ⊆
      pull X (E.preparedSettle f prepared) (solutions X (E.information f)) :=
  fun solution solved => E.result_refines f prepared solution.2 solved

/-- **Knowledge only refines along a run.** -/
theorem run_solutions_subset (P : Step X O State Firing) {s : State} (run : P.Run s) :
    solutions X (P.knowledge run.last) ⊆ pull X run.toLast (solutions X (P.knowledge s)) :=
  fun solution solved => run.models_start solution.2 solved

/-- **The knowledge of two coexisting states is the meet of their transported knowledges.** -/
theorem pair_solutions (E : EffectCore X O State Firing) {left right : State}
    (pair : E.NativePair left right) :
    solutions X (E.knowledge pair.state) =
      pull X pair.leftMap (solutions X (E.knowledge left)) ⊓
        pull X pair.rightMap (solutions X (E.knowledge right)) := by
  ext solution
  exact pair.models_iff solution.2

end Step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
