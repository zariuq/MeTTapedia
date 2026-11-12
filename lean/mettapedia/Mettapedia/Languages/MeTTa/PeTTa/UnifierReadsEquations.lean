import Mettapedia.Languages.MeTTa.PeTTa.ListViewMeaning
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintRefusal
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingDecides

/-!
# The model's unifier is a lawful reading of equations

`ListViewMeaning` says what a lawful reading is and shows that any two agree. This module
constructs one, for equations between terms: the model's own unifier, `Unifying.unify`.

* Frames are the bindings in solved form (`Unifying.Idempotent`). A frame means the
  valuations that solve its bindings read as equations
  (`UnifyingConstraintPresentation.presentation`).
* Telling an equation runs the unifier on it. The three laws of a lawful reading are the
  three facts already proved of the unifier, joined here:
  - a successful unification narrows the models to exactly those of the equation
    (`UnifyingConstraintPresentation.successful_models_iff`);
  - a clash means no model is left
    (`UnifyingConstraintPresentation.clashed_has_no_source_solution`);
  - the unifier never runs out of its fuel (`Unifying.unify_decides`), so there is no third
    outcome.
* The models of those theorems are the environments of the source judgment
  (`EagerDFS.Destination`). A valuation and an environment are the same thing seen two ways
  (`valuationOf`, `modelOf`, `valuationOf_modelOf`), and a term under a valuation is the
  term read under the environment (`instantiate_valuationOf`). So this module adds no
  second notion of meaning: it restates the existing one.

Consequence (`unifier_accepts_iff_solvable`): the unifier accepts a list of equations
exactly when the equations have a solution, and the frame it reaches means their solutions.

What this does not cover: the list view. Told through the pattern unifier, a view of an
unknown is kept as an equation whose solutions are not the view's
(`ListView.model_answer_has_none_of_the_solutions`). The reading constructed here is lawful
for equations alone; a lawful reading of views and equations together is still to be
constructed.

Controls: a binding and a use of it are accepted (`accepts_a_binding_and_its_use`); two
different values for one unknown are refused (`refuses_two_values_for_one_unknown`), and so
is a term that would contain itself (`refuses_a_term_inside_itself`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ListView

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination
  (Environment Equations Solves encode decode decode_encode)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation
  (environment presentation read_expression successful_models_iff
    clashed_has_no_source_solution environment_models_presentation)
open Mettapedia.Languages.MeTTa.PeTTa.Unifying
  (Unified unify unifyTerms Idempotent unifyTerms_sound unify_decides)

/-! ## A valuation and an environment of the source judgment are the same thing -/

/-- The valuation an environment gives: each unknown read under it. -/
def valuationOf (model : Environment) : Valuation := fun name => EagerDFS.Destination.read model (.var name)

/-- An environment that gives a valuation. -/
def modelOf (ρ : Valuation) : Environment := fun name => encode (ρ name)

theorem valuationOf_modelOf (ρ : Valuation) : valuationOf (modelOf ρ) = ρ := by
  funext name
  simp [valuationOf, modelOf, EagerDFS.Destination.read, encode]

/-- A term under the valuation of an environment is the term read under the environment. -/
theorem instantiate_valuationOf (model : Environment) :
    ∀ term : Atom, instantiate (valuationOf model) term = EagerDFS.Destination.read model term
  | .var name => by simp [valuationOf]
  | .symbol name => by
      simp [EagerDFS.Destination.read, encode, decode]
  | .grounded value => by
      simp [instantiate, EagerDFS.Destination.read, encode, decode]
  | .expression items => by
      rw [instantiate_expression, read_expression, instantiateList_valuationOf model items]
where
  /-- The same for the items of a list. -/
  instantiateList_valuationOf (model : Environment) :
      ∀ items : List Atom,
        instantiate.instantiateList (valuationOf model) items = items.map (EagerDFS.Destination.read model)
    | [] => by simp
    | first :: rest => by
        rw [instantiateList_cons, List.map_cons, instantiate_valuationOf model first,
          instantiateList_valuationOf model rest]

theorem read_modelOf (ρ : Valuation) (term : Atom) :
    EagerDFS.Destination.read (modelOf ρ) term = instantiate ρ term := by
  rw [← instantiate_valuationOf, valuationOf_modelOf]

/-! ## Equations as facts -/

/-- An equation between two terms under a valuation. -/
def EquationHolds (ρ : Valuation) (equation : Atom × Atom) : Prop :=
  instantiate ρ equation.1 = instantiate ρ equation.2

/-- The source judgment's solutions are the solutions of the equations as facts. -/
theorem solves_modelOf (ρ : Valuation) (source : Equations) :
    Solves (modelOf ρ) source ↔ ρ ∈ SolutionsOf EquationHolds source := by
  simp only [Solves, SolutionsOf, EquationHolds, read_modelOf, Set.mem_ofPred_eq]

/-! ## The unifier as a reading -/

theorem idempotent_nil : Idempotent ([] : Subst) := by
  intro name value found
  simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup] at found

/-- Tell the unifier an equation: the bindings it answers, in solved form, or a refusal. -/
def tellEquation (frame : {bindings : Subst // Idempotent bindings}) (equation : Atom × Atom) :
    Option {bindings : Subst // Idempotent bindings} :=
  match unified : unify frame.1 equation.1 equation.2 with
  | .ok bound =>
      some ⟨bound,
        (unifyTerms_sound _ frame.1 bound equation.1 equation.2 frame.2 unified).1⟩
  | .clash => none
  | .exhausted => none

theorem tellEquation_some {frame next : {bindings : Subst // Idempotent bindings}}
    {equation : Atom × Atom} (told : tellEquation frame equation = some next) :
    unify frame.1 equation.1 equation.2 = .ok next.1 := by
  unfold tellEquation at told
  split at told
  · rename_i bound unified
    simp only [Option.some.injEq] at told
    subst told
    exact unified
  · cases told
  · cases told

theorem tellEquation_none {frame : {bindings : Subst // Idempotent bindings}}
    {equation : Atom × Atom} (refused : tellEquation frame equation = none) :
    unify frame.1 equation.1 equation.2 = .clash := by
  unfold tellEquation at refused
  split at refused
  · cases refused
  · assumption
  · rename_i exhausted
    exact absurd exhausted (unify_decides frame.1 equation.1 equation.2 frame.2)

/-- The model's unifier, as a reading of equations between terms. It is lawful. -/
def unifierReading : Reading EquationHolds where
  Frame := {bindings : Subst // Idempotent bindings}
  empty := ⟨[], idempotent_nil⟩
  Denotes frame := SolutionsOf EquationHolds (presentation frame.1)
  tell := tellEquation
  empty_denotes := by
    show SolutionsOf EquationHolds (presentation []) = Set.univ
    simp [presentation, solutionsOf_nil]
  frame_satisfiable frame := by
    refine ⟨valuationOf (environment frame.1), ?_⟩
    intro pair member
    have solved := environment_models_presentation frame.1 frame.2 pair member
    show instantiate _ pair.1 = instantiate _ pair.2
    rw [instantiate_valuationOf, instantiate_valuationOf]
    exact solved
  told := by
    intro frame equation next told
    have unified := tellEquation_some told
    ext ρ
    have law := successful_models_iff _ frame.1 next.1 equation.1 equation.2 frame.2 unified
      (modelOf ρ)
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ← solves_modelOf, EquationHolds,
      ← read_modelOf]
    exact law
  refused := by
    intro frame equation refused
    have clashed := tellEquation_none refused
    ext ρ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨possible, holds⟩
    exact clashed_has_no_source_solution _ frame.1 equation.1 equation.2 frame.2 clashed
      ⟨modelOf ρ, (solves_modelOf ρ _).mpr possible, by
        simpa [EquationHolds, read_modelOf] using holds⟩

/-- The model's unifier accepts a list of equations exactly when they have a solution. -/
theorem unifier_accepts_iff_solvable (equations : List (Atom × Atom)) :
    (unifierReading.tellAll unifierReading.empty equations).isSome ↔
      (SolutionsOf EquationHolds equations).Nonempty :=
  unifierReading.accepts_iff_satisfiable equations

/-- The frame the unifier reaches means the solutions of the equations it was told. -/
theorem unifier_frame_means_the_solutions {equations : List (Atom × Atom)}
    {frame : unifierReading.Frame}
    (reached : unifierReading.tellAll unifierReading.empty equations = some frame) :
    SolutionsOf EquationHolds (presentation frame.1) = SolutionsOf EquationHolds equations :=
  unifierReading.denotes_the_solutions reached

/-! ## Controls -/

/-- Positive: `$x = p` and `$y = ($x)` are accepted. -/
theorem accepts_a_binding_and_its_use :
    (unifierReading.tellAll unifierReading.empty
      [(.var "x", .symbol "p"), (.var "y", .expression [.var "x"])]).isSome = true := by
  decide +kernel

/-- Negative: `$x = p` and `$x = q` are refused. -/
theorem refuses_two_values_for_one_unknown :
    (unifierReading.tellAll unifierReading.empty
      [(.var "x", .symbol "p"), (.var "x", .symbol "q")]).isSome = false := by
  decide +kernel

/-- Negative: `$x = ($x)` is refused; no term contains itself. -/
theorem refuses_a_term_inside_itself :
    (unifierReading.tellAll unifierReading.empty
      [(.var "x", .expression [.var "x"])]).isSome = false := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.ListView
