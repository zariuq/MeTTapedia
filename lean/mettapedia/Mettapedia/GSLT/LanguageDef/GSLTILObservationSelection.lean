import Mettapedia.Cybernetics.ObservedVariety
import Mettapedia.GSLT.LanguageDef.GSLTILElaborationSelection

/-!
# Observer-indexed selection of relational elaborations

An authored GSLT-IL command may have several valid elaboration worlds.  The
existing `ExactSelection` contracts each accepted world fibre to one internal
command.  That is the right criterion for clients which inspect the complete
internal command, but it is stronger than necessary for clients which declare
a coarser observation.

This module isolates the weaker exactness notion.  A selection is
observationally exact when every accepted elaboration has the same declared
view as the selected elaboration.  The relational worlds remain available;
only the selected client view is contracted.

The main characterization is non-vacuous:

* observational selection exists exactly when every command is covered and
  the observation is constant on its accepted elaboration fibre;
* the identity observer recovers ordinary exact selection; and
* one occurrence-ambiguous authored command is admissible at a constant view
  but inadmissible at the identity view.

This is a selection theorem, not an adequacy theorem for a dependent type
theory.  Every selected internal command is still required to satisfy the
independently defined authored `Elaborates` relation through `Profile.sound`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.ObservationSelection

open Mettapedia.Cybernetics
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.ElaborationSelection
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uView

/-- The declared observation is constant on every accepted elaboration fibre.
Distinct internal commands may remain as long as this client view cannot
distinguish them. -/
def ObservationInvariant {program : Program}
    (profile : Profile program) {View : Type uView}
    (observer : Observer Pattern View) : Prop :=
  forall command {first second},
    profile.Accepts command first -> profile.Accepts command second ->
      observer.observe first = observer.observe second

/-- A sound elaboration choice which represents every accepted world exactly
at one declared observation.  It does not claim that accepted internal
commands themselves are equal. -/
structure ObservationalSelection {program : Program}
    (profile : Profile program) {View : Type uView}
    (observer : Observer Pattern View) extends SoundSelection profile where
  observes : forall command {internal}, profile.Accepts command internal ->
    observer.observe (select command) = observer.observe internal

namespace ObservationalSelection

/-- Literal exactness implies exactness for every observer. -/
def ofExact {program : Program} {profile : Profile program}
    {View : Type uView} (observer : Observer Pattern View)
    (selection : ExactSelection profile) :
    ObservationalSelection profile observer where
  select := selection.select
  selected := selection.selected
  observes := by
    intro command internal accepted
    exact congrArg observer.observe (selection.reflects command accepted)

/-- A sound selection is observationally exact at the constant view. -/
def atConstant {program : Program} {profile : Profile program}
    (selection : SoundSelection profile) :
    ObservationalSelection profile
      ({ observe := fun _ : Pattern => () } : Observer Pattern Unit) where
  select := selection.select
  selected := selection.selected
  observes := by intro command internal accepted; rfl

/-- Observational exactness descends to every coarser postcomposed view. -/
def postcompose {program : Program} {profile : Profile program}
    {View : Type uView} {observer : Observer Pattern View}
    (selection : ObservationalSelection profile observer)
    {Summary : Type*} (summarize : View -> Summary) :
    ObservationalSelection profile (observer.postcompose summarize) where
  select := selection.select
  selected := selection.selected
  observes := by
    intro command internal accepted
    exact congrArg summarize (selection.observes command accepted)

/-- An identity-observational selection is an ordinary exact selection. -/
def toExactOfIdentity {program : Program} {profile : Profile program}
    (selection : ObservationalSelection profile (Observer.identity Pattern)) :
    ExactSelection profile where
  select := selection.select
  selected := selection.selected
  reflects := by
    intro command internal accepted
    simpa [Observer.identity] using selection.observes command accepted

end ObservationalSelection

/-! ## Exact existence criterion -/

/-- An observationally exact selection supplies coverage and fibre
invariance. -/
theorem covered_and_invariant_of_selection {program : Program}
    {profile : Profile program} {View : Type uView}
    {observer : Observer Pattern View}
    (selection : ObservationalSelection profile observer) :
    profile.Covered /\ ObservationInvariant profile observer := by
  constructor
  · intro command
    exact ⟨selection.select command, selection.selected command⟩
  · intro command first second firstAccepted secondAccepted
    exact (selection.observes command firstAccepted).symm.trans
      (selection.observes command secondAccepted)

/-- Coverage plus observational invariance constructs an observationally
exact selection.  The choice remains explicit in the resulting object; this
theorem does not identify the unselected worlds. -/
noncomputable def selectionOfCoveredInvariant {program : Program}
    {profile : Profile program} {View : Type uView}
    {observer : Observer Pattern View}
    (covered : profile.Covered)
    (invariant : ObservationInvariant profile observer) :
    ObservationalSelection profile observer := by
  let select : profile.Command -> Pattern := fun command =>
    Classical.choose (covered command)
  have selected : forall command, profile.Accepts command (select command) :=
    fun command => Classical.choose_spec (covered command)
  exact
    { select := select
      selected := selected
      observes := fun command {_} accepted =>
        invariant command (selected command) accepted }

/-- Observational selection exists exactly for covered profiles whose
accepted worlds are indistinguishable to the declared observer. -/
theorem nonempty_iff_covered_and_observationInvariant
    {program : Program} (profile : Profile program)
    {View : Type uView} (observer : Observer Pattern View) :
    Nonempty (ObservationalSelection profile observer) <->
      profile.Covered /\ ObservationInvariant profile observer := by
  constructor
  · rintro ⟨selection⟩
    exact covered_and_invariant_of_selection selection
  · rintro ⟨covered, invariant⟩
    exact ⟨selectionOfCoveredInvariant covered invariant⟩

/-- At the fully informative observer, observational selection is exactly
ordinary exact selection. -/
theorem nonempty_identity_iff_exact {program : Program}
    (profile : Profile program) :
    Nonempty
        (ObservationalSelection profile (Observer.identity Pattern)) <->
      Nonempty (ExactSelection profile) := by
  constructor
  · rintro ⟨selection⟩
    exact ⟨selection.toExactOfIdentity⟩
  · rintro ⟨selection⟩
    exact
      ⟨ObservationalSelection.ofExact (Observer.identity Pattern) selection⟩

/-! ## Positive and negative control on the same authored ambiguity -/

/-- The constant readout used only to show that a coarse client may lawfully
ignore which internal elaboration occurrence was selected. -/
def constantPatternObserver : Observer Pattern Unit where
  observe := fun _ => ()

namespace AmbiguityCanary

private def atom (name : String) : Pattern := .apply name []
private def sourceSpace := atom "observation-source-space"
private def targetA := atom "observation-target-a"
private def targetB := atom "observation-target-b"
private def state := atom "observation-state"

private def routeA : RouteDecl :=
  { occurrence := atom "observation-route-a"
    name := "observation-shared"
    sourceSpace := sourceSpace
    targetSpace := targetA }

private def routeB : RouteDecl :=
  { occurrence := atom "observation-route-b"
    name := "observation-shared"
    sourceSpace := sourceSpace
    targetSpace := targetB }

def program : Program :=
  { spaceRules := []
    routes := [routeA, routeB]
    routeRules := [] }

private def surface : Pattern := routeCall "observation-shared" state

private def internalA : Pattern :=
  viaPattern forwardKind (routeIdentity routeA)
    routeA.sourceSpace routeA.targetSpace state

private def internalB : Pattern :=
  viaPattern forwardKind (routeIdentity routeB)
    routeB.sourceSpace routeB.targetSpace state

private theorem elaboratesA : Elaborates program surface internalA := by
  simpa [program, surface, internalA, routeA] using
    (Elaborates.route (program := program) (route := routeA)
      (by simp [program]) state)

private theorem elaboratesB : Elaborates program surface internalB := by
  simpa [program, surface, internalB, routeB] using
    (Elaborates.route (program := program) (route := routeB)
      (by simp [program]) state)

private theorem internals_distinct : internalA ≠ internalB := by
  simp [internalA, internalB, routeIdentity, routeA, routeB, atom,
    viaPattern, Pattern.apply.injEq]

def profile : Profile program where
  Command := Unit
  surface := fun _ => surface
  Accepts := fun _ internal => Elaborates program surface internal
  sound := _root_.id

def chooseA : SoundSelection profile where
  select := fun _ => internalA
  selected := fun _ => elaboratesA

theorem noExactSelection : Not (Nonempty (ExactSelection profile)) := by
  rintro ⟨selection⟩
  have first := selection.reflects () elaboratesA
  have second := selection.reflects () elaboratesB
  exact internals_distinct (first.symm.trans second)

end AmbiguityCanary

/-- There is one authored profile for which a coarse observational selection
exists, while both identity-observational and literal exact selection are
impossible.  Thus observer-indexed selection is strictly weaker than silently
declaring the elaboration relation functional. -/
theorem ambiguity_is_admissible_coarsely_but_not_finely :
    exists (program : Program) (profile : Profile program),
      Nonempty (ObservationalSelection profile constantPatternObserver) /\
      Not (Nonempty
        (ObservationalSelection profile (Observer.identity Pattern))) /\
      Not (Nonempty (ExactSelection profile)) := by
  refine ⟨AmbiguityCanary.program, AmbiguityCanary.profile, ?_, ?_, ?_⟩
  · exact
      ⟨ObservationalSelection.atConstant
        AmbiguityCanary.chooseA⟩
  · rw [nonempty_identity_iff_exact]
    exact AmbiguityCanary.noExactSelection
  · exact AmbiguityCanary.noExactSelection

/-! ## Axiom audit -/

#print axioms covered_and_invariant_of_selection
#print axioms nonempty_iff_covered_and_observationInvariant
#print axioms nonempty_identity_iff_exact
#print axioms ambiguity_is_admissible_coarsely_but_not_finely

end Mettapedia.GSLT.LanguageDef.GSLTIL.ObservationSelection
