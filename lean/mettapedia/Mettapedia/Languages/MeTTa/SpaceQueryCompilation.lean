import Mettapedia.GSLT.Core.Composition

/-!
# Space/query compilation as an indexed realization

A MeTTa compiler does not need a Prolog-shaped program unit.  Its stable
definition-side unit is a space view at one revision, and its call-side input
is a query.  This module lifts an exact realization of one equation to an
exact realization of the whole ordered space view.

The named observation is `Query -> List Occurrence`.  Consequently the
adequacy theorem preserves answer order and multiplicity by ordinary list
equality; neither can be erased accidentally by replacing the observation
with a set.  The revision is an index of both source and artifact, so an
artifact from one revision cannot be consumed as an artifact of another
without an explicit transport.

This is proof-erased compilation infrastructure.  Runtime artifacts contain
templates, not proofs of the theorem below.
-/

namespace Mettapedia.Languages.MeTTa.SpaceQueryCompilation

open Mettapedia.GSLT

universe uRevision uEquation uTemplate uQuery uOccurrence

/-- The ordered equations visible in one space revision. -/
structure SpaceView (Revision : Type uRevision) (Equation : Type uEquation)
    (revision : Revision) where
  equations : List Equation

/-- The ordered equation templates generated for one space revision. -/
structure CompiledSpaceView (Revision : Type uRevision)
    (Template : Type uTemplate) (revision : Revision) where
  templates : List Template

/-- Interpret a space by concatenating each equation's occurrence bag in
authored order. -/
def observeSpaceSource {Revision : Type uRevision}
    {Equation : Type uEquation} {Query : Type uQuery}
    {Occurrence : Type uOccurrence} {revision : Revision}
    (observeEquation : Equation -> Query -> List Occurrence)
    (space : SpaceView Revision Equation revision) (query : Query) :
    List Occurrence :=
  space.equations.flatMap fun equation => observeEquation equation query

/-- Execute a compiled space by concatenating each template's occurrence bag
in the same authored order. -/
def observeCompiledSpace {Revision : Type uRevision}
    {Template : Type uTemplate} {Query : Type uQuery}
    {Occurrence : Type uOccurrence} {revision : Revision}
    (observeTemplate : Template -> Query -> List Occurrence)
    (space : CompiledSpaceView Revision Template revision) (query : Query) :
    List Occurrence :=
  space.templates.flatMap fun template => observeTemplate template query

/-- Compile an ordered space componentwise with the already adequate
equation-template realization. -/
def compileSpace {Revision : Type uRevision} {Equation : Type uEquation}
    {Template : Type uTemplate} {Query : Type uQuery}
    {Occurrence : Type uOccurrence}
    (equationRealization :
      Realization (fun _ : Revision => Equation) (fun _ => Template)
        (fun _ => Query -> List Occurrence))
    (revision : Revision) (space : SpaceView Revision Equation revision) :
    CompiledSpaceView Revision Template revision :=
  { templates := space.equations.map (equationRealization.compile revision) }

/-- Componentwise adequate equation templates preserve the complete ordered
occurrence bag of an equation inventory. -/
theorem observe_compiled_equations_eq_source
    {Revision : Type uRevision} {Equation : Type uEquation}
    {Template : Type uTemplate} {Query : Type uQuery}
    {Occurrence : Type uOccurrence}
    (equationRealization :
      Realization (fun _ : Revision => Equation) (fun _ => Template)
        (fun _ => Query -> List Occurrence))
    (revision : Revision) (equations : List Equation) (query : Query) :
    (equations.map (equationRealization.compile revision)).flatMap
        (fun template =>
          equationRealization.observeArtifact revision template query) =
      equations.flatMap (fun equation =>
        equationRealization.observeSource revision equation query) := by
  induction equations with
  | nil => rfl
  | cons equation rest inductionHypothesis =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [equationRealization.adequate revision equation,
        inductionHypothesis]

/-- Exact equation-template compilation lifts to an indexed realization of
the whole space-at-revision.  Its observation is the query-indexed ordered
occurrence bag. -/
def spaceRealization {Revision : Type uRevision} {Equation : Type uEquation}
    {Template : Type uTemplate} {Query : Type uQuery}
    {Occurrence : Type uOccurrence}
    (equationRealization :
      Realization (fun _ : Revision => Equation) (fun _ => Template)
        (fun _ => Query -> List Occurrence)) :
    Realization
      (SpaceView Revision Equation)
      (CompiledSpaceView Revision Template)
      (fun _ => Query -> List Occurrence) where
  compile := compileSpace equationRealization
  observeSource := fun revision space =>
    observeSpaceSource (equationRealization.observeSource revision) space
  observeArtifact := fun revision space =>
    observeCompiledSpace (equationRealization.observeArtifact revision) space
  adequate := by
    intro revision space
    funext query
    exact observe_compiled_equations_eq_source equationRealization revision
      space.equations query

/-- The governing future transport obligation.  A cross-dialect equation and
template translation must commute with compilation.  This module states the
square but does not claim an instance for any dialect pair. -/
def CompilationCommutes
    {Revision : Type uRevision}
    {SourceEquation TargetEquation : Type uEquation}
    {SourceTemplate TargetTemplate : Type uTemplate}
    {Query : Type uQuery} {Occurrence : Type uOccurrence}
    (source :
      Realization (fun _ : Revision => SourceEquation)
        (fun _ => SourceTemplate) (fun _ => Query -> List Occurrence))
    (target :
      Realization (fun _ : Revision => TargetEquation)
        (fun _ => TargetTemplate) (fun _ => Query -> List Occurrence))
    (translateEquation : SourceEquation -> TargetEquation)
    (translateTemplate : SourceTemplate -> TargetTemplate) : Prop :=
  forall revision equation,
    translateTemplate (source.compile revision equation) =
      target.compile revision (translateEquation equation)

/-! ## Non-vacuous controls -/

namespace Controls

inductive Equation where
  | first
  | second
deriving DecidableEq

inductive Template where
  | first
  | second
deriving DecidableEq

inductive Occurrence where
  | left
  | right
deriving DecidableEq

def equationRealization :
    SimpleRealization Equation Template (Unit -> List Occurrence) where
  compile _ equation :=
    match equation with
    | .first => .first
    | .second => .second
  observeSource _ equation _ :=
    match equation with
    | .first => [.left, .left]
    | .second => [.right]
  observeArtifact _ template _ :=
    match template with
    | .first => [.left, .left]
    | .second => [.right]
  adequate := by
    intro _ equation
    cases equation <;> rfl

def sourceSpace : SpaceView Unit Equation () :=
  { equations := [.first, .second] }

/-- Positive control: compilation retains both source order and the duplicate
occurrence emitted by the first equation. -/
example :
    (spaceRealization equationRealization).observeArtifact ()
        ((spaceRealization equationRealization).compile () sourceSpace) () =
      [.left, .left, .right] := by
  rfl

/-- Negative control for order: the same support in a different order is not
the same observation. -/
theorem order_is_observable :
    ([Occurrence.left, .right] : List Occurrence) ≠ [.right, .left] := by
  decide

/-- Negative control for multiplicity: deleting one occurrence is not the
same observation. -/
theorem multiplicity_is_observable :
    ([Occurrence.left, .left, .right] : List Occurrence) ≠ [.left, .right] := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.SpaceQueryCompilation
