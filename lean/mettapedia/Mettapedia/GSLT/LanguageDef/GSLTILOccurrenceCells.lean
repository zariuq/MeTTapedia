import Mettapedia.GSLT.LanguageDef.GSLTILCoherentCompilation

/-!
# Occurrence-preserving GSLT-IL compilation cells

The proposition-valued wire relation is the correct reachability quotient,
but it cannot remember which of two visibly coincident authored occurrences
produced a transition.  A compilation cell therefore lives over a pair of
boundaries `(surface command, internal command)` and retains:

* the exact authored event;
* elaborations of both surface endpoints;
* agreement with the canonical internal endpoints selected by that event.

Paths of these cells have two compositional projections.  The surface
projection is the original occurrence-bearing authored path.  The internal
projection is the strict wire path.  A coherent compilation certificate lifts
to one such paired path, and its surface projection reflects the authored path
exactly rather than merely preserving reachability.

The separating canary proves why the extra layer is necessary: two distinct
authored occurrences induce distinct compilation cells even though their
proposition-valued retained wire steps are equal.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.OccurrenceCells

open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.FreePath
open Mettapedia.GSLT.LanguageDef.GSLTIL.WireCells
open Mettapedia.GSLT.LanguageDef.GSLTIL.CoherentCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A double boundary retains both the authored command and its selected
internal elaboration. -/
abbrev Boundary := Pattern × Pattern

/-- One occurrence-preserving compilation square.  The indices enforce
surface and internal composability independently. -/
structure OccurrenceWireCell (program : Program)
    (source target : Boundary) where
  event : AuthoredEvent program source.1 target.1
  sourceElaboration : Elaborates program source.1 source.2
  targetElaboration : Elaborates program target.1 target.2
  sourceCanonical : source.2 = (WireCell.ofEvent event).sourceIR
  targetCanonical : target.2 = (WireCell.ofEvent event).targetIR

namespace OccurrenceWireCell

/-- Every authored generator has its canonical occurrence-preserving square. -/
def ofEvent {program : Program} {source target : Pattern}
    (event : AuthoredEvent program source target) :
    OccurrenceWireCell program
      (source, (WireCell.ofEvent event).sourceIR)
      (target, (WireCell.ofEvent event).targetIR) where
  event := event
  sourceElaboration := (WireCell.ofEvent event).sourceElaboration
  targetElaboration := (WireCell.ofEvent event).targetElaboration
  sourceCanonical := rfl
  targetCanonical := rfl

/-- Forget occurrence identity only at the established proposition-valued
wire boundary. -/
def toRetainedWireStep {program : Program} {source target : Boundary}
    (cell : OccurrenceWireCell program source target) :
    RetainedWireStep program.toCatalog source.2 target.2 := by
  rw [cell.sourceCanonical, cell.targetCanonical]
  exact ⟨(WireCell.ofEvent cell.event).wire⟩

/-- The authored occurrence remains inspectable before the wire quotient. -/
def occurrence {program : Program} {source target : Boundary}
    (cell : OccurrenceWireCell program source target) : Pattern :=
  cell.event.occurrence

@[simp] theorem occurrence_ofEvent
    {program : Program} {source target : Pattern}
    (event : AuthoredEvent program source target) :
    (ofEvent event).occurrence = event.occurrence :=
  rfl

end OccurrenceWireCell

/-- Strictly composable paths of occurrence-preserving compilation squares. -/
abbrev OccurrenceWirePath (program : Program) :=
  Route (OccurrenceWireCell program)

namespace OccurrenceWirePath

/-- Project a paired path to its occurrence-bearing authored path. -/
def surfacePath {program : Program} {source target : Boundary} :
    OccurrenceWirePath program source target →
      AuthoredPath program source.1 target.1
  | .refl _ => .refl source.1
  | .cons cell rest => .cons cell.event (surfacePath rest)

/-- Project a paired path to its strict proposition-valued wire path. -/
def wirePath {program : Program} {source target : Boundary} :
    OccurrenceWirePath program source target →
      Route (RetainedWireStep program.toCatalog) source.2 target.2
  | .refl _ => .refl source.2
  | .cons cell rest => .cons cell.toRetainedWireStep (wirePath rest)

@[simp] theorem surfacePath_refl {program : Program} (boundary : Boundary) :
    surfacePath (.refl boundary : OccurrenceWirePath program boundary boundary) =
      .refl boundary.1 :=
  rfl

@[simp] theorem wirePath_refl {program : Program} (boundary : Boundary) :
    wirePath (.refl boundary : OccurrenceWirePath program boundary boundary) =
      .refl boundary.2 :=
  rfl

theorem surfacePath_append {program : Program}
    {source middle target : Boundary}
    (earlier : OccurrenceWirePath program source middle)
    (later : OccurrenceWirePath program middle target) :
    surfacePath (earlier.append later) =
      (surfacePath earlier).append (surfacePath later) := by
  induction earlier with
  | refl => rfl
  | cons cell rest inductionHypothesis =>
      change Route.cons cell.event (surfacePath (rest.append later)) =
        Route.cons cell.event
          ((surfacePath rest).append (surfacePath later))
      rw [inductionHypothesis]

theorem wirePath_append {program : Program}
    {source middle target : Boundary}
    (earlier : OccurrenceWirePath program source middle)
    (later : OccurrenceWirePath program middle target) :
    wirePath (earlier.append later) =
      (wirePath earlier).append (wirePath later) := by
  induction earlier with
  | refl => rfl
  | cons cell rest inductionHypothesis =>
      change Route.cons cell.toRetainedWireStep
          (wirePath (rest.append later)) =
        Route.cons cell.toRetainedWireStep
          ((wirePath rest).append (wirePath later))
      rw [inductionHypothesis]

/-- A paired path plus its final elaboration reconstructs the original
coherence certificate.  Internal adjacency is already carried by the path
indices; no route-name search or global elaborator is needed. -/
noncomputable def toCertificate {program : Program}
    {source target : Boundary}
    (path : OccurrenceWirePath program source target)
    (targetElaboration : Elaborates program target.1 target.2) :
    Certificate path.surfacePath source.2 target.2 := by
  induction path with
  | refl boundary =>
      exact .refl targetElaboration
  | @cons source middle target cell rest inductionHypothesis =>
      have tail := inductionHypothesis targetElaboration
      rw [cell.targetCanonical] at tail
      have compiled := Certificate.cons cell.event _ tail
      rw [← cell.sourceCanonical] at compiled
      exact compiled

@[simp] theorem length_surfacePath {program : Program}
    {source target : Boundary} (path : OccurrenceWirePath program source target) :
    path.surfacePath.length = path.length := by
  induction path with
  | refl => rfl
  | cons cell rest inductionHypothesis =>
      simp [surfacePath, Route.length, inductionHypothesis]

@[simp] theorem length_wirePath {program : Program}
    {source target : Boundary} (path : OccurrenceWirePath program source target) :
    path.wirePath.length = path.length := by
  induction path with
  | refl => rfl
  | cons cell rest inductionHypothesis =>
      simp [wirePath, Route.length, inductionHypothesis]

end OccurrenceWirePath

/-! ## Coherent compilation lifts to paired paths -/

/-- The exact double-cell realization of one authored path.  Endpoint
elaborations are retained explicitly so reflexive paths are meaningful too. -/
structure OccurrenceCompilation {program : Program}
    {source target : Pattern} (path : AuthoredPath program source target) where
  sourceIR : Pattern
  targetIR : Pattern
  compiled : OccurrenceWirePath program (source, sourceIR) (target, targetIR)
  sourceElaboration : Elaborates program source sourceIR
  targetElaboration : Elaborates program target targetIR
  surfaceExact : compiled.surfacePath = path

namespace CertificateBridge

/-- A coherence certificate compiles to a path that retains both authored
occurrences and strict internal transitions. -/
def toOccurrenceWirePath
    {program : Program} {source target sourceIR targetIR : Pattern}
    {path : AuthoredPath program source target} :
    Certificate path sourceIR targetIR →
      OccurrenceWirePath program (source, sourceIR) (target, targetIR)
  | .refl _ => .refl _
  | .cons event _ tail =>
      .cons (OccurrenceWireCell.ofEvent event)
        (toOccurrenceWirePath tail)

/-- The paired compilation reflects the exact authored path, including every
event occurrence. -/
@[simp] theorem surfacePath_toOccurrenceWirePath
    {program : Program} {source target sourceIR targetIR : Pattern}
    {path : AuthoredPath program source target}
    (certificate : Certificate path sourceIR targetIR) :
    OccurrenceWirePath.surfacePath
        (toOccurrenceWirePath certificate) = path := by
  induction certificate with
  | refl => rfl
  | cons event rest tail inductionHypothesis =>
      change Route.cons event
          (OccurrenceWirePath.surfacePath (toOccurrenceWirePath tail)) =
        Route.cons event rest
      rw [inductionHypothesis]

/-- Forgetting occurrences from the paired compilation agrees exactly with
the established strict wire compilation. -/
@[simp] theorem wirePath_toOccurrenceWirePath
    {program : Program} {source target sourceIR targetIR : Pattern}
    {path : AuthoredPath program source target}
    (certificate : Certificate path sourceIR targetIR) :
    OccurrenceWirePath.wirePath
        (toOccurrenceWirePath certificate) = certificate.toWirePath := by
  induction certificate with
  | refl => rfl
  | cons event rest tail inductionHypothesis =>
      change Route.cons
          (OccurrenceWireCell.ofEvent event).toRetainedWireStep
          (OccurrenceWirePath.wirePath (toOccurrenceWirePath tail)) =
        Route.cons ⟨(WireCell.ofEvent event).wire⟩ tail.toWirePath
      rw [inductionHypothesis]

end CertificateBridge

namespace OccurrenceCompilation

/-- Every ordinary coherence certificate has a canonical occurrence-
preserving double-cell realization. -/
def ofCertificate {program : Program}
    {source target sourceIR targetIR : Pattern}
    {path : AuthoredPath program source target}
    (certificate : Certificate path sourceIR targetIR) :
    OccurrenceCompilation path where
  sourceIR := sourceIR
  targetIR := targetIR
  compiled := CertificateBridge.toOccurrenceWirePath certificate
  sourceElaboration := certificate.sourceElaboration
  targetElaboration := certificate.targetElaboration
  surfaceExact := CertificateBridge.surfacePath_toOccurrenceWirePath certificate

/-- A double-cell realization reconstructs a coherence certificate for the
exact authored path it claims to compile. -/
noncomputable def toCertificate {program : Program}
    {source target : Pattern} {path : AuthoredPath program source target}
    (compilation : OccurrenceCompilation path) :
    Certificate path compilation.sourceIR compilation.targetIR := by
  have certificate := compilation.compiled.toCertificate
    compilation.targetElaboration
  rw [compilation.surfaceExact] at certificate
  exact certificate

/-- Double-cell realization is exactly the existing compilability criterion,
now with occurrence identity retained rather than quotiented. -/
theorem nonempty_iff_compilable {program : Program}
    {source target : Pattern} {path : AuthoredPath program source target} :
    Nonempty (OccurrenceCompilation path) ↔
      Certificate.Compilable path := by
  constructor
  · rintro ⟨compilation⟩
    exact Certificate.compilable_of_certificate compilation.toCertificate
  · intro compilable
    obtain ⟨⟨sourceIR, targetIR, certificate⟩⟩ :=
      Certificate.certificate_of_compilable compilable
    exact ⟨ofCertificate certificate⟩

end OccurrenceCompilation

/-! ## The wire quotient is genuinely non-faithful -/

namespace DuplicateOccurrenceCanary

private def atom (name : String) : Pattern := .apply name []
private def space := atom "space"
private def input := atom "input"
private def output := atom "output"

private def firstRule : SpaceRule :=
  { occurrence := atom "first-occurrence"
    space := space
    source := input
    target := output }

private def secondRule : SpaceRule :=
  { occurrence := atom "second-occurrence"
    space := space
    source := input
    target := output }

private def program : Program :=
  { spaceRules := [firstRule, secondRule]
    routes := []
    routeRules := [] }

private def firstEvent : AuthoredEvent program
    (inSpace space input) (inSpace space output) :=
  .inSpace firstRule (by simp [program])

private def secondEvent : AuthoredEvent program
    (inSpace space input) (inSpace space output) :=
  .inSpace secondRule (by simp [program])

private abbrev sourceBoundary : Boundary :=
  (inSpace space input, (WireCell.ofEvent firstEvent).sourceIR)

private abbrev targetBoundary : Boundary :=
  (inSpace space output, (WireCell.ofEvent firstEvent).targetIR)

private def firstCell : OccurrenceWireCell program sourceBoundary targetBoundary :=
  OccurrenceWireCell.ofEvent firstEvent

private def secondCell : OccurrenceWireCell program sourceBoundary targetBoundary :=
  OccurrenceWireCell.ofEvent secondEvent

/-- Distinct authored occurrences remain distinct compilation cells. -/
theorem occurrence_cells_distinct : firstCell ≠ secondCell := by
  intro equal
  have occurrenceEqual :=
    congrArg OccurrenceWireCell.occurrence equal
  change atom "first-occurrence" = atom "second-occurrence" at occurrenceEqual
  simp [atom] at occurrenceEqual

/-- The proposition-valued wire quotient identifies those same cells. -/
theorem retained_wire_steps_equal :
    firstCell.toRetainedWireStep = secondCell.toRetainedWireStep := by
  rcases firstCell.toRetainedWireStep with ⟨firstStep⟩
  rcases secondCell.toRetainedWireStep with ⟨secondStep⟩
  congr

/-- Therefore occurrence erasure is not injective, even for one-step cells
with identical visible and internal endpoints. -/
theorem occurrence_erasure_not_injective :
    ¬ Function.Injective
      (fun cell : OccurrenceWireCell program sourceBoundary targetBoundary =>
        cell.toRetainedWireStep) := by
  intro injective
  exact occurrence_cells_distinct
    (injective retained_wire_steps_equal)

/-- Some occurrence-indexed compilation fibre contains distinct authored
cells that the proposition-valued wire semantics identifies.  The witness is
packaged existentially so the universal structure depends on the phenomenon,
not on the private syntax of this canary. -/
theorem exists_distinct_cells_with_equal_wire_steps :
    ∃ (program : Program) (sourceBoundary targetBoundary : Boundary)
      (first second : OccurrenceWireCell program sourceBoundary targetBoundary),
      first ≠ second ∧
        first.toRetainedWireStep = second.toRetainedWireStep := by
  exact ⟨program, sourceBoundary, targetBoundary, firstCell, secondCell,
    occurrence_cells_distinct, retained_wire_steps_equal⟩

/-- The established ambiguous surface path has no occurrence-preserving
strict realization; it remains valid in the ambient authored layer. -/
theorem ambiguous_path_has_no_occurrence_compilation :
    IsEmpty (OccurrenceCompilation
      AmbiguousIntermediateCanary.authoredPath) :=
  ⟨by
    intro compilation
    exact CoherentCompilation.Canaries.ambiguous_path_not_compilable
      (OccurrenceCompilation.nonempty_iff_compilable.mp ⟨compilation⟩)⟩

end DuplicateOccurrenceCanary

#print axioms OccurrenceWirePath.surfacePath_append
#print axioms OccurrenceWirePath.wirePath_append
#print axioms OccurrenceWirePath.toCertificate
#print axioms CertificateBridge.surfacePath_toOccurrenceWirePath
#print axioms CertificateBridge.wirePath_toOccurrenceWirePath
#print axioms OccurrenceCompilation.nonempty_iff_compilable
#print axioms DuplicateOccurrenceCanary.occurrence_cells_distinct
#print axioms DuplicateOccurrenceCanary.retained_wire_steps_equal
#print axioms DuplicateOccurrenceCanary.occurrence_erasure_not_injective
#print axioms DuplicateOccurrenceCanary.exists_distinct_cells_with_equal_wire_steps
#print axioms DuplicateOccurrenceCanary.ambiguous_path_has_no_occurrence_compilation

end Mettapedia.GSLT.LanguageDef.GSLTIL.OccurrenceCells
