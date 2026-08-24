import Mettapedia.GSLT.LanguageDef.GSLTILFreePath

/-!
# GSLT-IL wire cells and path adequacy

An authored step elaborates to a wire step, but independently elaborating two
adjacent surface steps need not choose the same intermediate route occurrence.
The correct ambient semantics is therefore a cell: it retains both endpoint
elaborations and the wire step between them. Cells compose through their
surface endpoints; strict wire paths require an additional coherence license.

This module proves preservation and reflection between occurrence-bearing
authored events and wire cells, lifts that result to free paths, and gives a
negative witness against silently treating arbitrary surface paths as strict
wire paths.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.WireCells

open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.FreePath
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The internal wire command determines the surface command that elaborated
to it. Public route names may be ambiguous forward, but route occurrence is
retained in the internal command. -/
theorem elaborates_reflects_source (program : Program)
    {first second internal : Pattern}
    (firstElaboration : Elaborates program first internal)
    (secondElaboration : Elaborates program second internal) :
    first = second := by
  cases firstElaboration with
  | inSpace firstSpace firstState =>
      generalize internalEq : atPattern firstSpace firstState =
        secondInternal at secondElaboration
      cases secondElaboration with
      | inSpace secondSpace secondState =>
          simp [atPattern, inSpace, Pattern.apply.injEq] at internalEq ⊢
          exact internalEq
      | @route secondRoute secondMember secondState =>
          simp [atPattern, viaPattern, Pattern.apply.injEq] at internalEq
  | @route firstRoute firstMember firstState =>
      generalize internalEq :
        viaPattern forwardKind (routeIdentity firstRoute)
          firstRoute.sourceSpace firstRoute.targetSpace firstState =
        secondInternal at secondElaboration
      cases secondElaboration with
      | inSpace secondSpace secondState =>
          simp [atPattern, viaPattern, Pattern.apply.injEq] at internalEq
      | @route secondRoute secondMember secondState =>
          simp [viaPattern, routeIdentity, symbol, routeCall,
            Pattern.apply.injEq] at internalEq ⊢
          exact ⟨internalEq.1.2.1, internalEq.2.2.2⟩

/-- One occurrence-bearing wire cell over a pair of surface commands. -/
structure WireCell (program : Program) (source target : Pattern) where
  sourceIR : Pattern
  targetIR : Pattern
  sourceElaboration : Elaborates program source sourceIR
  targetElaboration : Elaborates program target targetIR
  wire : WireStep program.toCatalog sourceIR targetIR

namespace WireCell

/-- Exact authored generators have canonical wire cells. -/
def ofEvent {program : Program} {source target : Pattern}
    (event : AuthoredEvent program source target) :
    WireCell program source target :=
  match event with
  | .inSpace rule member =>
      { sourceIR := atPattern rule.space rule.source
        targetIR := atPattern rule.space rule.target
        sourceElaboration := .inSpace _ _
        targetElaboration := .inSpace _ _
        wire := by
          have rowMember : rule.toFibreRow ∈
              program.toCatalog.fibreRows :=
            (mem_toCatalog_fibreRows_iff program _).2
              ⟨rule, member, rfl⟩
          simpa [SpaceRule.toFibreRow] using WireStep.fibreAt rowMember }
  | .underRoute route rule routeMember ruleMember sameSpace =>
      { sourceIR := viaPattern forwardKind (routeIdentity route)
          route.sourceSpace route.targetSpace rule.source
        targetIR := viaPattern forwardKind (routeIdentity route)
          route.sourceSpace route.targetSpace rule.target
        sourceElaboration := .route routeMember _
        targetElaboration := .route routeMember _
        wire := by
          have rowMember : rule.toFibreRow ∈
              program.toCatalog.fibreRows :=
            (mem_toCatalog_fibreRows_iff program _).2
              ⟨rule, ruleMember, rfl⟩
          have step := WireStep.fibreUnderVia rowMember forwardKind
            (routeIdentity route) route.targetSpace
          simpa [SpaceRule.toFibreRow, sameSpace] using step }
  | .applyRoute route rule routeMember ruleMember sameName =>
      { sourceIR := viaPattern forwardKind (routeIdentity route)
          route.sourceSpace route.targetSpace rule.source
        targetIR := atPattern route.targetSpace rule.target
        sourceElaboration := .route routeMember _
        targetElaboration := .inSpace _ _
        wire := by
          have rowMember : route.withRule rule ∈
              program.toCatalog.transportRows :=
            (mem_toCatalog_transportRows_iff program _).2
              ⟨route, routeMember, rule, ruleMember, sameName, rfl⟩
          simpa [RouteDecl.withRule] using WireStep.applyVia rowMember }

/-- Every wire cell over surface endpoints reflects at least one exact
authored event over those same endpoints. -/
theorem toEvent {program : Program} {source target : Pattern}
    (cell : WireCell program source target) :
    Nonempty (AuthoredEvent program source target) := by
  obtain ⟨reached, sourceStep, reachedElaboration⟩ :=
    step_reflected program cell.sourceElaboration cell.wire
  have reachedEq : reached = target :=
    elaborates_reflects_source program reachedElaboration
      cell.targetElaboration
  subst reached
  exact AuthoredEvent.ofStep sourceStep

theorem nonempty_iff_event {program : Program} {source target : Pattern} :
    Nonempty (WireCell program source target) ↔
      Nonempty (AuthoredEvent program source target) := by
  constructor
  · rintro ⟨cell⟩
    exact cell.toEvent
  · rintro ⟨event⟩
    exact ⟨ofEvent event⟩

end WireCell

/-- Surface-composable paths of wire cells.  Adjacent cells need not yet have
definitionally equal internal endpoint elaborations. -/
abbrev WireCellPath (program : Program) := Route (WireCell program)

namespace WireCellPath

def ofAuthoredPath {program : Program} {source target : Pattern} :
    AuthoredPath program source target → WireCellPath program source target
  | .refl object => .refl object
  | .cons event rest => .cons (WireCell.ofEvent event) (ofAuthoredPath rest)

theorem toAuthoredPath {program : Program} {source target : Pattern}
    (path : WireCellPath program source target) :
    Nonempty (AuthoredPath program source target) := by
  induction path with
  | refl object => exact ⟨.refl object⟩
  | cons cell rest inductionHypothesis =>
      obtain ⟨event⟩ := cell.toEvent
      obtain ⟨path⟩ := inductionHypothesis
      exact ⟨.cons event path⟩

theorem nonempty_iff_authoredPath
    {program : Program} {source target : Pattern} :
    Nonempty (WireCellPath program source target) ↔
      Nonempty (AuthoredPath program source target) := by
  constructor
  · rintro ⟨path⟩
    exact path.toAuthoredPath
  · rintro ⟨path⟩
    exact ⟨ofAuthoredPath path⟩

theorem ofAuthoredPath_append {program : Program}
    {source middle target : Pattern}
    (earlier : AuthoredPath program source middle)
    (later : AuthoredPath program middle target) :
    ofAuthoredPath (earlier.append later) =
      (ofAuthoredPath earlier).append (ofAuthoredPath later) := by
  induction earlier with
  | refl => rfl
  | cons event rest inductionHypothesis =>
      change
        Route.cons (WireCell.ofEvent event)
            (ofAuthoredPath (rest.append later)) =
          Route.cons (WireCell.ofEvent event)
            ((ofAuthoredPath rest).append (ofAuthoredPath later))
      rw [inductionHypothesis]

end WireCellPath

/-! ## Strict-intermediate-coherence negative control -/

namespace AmbiguousIntermediateCanary

private def atom (name : String) : Pattern := .apply name []
private def spaceA := atom "space-a"
private def spaceB := atom "space-b"
private def targetA := atom "target-a"
private def targetB := atom "target-b"
private def input := atom "input"
private def middle := atom "middle"
private def output := atom "output"

private def routeA : RouteDecl :=
  { occurrence := atom "route-a"
    name := "shared"
    sourceSpace := spaceA
    targetSpace := targetA }

private def routeB : RouteDecl :=
  { occurrence := atom "route-b"
    name := "shared"
    sourceSpace := spaceB
    targetSpace := targetB }

private def localRule : SpaceRule :=
  { occurrence := atom "local"
    space := spaceA
    source := input
    target := middle }

private def transportRule : RouteRule :=
  { occurrence := atom "transport"
    name := "shared"
    source := middle
    target := output }

private def program : Program :=
  { spaceRules := [localRule]
    routes := [routeA, routeB]
    routeRules := [transportRule] }

private def firstEvent : AuthoredEvent program
    (routeCall "shared" input) (routeCall "shared" middle) :=
  .underRoute routeA localRule (by simp [program]) (by simp [program]) rfl

private def secondEvent : AuthoredEvent program
    (routeCall "shared" middle) (inSpace targetB output) :=
  .applyRoute routeB transportRule (by simp [program]) (by simp [program]) rfl

def authoredPath : AuthoredPath program
    (routeCall "shared" input) (inSpace targetB output) :=
  .cons firstEvent (.cons secondEvent (.refl _))

/-- The surface path is valid, but the canonical wire cells select different
route occurrences for their common surface middle. -/
theorem canonical_cells_do_not_strictly_join :
    (WireCell.ofEvent firstEvent).targetIR ≠
      (WireCell.ofEvent secondEvent).sourceIR := by
  simp [firstEvent, secondEvent, WireCell.ofEvent, routeIdentity,
    routeA, routeB, atom, viaPattern, Pattern.apply.injEq]

/-- There is no global elaboration function that represents every authored
elaboration exactly.  The common surface middle elaborates through two
distinct route occurrences.  A universal semantics must therefore retain an
elaboration relation or a selected coherence witness; it cannot silently use
a function on raw commands. -/
theorem no_function_represents_all_elaborations :
    ¬ ∃ elaborate : Pattern -> Pattern,
      ∀ surface internal,
        Elaborates program surface internal ↔ elaborate surface = internal := by
  rintro ⟨elaborate, represents⟩
  have firstEq :=
    (represents (routeCall "shared" middle)
      (WireCell.ofEvent firstEvent).targetIR).mp
        (WireCell.ofEvent firstEvent).targetElaboration
  have secondEq :=
    (represents (routeCall "shared" middle)
      (WireCell.ofEvent secondEvent).sourceIR).mp
        (WireCell.ofEvent secondEvent).sourceElaboration
  exact canonical_cells_do_not_strictly_join (firstEq.symm.trans secondEq)

end AmbiguousIntermediateCanary

/-- Some finite authored GSLT-IL program necessarily has relational rather
than functional elaboration.  The concrete ambiguity witness stays private;
the public theorem records the language-level obstruction. -/
theorem exists_program_without_global_functional_elaboration :
    ∃ program : Program,
      ¬ ∃ elaborate : Pattern → Pattern,
        ∀ surface internal,
          Elaborates program surface internal ↔
            elaborate surface = internal := by
  exact ⟨AmbiguousIntermediateCanary.program,
    AmbiguousIntermediateCanary.no_function_represents_all_elaborations⟩

#print axioms elaborates_reflects_source
#print axioms WireCell.nonempty_iff_event
#print axioms WireCellPath.nonempty_iff_authoredPath
#print axioms WireCellPath.ofAuthoredPath_append
#print axioms AmbiguousIntermediateCanary.canonical_cells_do_not_strictly_join
#print axioms AmbiguousIntermediateCanary.no_function_represents_all_elaborations
#print axioms exists_program_without_global_functional_elaboration

end Mettapedia.GSLT.LanguageDef.GSLTIL.WireCells
