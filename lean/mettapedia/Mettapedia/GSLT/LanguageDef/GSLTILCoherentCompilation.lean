import Mettapedia.GSLT.LanguageDef.GSLTILWireCells

/-!
# Coherent compilation of authored GSLT-IL paths

An authored path is freely composable at its public endpoints.  Its canonical
wire cells form a strict internal path only when every adjacent pair chooses
the same elaborated intermediate command.  That condition is retained here as
an intrinsic compilation certificate.

The certificate is constructed once.  Its executable readout is an ordinary
proof-relevant route of `WireStep`s: no elaborator, route-name search, or
coherence test remains in the compiled path.  Failure to construct the
certificate does not invalidate the authored path.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.CoherentCompilation

open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.FreePath
open Mettapedia.GSLT.LanguageDef.GSLTIL.WireCells
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A proof-relevant wrapper around the proposition-valued wire relation.
Distinct compiled occurrences remain distinct route entries even when their
underlying reachability proofs are proof-irrelevant. -/
structure RetainedWireStep (catalog : Catalog)
    (source target : Pattern) : Type where
  step : WireStep catalog source target

/-- A certificate that the canonical wire cells of an authored path join at
their exact internal endpoints.  The internal source and target are indices,
so adjacency is enforced by construction rather than checked during
execution. -/
inductive Certificate {program : Program} :
    {source target : Pattern} → AuthoredPath program source target →
      Pattern → Pattern → Type where
  | refl {surface internal : Pattern}
      (elaboration : Elaborates program surface internal) :
      Certificate (.refl surface) internal internal
  | cons {source middle target targetIR : Pattern}
      (event : AuthoredEvent program source middle)
      (rest : AuthoredPath program middle target)
      (tail : Certificate rest (WireCell.ofEvent event).targetIR targetIR) :
      Certificate (.cons event rest)
        (WireCell.ofEvent event).sourceIR targetIR

namespace Certificate

/-- Erase a coherence certificate to the strict wire path that the runtime
may execute directly. -/
def toWirePath {program : Program} {source target sourceIR targetIR : Pattern}
    {path : AuthoredPath program source target} :
    Certificate path sourceIR targetIR →
      Route (RetainedWireStep program.toCatalog) sourceIR targetIR
  | .refl _ => .refl sourceIR
  | .cons event _ tail =>
      .cons ⟨(WireCell.ofEvent event).wire⟩ tail.toWirePath

/-- The indexed internal source still elaborates from the authored source. -/
theorem sourceElaboration {program : Program}
    {source target sourceIR targetIR : Pattern}
    {path : AuthoredPath program source target}
    (certificate : Certificate path sourceIR targetIR) :
    Elaborates program source sourceIR := by
  cases certificate with
  | refl elaboration => exact elaboration
  | cons event rest tail => exact (WireCell.ofEvent event).sourceElaboration

/-- The indexed internal target still elaborates from the authored target. -/
theorem targetElaboration {program : Program}
    {source target sourceIR targetIR : Pattern}
    {path : AuthoredPath program source target}
    (certificate : Certificate path sourceIR targetIR) :
    Elaborates program target targetIR := by
  induction certificate with
  | refl elaboration => exact elaboration
  | cons event rest tail inductionHypothesis => exact inductionHypothesis

/-- A single authored event always has a coherent strict compilation. -/
def singleton {program : Program} {source target : Pattern}
    (event : AuthoredEvent program source target) :
    Certificate (Route.cons event (Route.refl target))
      (WireCell.ofEvent event).sourceIR
      (WireCell.ofEvent event).targetIR :=
  Certificate.cons event (Route.refl target)
    (Certificate.refl (WireCell.ofEvent event).targetElaboration)

/-- Coherent compilations compose exactly when their internal boundary is the
same index. -/
noncomputable def append {program : Program}
    {first middle last firstIR middleIR lastIR : Pattern}
    {earlier : AuthoredPath program first middle}
    {later : AuthoredPath program middle last}
    (front : Certificate earlier firstIR middleIR)
    (back : Certificate later middleIR lastIR) :
    Certificate (earlier.append later) firstIR lastIR := by
  induction front with
  | refl => exact back
  | cons event rest tail inductionHypothesis =>
      exact .cons event _ (inductionHypothesis back)

/-- The internal source index of a nonempty certificate is the canonical
source of its first event. -/
theorem sourceIR_eq_of_cons {program : Program}
    {source middle target sourceIR targetIR : Pattern}
    (event : AuthoredEvent program source middle)
    (rest : AuthoredPath program middle target)
    (certificate : Certificate (Route.cons event rest) sourceIR targetIR) :
    sourceIR = (WireCell.ofEvent event).sourceIR := by
  cases certificate
  rfl

/-- Any certificate for two adjacent generators witnesses equality of their
canonical internal boundary. -/
theorem adjacentInternalEq {program : Program}
    {source middle next target sourceIR targetIR : Pattern}
    (first : AuthoredEvent program source middle)
    (second : AuthoredEvent program middle next)
    (rest : AuthoredPath program next target)
    (certificate : Certificate
      (Route.cons first (Route.cons second rest)) sourceIR targetIR) :
    (WireCell.ofEvent first).targetIR =
      (WireCell.ofEvent second).sourceIR := by
  cases certificate with
  | cons _ _ tail =>
      exact sourceIR_eq_of_cons second rest tail

/-- The first adjacent boundary of a path, when present, is internally
coherent. -/
def FirstBoundaryCoherent {program : Program} :
    {source target : Pattern} → AuthoredPath program source target → Prop
  | _, _, .refl _ => True
  | _, _, .cons _ (.refl _) => True
  | _, _, .cons first (.cons second _rest) =>
      (WireCell.ofEvent first).targetIR =
        (WireCell.ofEvent second).sourceIR

theorem firstBoundaryCoherent {program : Program}
    {source target sourceIR targetIR : Pattern}
    {path : AuthoredPath program source target}
    (certificate : Certificate path sourceIR targetIR) :
    FirstBoundaryCoherent path := by
  cases certificate with
  | refl => trivial
  | cons first rest tail =>
      cases rest with
      | refl => trivial
      | cons second rest =>
          exact adjacentInternalEq first second rest
            (Certificate.cons first _ tail)

/-- Exact admission criterion for canonical strict compilation.  A reflexive
path must still name an elaborable command; a nonempty path is compilable
exactly when every adjacent pair of canonical cells agrees internally. -/
def Compilable {program : Program} :
    {source target : Pattern} → AuthoredPath program source target → Prop
  | _, _, .refl surface =>
      ∃ internal, Elaborates program surface internal
  | _, _, .cons _ (.refl _) => True
  | _, _, .cons first (.cons second rest) =>
      (WireCell.ofEvent first).targetIR =
          (WireCell.ofEvent second).sourceIR ∧
        Compilable (.cons second rest)

theorem compilable_of_certificate {program : Program}
    {source target sourceIR targetIR : Pattern}
    {path : AuthoredPath program source target}
    (certificate : Certificate path sourceIR targetIR) :
    Compilable path := by
  induction certificate with
  | refl elaboration => exact ⟨_, elaboration⟩
  | cons first rest tail inductionHypothesis =>
      cases rest with
      | refl => trivial
      | cons second rest =>
          exact ⟨sourceIR_eq_of_cons second rest tail,
            inductionHypothesis⟩

theorem certificate_of_compilable {program : Program}
    {source target : Pattern} {path : AuthoredPath program source target}
    (compilable : Compilable path) :
    Nonempty (Σ sourceIR targetIR, Certificate path sourceIR targetIR) := by
  induction path with
  | refl surface =>
      obtain ⟨internal, elaboration⟩ := compilable
      exact ⟨⟨internal, internal, .refl elaboration⟩⟩
  | cons first rest inductionHypothesis =>
      cases rest with
      | refl =>
          exact ⟨⟨(WireCell.ofEvent first).sourceIR,
            (WireCell.ofEvent first).targetIR, singleton first⟩⟩
      | cons second rest =>
          obtain ⟨boundary, tailCompilable⟩ := compilable
          obtain ⟨⟨tailSource, tailTarget, tailCertificate⟩⟩ :=
            inductionHypothesis tailCompilable
          have tailSourceEq : tailSource =
              (WireCell.ofEvent second).sourceIR :=
            sourceIR_eq_of_cons second rest tailCertificate
          have join : (WireCell.ofEvent first).targetIR = tailSource :=
            boundary.trans tailSourceEq.symm
          have joinedTail : Certificate (Route.cons second rest)
              (WireCell.ofEvent first).targetIR tailTarget := by
            rw [join]
            exact tailCertificate
          exact ⟨⟨(WireCell.ofEvent first).sourceIR, tailTarget,
            .cons first _ joinedTail⟩⟩

theorem nonempty_certificate_iff_compilable {program : Program}
    {source target : Pattern} {path : AuthoredPath program source target} :
    Nonempty (Σ sourceIR targetIR, Certificate path sourceIR targetIR) ↔
      Compilable path := by
  constructor
  · rintro ⟨⟨sourceIR, targetIR, certificate⟩⟩
    exact compilable_of_certificate certificate
  · exact certificate_of_compilable

theorem toWirePath_append {program : Program}
    {first middle last firstIR middleIR lastIR : Pattern}
    {earlier : AuthoredPath program first middle}
    {later : AuthoredPath program middle last}
    (front : Certificate earlier firstIR middleIR)
    (back : Certificate later middleIR lastIR) :
    (front.append back).toWirePath =
      front.toWirePath.append back.toWirePath := by
  induction front with
  | refl => simp [append, toWirePath]
  | cons event rest tail inductionHypothesis =>
      change
        Route.cons ⟨(WireCell.ofEvent event).wire⟩
            ((tail.append back).toWirePath) =
          Route.cons ⟨(WireCell.ofEvent event).wire⟩
            (tail.toWirePath.append back.toWirePath)
      rw [inductionHypothesis]

/-- Compilation retains every authored occurrence as one wire transition. -/
theorem toWirePath_length {program : Program}
    {source target sourceIR targetIR : Pattern}
    {path : AuthoredPath program source target}
    (certificate : Certificate path sourceIR targetIR) :
    certificate.toWirePath.length = path.length := by
  induction certificate with
  | refl => rfl
  | cons event rest tail inductionHypothesis =>
      simp [toWirePath, Route.length, inductionHypothesis]

end Certificate

/-! ## Positive and negative controls -/

namespace Canaries

private def atom (name : String) : Pattern := .apply name []
private def space := atom "space"
private def input := atom "input"
private def middle := atom "middle"
private def output := atom "output"

private def firstRule : SpaceRule :=
  { occurrence := atom "first"
    space := space
    source := input
    target := middle }

private def secondRule : SpaceRule :=
  { occurrence := atom "second"
    space := space
    source := middle
    target := output }

private def program : Program :=
  { spaceRules := [firstRule, secondRule]
    routes := []
    routeRules := [] }

private def firstEvent : AuthoredEvent program
    (inSpace space input) (inSpace space middle) :=
  .inSpace firstRule (by simp [program])

private def secondEvent : AuthoredEvent program
    (inSpace space middle) (inSpace space output) :=
  .inSpace secondRule (by simp [program])

private def path : AuthoredPath program
    (inSpace space input) (inSpace space output) :=
  .cons firstEvent (.cons secondEvent (.refl _))

/-- Two unambiguous adjacent rules compile to a two-step strict wire path. -/
def positive : Certificate path
    (WireCell.ofEvent firstEvent).sourceIR
    (WireCell.ofEvent secondEvent).targetIR :=
  Certificate.cons firstEvent _
    (Certificate.cons secondEvent _
      (Certificate.refl
        (WireCell.ofEvent secondEvent).targetElaboration))

theorem positive_length : positive.toWirePath.length = 2 := by
  rfl

theorem positive_compilable : Certificate.Compilable path :=
  Certificate.compilable_of_certificate positive

/-- The ambiguous-route surface path from `GSLTILWireCells` remains valid,
but it has no canonical strict compilation. -/
theorem ambiguous_path_has_no_certificate :
    IsEmpty (Σ sourceIR targetIR,
      Certificate AmbiguousIntermediateCanary.authoredPath sourceIR targetIR) :=
  ⟨by
    rintro ⟨sourceIR, targetIR, certificate⟩
    have boundary := Certificate.firstBoundaryCoherent certificate
    simp only [AmbiguousIntermediateCanary.authoredPath,
      Certificate.FirstBoundaryCoherent] at boundary
    exact AmbiguousIntermediateCanary.canonical_cells_do_not_strictly_join
      boundary⟩

theorem ambiguous_path_not_compilable :
    ¬ Certificate.Compilable
      AmbiguousIntermediateCanary.authoredPath := by
  intro compilable
  obtain ⟨certificate⟩ :=
    Certificate.certificate_of_compilable compilable
  exact ambiguous_path_has_no_certificate.false certificate

end Canaries

#print axioms Certificate.sourceElaboration
#print axioms Certificate.targetElaboration
#print axioms Certificate.adjacentInternalEq
#print axioms Certificate.firstBoundaryCoherent
#print axioms Certificate.nonempty_certificate_iff_compilable
#print axioms Certificate.toWirePath_append
#print axioms Certificate.toWirePath_length
#print axioms Canaries.positive_length
#print axioms Canaries.positive_compilable
#print axioms Canaries.ambiguous_path_has_no_certificate
#print axioms Canaries.ambiguous_path_not_compilable

end Mettapedia.GSLT.LanguageDef.GSLTIL.CoherentCompilation
