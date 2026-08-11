import Mettapedia.GSLT.LanguageDef.GSLTILSurface

/-!
# Executable canaries for the finite GSLT-IL boundary

The positive fixture contains both axes that the metalanguage must keep
distinct: computation revises a state inside a stage, while transport changes
the stage interpreting that state.  The catalog contains the naturality
square explicitly, and the authored GSLT admits both two-step routes.

The negative fixtures show that an unregistered route at a quiescent state is
inert and that repeated catalog rows remain repeated executor occurrences.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.Canary

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

private def symbol (name : String) : Pattern := .apply name []

private def stage0 := symbol "stage-0"
private def stage1 := symbol "stage-1"
private def ready := symbol "ready"
private def done := symbol "done"
private def mappedReady := symbol "mapped-ready"
private def mappedDone := symbol "mapped-done"
private def exactKind := symbol "exact"
private def growthRoute := symbol "grow-0-1"
private def missingRoute := symbol "missing-route"

private def sourceRevision : FibreRow :=
  { stage := stage0, source := ready, target := done }

private def targetRevision : FibreRow :=
  { stage := stage1, source := mappedReady, target := mappedDone }

private def readyTransport : TransportRow :=
  { kind := exactKind
    route := growthRoute
    sourceStage := stage0
    targetStage := stage1
    source := ready
    target := mappedReady }

private def doneTransport : TransportRow :=
  { kind := exactKind
    route := growthRoute
    sourceStage := stage0
    targetStage := stage1
    source := done
    target := mappedDone }

/-- One finite catalog whose two axes commute. -/
def catalog : Catalog :=
  { fibreRows := [sourceRevision, targetRevision]
    transportRows := [readyTransport, doneTransport] }

private theorem sourceRevision_mem : sourceRevision ∈ catalog.fibreRows := by
  simp [catalog]

private theorem targetRevision_mem : targetRevision ∈ catalog.fibreRows := by
  simp [catalog]

private theorem readyTransport_mem : readyTransport ∈ catalog.transportRows := by
  simp [catalog]

private theorem doneTransport_mem : doneTransport ∈ catalog.transportRows := by
  simp [catalog]

private def start : Pattern :=
  viaPattern exactKind growthRoute stage0 stage1 ready

private def revisedBeforeTransport : Pattern :=
  viaPattern exactKind growthRoute stage0 stage1 done

private def transportedBeforeRevision : Pattern :=
  atPattern stage1 mappedReady

private def joined : Pattern :=
  atPattern stage1 mappedDone

private theorem step_source_revision :
    (totalTheory catalog).Step start revisedBeforeTransport :=
  (totalTheory_step_iff_wireStep catalog
    (.pending exactKind growthRoute stage0 stage1 ready)).2
      (.fibreUnderVia sourceRevision_mem exactKind growthRoute stage1)

private theorem step_transport_after_revision :
    (totalTheory catalog).Step revisedBeforeTransport joined :=
  (totalTheory_step_iff_wireStep catalog
    (.pending exactKind growthRoute stage0 stage1 done)).2
      (.applyVia doneTransport_mem)

private theorem step_transport_before_revision :
    (totalTheory catalog).Step start transportedBeforeRevision :=
  (totalTheory_step_iff_wireStep catalog
    (.pending exactKind growthRoute stage0 stage1 ready)).2
      (.applyVia readyTransport_mem)

private theorem step_target_revision :
    (totalTheory catalog).Step transportedBeforeRevision joined :=
  (totalTheory_step_iff_wireStep catalog
    (.returned stage1 mappedReady)).2
      (.fibreAt targetRevision_mem)

/-- Positive: revising before transport reaches the common target. -/
def reviseThenTransport :
    (totalTheory catalog).MultiStep start joined :=
  .step step_source_revision
    (.step step_transport_after_revision
      (@GSLT.MultiStep.refl (totalTheory catalog) joined))

/-- Positive: transporting before revision reaches the same target. -/
def transportThenRevise :
    (totalTheory catalog).MultiStep start joined :=
  .step step_transport_before_revision
    (.step step_target_revision
      (@GSLT.MultiStep.refl (totalTheory catalog) joined))

/-- The two-axis canary has two independently checked routes to one endpoint. -/
theorem two_axis_square_is_filled :
    Nonempty ((totalTheory catalog).MultiStep start joined) ∧
      Nonempty ((totalTheory catalog).MultiStep start joined) :=
  ⟨⟨reviseThenTransport⟩, ⟨transportThenRevise⟩⟩

/-- Negative: once the source state is quiescent, an unregistered route
cannot manufacture either a local or a transport successor. -/
theorem unregistered_route_inert :
    rewriteStepWithPremisesUsing (relationEnv catalog) language
        (viaPattern exactKind missingRoute stage0 stage1 done) = [] := by
  rw [execute_via]
  simp [catalog, fibreTargets, transportTargets, sourceRevision,
    targetRevision, readyTransport, doneTransport, exactKind, missingRoute,
    growthRoute, stage0, stage1, ready, done, mappedReady, mappedDone, symbol]

/-- Repeated semantic rows remain repeated executor occurrences rather than
being silently quotiented to support. -/
theorem repeated_rows_preserve_occurrences :
    let repeated : Catalog :=
      { fibreRows := [sourceRevision, sourceRevision]
        transportRows := [] }
    rewriteStepWithPremisesUsing (relationEnv repeated) language
        (atPattern stage0 ready) =
      [atPattern stage0 done, atPattern stage0 done] := by
  dsimp
  rw [execute_at]
  simp [fibreTargets, sourceRevision]

#print axioms two_axis_square_is_filled
#print axioms unregistered_route_inert
#print axioms repeated_rows_preserve_occurrences

end Mettapedia.GSLT.LanguageDef.GSLTIL.Canary

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.Surface.Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.GSLT.LanguageDef.GSLTIL.Surface
open Mettapedia.OSLF.MeTTaIL.Syntax

private def atom (name : String) : Pattern := .apply name []

private def space0 := atom "space-0"
private def space1 := atom "space-1"
private def ready := atom "ready"
private def done := atom "done"
private def mappedReady := atom "mapped-ready"
private def mappedDone := atom "mapped-done"

private def sourceRule : SpaceRule :=
  { occurrence := atom "source-rule"
    space := space0
    source := ready
    target := done }

private def targetRule : SpaceRule :=
  { occurrence := atom "target-rule"
    space := space1
    source := mappedReady
    target := mappedDone }

private def growth : RouteDecl :=
  { occurrence := atom "growth-declaration"
    name := "grow"
    sourceSpace := space0
    targetSpace := space1 }

private def readyMap : RouteRule :=
  { occurrence := atom "ready-map"
    name := "grow"
    source := ready
    target := mappedReady }

private def doneMap : RouteRule :=
  { occurrence := atom "done-map"
    name := "grow"
    source := done
    target := mappedDone }

/-- The public canary uses only spaces, directed equations, route
declarations, and ordinary route application. -/
def program : Program :=
  { spaceRules := [sourceRule, targetRule]
    routes := [growth]
    routeRules := [readyMap, doneMap] }

/-- Local computation remains available while a route application is
pending. -/
def computeBeforeRoute :
    Step program (routeCall "grow" ready) (routeCall "grow" done) :=
  .underRoute (route := growth) (rule := sourceRule)
    (by simp [program]) (by simp [program]) rfl

/-- The same pending command may instead cross its declared route. -/
def applyRouteBeforeCompute :
    Step program (routeCall "grow" ready) (inSpace space1 mappedReady) :=
  .applyRoute (route := growth) (rule := readyMap)
    (by simp [program]) (by simp [program]) rfl

/-- Both public successors elaborate to independently checked steps of the
typed command GSLT. -/
theorem public_two_axis_steps_refine :
    (∃ sourceIR targetIR,
      Elaborates program (routeCall "grow" ready) sourceIR ∧
      Elaborates program (routeCall "grow" done) targetIR ∧
      (totalTheory program.toCatalog).Step sourceIR targetIR) ∧
    (∃ sourceIR targetIR,
      Elaborates program (routeCall "grow" ready) sourceIR ∧
      Elaborates program (inSpace space1 mappedReady) targetIR ∧
      (totalTheory program.toCatalog).Step sourceIR targetIR) :=
  ⟨step_preserved_by_authored_gslt program computeBeforeRoute,
    step_preserved_by_authored_gslt program applyRouteBeforeCompute⟩

private def a := atom "a"
private def b := atom "b"
private def c := atom "c"
private def wrong := atom "wrong"

private def ruleAB : SpaceRule :=
  { occurrence := atom "rule-a-b"
    space := space0
    source := a
    target := b }

private def ruleBC : SpaceRule :=
  { occurrence := atom "rule-b-c"
    space := space0
    source := b
    target := c }

private def chainProgram : Program :=
  { spaceRules := [ruleAB, ruleBC]
    routes := []
    routeRules := [] }

private def stepAB :
    Step chainProgram (inSpace space0 a) (inSpace space0 b) :=
  .inSpace (rule := ruleAB) (by simp [chainProgram])

private def stepBC :
    Step chainProgram (inSpace space0 b) (inSpace space0 c) :=
  .inSpace (rule := ruleBC) (by simp [chainProgram])

/-- Two generating steps compose in the runner closure. -/
def chainRun : Runs chainProgram (inSpace space0 a) (inSpace space0 c) :=
  .tail stepAB (.tail stepBC (.refl _))

/-- The generating catalog contains no direct `a` to `c` rule merely because
the runner can compose the two authored rules. -/
theorem no_direct_chaining_rule :
    ¬ ∃ rule ∈ chainProgram.spaceRules,
      rule.space = space0 ∧ rule.source = a ∧ rule.target = c := by
  simp [chainProgram, ruleAB, ruleBC, space0, a, b, c, atom]

/-- Positive and negative sides of the relation-versus-runner boundary. -/
theorem chaining_is_derived_not_primitive :
    Nonempty (Runs chainProgram (inSpace space0 a) (inSpace space0 c)) ∧
      ¬ ∃ rule ∈ chainProgram.spaceRules,
        rule.space = space0 ∧ rule.source = a ∧ rule.target = c :=
  ⟨⟨chainRun⟩, no_direct_chaining_rule⟩

private def space2 := atom "space-2"

private def firstRoute : RouteDecl :=
  { occurrence := atom "first-declaration"
    name := "first"
    sourceSpace := space0
    targetSpace := space1 }

private def secondRoute : RouteDecl :=
  { occurrence := atom "second-declaration"
    name := "second"
    sourceSpace := space1
    targetSpace := space2 }

private def compositeRoute : RouteDecl :=
  { occurrence := atom "composite-declaration"
    name := "composite"
    sourceSpace := space0
    targetSpace := space2 }

private def firstMap : RouteRule :=
  { occurrence := atom "first-map"
    name := "first"
    source := a
    target := b }

private def secondMap : RouteRule :=
  { occurrence := atom "second-map"
    name := "second"
    source := b
    target := c }

private def compositeMap : RouteRule :=
  { occurrence := atom "composite-map"
    name := "composite"
    source := a
    target := c }

private def wrongCompositeMap : RouteRule :=
  { occurrence := atom "wrong-composite-map"
    name := "composite"
    source := a
    target := wrong }

private def compositionProgram : Program :=
  { spaceRules := []
    routes := [firstRoute, secondRoute, compositeRoute]
    routeRules := [firstMap, secondMap, compositeMap] }

private def noncommutingProgram : Program :=
  { spaceRules := []
    routes := [firstRoute, secondRoute, compositeRoute]
    routeRules := [firstMap, secondMap, wrongCompositeMap] }

/-- Positive: a separately declared composite route carries exactly the
relational composite of its two component routes. -/
theorem declared_route_composition :
    RoutesCompose compositionProgram firstRoute secondRoute compositeRoute := by
  constructor
  · simp [compositionProgram]
  · simp [compositionProgram]
  · simp [compositionProgram]
  · rfl
  · rfl
  · rfl
  · intro source target
    simp [RouteMaps, compositionProgram, firstRoute, secondRoute,
      compositeRoute, firstMap, secondMap, compositeMap]

/-- Negative: matching endpoints do not make a declared route a valid
composite when its action disagrees with the two-step route. -/
theorem endpoints_do_not_imply_composition :
    ¬ RoutesCompose noncommutingProgram firstRoute secondRoute
      compositeRoute := by
  intro composition
  have composedMaps :
      RouteMaps noncommutingProgram compositeRoute a c :=
    (composition.maps_iff a c).2 ⟨b, by
      simp [RouteMaps, noncommutingProgram, firstRoute, secondRoute,
        compositeRoute, firstMap, secondMap, wrongCompositeMap]⟩
  simp [RouteMaps, noncommutingProgram, firstRoute, secondRoute,
    compositeRoute, firstMap, secondMap, wrongCompositeMap, a, c, wrong,
    atom] at composedMaps

theorem missing_route_is_inert :
    ¬ ∃ target, Step program (routeCall "missing" done) target :=
  unregistered_route_inert program "missing" done (by
    intro route routeMember
    simp [program, growth] at routeMember
    subst route
    decide)

#print axioms public_two_axis_steps_refine
#print axioms step_reflected
#print axioms chaining_is_derived_not_primitive
#print axioms declared_route_composition
#print axioms endpoints_do_not_imply_composition
#print axioms missing_route_is_inert

end Mettapedia.GSLT.LanguageDef.GSLTIL.Surface.Canary
