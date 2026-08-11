import Mettapedia.GSLT.LanguageDef.GSLTIL

/-!
# A MeTTa-facing surface for finite GSLT-IL programs

The indexed command calculus retains dependent source and target indices in
its proof and compilation IR.  Authors do not need to repeat those indices on
every command.  This module gives the finite calculus a small MeTTa-facing
surface:

* `(in space (= left right))` declares a directed rule in one space;
* `(route name source target)` declares a forward operational route;
* `(= (name left) right)` declares one finite action of that route;
* `(in space state)` and `(name state)` are the corresponding commands.

The surface deliberately does not call a route exact.  Exactness, coverage,
conservativity, and realization adequacy are proof obligations on a route, not
unchecked authoring labels.

One surface step elaborates to one step of the typed `at`/`via` IR.  Repeated
stepping is the separate reflexive-transitive closure of this relation.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.Surface

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Surface syntax -/

def symbol (name : String) : Pattern := .apply name []

def inSpace (space state : Pattern) : Pattern :=
  .apply "in" [space, state]

def equation (left right : Pattern) : Pattern :=
  .apply "=" [left, right]

def routeDeclAtom (name : String) (source target : Pattern) : Pattern :=
  .apply "route" [symbol name, source, target]

def routeCall (name : String) (state : Pattern) : Pattern :=
  .apply name [state]

def request (command : Pattern) : Pattern :=
  .apply "!" [command]

/-! ## Occurrence-bearing authored rows -/

/-- One directed rule authored in a named semantic space. -/
structure SpaceRule where
  occurrence : Pattern
  space : Pattern
  source : Pattern
  target : Pattern
  deriving DecidableEq

/-- One named forward route.  Stronger route kinds are admitted by separate
proof-bearing layers rather than by changing this declaration. -/
structure RouteDecl where
  occurrence : Pattern
  name : String
  sourceSpace : Pattern
  targetSpace : Pattern
  deriving DecidableEq

/-- One finite input/output row for a named route. -/
structure RouteRule where
  occurrence : Pattern
  name : String
  source : Pattern
  target : Pattern
  deriving DecidableEq

/-- The finite program visible to the surface elaborator. -/
structure Program where
  spaceRules : List SpaceRule
  routes : List RouteDecl
  routeRules : List RouteRule

/-- The weak route kind assigned by the minimal surface. -/
def forwardKind : Pattern := symbol "forward"

/-- The internal route identity retains the declaration occurrence and both
endpoints.  Surface commands only name the route; elaboration restores the
redundant data needed by the dependent IR. -/
def routeIdentity (route : RouteDecl) : Pattern :=
  .apply "declared-route"
    [route.occurrence, symbol route.name, route.sourceSpace,
      route.targetSpace]

theorem routeIdentity_injective : Function.Injective routeIdentity := by
  intro first second sameIdentity
  cases first with
  | mk firstOccurrence firstName firstSource firstTarget =>
      cases second with
      | mk secondOccurrence secondName secondSource secondTarget =>
          simp [routeIdentity, symbol] at sameIdentity
          simp_all

def SpaceRule.toFibreRow (rule : SpaceRule) : FibreRow :=
  { stage := rule.space
    source := rule.source
    target := rule.target }

def RouteDecl.withRule (route : RouteDecl) (rule : RouteRule) : TransportRow :=
  { kind := forwardKind
    route := routeIdentity route
    sourceStage := route.sourceSpace
    targetStage := route.targetSpace
    source := rule.source
    target := rule.target }

/-- Elaborate the authored rows to the occurrence-preserving typed IR catalog.
The declaration occurrence is part of the internal route key, so two
same-named declarations do not become one route accidentally. -/
def Program.toCatalog (program : Program) : Catalog :=
  { fibreRows := program.spaceRules.map SpaceRule.toFibreRow
    transportRows := program.routes.flatMap fun route =>
      program.routeRules.filterMap fun rule =>
        if rule.name = route.name then some (route.withRule rule) else none }

theorem mem_toCatalog_fibreRows_iff (program : Program) (row : FibreRow) :
    row ∈ program.toCatalog.fibreRows ↔
      ∃ rule ∈ program.spaceRules, rule.toFibreRow = row := by
  simp [Program.toCatalog]

theorem mem_toCatalog_transportRows_iff
    (program : Program) (row : TransportRow) :
    row ∈ program.toCatalog.transportRows ↔
      ∃ route ∈ program.routes, ∃ rule ∈ program.routeRules,
        rule.name = route.name ∧ route.withRule rule = row := by
  simp [Program.toCatalog]

/-! ## Route laws -/

/-- The finite relational action declared for one route occurrence.  The
minimal surface permits a relation; functionality, totality, exactness, and
coverage are stronger evidence-bearing profiles. -/
def RouteMaps (program : Program) (route : RouteDecl)
    (source target : Pattern) : Prop :=
  route ∈ program.routes ∧
    ∃ rule ∈ program.routeRules,
      rule.name = route.name ∧ rule.source = source ∧ rule.target = target

/-- A declared route is the relational composite of two declared routes.
Composition is a law on the catalog, not another generating execution step. -/
structure RoutesCompose (program : Program)
    (earlier later composite : RouteDecl) : Prop where
  earlierMember : earlier ∈ program.routes
  laterMember : later ∈ program.routes
  compositeMember : composite ∈ program.routes
  middleSpace : earlier.targetSpace = later.sourceSpace
  sourceSpace : composite.sourceSpace = earlier.sourceSpace
  targetSpace : composite.targetSpace = later.targetSpace
  maps_iff : ∀ source target,
    RouteMaps program composite source target ↔
      ∃ middle,
        RouteMaps program earlier source middle ∧
          RouteMaps program later middle target

/-! ## Direct surface semantics -/

/-- The direct one-step meaning of the MeTTa-facing forms.  It is stated
without invoking the generic language executor, so refinement below is not a
definition-by-reuse argument. -/
inductive Step (program : Program) : Pattern → Pattern → Prop where
  | inSpace {rule : SpaceRule} :
      rule ∈ program.spaceRules →
      Step program (inSpace rule.space rule.source)
        (inSpace rule.space rule.target)
  | underRoute {route : RouteDecl} {rule : SpaceRule} :
      route ∈ program.routes →
      rule ∈ program.spaceRules →
      rule.space = route.sourceSpace →
      Step program (routeCall route.name rule.source)
        (routeCall route.name rule.target)
  | applyRoute {route : RouteDecl} {rule : RouteRule} :
      route ∈ program.routes →
      rule ∈ program.routeRules →
      rule.name = route.name →
      Step program (routeCall route.name rule.source)
        (inSpace route.targetSpace rule.target)

/-- The ordinary MeTTa `!` form is only the observable request envelope for
one generating step. -/
inductive RequestStep (program : Program) : Pattern → Pattern → Prop where
  | execute {source target : Pattern} :
      Step program source target →
      RequestStep program (request source) target

theorem requestStep_iff (program : Program) (source target : Pattern) :
    RequestStep program (request source) target ↔
      Step program source target := by
  constructor
  · intro step
    cases step
    assumption
  · exact RequestStep.execute

/-- Surface commands elaborate nondeterministically when the same public name
has several declaration occurrences.  Each declaration remains distinct in
the IR through `routeIdentity`. -/
inductive Elaborates (program : Program) : Pattern → Pattern → Prop where
  | inSpace (space state : Pattern) :
      Elaborates program (inSpace space state) (atPattern space state)
  | route {route : RouteDecl} :
      route ∈ program.routes →
      (state : Pattern) →
      Elaborates program (routeCall route.name state)
        (viaPattern forwardKind (routeIdentity route)
          route.sourceSpace route.targetSpace state)

/-- Every direct surface step is preserved by one independently defined wire
step after elaboration. -/
theorem step_preserved (program : Program) {source target : Pattern}
    (step : Step program source target) :
    ∃ sourceIR targetIR,
      Elaborates program source sourceIR ∧
      Elaborates program target targetIR ∧
      WireStep program.toCatalog sourceIR targetIR := by
  cases step with
  | @inSpace rule ruleMember =>
      have rowMember : SpaceRule.toFibreRow rule ∈
          program.toCatalog.fibreRows :=
        (mem_toCatalog_fibreRows_iff program _).2
        ⟨_, ruleMember, rfl⟩
      refine ⟨_, _, .inSpace _ _, .inSpace _ _, ?_⟩
      simpa [SpaceRule.toFibreRow] using WireStep.fibreAt rowMember
  | @underRoute route rule routeMember ruleMember sameSpace =>
      have rowMember : SpaceRule.toFibreRow rule ∈
          program.toCatalog.fibreRows :=
        (mem_toCatalog_fibreRows_iff program _).2
          ⟨_, ruleMember, rfl⟩
      refine ⟨_, _, .route routeMember _, .route routeMember _,
        ?_⟩
      have wire := WireStep.fibreUnderVia rowMember
        forwardKind (routeIdentity route) route.targetSpace
      simpa [SpaceRule.toFibreRow, sameSpace] using wire
  | @applyRoute route rule routeMember ruleMember sameName =>
      have rowMember : _ ∈ program.toCatalog.transportRows :=
        (mem_toCatalog_transportRows_iff program _).2
          ⟨_, routeMember, _, ruleMember, sameName, rfl⟩
      refine ⟨_, _, .route routeMember _, .inSpace _ _, ?_⟩
      simpa [RouteDecl.withRule] using WireStep.applyVia rowMember

/-- On commands obtained from the surface elaborator, the generated IR
catalog does not invent a surface transition. -/
theorem step_reflected (program : Program)
    {source sourceIR targetIR : Pattern}
    (sourceElaboration : Elaborates program source sourceIR)
    (wire : WireStep program.toCatalog sourceIR targetIR) :
    ∃ target, Step program source target ∧
      Elaborates program target targetIR := by
  cases sourceElaboration with
  | inSpace space state =>
      have accepted := wireStep_mem_executor program.toCatalog wire
      rw [execute_at] at accepted
      simp only [List.mem_map] at accepted
      obtain ⟨next, nextMember, rfl⟩ := accepted
      obtain ⟨row, rowMember, rowStage, rowSource, rowTarget⟩ :=
        (mem_fibreTargets_iff program.toCatalog space state next).1 nextMember
      obtain ⟨rule, ruleMember, rowEquality⟩ :=
        (mem_toCatalog_fibreRows_iff program row).1 rowMember
      have ruleStage : rule.space = space := by
        calc
          rule.space = row.stage := by
            simpa [SpaceRule.toFibreRow] using
              congrArg FibreRow.stage rowEquality
          _ = space := rowStage
      have ruleSource : rule.source = state := by
        calc
          rule.source = row.source := by
            simpa [SpaceRule.toFibreRow] using
              congrArg FibreRow.source rowEquality
          _ = state := rowSource
      have ruleTarget : rule.target = next := by
        calc
          rule.target = row.target := by
            simpa [SpaceRule.toFibreRow] using
              congrArg FibreRow.target rowEquality
          _ = next := rowTarget
      refine ⟨inSpace space next, ?_, .inSpace _ _⟩
      simpa [ruleStage, ruleSource, ruleTarget] using
        Step.inSpace (program := program) ruleMember
  | @route route routeMember state =>
      have accepted := wireStep_mem_executor program.toCatalog wire
      rw [execute_via, List.mem_append] at accepted
      rcases accepted with localMember | transportMember
      · simp only [List.mem_map] at localMember
        obtain ⟨next, nextMember, rfl⟩ := localMember
        obtain ⟨row, rowMember, rowStage, rowSource, rowTarget⟩ :=
          (mem_fibreTargets_iff program.toCatalog route.sourceSpace state next).1
            nextMember
        obtain ⟨rule, ruleMember, rowEquality⟩ :=
          (mem_toCatalog_fibreRows_iff program row).1 rowMember
        have ruleStage : rule.space = route.sourceSpace := by
          calc
            rule.space = row.stage := by
              simpa [SpaceRule.toFibreRow] using
                congrArg FibreRow.stage rowEquality
            _ = route.sourceSpace := rowStage
        have ruleSource : rule.source = state := by
          calc
            rule.source = row.source := by
              simpa [SpaceRule.toFibreRow] using
                congrArg FibreRow.source rowEquality
            _ = state := rowSource
        have ruleTarget : rule.target = next := by
          calc
            rule.target = row.target := by
              simpa [SpaceRule.toFibreRow] using
                congrArg FibreRow.target rowEquality
            _ = next := rowTarget
        refine ⟨routeCall route.name next, ?_, .route routeMember _⟩
        simpa [ruleSource, ruleTarget] using
          Step.underRoute (program := program) routeMember ruleMember ruleStage
      · simp only [List.mem_map] at transportMember
        obtain ⟨transported, transportedMember, rfl⟩ := transportMember
        obtain ⟨row, rowMember, rowKind, rowRoute, rowSourceStage,
            rowTargetStage, rowSource, rowTarget⟩ :=
          (mem_transportTargets_iff program.toCatalog forwardKind
            (routeIdentity route) route.sourceSpace route.targetSpace state
            transported).1 transportedMember
        obtain ⟨declared, declaredMember, rule, ruleMember, sameName,
            rowEquality⟩ :=
          (mem_toCatalog_transportRows_iff program row).1 rowMember
        have sameIdentity : routeIdentity declared = routeIdentity route := by
          calc
            routeIdentity declared = row.route := by
              simpa [RouteDecl.withRule] using
                congrArg TransportRow.route rowEquality
            _ = routeIdentity route := rowRoute
        have sameDeclaration : declared = route :=
          routeIdentity_injective sameIdentity
        subst declared
        have ruleSource : rule.source = state := by
          calc
            rule.source = row.source := by
              simpa [RouteDecl.withRule] using
                congrArg TransportRow.source rowEquality
            _ = state := rowSource
        have ruleTarget : rule.target = transported := by
          calc
            rule.target = row.target := by
              simpa [RouteDecl.withRule] using
                congrArg TransportRow.target rowEquality
            _ = transported := rowTarget
        refine ⟨inSpace route.targetSpace transported, ?_, .inSpace _ _⟩
        simpa [ruleSource, ruleTarget] using
          Step.applyRoute (program := program) routeMember ruleMember sameName

/-- Consequently every surface step is accepted by the authored GSLT after
elaboration. -/
theorem step_preserved_by_authored_gslt
    (program : Program) {source target : Pattern}
    (step : Step program source target) :
    ∃ sourceIR targetIR,
      Elaborates program source sourceIR ∧
      Elaborates program target targetIR ∧
      (totalTheory program.toCatalog).Step sourceIR targetIR := by
  obtain ⟨sourceIR, targetIR, sourceElaboration, targetElaboration, wire⟩ :=
    step_preserved program step
  exact ⟨sourceIR, targetIR, sourceElaboration, targetElaboration,
    (totalTheory_step_iff_wireStep program.toCatalog
      (by cases sourceElaboration <;> constructor)).2 wire⟩

/-! ## Closure is a derived runner -/

/-- Surface chaining is the ordinary reflexive-transitive closure of the
generating step relation, not an additional generating rewrite. -/
inductive Runs (program : Program) : Pattern → Pattern → Prop where
  | refl (state : Pattern) : Runs program state state
  | tail {source middle target : Pattern} :
      Step program source middle → Runs program middle target →
      Runs program source target

def Runs.single (program : Program) {source target : Pattern}
    (step : Step program source target) : Runs program source target :=
  .tail step (.refl target)

def Runs.trans (program : Program) {first middle last : Pattern}
    (earlier : Runs program first middle)
    (later : Runs program middle last) : Runs program first last :=
  by
    induction earlier with
    | refl => exact later
    | tail step rest inductionHypothesis =>
        exact .tail step (inductionHypothesis later)

/-- A unary command whose name has no route declaration remains inert. -/
theorem unregistered_route_inert (program : Program) (name : String)
    (state : Pattern)
    (unregistered : ∀ route ∈ program.routes, route.name ≠ name) :
    ¬ ∃ target, Step program (routeCall name state) target := by
  rintro ⟨target, step⟩
  cases step with
  | underRoute routeMember _ _ =>
      exact unregistered _ routeMember rfl
  | applyRoute routeMember _ _ =>
      exact unregistered _ routeMember rfl

end Mettapedia.GSLT.LanguageDef.GSLTIL.Surface
