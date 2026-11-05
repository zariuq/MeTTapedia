import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompletePlanWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.RunnerSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StandardWire
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesReady
import Mettapedia.OSLF.MeTTaIL.CollectionRootCoverage
import Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec
import Mettapedia.Languages.MeTTa.PeTTa.StdLib
import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

/-!
# Emitting a runnable MeTTa module for the complete machine

`emit?` takes a plan, a certified search profile, its expected type, how runs commit their
targets and a module name. It checks the obligations remaining for that profile and returns a MeTTa program with four entries over the complete
machine's libraries (`gslt_descent_execution`, `gslt_complete`, `gslt_collection_laws`,
`gslt_canonical`, `gslt_runner`):

- `name:begin source` returns the runner at the source, to continue with `gslt:runner:tick`
  and `gslt:runner:advance`;
- `name:run source ticks quantum` returns the trace of one path after that page: its phase and
  its states in order;
- `name:explore source work` returns the states every path has reached after `work` fair rounds;
- `name:edges source work` returns the transitions found by then, `(Edge state receipt target)`:
  every explored state's published receipts with their targets (`Complete.Graph`).

The class profile emits equations, premises that recurse through any rule, and unstratified plans: the
complete machine's child searches cover every declaration, so the stratification obligation is
not needed (`Complete.Classes`, `Complete.Explore`). The plan is inlined as data with the plan's
own free types as its table, and so are its declared collection and scope-extrusion laws: every
committed state is in their standard form, or in canonical form, which also sorts every unordered
collection, compared by the plan's name table (`StandardWire.planTable`) (`Complete.Normalized`).

The canonical root profile discharges set decomposition using its checked local rule and
algebra conditions and the source comparison of `CollectionRootCoverage`. It uses the same
four entry bodies, native runner and explorer. The public emitter selects a recognized profile
automatically, retaining the class strategy as its fallback.

The canonical occurrence profile also covers nested collection patterns and
permitted typed contexts with nullary guards or checked mixed input/output queries
over canonical finite provider rows. Its checked local conditions derive source
successor coverage, retaining collection-valued output captures and their
ordinary allocation traces. Quantified and child-step premises and additional
equation theories require further qualifications.

`emit?` refuses a plan with any undischarged admission obligation, a plan whose equations are not
balanced (`Predecessors.equationsChecked`, which the theorems of `Complete.Classes` assume), a plan
with dynamic provider relations (the MeTTa provider has no contract of its own yet), a name whose entries could collide with the
runtime's heads, the plan's data or the evaluator's own heads, and a program the renderer cannot
print. The runtime never defines, declares or calls an entry; `emit?` checks this on the runtime
itself.

`emitted_text_reads_back`: the emitted text reads back as exactly the emitted program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Eval
open CompletePlanWire (planTerm)

private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name

/-- What a module is emitted for: a plan, the bound types of its sources (empty for closed
sources), the type of its states, and how its runs commit targets. -/
structure Spec where
  plan : GeneralExecutionAdmission.Plan
  bound : List TypeExpr
  expected : TypeExpr
  mode : Complete.Normalized.Commit

def planAtom (spec : Spec) : Atom :=
  CettaWireAtom.encode (planTerm spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected)

/-- The plan's name table: its constructors and declared free names. -/
def table (spec : Spec) : List String :=
  StandardWire.planTable spec.plan (Complete.Footprint.declaredFootprint spec.plan)

theorem table_for (spec : Spec) : StandardWire.TableFor spec.plan (table spec) :=
  StandardWire.planTable_for spec.plan Complete.Footprint.declared_footprint

/-- The selected search implementation carries its local semantic authority.
The established class strategy remains the fallback. -/
inductive SearchProfile (spec : Spec) where
  | classes
  | rootCollection (certificate : CollectionRootSearch.CoverageProfile spec.plan)
      (closed : spec.bound = []) (canonical : spec.mode = .canonical)
  | collectionOccurrence (certificate : CollectionOccurrenceAdmission.Certificate spec.plan)
      (canonical : spec.mode = .canonical)

/-- Choose a root strategy only from recognized declaration and algebra
conditions. Language names play no role in selection. -/
def admittedProfile (spec : Spec) : SearchProfile spec :=
  if canonical : spec.mode = .canonical then
    if closed : spec.bound = [] then
      match CollectionRootSearch.coverageProfile? spec.plan with
      | some certificate => .rootCollection certificate closed canonical
      | none =>
          match CollectionOccurrenceAdmission.admit? spec.plan with
          | some certificate => .collectionOccurrence certificate canonical
          | none => .classes
    else
      match CollectionOccurrenceAdmission.admit? spec.plan with
      | some certificate => .collectionOccurrence certificate canonical
      | none => .classes
  else .classes

def backendAtom (spec : Spec) : SearchProfile spec → Atom
  | .classes => CompleteExecution.classSearchBackend
  | .rootCollection _ _ _ => CettaWireAtom.encode
      (.application "CollectionRootSearch" [encodeList Term.string (table spec)])
  | .collectionOccurrence _ _ => CettaWireAtom.encode
      (.application "CollectionOccurrenceSearch" [encodeList Term.string (table spec), .natural 0])

/-- How runs commit targets, as the runner reads it. -/
def standardAtom (spec : Spec) : Atom := CettaWireAtom.encode (StandardWire.commitTerm spec.plan spec.mode (table spec))

/-- The libraries an emitted module loads after. -/
abbrev runtime : Program := CompleteExecution.runnerLibrary.runtime

/-! ## The module -/

def beginHead (name : String) : String := name ++ ":begin"
def runHead (name : String) : String := name ++ ":run"
def exploreHead (name : String) : String := name ++ ":explore"
def edgesHead (name : String) : String := name ++ ":edges"

def entries (name : String) : List String := [beginHead name, runHead name, exploreHead name, edgesHead name]

def beginBody (spec : Spec) (profile : SearchProfile spec := .classes) : Atom :=
  a "gslt:runner:begin" [backendAtom spec profile, planAtom spec, standardAtom spec, v "source"]

def runBody (spec : Spec) (profile : SearchProfile spec := .classes) : Atom :=
  a "let" [v "machine", a "gslt:runner:begin" [backendAtom spec profile, planAtom spec, standardAtom spec, v "source"],
    a "let" [v "paged", a "gslt:runner:advance" [backendAtom spec profile, planAtom spec, standardAtom spec, v "ticks", v "quantum",
        v "machine"],
      a "gslt:runner:trace" [v "paged"]]]

def exploreBody (spec : Spec) (profile : SearchProfile spec := .classes) : Atom :=
  a "let" [v "explorer", a "gslt:explore:begin" [backendAtom spec profile, planAtom spec, standardAtom spec, v "source"],
    a "let" [v "explored", a "gslt:explore:rounds" [backendAtom spec profile, planAtom spec, standardAtom spec, v "work", v "explorer"],
      a "gslt:explore:states" [v "explored"]]]

def edgesBody (spec : Spec) (profile : SearchProfile spec := .classes) : Atom :=
  a "let" [v "explorer", a "gslt:explore:begin" [backendAtom spec profile, planAtom spec, standardAtom spec, v "source"],
    a "let" [v "explored", a "gslt:explore:rounds" [backendAtom spec profile, planAtom spec, standardAtom spec, v "work", v "explorer"],
      a "gslt:explore:edges" [backendAtom spec profile, standardAtom spec, v "explored"]]]

/-- `(: head (-> Atom … Atom %Undefined%))`: every argument is passed as data. -/
def declaration (head : String) (arity : Nat) : Atom :=
  .expression [.symbol ":", .symbol head,
    .expression (.symbol "->" :: (List.replicate arity (.symbol "Atom") ++ [.symbol "%Undefined%"]))]

def beginEquation (spec : Spec) (name : String) (profile : SearchProfile spec := .classes) : SpaceSemantics.Equation :=
  ⟨beginHead name, [v "source"], beginBody spec profile⟩
def runEquation (spec : Spec) (name : String) (profile : SearchProfile spec := .classes) : SpaceSemantics.Equation :=
  ⟨runHead name, [v "source", v "ticks", v "quantum"], runBody spec profile⟩
def exploreEquation (spec : Spec) (name : String) (profile : SearchProfile spec := .classes) : SpaceSemantics.Equation :=
  ⟨exploreHead name, [v "source", v "work"], exploreBody spec profile⟩
def edgesEquation (spec : Spec) (name : String) (profile : SearchProfile spec := .classes) : SpaceSemantics.Equation :=
  ⟨edgesHead name, [v "source", v "work"], edgesBody spec profile⟩

/-- The emitted program. -/
def program (spec : Spec) (name : String) (profile : SearchProfile spec := .classes) : Program where
  equations := [beginEquation spec name profile, runEquation spec name profile,
    exploreEquation spec name profile, edgesEquation spec name profile]
  declarations := [declaration (beginHead name) 1, declaration (runHead name) 3, declaration (exploreHead name) 2,
    declaration (edgesHead name) 2]
  layout := [.declaration, .equation, .declaration, .equation, .declaration, .equation, .declaration, .equation]

/-! ## Admission -/

def specialHeads : List String := ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]

/-- The heads that are not the module's own entries. -/
def allowed (name : String) (head : String) : Bool := !(entries name).contains head

def declaredHeadAllowed (name : String) : Atom → Bool
  | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => allowed name head
  | _ => true

/-- The entries are fresh: distinct, not evaluator or standard-library heads, never defined,
declared or called by the runtime, and never named by the inlined plan. -/
def namesFresh (spec : Spec) (name : String) (profile : SearchProfile spec := .classes) : Bool :=
  (entries name).Nodup &&
  (entries name).all (fun head => !specialHeads.contains head && !ioHead head && !StdLib.known head) &&
  allowed name "let" &&
  runtime.equations.all
    (fun equation => allowed name equation.head && codeWithin (allowed name) equation.body) &&
  runtime.declarations.all (declaredHeadAllowed name) &&
  codeWithin (allowed name) (beginBody spec profile) && codeWithin (allowed name) (runBody spec profile) &&
  codeWithin (allowed name) (exploreBody spec profile) && codeWithin (allowed name) (edgesBody spec profile)

/-- The admission obligations the complete machine needs discharged: all but stratification. -/
def pending (plan : GeneralExecutionAdmission.Plan) : List GeneralExecutionAdmission.Obligation :=
  plan.obligations.filter (· != .childStratification)

/-- Obligations are discharged by the selected realization. The class
matcher retains its set restriction. A root profile supplies the independent
source comparison needed to discharge that particular obligation. -/
def pendingFor (spec : Spec) : SearchProfile spec → List GeneralExecutionAdmission.Obligation
  | .classes => pending spec.plan
  | .rootCollection _ _ _ => (pending spec.plan).filter (· != .setDecomposition)
  | .collectionOccurrence _ _ => CollectionOccurrenceAdmission.pending spec.plan

theorem root_pending_discharged {spec : Spec} (certificate : CollectionRootSearch.CoverageProfile spec.plan)
    (closed : spec.bound = []) (canonical : spec.mode = .canonical) :
    pendingFor spec (.rootCollection certificate closed canonical) = [] := by
  have inherited := CollectionExecutionAdmission.inherited_discharged certificate.profile.collection
  unfold CollectionExecutionAdmission.inheritedObligations at inherited
  have reordered : (spec.plan.obligations.filter (· != .childStratification)).filter (· != .setDecomposition) =
      (spec.plan.obligations.filter (· != .setDecomposition)).filter (· != .childStratification) := by
    simp only [List.filter_filter]
    congr 1
    funext obligation
    exact Bool.and_comm _ _
  change (spec.plan.obligations.filter (· != .childStratification)).filter (· != .setDecomposition) = []
  rw [reordered, inherited]
  rfl

theorem occurrence_pending_discharged {spec : Spec}
    (certificate : CollectionOccurrenceAdmission.Certificate spec.plan)
    (canonical : spec.mode = .canonical) :
    pendingFor spec (.collectionOccurrence certificate canonical) = [] :=
  certificate.requirements.pending

/-- Why a language is not emitted. -/
inductive Refusal where
  | obligations (pending : List GeneralExecutionAdmission.Obligation)
  | unbalancedEquations
  | dynamicProvider
  | nameCollision (name : String)
  | unrenderable

/-- **The emitter.** -/
def emit? (spec : Spec) (name : String) (profile : SearchProfile spec := admittedProfile spec) : Except Refusal Program :=
  match pendingFor spec profile with
  | _ :: _ => .error (.obligations (pendingFor spec profile))
  | [] =>
    if Complete.Predecessors.equationsChecked spec.plan then
      if spec.plan.snapshot.provider.dynamicRelations.isEmpty then
        if namesFresh spec name profile then .ok (program spec name profile) else .error (.nameCollision name)
      else .error .dynamicProvider
    else .error .unbalancedEquations

/-- What an emitted module guarantees about its plan and name. -/
structure Emitted (spec : Spec) (name : String) (profile : SearchProfile spec := .classes) : Prop where
  complete : pendingFor spec profile = []
  balanced : Complete.Predecessors.equationsChecked spec.plan = true
  finiteProvider : spec.plan.snapshot.provider.dynamicRelations = []
  fresh : namesFresh spec name profile = true

theorem emit?_ok {spec : Spec} {name : String} {emitted : Program} {profile : SearchProfile spec}
    (ok : emit? spec name profile = .ok emitted) :
    emitted = program spec name profile ∧ Emitted spec name profile := by
  unfold emit? at ok
  split at ok
  · cases ok
  · rename_i none
    split at ok
    · rename_i balanced
      split at ok
      · rename_i finite
        split at ok
        · cases ok
          exact ⟨rfl, ⟨none, balanced, List.isEmpty_iff.mp finite, by assumption⟩⟩
        · cases ok
      · cases ok
    · cases ok

/-! ## The module as text -/

/-- **The emitter, as text.** -/
def emitText? (spec : Spec) (name : String) (profile : SearchProfile spec := admittedProfile spec) : Except Refusal String := do
  let emitted ← emit? spec name profile
  match ReadAfterRender.renderProgram? emitted with
  | some text => pure text
  | none => throw .unrenderable

private theorem loaded_program (spec : Spec) (name : String) (profile : SearchProfile spec) :
    SpaceSemantics.loadedAtoms (program spec name profile) =
      [declaration (beginHead name) 1, (beginEquation spec name profile).toAtom,
       declaration (runHead name) 3, (runEquation spec name profile).toAtom,
       declaration (exploreHead name) 2, (exploreEquation spec name profile).toAtom,
       declaration (edgesHead name) 2, (edgesEquation spec name profile).toAtom] := rfl

/-- **Emitted text reads back as the emitted program**, through the shared source reader. -/
theorem emitted_text_reads_back {spec : Spec} {name : String} {text : String} {profile : SearchProfile spec}
    (emitted : emitText? spec name profile = .ok text) :
    SpaceSemantics.readProgram text = .ok (program spec name profile) := by
  unfold emitText? at emitted
  cases ok : emit? spec name profile with
  | error refusal => rw [ok] at emitted; cases emitted
  | ok produced =>
    rw [ok] at emitted
    simp only [bind, Except.bind] at emitted
    obtain ⟨rfl, _⟩ := emit?_ok ok
    cases rendered : ReadAfterRender.renderProgram? (program spec name profile) with
    | none => rw [rendered] at emitted; cases emitted
    | some rendering =>
      rw [rendered] at emitted
      cases emitted
      have expressionsOnly : ReadAfterRender.AllExpressions (SpaceSemantics.loadedAtoms (program spec name profile)) := by
        rw [loaded_program]
        intro atom member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
      rw [ReadAfterRender.read_render rendered expressionsOnly, loaded_program]
      rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
