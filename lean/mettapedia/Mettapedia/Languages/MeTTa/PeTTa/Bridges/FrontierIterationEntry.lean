import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationRegion

/-!
# Checked authored entry for recursive frontier drivers

Recognition checks the actual driver equation, its locals and counter demand.
Names are parameters. Unrelated equations are retained; additional driver
equations conservatively refuse this grammar. Wrong-arity clauses do not
match the call, but mixed arities can affect source loading, so the conservative
admission profile refuses them too. The phase has its own
operational certificate, so the driver name alone admits no execution route.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.Dynamics.ObservationQualified
open Eval SpaceSemantics EffectfulQuerySource FrontierIterationSource

def equation (driver : String) (names : Names) (phase : Atom) : Equation :=
  ⟨driver, [.var names.frontier, .var names.counter], body driver names phase⟩

def candidates (program : Program) (driver : String) : List Equation :=
  program.equations.filter (fun row => row.head == driver && row.arguments.length == 2)

theorem clauses_candidates (program : Program) (driver : String) (values : List Atom) (arity : values.length = 2) :
    clauses program driver values = (candidates program driver).filterMap (fun row =>
      (matchValue.matchValues [] row.arguments values).map (fun bindings => .evaluate bindings row.body)) := by
  unfold clauses candidates
  rw [List.filterMap_filter]
  congr 1
  funext row
  by_cases sameHead : row.head = driver
  · by_cases sameArity : row.arguments.length = 2
    · simp [sameHead, sameArity]
    · have impossible : matchValue.matchValues [] row.arguments values = none := by
        cases matched : matchValue.matchValues [] row.arguments values with
        | none => rfl
        | some bindings => exact False.elim (sameArity ((matchValues_length matched).trans arity))
      simp [sameHead, sameArity, impossible]
  · simp [sameHead]

theorem selected_clauses (program : Program) (driver : String) (names : Names) (phase : Atom)
    (selected : candidates program driver = [equation driver names phase])
    (frontier : List Atom) (count : Nat) :
    clauses program driver [.expression frontier, number count] =
      [.evaluate (callee names frontier count) (body driver names phase)] := by
  have different : names.frontier ≠ names.counter := by
    have distinct := names.distinct
    simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
    exact distinct.1.1
  rw [clauses_candidates program driver _ rfl, selected]
  simp [equation, matchValue.matchValues, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    Subst.lookup, different, callee]

def prepare (program : Program) (driver : String) (names : Names) (phase : Atom) :
    Option (Certificate program driver names phase) :=
  if profile : ioHead driver = false ∧
      program.equations.all (fun row => row.head != driver || row.arguments.length == 2) = true then
    if notNative : StdLib.known driver = false then
      if notControl : driver ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"] then
        if registered : program.equations.any (·.head == driver) = true then
          if demanded : argumentIsRaw program driver 1 = false then
            match selected : candidates program driver with
            | [row] =>
                if sameHead : row.head = driver then
                  if sameArgs : row.arguments = [.var names.frontier, .var names.counter] then
                    if sameBody : row.body = body driver names phase then
                      have same : row = equation driver names phase := by
                        cases row
                        simp only [equation, Equation.mk.injEq]
                        exact ⟨sameHead, sameArgs, sameBody⟩
                      some ⟨profile.1, notNative, notControl, registered, demanded,
                        selected_clauses program driver names phase (by simpa only [same] using selected)⟩
                    else none
                  else none
                else none
            | _ => none
          else none
        else none
      else none
    else none
  else none

def classify {Regime : Type} (observation : PureCallExtraction.Observation) (regime : Regime)
    (program : Program) (driver : String) (names : Names) (phase : Atom) (worker : Body)
    (law : ∀ bindings before after next, worker bindings before = some (after, next) →
      PureReturns program bindings before phase after (.expression next))
    (fuel : Nat) (frontier : List Atom) (count : Nat) :
    Option (CertifiedRegion (PureCallPortfolio.boundary program (callee names frontier count)
      (FrontierIterationRegion.entry driver names)) Regime) :=
  match observation with
  | .exactPage => none
  | .completedResult => (prepare program driver names phase).map
      (fun certificate => FrontierIterationRegion.region regime certificate worker law fuel frontier count)

theorem accepted_execution_exact {Regime : Type} (observation : PureCallExtraction.Observation) (regime : Regime)
    (program : Program) (driver : String) (names : Names) (phase : Atom) (worker : Body)
    (law : ∀ bindings before after next, worker bindings before = some (after, next) →
      PureReturns program bindings before phase after (.expression next))
    (fuel : Nat) (frontier : List Atom) (count : Nat)
    (plan : CertifiedRegion (PureCallPortfolio.boundary program (callee names frontier count)
      (FrontierIterationRegion.entry driver names)) Regime)
    (accepted : classify observation regime program driver names phase worker law fuel frontier count = some plan)
    (before : Effects.State) :
    plan.execute before = PureCallPortfolio.sourceMeaning program (callee names frontier count)
      (FrontierIterationRegion.entry driver names) before := by
  cases observation with
  | exactPage => cases accepted
  | completedResult =>
      obtain ⟨certificate, _, same⟩ := Option.map_eq_some_iff.mp accepted
      subst plan
      exact FrontierIterationRegion.execute_exact regime certificate worker law fuel frontier count before

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FrontierIterationEntry
