import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryIteration

/-!
# Authored PeTTa drivers for finite fresh-insertion phases

The actual clause selected for the captured destination must have the stated
driver body. Other unmatched equations may remain in the program. The driver
counts the phase, stops on zero and otherwise invokes itself through ordinary
source dispatch. Its source result is true and the final state; the private
worker's phase-count trace is separate evidence, not fabricated output.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryDriver

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst atomFreeVars)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveRegionProvenance
open FlatQueryRowCodec FlatQueryDomainInvariant FiniteNestedQuerySource
open Eval SpaceSemantics NamedSpaces

variable {Value : Type} [DecidableEq Value]

def callee (spaceName : String) (target : Handle) : Subst := [(spaceName, Effects.handleValue target)]

def phase {codec : Codec Value} {names : Inventory String} (queries : List (Query codec names))
    (head : FlatQueryOutputDomain.Head codec names) (spaceName temporary : String) : Atom :=
  .expression [.symbol "size-atom", .expression [.symbol "collapse",
    NestedQuerySource.source (queries.map Query.leg) (FreshQueryMaterialization.bodySource spaceName temporary head.1)]]

def condition (progress : String) : Atom := .expression [.symbol "==", .var progress, .grounded (.int 0)]

def call (driver spaceName : String) : Atom := .expression [.symbol driver, .var spaceName]

def body {codec : Codec Value} {names : Inventory String} (queries : List (Query codec names))
    (head : FlatQueryOutputDomain.Head codec names) (driver spaceName temporary progress : String) : Atom :=
  .expression [.symbol "let", .var progress, phase queries head spaceName temporary,
    .expression [.symbol "if", condition progress, Effects.boolean true, call driver spaceName]]

structure Certificate {codec : Codec Value} {names : Inventory String} (program : Program)
    (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (driver spaceName temporary progress : String) (target : Handle) : Type where
  notIO : ioHead driver = false
  notNative : StdLib.known driver = false
  notControl : driver ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"]
  registered : program.equations.any (·.head == driver) = true
  selected : clauses program driver [Effects.handleValue target] =
    [.evaluate (callee spaceName target) (body queries head driver spaceName temporary progress)]
  freshTemporary : temporary ≠ spaceName
  freshProgress : progress ≠ spaceName
  outside : ∀ query ∈ queries, temporary ∉ atomFreeVars query.source

def prepare {codec : Codec Value} {names : Inventory String} (program : Program)
    (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (driver spaceName temporary progress : String) (target : Handle) :
    Option (Certificate program queries head driver spaceName temporary progress target) :=
  if noIO : ioHead driver = false then
    if noNative : StdLib.known driver = false then
      if ordinary : driver ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"] then
        if registered : program.equations.any (·.head == driver) = true then
          if freshTemp : temporary ≠ spaceName then
            if freshCount : progress ≠ spaceName then
              if outside : ∀ query ∈ queries, temporary ∉ atomFreeVars query.source then
                match chosen : clauses program driver [Effects.handleValue target] with
                | [.evaluate bindings expression] =>
                    if sameBindings : bindings = callee spaceName target then
                      if sameBody : expression = body queries head driver spaceName temporary progress then
                        some ⟨noIO, noNative, ordinary, registered, by simpa only [sameBindings, sameBody] using chosen,
                          freshTemp, freshCount, outside⟩
                      else none
                    else none
                | _ => none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

omit [DecidableEq Value] in
theorem Certificate.calls {codec : Codec Value} {names : Inventory String} {program : Program}
    {queries : List (Query codec names)} {head : FlatQueryOutputDomain.Head codec names}
    {driver spaceName temporary progress : String} {target : Handle}
    (certificate : Certificate program queries head driver spaceName temporary progress target)
    (bindings : Subst) (before after : Effects.State)
    (location : Subst.lookup bindings spaceName = some (Effects.handleValue target))
    (returned : PureReturns program (callee spaceName target) before
      (body queries head driver spaceName temporary progress) after (Effects.boolean true)) :
    PureReturns program bindings before (call driver spaceName) after (Effects.boolean true) := by
  apply authored_variable_call_returns program bindings (callee spaceName target) before after driver [spaceName]
    _ _ certificate.notIO certificate.notNative certificate.registered _ returned certificate.notControl
  simpa only [List.map_cons, List.map_nil, applySubst, location, Option.getD_some] using certificate.selected

theorem phase_returns {codec : Codec Value} {names : Inventory String} (domain : Finset Value)
    (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (program : Program) (spaceName temporary : String) (target : Handle)
    (before after : Effects.State) (answers : List Atom)
    (bound : BindingsInDomain codec names domain (callee spaceName target)) (valid : ViewsInDomain domain queries before)
    (different : temporary ≠ spaceName) (outside : ∀ query ∈ queries, temporary ∉ atomFreeVars query.source)
    (completed : FiniteNestedQuerySource.run queries head target (callee spaceName target) before = some (after, answers)) :
    PureReturns program (callee spaceName target) before (phase queries head spaceName temporary) after (.grounded (.int answers.length)) := by
  have returned := source_returns domain queries head constants program spaceName temporary target (callee spaceName target)
    before after answers bound valid different outside ⟨by simp [callee, Subst.lookup], by simp [callee, Subst.lookup, Ne.symm different]⟩ completed
  have collected := collapse_returns program (callee spaceName target) before after _ _ returned
  exact native_unary_call_returns program (callee spaceName target) before after after "size-atom" _ _ _
    (by decide) (by decide) (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) collected rfl (by decide)

def progressBindings (spaceName progress : String) (target : Handle) (count : Nat) : Subst :=
  (progress, .grounded (.int count)) :: callee spaceName target

theorem condition_returns (program : Program) (spaceName progress : String) (target : Handle)
    (state : Effects.State) (count : Nat) :
    PureReturns program (progressBindings spaceName progress target count) state (condition progress) state
      (Effects.boolean (decide (count = 0))) := by
  have first := variable_returns program (progressBindings spaceName progress target count) state progress
  have firstValue : applySubst (progressBindings spaceName progress target count) (.var progress) = .grounded (.int count) := by
    simp [applySubst, progressBindings, Subst.lookup]
  have equal : ((Atom.grounded (.int count)) == Atom.grounded (.int 0)) = decide (count = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp
  exact native_binary_call_returns program _ state state state state "==" _ _ _ _ _
    (by decide) (by decide)
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument])
    (by simpa only [firstValue] using first) (grounded_returns program _ state (.int 0))
    (by simp only [StdLib.structural_equality, equal]) (by decide)

theorem body_returns {codec : Codec Value} {names : Inventory String} {program : Program}
    {queries : List (Query codec names)} {head : FlatQueryOutputDomain.Head codec names}
    {driver spaceName temporary progress : String} {target : Handle}
    (certificate : Certificate program queries head driver spaceName temporary progress target)
    (domain : Finset Value) (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (bound : BindingsInDomain codec names domain (callee spaceName target))
    (allowance : Nat) (before after : Effects.State) (counts : List Nat) (valid : ViewsInDomain domain queries before)
    (completed : FiniteNestedQueryIteration.iterate queries head target (callee spaceName target) allowance before = some (after, counts)) :
    PureReturns program (callee spaceName target) before (body queries head driver spaceName temporary progress) after (Effects.boolean true) := by
  induction allowance generalizing before after counts with
  | zero => cases completed
  | succ allowance ih =>
      obtain ⟨first, phaseRun, tail⟩ := Option.bind_eq_some_iff.mp completed
      have phaseSource := phase_returns domain queries head constants program spaceName temporary target before first.1 first.2
        bound valid certificate.freshTemporary certificate.outside phaseRun
      have compare := condition_returns program spaceName progress target first.1 first.2.length
      have fresh : Subst.lookup (callee spaceName target) progress = none := by
        simp [callee, Subst.lookup, Ne.symm certificate.freshProgress]
      apply let_returns program (callee spaceName target) (progressBindings spaceName progress target first.2.length)
        before first.1 after (.var progress) _ _ (.grounded (.int first.2.length)) (Effects.boolean true) phaseSource
        (by simp [matchBinding, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, fresh, progressBindings])
      split at tail
      next quiet =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj tail)
        apply if_returns program _ first.1 first.1 first.1 _ (Effects.boolean true) _ _ _
          (by simpa only [quiet, decide_true] using compare)
        simpa [Effects.boolean] using grounded_returns program (progressBindings spaceName progress target first.2.length) first.1 (.bool true)
      next productive =>
        obtain ⟨later, continued, same⟩ := Option.bind_eq_some_iff.mp tail
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
        have nextValid := run_preserves domain queries queries (fun _ member => member) head constants target (callee spaceName target)
          before first.1 first.2 bound valid phaseRun
        have recursive := certificate.calls (progressBindings spaceName progress target first.2.length) first.1 later.1
          (by simp [progressBindings, callee, Subst.lookup, certificate.freshProgress])
          (ih first.1 later.1 later.2 nextValid continued)
        apply if_returns program _ first.1 first.1 later.1 _ (Effects.boolean false) _ _ _
          (by simpa only [productive, decide_false] using compare)
        simpa [Effects.boolean] using recursive

/-- Finite source data, static coverage and actual recursive dispatch jointly
give a completed source call and a saturated final state. -/
theorem terminates {codec : Codec Value} {names : Inventory String} {program : Program}
    {queries : List (Query codec names)} {head : FlatQueryOutputDomain.Head codec names}
    {driver spaceName temporary progress : String} {target : Handle}
    (certificate : Certificate program queries head driver spaceName temporary progress target)
    (domain : Finset Value) (data : FiniteNestedQueryCompletion.DataHead head)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (bound : BindingsInDomain codec names domain (callee spaceName target))
    (covered : FiniteNestedQueryCompletion.Covered queries (callee spaceName target))
    (before : Effects.State) (rows : List Atom) (valid : ViewsInDomain domain queries before)
    (snapshot : before.read target = some rows) :
    ∃ after counts,
      FiniteNestedQueryIteration.iterate queries head target (callee spaceName target)
        (domain.card ^ head.2.cells.length + 1) before = some (after, counts) ∧
      PureReturns program (callee spaceName target) before (call driver spaceName) after (Effects.boolean true) ∧
      FreshNestedQuerySource.SaturatedAt after target head.1 (queries.map Query.leg) (callee spaceName target) := by
  obtain ⟨after, counts, completed⟩ := FiniteNestedQueryIteration.catalogue_allowance domain queries head data constants target
    (callee spaceName target) before rows bound valid covered snapshot
  refine ⟨after, counts, completed, ?_, ?_⟩
  · exact certificate.calls (callee spaceName target) before after (by simp [callee, Subst.lookup])
      (body_returns certificate domain constants bound _ before after counts valid completed)
  · exact FiniteNestedQueryIteration.saturated domain queries head constants target (callee spaceName target)
      _ before after counts bound valid completed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryDriver
