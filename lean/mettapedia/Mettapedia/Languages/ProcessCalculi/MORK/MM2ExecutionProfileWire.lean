import Mettapedia.Languages.ProcessCalculi.MORK.ProviderExtension

/-!
# Canonical execution-profile wire for MM2

The native support-transform compiler consumes this wire as authored data.
Its core source and sink declarations are projected from the same provider
catalog used by the Lean execution semantics.  Runtime extensions that do not
yet have contracts in that catalog remain separately identified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire

open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ProviderExtension

/-- A syntax spelling, arity, and semantic identity for one provider. -/
structure OperatorDecl where
  interface : String
  arity : Nat
  semanticId : String
deriving Repr, DecidableEq

def OperatorDecl.asProvider (role : ProviderRole)
    (declaration : OperatorDecl) : ProviderDecl :=
  { role
    interface := declaration.interface
    arity := declaration.arity
    semanticId := declaration.semanticId }

inductive SchedulerPolicy where
  | leastMorkCompactExpressionKey
deriving Repr, DecidableEq

inductive TransitionLaw where
  | consumeSelected
  | snapshotIncludesSelected
  | relationalProductMayReuseSupport
  | stageAllMatchesPerSink
  | finalizeSinksLeftToRight
deriving Repr, DecidableEq

inductive FuelPolicy where
  | exactUpperBound
deriving Repr, DecidableEq

inductive CompletionPolicy where
  | noSupportedWork
deriving Repr, DecidableEq

inductive ObservationPolicy where
  | support
deriving Repr, DecidableEq

structure WorkShell where
  head : String
  arity : Nat
  locationPosition : Nat
  inputPosition : Nat
  outputPosition : Nat
deriving Repr, DecidableEq

structure InputProfile where
  compatibility : OperatorDecl
  explicitHead : String
  explicitSources : List OperatorDecl
deriving Repr, DecidableEq

structure OutputProfile where
  compatibility : OperatorDecl
  explicitHead : String
  coreSinks : List OperatorDecl
  extensionSinks : List OperatorDecl
deriving Repr, DecidableEq

/-- The finite authored data consumed by the generic support-transform
compiler.  Provider extension declarations are retained separately from the
catalogued core so their different proof status cannot be erased by rendering.
-/
structure ExecutionPresentation where
  name : String
  profile : String
  carrier : String
  workShell : WorkShell
  scheduler : SchedulerPolicy
  unsupported : UnsupportedExecPolicy
  transitions : List TransitionLaw
  input : InputProfile
  output : OutputProfile
  fuel : FuelPolicy
  completion : CompletionPolicy
  observation : ObservationPolicy
deriving Repr, DecidableEq

def snapshotMatch : OperatorDecl :=
  { interface := ",", arity := 1,
    semanticId := "support.snapshot-match.v1" }

def btmMatch : OperatorDecl :=
  { interface := "BTM", arity := 1,
    semanticId := "support.snapshot-match.v1" }

def equalMatch : OperatorDecl :=
  { interface := "==", arity := 2,
    semanticId := "support.equal.v1" }

def notEqualMatch : OperatorDecl :=
  { interface := "!=", arity := 2,
    semanticId := "support.not-equal.v1" }

def compatibilityAdd : OperatorDecl :=
  { interface := ",", arity := 1, semanticId := "support.add.v1" }

def addSink : OperatorDecl :=
  { interface := "+", arity := 1, semanticId := "support.add.v1" }

def removeSink : OperatorDecl :=
  { interface := "-", arity := 1, semanticId := "support.remove.v1" }

def headSink : OperatorDecl :=
  { interface := "head", arity := 2, semanticId := "support.head.v1" }

def tailSink : OperatorDecl :=
  { interface := "tail", arity := 2, semanticId := "support.tail.v1" }

/-- Cardinality is a declared runtime extension.  Its batch law is not part of
`supportCoreCatalog`. -/
def countSink : OperatorDecl :=
  { interface := "count", arity := 3,
    semanticId := "support.group-cardinality.v1" }

/-- Exact floating evaluation is a declared foreign-provider extension.  It
is not assigned the meaning of an ordinary support sink. -/
def pureSink : OperatorDecl :=
  { interface := "pure", arity := 3,
    semanticId := "support.evaluate-project.mm2-pure-f64.v1" }

/-- The maintained open-world MM2 execution presentation. -/
def presentation : ExecutionPresentation :=
  { name := "mm2"
    profile := "gslt"
    carrier := "support"
    workShell :=
      { head := "exec", arity := 3, locationPosition := 0,
        inputPosition := 1, outputPosition := 2 }
    scheduler := .leastMorkCompactExpressionKey
    unsupported := .leaveInert
    transitions :=
      [ .consumeSelected
      , .snapshotIncludesSelected
      , .relationalProductMayReuseSupport
      , .stageAllMatchesPerSink
      , .finalizeSinksLeftToRight ]
    input :=
      { compatibility := snapshotMatch
        explicitHead := "I"
        explicitSources := [btmMatch, equalMatch, notEqualMatch] }
    output :=
      { compatibility := compatibilityAdd
        explicitHead := "O"
        coreSinks := [addSink, removeSink, headSink, tailSink]
        extensionSinks := [countSink, pureSink] }
    fuel := .exactUpperBound
    completion := .noSupportedWork
    observation := .support }

def ExecutionPresentation.coreProviderDeclarations
    (source : ExecutionPresentation) : List ProviderDecl :=
  source.input.compatibility.asProvider .source ::
    source.input.explicitSources.map (OperatorDecl.asProvider .source) ++
    source.output.compatibility.asProvider .sink ::
    source.output.coreSinks.map (OperatorDecl.asProvider .sink)

def ExecutionPresentation.extensionProviderDeclarations
    (source : ExecutionPresentation) : List ProviderDecl :=
  source.output.extensionSinks.map (OperatorDecl.asProvider .sink)

theorem core_provider_declarations_exact :
    presentation.coreProviderDeclarations =
      [ { role := .source, interface := ",", arity := 1,
          semanticId := "support.snapshot-match.v1" }
      , { role := .source, interface := "BTM", arity := 1,
          semanticId := "support.snapshot-match.v1" }
      , { role := .source, interface := "==", arity := 2,
          semanticId := "support.equal.v1" }
      , { role := .source, interface := "!=", arity := 2,
          semanticId := "support.not-equal.v1" }
      , { role := .sink, interface := ",", arity := 1,
          semanticId := "support.add.v1" }
      , { role := .sink, interface := "+", arity := 1,
          semanticId := "support.add.v1" }
      , { role := .sink, interface := "-", arity := 1,
          semanticId := "support.remove.v1" }
      , { role := .sink, interface := "head", arity := 2,
          semanticId := "support.head.v1" }
      , { role := .sink, interface := "tail", arity := 2,
          semanticId := "support.tail.v1" } ] := by
  rfl

theorem core_provider_declarations_admitted :
    LibraryAdmissible supportCoreCatalog
      presentation.coreProviderDeclarations = true := by
  decide +kernel

/-- The core profile is an admitted provider-library fibre over the exact
support catalog used by the Lean execution semantics. -/
noncomputable def coreLibrary : AdmittedLibrary supportCoreCatalog :=
  ⟨presentation.coreProviderDeclarations,
    core_provider_declarations_admitted⟩

/-- Every catalogued operator named by the execution profile resolves to the
existing law-bearing duplicate-free-list implementation.  The comma forms are
aliases: physical selection depends on semantic identity, role, and arity.
-/
theorem cSupportCoreFactory_covers_profile_core :
    cSupportCoreFactory.Covers coreLibrary := by
  intro declaration member
  have coreCover (canonical : ProviderDecl)
      (canonicalMember : canonical ∈ supportCoreDeclarations) :
      canonical.nativeKey ∈
        cSupportCoreFactory.providers.map NativeProviderWitness.nativeKey := by
    exact cSupportCoreFactory_covers canonical (by
      change canonical ∈ supportCoreDeclarations
      exact canonicalMember)
  change declaration ∈ presentation.coreProviderDeclarations at member
  rw [core_provider_declarations_exact] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [ProviderDecl.nativeKey, OperatorDecl.asProvider, snapshotMatch,
      btmMatch] using coreCover (btmMatch.asProvider .source) (by decide)
  · exact coreCover (btmMatch.asProvider .source) (by decide)
  · exact coreCover (equalMatch.asProvider .source) (by decide)
  · exact coreCover (notEqualMatch.asProvider .source) (by decide)
  · simpa [ProviderDecl.nativeKey, OperatorDecl.asProvider, compatibilityAdd,
      addSink] using coreCover (addSink.asProvider .sink) (by decide)
  · exact coreCover (addSink.asProvider .sink) (by decide)
  · exact coreCover (removeSink.asProvider .sink) (by decide)
  · exact coreCover (headSink.asProvider .sink) (by decide)
  · exact coreCover (tailSink.asProvider .sink) (by decide)

theorem extension_provider_declarations_exact :
    presentation.extensionProviderDeclarations =
      [ { role := .sink, interface := "count", arity := 3,
          semanticId := "support.group-cardinality.v1" }
      , { role := .sink, interface := "pure", arity := 3,
          semanticId := "support.evaluate-project.mm2-pure-f64.v1" } ] := by
  rfl

/-- Neither declared extension is silently admitted by the smaller support
catalog.  Each needs its own batch or foreign-provider contract. -/
theorem extensions_not_in_support_core :
    presentation.extensionProviderDeclarations.all
      (fun declaration => !declaration.catalogued supportCoreCatalog) = true := by
  decide +kernel

private def renderScheduler : SchedulerPolicy -> String
  | .leastMorkCompactExpressionKey =>
      "least-mork-compact-expression-key-v1"

private def renderUnsupported : UnsupportedExecPolicy -> String
  | .leaveInert => "leave-inert"
  | .consume => "consume"

private def renderTransition : TransitionLaw -> String
  | .consumeSelected => "consume-selected"
  | .snapshotIncludesSelected => "snapshot-includes-selected"
  | .relationalProductMayReuseSupport =>
      "relational-product-may-reuse-support"
  | .stageAllMatchesPerSink => "stage-all-matches-per-sink"
  | .finalizeSinksLeftToRight => "finalize-sinks-left-to-right"

private def renderFuel : FuelPolicy -> String
  | .exactUpperBound => "exact-upper-bound"

private def renderCompletion : CompletionPolicy -> String
  | .noSupportedWork => "no-supported-work"

private def renderObservation : ObservationPolicy -> String
  | .support => "support"

private def renderExplicitOperator (kind : String)
    (declaration : OperatorDecl) : String :=
  "    (" ++ kind ++ " " ++ declaration.interface ++ " " ++
    toString declaration.arity ++ " " ++ declaration.semanticId ++ ")"

private def renderTransitions (laws : List TransitionLaw) : String :=
  String.intercalate "\n" (laws.map fun law => "    " ++ renderTransition law)

private def renderExplicitOperators (kind : String)
    (declarations : List OperatorDecl) : String :=
  String.intercalate "\n" (declarations.map (renderExplicitOperator kind))

private def wireHeader : String :=
  "; Strict, open-world MM2 support-transform profile.\n" ++
  ";\n" ++
  "; This presentation defines one finite-set work-queue GSLT.  Its C\n" ++
  "; realizations are generic over every symbol below: the authored profile owns\n" ++
  "; the vocabulary and policies, while native C and Rust/PathMap via C ABI own\n" ++
  "; only structural terms, matching, finite support, exact resource bounds, and\n" ++
  "; diagnostics.\n"

/-- Render one typed execution presentation to the generic compiler wire. -/
def render (source : ExecutionPresentation) : String :=
  let shell := source.workShell
  wireHeader ++
  "(gslt-support-transform-language-v1\n" ++
  "  (name " ++ source.name ++ ")\n" ++
  "  (profile " ++ source.profile ++ ")\n" ++
  "  (carrier " ++ source.carrier ++ ")\n" ++
  "  (work-shell " ++ shell.head ++ " " ++ toString shell.arity ++ " " ++
    toString shell.locationPosition ++ " " ++ toString shell.inputPosition ++
    " " ++ toString shell.outputPosition ++ ")\n" ++
  "  (scheduler " ++ renderScheduler source.scheduler ++ ")\n" ++
  "  (unsupported " ++ renderUnsupported source.unsupported ++ ")\n" ++
  "  (transition\n" ++ renderTransitions source.transitions ++ ")\n" ++
  "  (input-compat \"" ++ source.input.compatibility.interface ++ "\" " ++
    source.input.compatibility.semanticId ++ ")\n" ++
  "  (input-explicit " ++ source.input.explicitHead ++ "\n" ++
    renderExplicitOperators "source" source.input.explicitSources ++ ")\n" ++
  "  (output-compat \"" ++ source.output.compatibility.interface ++ "\" " ++
    source.output.compatibility.semanticId ++ ")\n" ++
  "  (output-explicit " ++ source.output.explicitHead ++ "\n" ++
    renderExplicitOperators "sink"
      (source.output.coreSinks ++ source.output.extensionSinks) ++ ")\n" ++
  "  (fuel " ++ renderFuel source.fuel ++ ")\n" ++
  "  (completion " ++ renderCompletion source.completion ++ ")\n" ++
  "  (observation " ++ renderObservation source.observation ++ "))\n"

/-- Canonical generated execution-profile source. -/
def wire : String := render presentation

theorem wire_nonempty : wire ≠ "" := by
  decide +kernel

private def presentationWithoutNotEqual : ExecutionPresentation :=
  { presentation with
    input :=
      { presentation.input with
        explicitSources := [btmMatch, equalMatch] } }

/-- Removing a modeled source operator changes the generated source. -/
theorem removing_not_equal_changes_wire :
    render presentationWithoutNotEqual ≠ wire := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms core_provider_declarations_exact
#print axioms core_provider_declarations_admitted
#print axioms cSupportCoreFactory_covers_profile_core
#print axioms extension_provider_declarations_exact
#print axioms extensions_not_in_support_core
#print axioms wire_nonempty
#print axioms removing_not_equal_changes_wire

end Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire
