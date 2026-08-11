import Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone
import Mettapedia.GSLT.LanguageDef.OracleExtension
import Mettapedia.Languages.ProcessCalculi.MORK.GSLTSemantics

/-!
# Authored MM2 source and sink providers

MM2's compact calculus delegates substantial behavior to named sources and
sinks.  This module keeps three levels separate:

* `ProviderSyntax` is the compositional authored declaration language;
* `SemanticCatalog` assigns mathematical behavior to semantic identities;
* native source and sink realizations carry pointwise refinement laws.

The sink realization interface exposes an opaque stage state, but staging has
no live-space argument.  All rows are staged before the one finalization that
may update the live space.  This is the semantic boundary needed by generated
C or Rust plugin tables; it is not a host implementation stored in the
language definition.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.ProviderExtension

open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone
open Mettapedia.GSLT.LanguageDef.OracleExtension
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.MORK

/-! ## Authored declarations -/

/-- Whether a provider participates in input matching or output finalization. -/
inductive ProviderRole where
  | source
  | sink
deriving Repr, DecidableEq

/-- One language-visible source or sink declaration.

`semanticId` names authored behavior, whereas `surface` is the spelling used
inside an MM2 directive.  A native library registers against the former and
must separately prove that it realizes the catalog meaning. -/
structure ProviderDecl where
  role : ProviderRole
  surface : String
  arity : Nat
  semanticId : String
deriving Repr, DecidableEq

/-- Structural source syntax for provider declarations. -/
inductive ProviderSyntax where
  | declare (role : ProviderRole) (surface : String) (arity : Nat)
      (semanticId : String)
deriving Repr, DecidableEq

def encodeProvider (declaration : ProviderDecl) : ProviderSyntax :=
  .declare declaration.role declaration.surface declaration.arity
    declaration.semanticId

def decodeProvider : ProviderSyntax → ProviderDecl
  | .declare role surface arity semanticId =>
      { role, surface, arity, semanticId }

@[simp] theorem decodeProvider_encodeProvider (declaration : ProviderDecl) :
    decodeProvider (encodeProvider declaration) = declaration := by
  cases declaration
  rfl

@[simp] theorem encodeProvider_decodeProvider (source : ProviderSyntax) :
    encodeProvider (decodeProvider source) = source := by
  cases source
  rfl

def providerCodec : ExactDeclarationCodec ProviderSyntax ProviderDecl where
  encode := encodeProvider
  decode := decodeProvider
  decode_encode := decodeProvider_encodeProvider
  encode_decode := encodeProvider_decodeProvider

/-! ## Semantic catalogs and admission -/

abbrev SourceRows := List (Subst × Atom)

/-- Mathematical contract for one source identity.  Rejected arguments are
not an empty match: the surrounding interpreter leaves their directive inert.
An accepted source may successfully return the empty row list. -/
structure SourceContract (Fault : Type) where
  arity : Nat
  accepts : List Atom → Bool
  run : Subst → Space → List Atom → Except Fault SourceRows

/-- Mathematical contract for one sink identity.  Rows are supplied as one
batch, making its occurrence/support algebra an explicit part of the meaning. -/
structure SinkContract (Fault : Type) where
  arity : Nat
  accepts : List Atom → Bool
  run : List Atom → List Subst → Space → Except Fault Space

/-- An extensible catalog of authored meanings.  Missing identities are not
errors; a profile mentioning one simply fails admission. -/
structure SemanticCatalog (Fault : Type) where
  source : String → Option (SourceContract Fault)
  sink : String → Option (SinkContract Fault)

def ProviderDecl.catalogued (catalog : SemanticCatalog Fault)
    (declaration : ProviderDecl) : Bool :=
  match declaration.role with
  | .source =>
      match catalog.source declaration.semanticId with
      | none => false
      | some contract => decide (contract.arity = declaration.arity)
  | .sink =>
      match catalog.sink declaration.semanticId with
      | none => false
      | some contract => decide (contract.arity = declaration.arity)

def ProviderDecl.admissibleFor (catalog : SemanticCatalog Fault)
    (declaration : ProviderDecl) : Bool :=
  !declaration.surface.isEmpty &&
    !declaration.semanticId.isEmpty &&
    declaration.catalogued catalog

/-- A provider library has unique surfaces on each side of the interaction
boundary and every semantic identity is supplied by its catalog.  Source and
sink surfaces may intentionally share a spelling, as comma input/output do. -/
def LibraryAdmissible (catalog : SemanticCatalog Fault)
    (declarations : List ProviderDecl) : Bool :=
  decide (declarations.map (fun declaration =>
      (declaration.role, declaration.surface))).Nodup &&
    declarations.all (ProviderDecl.admissibleFor catalog)

abbrev AdmittedLibrary (catalog : SemanticCatalog Fault) :=
  { declarations : List ProviderDecl //
    LibraryAdmissible catalog declarations = true }

def providerAuthoringGSLT : DeclarationAuthoringGSLT ProviderDecl :=
  providerCodec.compositionalElaboration

def providerDocumentGSLT : Mettapedia.GSLT.GSLT :=
  providerAuthoringGSLT.authoring.theory

private def elaborateLibrary? (catalog : SemanticCatalog Fault)
    (source : DeclarationDocument ProviderSyntax) :
    Option (AdmittedLibrary catalog) :=
  let declarations := providerCodec.elaborate source
  if admitted : LibraryAdmissible catalog declarations = true then
    some ⟨declarations, admitted⟩
  else
    none

private def quoteLibrary (catalog : SemanticCatalog Fault)
    (library : AdmittedLibrary catalog) :
    DeclarationDocument ProviderSyntax :=
  providerCodec.quote library.1

/-- Provider declarations are a catalog-indexed, coGSLT-authored layer. -/
def layer (Fault : Type) : CoGSLTLayer (SemanticCatalog Fault) where
  Fiber := AdmittedLibrary
  sourceGSLT := fun _ => providerDocumentGSLT
  elaborate := elaborateLibrary?
  quote := quoteLibrary
  elaborate_quote := by
    intro catalog library
    simp [quoteLibrary, elaborateLibrary?,
      ExactDeclarationCodec.elaborate_quote, library.2]
  elaborate_equation := by
    intro catalog source target equal
    unfold elaborateLibrary?
    rw [providerCodec.elaborate_equation equal]
  elaborate_rewrite := by
    intro catalog source target impossible
    exact False.elim impossible

@[simp] theorem layer_elaborate_quote (catalog : SemanticCatalog Fault)
    (library : AdmittedLibrary catalog) :
    (layer Fault).elaborate catalog ((layer Fault).quote catalog library) =
      some library :=
  (layer Fault).elaborate_quote catalog library

/-! ## Oracle-interface projection -/

/-- The small type vocabulary exposed by the generated provider ABI. -/
def providerAbiLanguage : LanguageDef :=
  { LanguageDef.empty "mm2-provider-abi" with
    types := ["Atom", "Substitution", "Space", "Rows"] }

private def providerOracleName (declaration : ProviderDecl) : String :=
  match declaration.role with
  | .source => "source/" ++ declaration.surface ++ "/" ++ declaration.semanticId
  | .sink => "sink/" ++ declaration.surface ++ "/" ++ declaration.semanticId

/-- Every provider declaration induces a typed oracle interface.  This is the
projection consumed by a generic FFI generator; the richer provider layer
retains batching and interpretation role. -/
def ProviderDecl.toOracleDecl (declaration : ProviderDecl) : OracleDecl :=
  let arguments := List.replicate declaration.arity (.base "Atom")
  match declaration.role with
  | .source =>
      { name := providerOracleName declaration
        argTypes := [.base "Substitution", .base "Space"] ++ arguments
        resultType := .base "Rows" }
  | .sink =>
      { name := providerOracleName declaration
        argTypes := arguments ++ [.base "Rows", .base "Space"]
        resultType := .base "Space" }

/-- The generated oracle signature mentions only types declared by the
provider ABI language. -/
theorem toOracleDecl_admissible (declaration : ProviderDecl) :
    Mettapedia.GSLT.LanguageDef.OracleExtension.OracleDecl.admissibleFor
      providerAbiLanguage declaration.toOracleDecl = true := by
  cases declaration with
  | mk role surface arity semanticId =>
      cases role <;>
        simp [ProviderDecl.toOracleDecl, providerOracleName,
          Mettapedia.GSLT.LanguageDef.OracleExtension.OracleDecl.admissibleFor,
          TypeDeclaredBy, providerAbiLanguage, TypeExpr.baseNames,
          LanguageDef.typeNames, TypeDecl.plain]

/-! ## Law-bearing native realizations -/

/-- Relational refinement for fallible provider results.  Successful native
and semantic values are compared by the declared observation relation; faults
must agree exactly. -/
inductive ExceptRefines (valueRefines : NativeValue → SemanticValue → Prop) :
    Except Fault NativeValue → Except Fault SemanticValue → Prop where
  | ok {native semantic} : valueRefines native semantic →
      ExceptRefines valueRefines (.ok native) (.ok semantic)
  | error (fault : Fault) :
      ExceptRefines valueRefines (.error fault) (.error fault)

/-- A native source implementation may use a different physical space and row
carrier.  Its declared row observation is relational, so a support-valued
language need not pretend that native enumeration order is semantic. -/
structure NativeSourceRealization (contract : SourceContract Fault)
    (NativeSpace NativeRows : Type) where
  observeSpace : NativeSpace → Space
  validSpace : NativeSpace → Prop
  rowsRefine : NativeRows → SourceRows → Prop
  accepts : List Atom → Bool
  run : Subst → NativeSpace → List Atom → Except Fault NativeRows
  accepts_refines : ∀ arguments, accepts arguments = contract.accepts arguments
  run_refines : ∀ substitution nativeSpace arguments,
    validSpace nativeSpace →
    contract.accepts arguments = true →
      ExceptRefines rowsRefine
        (run substitution nativeSpace arguments)
        (contract.run substitution (observeSpace nativeSpace) arguments)

/-- Stage rows without access to the live space.  This restriction is the
formal counterpart of a provider ABI whose `stage` callback receives only its
opaque state, invocation arguments, and one substitution row. -/
def stageRows (stage : List Atom → State → Subst → Except Fault State)
    (arguments : List Atom) : State → List Subst → Except Fault State
  | state, [] => .ok state
  | state, row :: rows => do
      let next ← stage arguments state row
      stageRows stage arguments next rows

def observeExcept (observe : NativeSpace → Space) :
    Except Fault NativeSpace → Except Fault Space
  | .ok native => .ok (observe native)
  | .error fault => .error fault

/-- A native sink implementation has an opaque stage type and a single
finalizer.  Its refinement law is observation-indexed so list-backed C and
PathMap-backed Rust realizations may use different physical carriers. -/
structure NativeSinkRealization (contract : SinkContract Fault)
    (NativeSpace : Type) where
  Stage : Type
  observe : NativeSpace → Space
  accepts : List Atom → Bool
  init : List Atom → Stage
  stage : List Atom → Stage → Subst → Except Fault Stage
  finalize : List Atom → Stage → NativeSpace → Except Fault NativeSpace
  accepts_refines : ∀ arguments, accepts arguments = contract.accepts arguments
  run_refines : ∀ arguments rows native,
    contract.accepts arguments = true →
      observeExcept observe (do
        let staged ← stageRows stage arguments (init arguments) rows
        finalize arguments staged native) =
      contract.run arguments rows (observe native)

/-- Physical implementations are selected by semantic identity, role, and
arity.  Surface spellings are deliberately absent: aliases are a property of
the authored library, not a second implementation identity. -/
structure NativeProviderKey where
  role : ProviderRole
  semanticId : String
  arity : Nat
deriving Repr, DecidableEq

def ProviderDecl.nativeKey (declaration : ProviderDecl) : NativeProviderKey :=
  { role := declaration.role
    semanticId := declaration.semanticId
    arity := declaration.arity }

/-- One native implementation together with evidence that its contract is the
meaning selected by the semantic catalog. -/
inductive NativeProviderWitness (catalog : SemanticCatalog Fault)
    (NativeSpace NativeRows : Type) where
  | source (semanticId : String) (contract : SourceContract Fault)
      (catalogued : catalog.source semanticId = some contract)
      (realization : NativeSourceRealization contract NativeSpace NativeRows)
  | sink (semanticId : String) (contract : SinkContract Fault)
      (catalogued : catalog.sink semanticId = some contract)
      (realization : NativeSinkRealization contract NativeSpace)

def NativeProviderWitness.nativeKey
    {catalog : SemanticCatalog Fault} {NativeSpace NativeRows : Type} :
    NativeProviderWitness catalog NativeSpace NativeRows → NativeProviderKey
  | .source semanticId contract _ _ =>
      { role := .source, semanticId, arity := contract.arity }
  | .sink semanticId contract _ _ =>
      { role := .sink, semanticId, arity := contract.arity }

/-- A generated provider factory is a duplicate-free collection of
law-bearing native implementations. -/
structure NativeProviderFactory (catalog : SemanticCatalog Fault)
    (NativeSpace NativeRows : Type) where
  providers : List (NativeProviderWitness catalog NativeSpace NativeRows)
  unique : (providers.map NativeProviderWitness.nativeKey).Nodup

/-- Every declaration in an authored library resolves to a native witness.
Because factory keys omit surface spelling, one implementation may realize
multiple authored aliases without changing their semantics. -/
def NativeProviderFactory.Covers
    {catalog : SemanticCatalog Fault} {NativeSpace NativeRows : Type}
    (factory : NativeProviderFactory catalog NativeSpace NativeRows)
    (library : AdmittedLibrary catalog) : Prop :=
  ∀ declaration ∈ library.1,
    declaration.nativeKey ∈
      factory.providers.map NativeProviderWitness.nativeKey

/-! ## Open-world dispatch -/

def dispatchSource {Fault NativeSpace NativeRows : Type}
    {contract : SourceContract Fault}
    (realization : NativeSourceRealization contract NativeSpace NativeRows)
    (original : Atom) (substitution : Subst) (space : NativeSpace)
    (arguments : List Atom) :
    BoundaryOutcome Atom NativeRows Fault :=
  if realization.accepts arguments then
    match realization.run substitution space arguments with
    | .ok rows => .returned rows
    | .error fault =>
        (BoundaryOutcome.fault fault : BoundaryOutcome Atom NativeRows Fault)
  else
    .inert original

/-- Rejected arguments preserve the entire original source form. -/
theorem dispatchSource_rejected_inert
    {Fault NativeSpace NativeRows : Type} {contract : SourceContract Fault}
    (realization : NativeSourceRealization contract NativeSpace NativeRows)
    (original : Atom) (substitution : Subst) (space : NativeSpace)
    (arguments : List Atom)
    (rejected : realization.accepts arguments = false) :
    dispatchSource realization original substitution space arguments =
      (BoundaryOutcome.inert original :
        BoundaryOutcome Atom NativeRows Fault) := by
  simp [dispatchSource, rejected]

/-- A successful empty relation is observably different from declining to
interpret the source form. -/
theorem returned_empty_ne_inert {Fault : Type} (original : Atom) :
    (BoundaryOutcome.returned ([] : SourceRows) :
      BoundaryOutcome Atom SourceRows Fault) ≠ .inert original := by
  intro impossible
  cases impossible

/-! ## The admitted support-core catalog -/

private def sourceFactorFor (semanticId : String)
    (arguments : List Atom) : Option SourceFactor :=
  match semanticId with
  | "support.snapshot-match.v1" =>
      parseSupportedSourceFactor
        (.expression (.symbol "BTM" :: arguments))
  | "support.equal.v1" =>
      parseSupportedSourceFactor
        (.expression (.symbol "==" :: arguments))
  | "support.not-equal.v1" =>
      parseSupportedSourceFactor
        (.expression (.symbol "!=" :: arguments))
  | _ => none

private def sinkFor (semanticId : String) (arguments : List Atom) : Option Sink :=
  match semanticId with
  | "support.add.v1" =>
      parseSupportedSink (.expression (.symbol "+" :: arguments))
  | "support.remove.v1" =>
      parseSupportedSink (.expression (.symbol "-" :: arguments))
  | "support.head.v1" =>
      parseSupportedSink (.expression (.symbol "head" :: arguments))
  | "support.tail.v1" =>
      parseSupportedSink (.expression (.symbol "tail" :: arguments))
  | _ => none

private noncomputable def sourceContractFor (semanticId : String) (arity : Nat) :
    SourceContract String where
  arity := arity
  accepts := fun arguments =>
    decide (arguments.length = arity) &&
      (sourceFactorFor semanticId arguments).isSome
  run := fun substitution space arguments =>
    match sourceFactorFor semanticId arguments with
    | none => .ok []
    | some factor => .ok (matchSourceFactor substitution space factor)

private noncomputable def sinkContractFor (semanticId : String) (arity : Nat) :
    SinkContract String where
  arity := arity
  accepts := fun arguments =>
    decide (arguments.length = arity) &&
      (sinkFor semanticId arguments).isSome
  run := fun arguments rows space =>
    match sinkFor semanticId arguments with
    | none => .ok space
    | some sink =>
        .ok (applyMorkSinkBatch space rows (mkTemplate [sink]))

/-- Catalog for the exact source/sink fragment currently modeled in Lean.
`count` and `pure` are intentionally absent until their batching and foreign
evaluation laws are admitted at this same boundary. -/
noncomputable def supportCoreCatalog : SemanticCatalog String where
  source := fun semanticId =>
    match semanticId with
    | "support.snapshot-match.v1" => some (sourceContractFor semanticId 1)
    | "support.equal.v1" => some (sourceContractFor semanticId 2)
    | "support.not-equal.v1" => some (sourceContractFor semanticId 2)
    | _ => none
  sink := fun semanticId =>
    match semanticId with
    | "support.add.v1" => some (sinkContractFor semanticId 1)
    | "support.remove.v1" => some (sinkContractFor semanticId 1)
    | "support.head.v1" => some (sinkContractFor semanticId 2)
    | "support.tail.v1" => some (sinkContractFor semanticId 2)
    | _ => none

def supportCoreDeclarations : List ProviderDecl :=
  [ { role := .source, surface := "BTM", arity := 1,
      semanticId := "support.snapshot-match.v1" }
  , { role := .source, surface := "==", arity := 2,
      semanticId := "support.equal.v1" }
  , { role := .source, surface := "!=", arity := 2,
      semanticId := "support.not-equal.v1" }
  , { role := .sink, surface := "+", arity := 1,
      semanticId := "support.add.v1" }
  , { role := .sink, surface := "-", arity := 1,
      semanticId := "support.remove.v1" }
  , { role := .sink, surface := "head", arity := 2,
      semanticId := "support.head.v1" }
  , { role := .sink, surface := "tail", arity := 2,
      semanticId := "support.tail.v1" } ]

noncomputable def supportCoreLibrary : AdmittedLibrary supportCoreCatalog :=
  ⟨supportCoreDeclarations, by decide⟩

/-! ### Reference-realization adequacy -/

/-- Support observation forgets row order and duplicate enumeration while
retaining exactly which substitution/witness rows were produced. -/
def SupportRowsRefine (native semantic : SourceRows) : Prop :=
  ∀ row, row ∈ native ↔ row ∈ semantic

private def cSourceRun (semanticId : String) (substitution : Subst)
    (nativeSpace : List Atom) (arguments : List Atom) :
    Except String SourceRows :=
  match sourceFactorFor semanticId arguments with
  | none => .ok []
  | some factor =>
      .ok (Conformance.Computable.cmatchSourceFactor
        substitution nativeSpace factor)

/-- The computable list source provider and the authored source contract have
the same rows, extensionally, after observing the native space as support. -/
theorem cSourceContractFor_refines
    (semanticId : String) (arity : Nat) (arguments : List Atom)
    (factor : SourceFactor)
    (parsed : sourceFactorFor semanticId arguments = some factor)
    (substitution : Subst) (nativeSpace : List Atom)
    (nodup : nativeSpace.Nodup) (resultSubstitution : Subst) (witness : Atom) :
    (resultSubstitution, witness) ∈
        Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.cmatchSourceFactor
          substitution nativeSpace factor ↔
      ∃ rows,
        (sourceContractFor semanticId arity).run substitution
            nativeSpace.toFinset arguments = .ok rows ∧
          (resultSubstitution, witness) ∈ rows := by
  simp only [sourceContractFor, parsed]
  constructor
  · intro matched
    refine ⟨matchSourceFactor substitution nativeSpace.toFinset factor,
      rfl, ?_⟩
    exact Conformance.cmatchSourceFactor_sound substitution nativeSpace
      factor nodup resultSubstitution witness matched
  · rintro ⟨rows, rowsEqual, member⟩
    simp only [Except.ok.injEq] at rowsEqual
    subst rows
    exact Conformance.cmatchSourceFactor_complete substitution nativeSpace
      factor resultSubstitution witness member

/-- The duplicate-free list source implementation is a law-bearing native
realization of the authored support contract. -/
noncomputable def cSourceRealization (semanticId : String) (arity : Nat) :
    NativeSourceRealization (sourceContractFor semanticId arity)
      (List Atom) SourceRows where
  observeSpace := List.toFinset
  validSpace := List.Nodup
  rowsRefine := SupportRowsRefine
  accepts := (sourceContractFor semanticId arity).accepts
  run := cSourceRun semanticId
  accepts_refines := fun _ => rfl
  run_refines := by
    intro substitution nativeSpace arguments nodup _accepted
    cases parsed : sourceFactorFor semanticId arguments with
    | none =>
        simp only [cSourceRun, sourceContractFor, parsed]
        apply ExceptRefines.ok
        simp [SupportRowsRefine]
    | some factor =>
        simp only [cSourceRun, sourceContractFor, parsed]
        apply ExceptRefines.ok
        intro result
        rcases result with ⟨resultSubstitution, witness⟩
        exact ⟨
          Conformance.cmatchSourceFactor_sound substitution nativeSpace
            factor nodup resultSubstitution witness,
          Conformance.cmatchSourceFactor_complete substitution nativeSpace
            factor resultSubstitution witness⟩

/-- The computable staged sink provider realizes the authored batch contract
after observing its duplicate-free list carrier as finite support. -/
theorem cSinkContractFor_refines
    (semanticId : String) (arity : Nat) (arguments : List Atom) (sink : Sink)
    (parsed : sinkFor semanticId arguments = some sink)
    (rows : List Subst) (nativeSpace : List Atom) :
    (Except.ok
        (WQComputable.cApplyMorkSinkBatch rows nativeSpace [sink]).toFinset :
        Except String Space) =
      (sinkContractFor semanticId arity).run arguments rows nativeSpace.toFinset := by
  simp only [sinkContractFor, parsed]
  exact congrArg Except.ok
    (cApplyMorkSinkBatch_toFinset rows nativeSpace [sink])

private def cStageRow (_arguments : List Atom) (state : List Subst)
    (row : Subst) : Except String (List Subst) :=
  .ok (state ++ [row])

@[simp] theorem stageRows_cStageRow (arguments : List Atom)
    (initial rows : List Subst) :
    stageRows cStageRow arguments initial rows = .ok (initial ++ rows) := by
  induction rows generalizing initial with
  | nil => simp [stageRows]
  | cons row rest induction =>
      change stageRows cStageRow arguments (initial ++ [row]) rest =
        .ok (initial ++ row :: rest)
      rw [induction]
      congr 1
      simp [List.append_assoc]

private def cSinkFinalize (semanticId : String) (arguments : List Atom)
    (rows : List Subst) (nativeSpace : List Atom) :
    Except String (List Atom) :=
  match sinkFor semanticId arguments with
  | none => .ok nativeSpace
  | some sink => .ok (WQComputable.cApplyMorkSinkBatch rows nativeSpace [sink])

/-- The list-backed C reference sink is a law-bearing staged realization of
the authored support contract.  Its stage callback cannot inspect or mutate
the live space; the entire row batch is committed by one finalizer. -/
noncomputable def cSinkRealization (semanticId : String) (arity : Nat) :
    NativeSinkRealization (sinkContractFor semanticId arity) (List Atom) where
  Stage := List Subst
  observe := List.toFinset
  accepts := (sinkContractFor semanticId arity).accepts
  init := fun _ => []
  stage := cStageRow
  finalize := cSinkFinalize semanticId
  accepts_refines := fun _ => rfl
  run_refines := by
    intro arguments rows nativeSpace _accepted
    simp only [stageRows_cStageRow, List.nil_append]
    rw [show
      (do
        let staged ← (Except.ok rows : Except String (List Subst))
        cSinkFinalize semanticId arguments staged nativeSpace) =
          cSinkFinalize semanticId arguments rows nativeSpace by rfl]
    cases parsed : sinkFor semanticId arguments with
    | none =>
        simp [cSinkFinalize, sinkContractFor, parsed, observeExcept]
    | some sink =>
        simp only [cSinkFinalize, sinkContractFor, parsed, observeExcept]
        exact congrArg Except.ok
          (cApplyMorkSinkBatch_toFinset rows nativeSpace [sink])

/-- The complete support-core factory for the duplicate-free C-list carrier.
Each entry is selected by semantic identity and carries its catalog-refinement
witness. -/
noncomputable def cSupportCoreFactory :
    NativeProviderFactory supportCoreCatalog (List Atom) SourceRows where
  providers :=
    [ .source "support.snapshot-match.v1"
        (sourceContractFor "support.snapshot-match.v1" 1) rfl
        (cSourceRealization "support.snapshot-match.v1" 1)
    , .source "support.equal.v1"
        (sourceContractFor "support.equal.v1" 2) rfl
        (cSourceRealization "support.equal.v1" 2)
    , .source "support.not-equal.v1"
        (sourceContractFor "support.not-equal.v1" 2) rfl
        (cSourceRealization "support.not-equal.v1" 2)
    , .sink "support.add.v1"
        (sinkContractFor "support.add.v1" 1) rfl
        (cSinkRealization "support.add.v1" 1)
    , .sink "support.remove.v1"
        (sinkContractFor "support.remove.v1" 1) rfl
        (cSinkRealization "support.remove.v1" 1)
    , .sink "support.head.v1"
        (sinkContractFor "support.head.v1" 2) rfl
        (cSinkRealization "support.head.v1" 2)
    , .sink "support.tail.v1"
        (sinkContractFor "support.tail.v1" 2) rfl
        (cSinkRealization "support.tail.v1" 2) ]
  unique := by decide

theorem cSupportCoreFactory_covers :
    cSupportCoreFactory.Covers supportCoreLibrary := by
  intro declaration member
  simp [supportCoreLibrary, supportCoreDeclarations] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ProviderDecl.nativeKey, cSupportCoreFactory,
      NativeProviderWitness.nativeKey, sourceContractFor, sinkContractFor]

/-- Positive alias canary: physical selection is independent of the authored
surface spelling. -/
noncomputable def supportAliasLibrary : AdmittedLibrary supportCoreCatalog :=
  ⟨[{ role := .source, surface := "scan", arity := 1,
      semanticId := "support.snapshot-match.v1" }], by decide⟩

theorem cSupportCoreFactory_covers_alias :
    cSupportCoreFactory.Covers supportAliasLibrary := by
  simp [NativeProviderFactory.Covers, supportAliasLibrary,
    ProviderDecl.nativeKey, cSupportCoreFactory,
    NativeProviderWitness.nativeKey, sourceContractFor]

/-- Positive: the complete admitted support-core library round-trips through
its authored provider-document GSLT. -/
example :
    (layer String).elaborate supportCoreCatalog
        ((layer String).quote supportCoreCatalog supportCoreLibrary) =
      some supportCoreLibrary :=
  layer_elaborate_quote supportCoreCatalog supportCoreLibrary

/-- Negative: a surface without a catalog meaning is rejected. -/
example :
    LibraryAdmissible supportCoreCatalog
      [{ role := .sink, surface := "mystery", arity := 1,
         semanticId := "support.missing.v1" }] = false := by
  decide

/-- Negative: duplicate source surfaces are rejected even when their semantic
identities differ. -/
example :
    LibraryAdmissible supportCoreCatalog
      [{ role := .source, surface := "BTM", arity := 1,
         semanticId := "support.snapshot-match.v1" },
       { role := .source, surface := "BTM", arity := 2,
         semanticId := "support.equal.v1" }] = false := by
  decide

/-- Negative: a known semantic identity cannot be exposed through an ABI with
the wrong arity. -/
example :
    LibraryAdmissible supportCoreCatalog
      [{ role := .source, surface := "BTM2", arity := 2,
         semanticId := "support.snapshot-match.v1" }] = false := by
  decide

section AxiomAudit

#print axioms layer_elaborate_quote
#print axioms toOracleDecl_admissible
#print axioms dispatchSource_rejected_inert
#print axioms returned_empty_ne_inert
#print axioms cSourceContractFor_refines
#print axioms cSinkContractFor_refines
#print axioms stageRows_cStageRow
#print axioms cSinkRealization
#print axioms cSupportCoreFactory_covers
#print axioms cSupportCoreFactory_covers_alias

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.ProviderExtension
