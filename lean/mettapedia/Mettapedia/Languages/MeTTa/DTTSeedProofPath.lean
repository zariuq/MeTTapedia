import Mettapedia.Languages.MeTTa.PeTTa.TypedEval
import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.NatDecl
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.RecursorDecl
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.InductiveDecl
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding

/-!
# DTT Seed Proof Path

A tiny, executable proof path for the he-prime DTT tranche:

1. A typed PeTTa rule application is accepted by the typed evaluation judgment.
2. Erasing the type guard gives an ordinary PeTTa evaluation.
3. The same rule application is sound in the compiled LP model.
4. The TwoSortPiSigmaId side has the matching checked-step shape: a typed closed term
   reduces while preserving its type.

This file is intentionally small. It records the first reusable proof shape for
the typed-example corpus without claiming an end-to-end CeTTa runtime theorem.
-/

namespace Mettapedia.Languages.MeTTa.DTTSeedProofPath

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Logic.LP
open Mettapedia.OSLF.MeTTaIL.LPBridge
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationEnv
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.UnitDecl
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.NatDecl
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.RecursorDecl
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.IndDecl
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.ProfileTheory
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Assembly
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding

/-! ## PeTTa-side typed program -/

def natPattern : Pattern := .apply "Nat" []
def zeroPattern : Pattern := .apply "zero" []
def onePattern : Pattern := .apply "one" []
def succPattern : Pattern := .apply "succ" []
def typedSuccCall : Pattern := .apply "succ" [zeroPattern]

def succTypeAnnotation : Pattern :=
  typeAnnotationPat succPattern (arrowType natPattern natPattern)

def typedSuccRule : RewriteRule :=
  { name := "succ-rule"
    typeContext := []
    left := typedSuccCall
    right := onePattern
    premises := [] }

def typedSuccSpace : PeTTaSpace :=
  { facts := [succTypeAnnotation]
    rules := [typedSuccRule] }

theorem typedSucc_eval :
    TypedPeTTaEval typedSuccSpace typedSuccCall [onePattern] := by
  apply TypedPeTTaEval.ruleApp
      (r := typedSuccRule)
      (bs := [])
      (c := "succ")
      (args := [zeroPattern])
      (q := onePattern)
  · simp [typedSuccSpace]
  · rfl
  · simp [typedSuccRule, typedSuccCall, zeroPattern, matchPattern, matchArgs, mergeBindings]
  · simp [typedSuccRule, onePattern, applyBindings]
  · exact Or.inr
      ⟨natPattern, natPattern,
        MeTTaType.typeAnnotation succPattern (arrowType natPattern natPattern)
          (by simp [typedSuccSpace, succTypeAnnotation])⟩

theorem typedSucc_erases_to_petta :
    PeTTaEval typedSuccSpace typedSuccCall [onePattern] :=
  typedEval_sound typedSucc_eval

theorem typedSucc_rule_lp_sound :
    encodeReduces typedSuccCall onePattern ∈
      leastHerbrandModel (pettaSpaceToLPKB typedSuccSpace) := by
  apply petta_ruleApp_lp_sound
      (s := typedSuccSpace)
      (r := typedSuccRule)
      (bs := [])
      (p := typedSuccCall)
      (q := onePattern)
  · simp [typedSuccSpace]
  · rfl
  · simp [typedSuccRule, typedSuccCall, zeroPattern, matchPattern, matchArgs, mergeBindings]
  · simp [typedSuccRule, onePattern, applyBindings]
  · native_decide

theorem typedSucc_first_proof_path :
    TypedPeTTaEval typedSuccSpace typedSuccCall [onePattern] ∧
    PeTTaEval typedSuccSpace typedSuccCall [onePattern] ∧
    encodeReduces typedSuccCall onePattern ∈
      leastHerbrandModel (pettaSpaceToLPKB typedSuccSpace) :=
  ⟨typedSucc_eval, typedSucc_erases_to_petta, typedSucc_rule_lp_sound⟩

/-! ## TwoSortPiSigmaId-side checked-step shape -/

theorem pureNatAlias_preserves_type_step :
    ∃ A : ScopedTerm 0,
      HasTypeDecl natDeclEnv .nil ((.const natAliasName : ScopedTerm 0)) A ∧
      RedDecl natDeclEnv
        ((.const natAliasName : ScopedTerm 0))
        ((.const natZeroName : ScopedTerm 0)) ∧
      HasTypeDecl natDeclEnv .nil ((.const natZeroName : ScopedTerm 0)) A :=
  natAlias_checked_step

/-! ## Recursor / inductive triangulation seeds -/

theorem pureNatRec_declared_type :
    HasTypeDecl natRecDeclEnv .nil ((.const natRecName : ScopedTerm 0)) natRecType :=
  hasType_natRec

theorem pureNatRec_env_wellFormed :
    DeclEnvWellFormed natRecDeclEnv :=
  natRecDeclEnv_wellFormed

/-- Honest current NatRec status: the recursor type is declared in the oracle
environment, but executable iota rules are not yet generated for Nat. -/
theorem pureNatRec_no_iota_value_yet :
    valueOf? natRecDeclEnv natRecName = none := by
  decide

theorem pureNatRec_generated_iota_obligations_no_value :
    generatedRecursorPilot natRecContract =
      some
        { contract := natRecContract
          obligations := [natRecZeroIotaObligation, natRecSuccIotaObligation]
          value? := none } :=
  generatedRecursorPilot_nat_obligations_no_value

theorem pureNatRec_zero_iota_rule_generated :
    generateClosedIotaRule? natRecZeroIotaObligation =
        some natRecZeroClosedIotaRule ∧
      natRecZeroClosedIotaRule.source = natRecZeroClosedSource ∧
      natRecZeroClosedIotaRule.target = natZeroTerm :=
  ⟨generateClosedIotaRule_nat_zero, natRecZeroClosedIotaRule_source_target⟩

theorem pureNatRec_succ_iota_rule_still_open :
    generateClosedIotaRule? natRecSuccIotaObligation = none :=
  generateClosedIotaRule_nat_succ_still_open

/-- The smallest executable recursor witness currently available is Unit.rec:
it has a checked declaration-aware iota-style run. -/
theorem pureUnitRec_iota_oracle :
    HasTypeDecl unitRecDeclEnv .nil unitRecOnCtor (.const unitTyName) ∧
      RedStarDecl unitRecDeclEnv unitRecOnCtor unitCtorTerm ∧
      HasTypeDecl unitRecDeclEnv .nil unitCtorTerm (.const unitTyName) :=
  unitRecOnCtor_preserves_type_to_result

structure PureUnitRecBoundaryOracle where
  frontier :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage unitRecContract
  sourceType :
    HasTypeDecl unitRecDeclEnv .nil unitRecOnCtor (.const unitTyName)
  reduces :
    RedStarDecl unitRecDeclEnv unitRecOnCtor unitCtorTerm
  targetType :
    HasTypeDecl unitRecDeclEnv .nil unitCtorTerm (.const unitTyName)

/-- Closed Unit-rec seed packaged with the current declaration-side frontier.
This reuses the historically named conditional-frontier package, now discharged
through the declaration-side Church-Rosser theorem. It is a reusable
certificate, not a re-proof of the metatheorem. -/
def pureUnitRec_currentBoundary_conditional_oracle_certificate_of_decl_package
    (hDeclPkg :
      DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    PureUnitRecBoundaryOracle :=
  let hAdm : GeneratedRecursorContractAdmitted unitRecContract :=
    ⟨{ contract := unitRecContract
       obligations := [unitRecCtorIotaObligation]
       value? := some unitRecValue },
      generatedRecursorPilot_unit⟩
  { frontier :=
      generatedRecursorContract_admitted_current_boundary_package_of_conditional_frontier_of_decl_package
        (contract := unitRecContract) hAdm hDeclPkg
    sourceType := pureUnitRec_iota_oracle.1
    reduces := pureUnitRec_iota_oracle.2.1
    targetType := pureUnitRec_iota_oracle.2.2 }

def pureUnitRec_currentBoundary_conditional_oracle_certificate
    : PureUnitRecBoundaryOracle :=
  let hAdm : GeneratedRecursorContractAdmitted unitRecContract :=
    ⟨{ contract := unitRecContract
       obligations := [unitRecCtorIotaObligation]
       value? := some unitRecValue },
      generatedRecursorPilot_unit⟩
  { frontier :=
      generatedRecursorContract_admitted_current_boundary_package_of_conditional_frontier_sealed
        (contract := unitRecContract) hAdm
    sourceType := pureUnitRec_iota_oracle.1
    reduces := pureUnitRec_iota_oracle.2.1
    targetType := pureUnitRec_iota_oracle.2.2 }

theorem pureUnitRec_currentBoundary_conditional_oracle_connection_of_decl_package
    (hDeclPkg :
      DeclChurchRosserFrontierPackage unitRecDeclEnv) :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage unitRecContract ∧
      HasTypeDecl unitRecDeclEnv .nil unitRecOnCtor (.const unitTyName) ∧
      RedStarDecl unitRecDeclEnv unitRecOnCtor unitCtorTerm ∧
      HasTypeDecl unitRecDeclEnv .nil unitCtorTerm (.const unitTyName) :=
  ⟨ pureUnitRec_currentBoundary_conditional_oracle_certificate_of_decl_package hDeclPkg |>.frontier
  , pureUnitRec_currentBoundary_conditional_oracle_certificate_of_decl_package hDeclPkg |>.sourceType
  , pureUnitRec_currentBoundary_conditional_oracle_certificate_of_decl_package hDeclPkg |>.reduces
  , pureUnitRec_currentBoundary_conditional_oracle_certificate_of_decl_package hDeclPkg |>.targetType
  ⟩

theorem pureUnitRec_currentBoundary_conditional_oracle_connection
    :
    GeneratedRecursorCurrentBoundaryConditionalFrontierPackage unitRecContract ∧
      HasTypeDecl unitRecDeclEnv .nil unitRecOnCtor (.const unitTyName) ∧
      RedStarDecl unitRecDeclEnv unitRecOnCtor unitCtorTerm ∧
      HasTypeDecl unitRecDeclEnv .nil unitCtorTerm (.const unitTyName) :=
  ⟨ pureUnitRec_currentBoundary_conditional_oracle_certificate |>.frontier
  , pureUnitRec_currentBoundary_conditional_oracle_certificate |>.sourceType
  , pureUnitRec_currentBoundary_conditional_oracle_certificate |>.reduces
  , pureUnitRec_currentBoundary_conditional_oracle_certificate |>.targetType
  ⟩

/-! ## Smallest he-prime runtime/oracle connection -/

def tutUnitPattern : Pattern := .apply "TutUnit" []
def tutUnitCtorPattern : Pattern := .apply "TutUnitCtor" []
def tutUnitRecSyntaxOnCtorPattern : Pattern :=
  .apply "TutUnitRecSyntax" [tutUnitPattern, tutUnitCtorPattern, tutUnitCtorPattern]

def elaborateTutUnitOraclePattern : Pattern → Option (ScopedTerm 0)
  | .apply "TutUnit" [] => some unitTyTerm
  | .apply "TutUnitCtor" [] => some unitCtorTerm
  | .apply "TutUnitRecSyntax"
      [.apply "TutUnit" [], .apply "TutUnitCtor" [], .apply "TutUnitCtor" []] =>
      some unitRecOnCtor
  | _ => none

structure HePrimeOracleReduction where
  syntaxSource : Pattern
  syntaxTarget : Pattern
  source : ScopedTerm 0
  target : ScopedTerm 0
  sourceElab : elaborateTutUnitOraclePattern syntaxSource = some source
  targetElab : elaborateTutUnitOraclePattern syntaxTarget = some target
  sourceType : HasTypeDecl unitRecDeclEnv .nil source (.const unitTyName)
  reduces : RedStarDecl unitRecDeclEnv source target
  targetType : HasTypeDecl unitRecDeclEnv .nil target (.const unitTyName)

/-- First runtime/oracle bridge: the he-prime syntax call
`(TutUnitRecSyntax TutUnit TutUnitCtor TutUnitCtor)` is the same closed
Unit-rec computation witnessed by the TwoSortPiSigmaId oracle. -/
def hePrime_tutUnitRecSyntax_oracle_certificate : HePrimeOracleReduction :=
  { syntaxSource := tutUnitRecSyntaxOnCtorPattern
    syntaxTarget := tutUnitCtorPattern
    source := unitRecOnCtor
    target := unitCtorTerm
    sourceElab := rfl
    targetElab := rfl
    sourceType := pureUnitRec_iota_oracle.1
    reduces := pureUnitRec_iota_oracle.2.1
    targetType := pureUnitRec_iota_oracle.2.2 }

theorem hePrime_tutUnitRecSyntax_oracle_connection :
    elaborateTutUnitOraclePattern tutUnitRecSyntaxOnCtorPattern = some unitRecOnCtor ∧
      elaborateTutUnitOraclePattern tutUnitCtorPattern = some unitCtorTerm ∧
      HasTypeDecl unitRecDeclEnv .nil unitRecOnCtor (.const unitTyName) ∧
      RedStarDecl unitRecDeclEnv unitRecOnCtor unitCtorTerm ∧
      HasTypeDecl unitRecDeclEnv .nil unitCtorTerm (.const unitTyName) :=
  ⟨ hePrime_tutUnitRecSyntax_oracle_certificate.sourceElab
  , hePrime_tutUnitRecSyntax_oracle_certificate.targetElab
  , hePrime_tutUnitRecSyntax_oracle_certificate.sourceType
  , hePrime_tutUnitRecSyntax_oracle_certificate.reduces
  , hePrime_tutUnitRecSyntax_oracle_certificate.targetType
  ⟩

/-! ## Current-boundary no-values slice -> quoted profile bridge -/

/-- On the strongest assumption-free checked-spec slice, any generated closed
recursor step chain transports through the declaration kernel into the quoted
Pure-profile theory star. This is the current honest interface theorem between
the recursor admission frontier and the engine-facing profile bridge: it uses
the all-none declaration package and does not cross the value-bearing delta
frontier. -/
theorem generatedRecursor_currentBoundary_noValues_profileBridge_of_all_none_specs
    {contract : FamilyRecursorDeclContract}
    {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract)
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u : ScopedTerm 0}
    (h :
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    TwoSortProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  let hPkg :=
    generatedRecursorContract_admitted_current_boundary_package_of_all_none_specs
      (contract := contract) (specs := specs) hAdm hSig hNone hReal
  let hBoundary :=
    checkedNoValuesDeclKernelBoundaryOfPackage
      hSig hNone (hSig.declSpecAndNoValuesPackage_of_all_none hNone)
  have hStepToDecl :
      ∀ {t u : ScopedTerm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl (envOfSpecs specs) t u :=
    hPkg.2.2.1.2.1
  exact
    checkedNoValuesDeclKernel_star_sound_twoSortProfileTheoryStepStar_quoteClosed
      hSig hNone hinst0 hcompat0 (hStepToDecl h)

/-- The same no-values current-boundary package gives the full typed/profile
transport: a generated closed recursor step chain preserves the declaration
type of a closed term and simultaneously yields the quoted Pure-profile star
witness. -/
theorem generatedRecursor_currentBoundary_noValues_subjectReduction_and_profileBridge_of_all_none_specs
    {contract : FamilyRecursorDeclContract}
    {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract)
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u A : ScopedTerm 0}
    (ht : HasTypeDecl (envOfSpecs specs) .nil t A)
    (h :
      Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u) :
    HasTypeDecl (envOfSpecs specs) .nil u A ∧
      TwoSortProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  let hPkg :=
    generatedRecursorContract_admitted_current_boundary_package_of_all_none_specs
      (contract := contract) (specs := specs) hAdm hSig hNone hReal
  let hBoundary :=
    checkedNoValuesDeclKernelBoundaryOfPackage
      hSig hNone (hSig.declSpecAndNoValuesPackage_of_all_none hNone)
  have hStepToDecl :
      ∀ {t u : ScopedTerm 0},
        Relation.ReflTransGen (GeneratedRecursorContractClosedIotaStep contract) t u →
          RedStarDecl (envOfSpecs specs) t u :=
    hPkg.2.2.1.2.1
  exact
    checkedNoValuesDeclKernelBoundary_closedSubjectReduction_and_profileBridge
      hBoundary hinst0 hcompat0 ht (hStepToDecl h)

/-- On the same assumption-free slice, a successful generated recursor
conversion-by-normalization witness yields a quoted common reduct in the
Pure-profile theory. This is the current bridge from the checked recursor
conversion service to the engine-facing quoted proof representation. -/
theorem generatedRecursor_currentBoundary_noValues_convByNormalization_profileBridge_of_all_none_specs
    {contract : FamilyRecursorDeclContract}
    {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hSig : SignatureWellFormed specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract)
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u : ScopedTerm 0}
    {w : GeneratedRecursorContractClosedIotaConvWitness contract t u}
    (hw :
      generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w) :
    ∃ q : Pattern,
      TwoSortProfileTheoryStepStar (quoteClosedTm t) q ∧
      TwoSortProfileTheoryStepStar (quoteClosedTm u) q := by
  let hPkg :=
    generatedRecursorContract_admitted_current_boundary_package_of_all_none_specs
      (contract := contract) (specs := specs) hAdm hSig hNone hReal
  let hBoundary :=
    checkedNoValuesDeclKernelBoundaryOfPackage
      hSig hNone (hSig.declSpecAndNoValuesPackage_of_all_none hNone)
  have hConvSome :
      ∀ {t u : ScopedTerm 0}
        {w : GeneratedRecursorContractClosedIotaConvWitness contract t u},
        generatedRecursorContractClosedIotaConvByNormalization? contract t u = some w →
          ConvDecl (envOfSpecs specs) t u :=
    hPkg.2.2.1.2.2.2.2.2.2.1
  exact
    checkedNoValuesDeclKernelBoundary_closedCommonReduct_profileBridge
      hBoundary hinst0 hcompat0 (hConvSome hw)

/-- Value-bearing current-boundary recursor packages over checked specs sit in
the same declaration kernel that already embeds into the Pure profile under a
Church-Rosser hypothesis. This is the current honest interface theorem on the
value-bearing side: it packages the admitted recursor frontier together with
the assembled declaration kernel boundary and the engine-facing kernel identity
and target profile, without overclaiming a quoted-step transport across delta. -/
theorem generatedRecursor_currentBoundary_churchRosser_frontier_and_embedding_of_specs
    {contract : FamilyRecursorDeclContract}
    {specs : List DeclSpec}
    (hAdm : GeneratedRecursorContractAdmitted contract)
    (hSig : SignatureWellFormed specs)
    (hCR : DeclChurchRosser (envOfSpecs specs))
    (hReal : GeneratedRecursorContractClosedIotaRealizedIn (envOfSpecs specs) contract) :
    GeneratedRecursorCurrentBoundaryChurchRosserFrontierPackage
        (envOfSpecs specs) contract ∧
      ∃ hBoundary : CheckedChurchRosserDeclKernelBoundary hSig hCR,
        (checkedChurchRosserDeclKernelIntoTwoSortProfile hSig hCR).kernel =
          hBoundary.typed ∧
        (checkedChurchRosserDeclKernelIntoTwoSortProfile hSig hCR).profile =
          Mettapedia.Languages.MeTTa.CoreProfile.twoSortProfile := by
  have hWf : DeclEnvWellFormed (envOfSpecs specs) :=
    envOfSpecs_wellFormed_of_specObligations specs hSig.obligations
  have hFrontier :
      GeneratedRecursorCurrentBoundaryChurchRosserFrontierPackage
        (envOfSpecs specs) contract :=
    generatedRecursorContract_admitted_current_boundary_package_of_church_rosser
      (contract := contract)
      (E := envOfSpecs specs)
      hAdm hWf hReal hCR
  let hBoundary := checkedChurchRosserDeclKernelBoundary hSig hCR
  have hEmbed :
      (checkedChurchRosserDeclKernelIntoTwoSortProfile hSig hCR).kernel =
          hBoundary.typed ∧
        (checkedChurchRosserDeclKernelIntoTwoSortProfile hSig hCR).profile =
          Mettapedia.Languages.MeTTa.CoreProfile.twoSortProfile :=
    checkedChurchRosserDeclKernelBoundary_kernel_and_profile hBoundary
  exact
    ⟨ hFrontier
    , ⟨ hBoundary, hEmbed ⟩
    ⟩

/-- General inductive checker pilot: standard Unit/Nat declarations are accepted
and a strictly negative constructor is rejected. -/
theorem simplest_general_inductive_checker_path :
    checkIndDecl unitDecl = some [unitTySpec, unitCtorSpec] ∧
      checkIndDecl natDecl = some [natTySpec, natZeroSpec, natSuccSpec] ∧
      checkIndDecl badNegDecl = none :=
  ⟨unitDecl_specs_agree, natDecl_specs_agree, check_badNegDecl⟩

/-! ## Capability-safety TwoSortPiSigmaId seed -/

def capPrincipalName : DeclName := `DTTSeed.Principal
def capSecretName : DeclName := `DTTSeed.Secret
def capAliceName : DeclName := `DTTSeed.Alice
def capBobName : DeclName := `DTTSeed.Bob
def capDocName : DeclName := `DTTSeed.Doc
def capCanReadName : DeclName := `DTTSeed.CanRead
def capReadOKName : DeclName := `DTTSeed.ReadOK
def capAliceDocCapName : DeclName := `DTTSeed.AliceDocCap
def capBobDocCapName : DeclName := `DTTSeed.BobDocCap
def capReadName : DeclName := `DTTSeed.read

def capPrincipalTy : ScopedTerm 0 := .const capPrincipalName
def capSecretTy : ScopedTerm 0 := .const capSecretName
def capAliceTerm : ScopedTerm 0 := .const capAliceName
def capBobTerm : ScopedTerm 0 := .const capBobName
def capDocTerm : ScopedTerm 0 := .const capDocName
def capAliceDocCapTerm : ScopedTerm 0 := .const capAliceDocCapName
def capBobDocCapTerm : ScopedTerm 0 := .const capBobDocCapName

def capCanReadType : ScopedTerm 0 :=
  .pi (.const capPrincipalName)
    (.pi (.const capSecretName) .u0)

def capReadOKType : ScopedTerm 0 :=
  .pi (.const capPrincipalName)
    (.pi (.const capSecretName) .u0)

def capCanRead (who doc : ScopedTerm 0) : ScopedTerm 0 :=
  .app (.app (.const capCanReadName) who) doc

def capReadOK (who doc : ScopedTerm 0) : ScopedTerm 0 :=
  .app (.app (.const capReadOKName) who) doc

def capAliceDocCapType : ScopedTerm 0 := capCanRead capAliceTerm capDocTerm
def capBobDocCapType : ScopedTerm 0 := capCanRead capBobTerm capDocTerm

def capReadType : ScopedTerm 0 :=
  .pi (.const capPrincipalName)
    (.pi (.const capSecretName)
      (.pi (.app (.app (.const capCanReadName) (.var 1)) (.var 0))
        (.app (.app (.const capReadOKName) (.var 2)) (.var 1))))

def capSpecs : List DeclSpec :=
  [ { name := capPrincipalName, type := .u0 }
  , { name := capSecretName, type := .u0 }
  , { name := capAliceName, type := capPrincipalTy }
  , { name := capBobName, type := capPrincipalTy }
  , { name := capDocName, type := capSecretTy }
  , { name := capCanReadName, type := capCanReadType }
  , { name := capReadOKName, type := capReadOKType }
  , { name := capAliceDocCapName, type := capAliceDocCapType }
  , { name := capBobDocCapName, type := capBobDocCapType }
  , { name := capReadName, type := capReadType }
  ]

def capDeclEnv : DeclEnv := envOfSpecs capSpecs

@[simp] theorem typeOf_capRead :
    typeOf? capDeclEnv capReadName = some capReadType := by
  decide

@[simp] theorem typeOf_capAlice :
    typeOf? capDeclEnv capAliceName = some capPrincipalTy := by
  decide

@[simp] theorem typeOf_capBob :
    typeOf? capDeclEnv capBobName = some capPrincipalTy := by
  decide

@[simp] theorem typeOf_capDoc :
    typeOf? capDeclEnv capDocName = some capSecretTy := by
  decide

@[simp] theorem typeOf_capAliceDocCap :
    typeOf? capDeclEnv capAliceDocCapName = some capAliceDocCapType := by
  decide

@[simp] theorem typeOf_capBobDocCap :
    typeOf? capDeclEnv capBobDocCapName = some capBobDocCapType := by
  decide

theorem hasType_capRead :
    HasTypeDecl capDeclEnv .nil ((.const capReadName : ScopedTerm 0)) capReadType :=
  hasType_const_from_lookup (E := capDeclEnv) (Γ := .nil) (c := capReadName) (A0 := capReadType) (by
    simp)

theorem hasType_capAlice :
    HasTypeDecl capDeclEnv .nil capAliceTerm capPrincipalTy :=
  hasType_const_from_lookup (E := capDeclEnv) (Γ := .nil) (c := capAliceName) (A0 := capPrincipalTy) (by
    simp)

theorem hasType_capBob :
    HasTypeDecl capDeclEnv .nil capBobTerm capPrincipalTy :=
  hasType_const_from_lookup (E := capDeclEnv) (Γ := .nil) (c := capBobName) (A0 := capPrincipalTy) (by
    simp)

theorem hasType_capDoc :
    HasTypeDecl capDeclEnv .nil capDocTerm capSecretTy :=
  hasType_const_from_lookup (E := capDeclEnv) (Γ := .nil) (c := capDocName) (A0 := capSecretTy) (by
    simp)

theorem hasType_capAliceDocCap :
    HasTypeDecl capDeclEnv .nil capAliceDocCapTerm capAliceDocCapType :=
  hasType_const_from_lookup
    (E := capDeclEnv) (Γ := .nil) (c := capAliceDocCapName) (A0 := capAliceDocCapType) (by
      simp)

theorem hasType_capBobDocCap :
    HasTypeDecl capDeclEnv .nil capBobDocCapTerm capBobDocCapType :=
  hasType_const_from_lookup
    (E := capDeclEnv) (Γ := .nil) (c := capBobDocCapName) (A0 := capBobDocCapType) (by
      simp)

def capReadAliceDocTerm : ScopedTerm 0 :=
  .app (.app (.app (.const capReadName) capAliceTerm) capDocTerm) capAliceDocCapTerm

def capReadAliceDocType : ScopedTerm 0 :=
  capReadOK capAliceTerm capDocTerm

theorem hasType_capReadAliceDoc :
    HasTypeDecl capDeclEnv .nil capReadAliceDocTerm capReadAliceDocType := by
  -- The declared result type and the substituted `inst0`/`subst` index are definitionally
  -- equal on these concrete closed terms, so `app_elim` chain typechecks directly.
  exact
    (HasTypeDecl.app_elim
      (HasTypeDecl.app_elim
        (HasTypeDecl.app_elim hasType_capRead hasType_capAlice)
      hasType_capDoc)
      hasType_capAliceDocCap)

def capReadBobDocPrefixTerm : ScopedTerm 0 :=
  .app (.app (.const capReadName) capBobTerm) capDocTerm

def capReadBobDocPrefixType : ScopedTerm 0 :=
  .pi capBobDocCapType (liftClosed (n := 1) (capReadOK capBobTerm capDocTerm))

def capReadBobDocWithAliceCapTerm : ScopedTerm 0 :=
  .app capReadBobDocPrefixTerm capAliceDocCapTerm

def capReadBobDocWithBobCapTerm : ScopedTerm 0 :=
  .app capReadBobDocPrefixTerm capBobDocCapTerm

def capReadBobDocType : ScopedTerm 0 :=
  capReadOK capBobTerm capDocTerm

theorem hasType_capReadBobDocPrefix :
    HasTypeDecl capDeclEnv .nil capReadBobDocPrefixTerm capReadBobDocPrefixType := by
  -- The `.pi` prefix type and the substituted `inst0`/`subst` index agree definitionally
  -- on these concrete closed terms, so the `app_elim` chain typechecks directly.
  exact
    (HasTypeDecl.app_elim
      (HasTypeDecl.app_elim hasType_capRead hasType_capBob)
      hasType_capDoc)

theorem capAliceDocCap_type_ne_bobDocCap_type :
    capAliceDocCapType ≠ capBobDocCapType := by
  decide

def capCapabilityOwner? : ScopedTerm 0 → Option (ScopedTerm 0)
  | .const c =>
      if c = capAliceDocCapName then some capAliceTerm
      else if c = capBobDocCapName then some capBobTerm
      else none
  | _ => none

def capCapabilitySecret? : ScopedTerm 0 → Option (ScopedTerm 0)
  | .const c =>
      if c = capAliceDocCapName then some capDocTerm
      else if c = capBobDocCapName then some capDocTerm
      else none
  | _ => none

def capReadRequestParts? : ScopedTerm 0 → Option (ScopedTerm 0 × ScopedTerm 0 × ScopedTerm 0)
  | .app (.app (.app (.const c) who) doc) cap =>
      if c = capReadName then some (who, doc, cap) else none
  | _ => none

def capAuthorizesReadRequest? (who doc cap : ScopedTerm 0) : Bool :=
  match capCapabilityOwner? cap, capCapabilitySecret? cap with
  | some owner, some capDoc =>
      if owner = who then
        if capDoc = doc then true else false
      else
        false
  | _, _ => false

theorem capability_alice_cap_authorizes_alice_request :
    capAuthorizesReadRequest? capAliceTerm capDocTerm capAliceDocCapTerm = true := by
  decide

theorem capability_bob_cap_authorizes_bob_request :
    capAuthorizesReadRequest? capBobTerm capDocTerm capBobDocCapTerm = true := by
  decide

theorem capability_bob_request_with_alice_cap_fails_owner_check :
    capReadRequestParts? capReadBobDocWithAliceCapTerm =
        some (capBobTerm, capDocTerm, capAliceDocCapTerm) ∧
      capCapabilityOwner? capAliceDocCapTerm = some capAliceTerm ∧
      capAliceTerm ≠ capBobTerm ∧
      capAuthorizesReadRequest? capBobTerm capDocTerm capAliceDocCapTerm = false := by
  decide

def inferClosedDeclAppType? (E : DeclEnv) : ScopedTerm 0 → Option (ScopedTerm 0)
  | .const c => typeOf? E c
  | .app f a =>
      match inferClosedDeclAppType? E f, inferClosedDeclAppType? E a with
      | some (.pi A B), some A' =>
          if A' = A then some (inst0 a B) else none
      | _, _ => none
  | .u0 => some .u1
  | _ => none

theorem capability_alice_read_certificate_accepts :
    inferClosedDeclAppType? capDeclEnv capReadAliceDocTerm =
      some capReadAliceDocType := by
  native_decide

theorem capability_bob_read_with_bob_cap_certificate_accepts :
    inferClosedDeclAppType? capDeclEnv capReadBobDocWithBobCapTerm =
      some capReadBobDocType := by
  native_decide

theorem capability_bob_cannot_read_with_alice_certificate :
    inferClosedDeclAppType? capDeclEnv capReadBobDocWithAliceCapTerm = none := by
  native_decide

theorem capability_wrong_principal_domain_mismatch :
    HasTypeDecl capDeclEnv .nil capReadBobDocPrefixTerm capReadBobDocPrefixType ∧
      HasTypeDecl capDeclEnv .nil capAliceDocCapTerm capAliceDocCapType ∧
      capAliceDocCapType ≠ capBobDocCapType :=
  ⟨hasType_capReadBobDocPrefix, hasType_capAliceDocCap, capAliceDocCap_type_ne_bobDocCap_type⟩

theorem capability_safety_seed :
    HasTypeDecl capDeclEnv .nil capReadAliceDocTerm capReadAliceDocType ∧
      HasTypeDecl capDeclEnv .nil capReadBobDocPrefixTerm capReadBobDocPrefixType ∧
      capAliceDocCapType ≠ capBobDocCapType ∧
      capAuthorizesReadRequest? capBobTerm capDocTerm capAliceDocCapTerm = false ∧
      inferClosedDeclAppType? capDeclEnv capReadBobDocWithAliceCapTerm = none :=
  ⟨hasType_capReadAliceDoc, hasType_capReadBobDocPrefix, capAliceDocCap_type_ne_bobDocCap_type,
    capability_bob_request_with_alice_cap_fails_owner_check.2.2.2,
    capability_bob_cannot_read_with_alice_certificate⟩

end Mettapedia.Languages.MeTTa.DTTSeedProofPath
