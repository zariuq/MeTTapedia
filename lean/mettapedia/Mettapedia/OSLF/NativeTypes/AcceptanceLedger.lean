import Mettapedia.OSLF.NativeTypes.Product
import Mettapedia.OSLF.NativeTypes.Consumers
import Mettapedia.OSLF.NativeTypes.GeneratedLogic
import Mettapedia.OSLF.NativeTypes.Executable
import Mettapedia.OSLF.NativeTypes.Instances.PeTTa.FrontDoor
import Mettapedia.OSLF.NativeTypes.Instances.MeTTaHE.FrontDoor
import Mettapedia.OSLF.NativeTypes.Instances.MeTTaZero.FrontDoor
import Mettapedia.OSLF.NativeTypes.Instances.MeTTaDialectControls
import Mettapedia.OSLF.NativeTypes.Instances.Dedukti.FrontDoorControls
import Mettapedia.OSLF.NativeTypes.Instances.Rho.CanonicalControls
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.FormulaControls
import Mettapedia.OSLF.Framework.FULLStatus
import Mettapedia.OSLF.Framework.BackwardSearchPlans
import Mettapedia.OSLF.Framework.FiniteModels
import Mettapedia.GSLT.LanguageDef.ModuleSource.FaithfulSpellingControls

/-!
# The acceptance ledger of executable OSLF

Each clause of the acceptance of deliverables D1–D10 is checked here against the library, when this module builds.

- `#acceptance clause modules…` takes the theorems the modules state and sorts them into positive ones (a proof, or an
  answer `.proved`) and negative ones (a negation, `False`, an answer `.refuted`, or `false`). It fails unless there
  are both, and fails on any axiom outside `propext`, `Classical.choice` and `Quot.sound`, `sorryAx` among them.
- `#witness clause in module names…` requires each named result to be stated in the module, with the same audit of its
  axioms.

The status table's rows of D8 are checked by `#guard`.
-/

namespace Mettapedia.OSLF.NativeTypes.AcceptanceLedger

open Lean Elab Command Meta

/-- The axioms every result may use. -/
def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether a statement refutes: its conclusion is a negation, an inequality or `False`; an equation with an answer
`.refuted`, `false` or `some false`; or an agreement whose verdict, its last argument, is `false`. -/
def refutes (statement : Expr) : MetaM Bool :=
  forallTelescope statement fun _ conclusion => do
    if conclusion.isAppOfArity ``Not 1 || conclusion.isAppOfArity ``Ne 3 || conclusion.isConstOf ``False then
      return true
    let isFalse (value : Expr) : Bool :=
      value.isConstOf ``Bool.false || (value.isAppOfArity ``Option.some 2 && value.appArg!.isConstOf ``Bool.false)
    if conclusion.isAppOfArity ``Eq 3 then
      let rhs := conclusion.appArg!
      return rhs.isAppOf ``Mettapedia.OSLF.NativeTypes.GeneratedLogic.Answer.refuted || isFalse rhs
    return conclusion.isApp && conclusion.appArg!.isConstOf ``Bool.false

/-- Whether a name was generated rather than stated. -/
def generated (name : Name) : Bool :=
  name.isInternalDetail ||
    match name with
    | .str _ last => last.startsWith "eq_" || last.startsWith "match_" || last.startsWith "proof_" ||
        last.endsWith "_unfold" || last == "induct" || last.startsWith "_"
    | _ => false

/-- The constants a module declares. -/
def declared (module : Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  let some index := env.getModuleIdx? module | throwError "the module {module} is not imported"
  let some data := env.header.moduleData[index.toNat]? | throwError "no data for the module {module}"
  return data.constNames

/-- The axioms the constants use, every one of them standard. -/
def audited (names : List Name) : CommandElabM (List Name) := do
  let mut all : NameSet := {}
  for name in names do
    for used in ← collectAxioms name do
      all := all.insert used
  for used in all.toList do
    unless standard.contains used do throwError "{used} is used, and is not one of the standard axioms"
  return all.toList

/-- `#acceptance clause modules…`: the clause has positive and negative controls in the modules, on standard axioms. -/
syntax (name := acceptance) "#acceptance " str ident+ : command

@[command_elab acceptance] def elabAcceptance : CommandElab := fun stx => do
  match stx with
  | `(#acceptance $clause:str $modules:ident*) => do
    let env ← getEnv
    let mut positive : Nat := 0
    let mut negative : Nat := 0
    let mut theorems : List Name := []
    for module in modules do
      for name in ← declared module.getId do
        if generated name then continue
        let some (.thmInfo info) := env.find? name | continue
        theorems := name :: theorems
        if ← liftTermElabM (refutes info.type) then negative := negative + 1 else positive := positive + 1
    if positive == 0 || negative == 0 then
      throwError "{clause.getString}: {positive} positive and {negative} negative theorems; the clause needs both"
    let axioms ← audited theorems
    logInfo m!"✓ {clause.getString}: {modules.size} modules, {theorems.length} theorems, {positive} positive and \
      {negative} negative; axioms {axioms}"
  | _ => throwUnsupportedSyntax

/-- `#witness clause in module names…`: each named result is stated in the module, on standard axioms. -/
syntax (name := witness) "#witness " str " in " ident ident+ : command

@[command_elab witness] def elabWitness : CommandElab := fun stx => do
  match stx with
  | `(#witness $clause:str in $module:ident $targets:ident*) => do
    let names ← declared module.getId
    let mut found : List Name := []
    for target in targets do
      let parts := target.getId.components
      let named := names.toList.filter fun name =>
        name.components.drop (name.components.length - parts.length) == parts
      if named.isEmpty then throwError "{clause.getString}: {target.getId} is not stated in {module.getId}"
      found := found ++ named
    let axioms ← audited found
    logInfo m!"✓ {clause.getString}: {found}; axioms {axioms}"
  | _ => throwUnsupportedSyntax

/-! ## D1. One front door -/

#witness "D1 a reading for every runtime driver: local, partial recursive, λ, ρ" in
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.LocalDriverReading LocalReading.reading
#witness "D1 a reading: partial recursive" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.PartrecDriverReading
  PartrecReading.localReading PartrecReading.driverReading
#witness "D1 a reading: λ" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.LambdaDriverReading LambdaReading.reading
#witness "D1 a reading: ρ" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoDriverReading Rho.driverReading
#witness "D1 a reading: answer bags" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBagReading
  AnswerBag.faithful AnswerBag.reading AnswerBag.meaning_iff
#witness "D1 a reading: normalized profiles" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedDriverReading
  NormalizedReading.reading NormalizedReading.test_agrees
#witness "D1 a reading: the authored normalized profile" in
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedAuthoredReading
  NormalizedReading.Authored.agreement NormalizedReading.Authored.reading
#witness "D1 a reading: the ρ model profile" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelReading
  RhoModel.faithful
#witness "D1 the runtime answers through the front door, with resumption and persistence" in
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.FrontDoorAgreement agrees_of_frontDoor askThrough
#witness "D1 persistence" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.Persistence search_persists
#acceptance "D1 every driver verdict also from the front door, the agreement proved"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.LambdaDriverReadingControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PartrecDriverReadingControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoDriverReadingControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedAuthoredReadingControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoModelReadingControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBagControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.ObservationAtomsControls

/-! ## D2. Equations through canonical forms -/

#acceptance "D2 ρ verdicts over canonical regions, and open without the forms"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoDriverReadingControls
  Mettapedia.OSLF.NativeTypes.Instances.Rho.CanonicalControls
#acceptance "D2 ambient verdicts"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCommControls
#acceptance "D2 a binder-equation certificate control with its negative"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateFreshEquationsControls

/-! ## D3. Every LanguageDef feature at the front door, each with positive and negative controls -/

#acceptance "D3 sorts and first-order constructors"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.ProtocolControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls
  Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls
#acceptance "D3 carrier kinds" Mettapedia.OSLF.NativeTypes.GeneratedLogic.CarrierControls
#acceptance "D3 abstractions"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.InstanceControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls
  Mettapedia.OSLF.NativeTypes.Instances.Rho.CanonicalControls
#acceptance "D3 multi-binders and wrapped collections"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalUnwrapControls
#acceptance "D3 vectors" Mettapedia.OSLF.NativeTypes.GeneratedLogic.FeatureControls
#acceptance "D3 bags"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.AnswerBagControls
#acceptance "D3 sets"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.NestedSetRuleControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.TwoLevelSetRuleControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureModuloControls
#acceptance "D3 collection algebras"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuControls
  Mettapedia.OSLF.NativeTypes.Instances.Rho.CanonicalControls
#acceptance "D3 authored equations"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateFreshEquationsControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoDriverReadingControls
#acceptance "D3 conditional equations" Mettapedia.OSLF.NativeTypes.GeneratedLogic.EquationControls
#acceptance "D3 relation queries with inputs"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls
#acceptance "D3 relation queries with outputs, and dynamic relations"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.ServedRelationControls
#acceptance "D3 freshness premises"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.FeatureControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.EquationControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureControls
#acceptance "D3 congruence premises"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureControls
#acceptance "D3 scoped-step premises"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.InstanceControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureControls
#acceptance "D3 universally quantified premises"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.FeatureControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CanonicalCaptureControls
#acceptance "D3 rule binding specifications"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.GroundSetPartsControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSControls
#acceptance "D3 evaluation policies, a proved lowering"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.HostEvaluationControls
#acceptance "D3 reflection"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoDriverReadingControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoPartnerControls
#acceptance "D3 set readings consume, keep and either"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadingControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredHereditaryControls
#witness "D3 either is consume over all presentations" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredReadings
  consume_step_iff either_step_iff consume_either
#acceptance "D3 the format's spellings, each and what it is not"
  Mettapedia.GSLT.LanguageDef.ModuleSource.FaithfulSpellingControls
-- The reader at parity with CeTTa's core dialect: its regex module reads as CeTTa elaborates it, and has a core.
#guard match Mettapedia.OSLF.NativeTypes.Product.ReaderParityControls.read with
  | .ok language =>
    decide (language.rewrites = Mettapedia.OSLF.NativeTypes.GeneratedLogic.RegexControls.regex.rewrites) &&
      (match language.toCore with | .ok _ => true | .error _ => false)
  | .error _ => false

/-! ## D4. Many sorts -/

#acceptance "D4 a two-sort language with sorted verdicts" Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySortedControls
#witness "D4 sorted verdicts" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySortedControls
  sorted_of_proved not_sorted_of_refuted
#witness "D4 the reduction to one sort over the sum carrier" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.ManySorted
  core_iff

/-! ## D5. Open terms, judgments and dependent types -/

#acceptance "D5 each judgment has a sound checker and a front-door entry"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.JudgmentControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.DependentJudgmentControls
#witness "D5 the checkers" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.Judgments
  entailsBy_sound piHolds_iff sigmaHolds_iff not_inhabited_iff
#witness "D5 open terms" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.OpenTerms openHolds_iff
#acceptance "D5 the agreement of the presheaf reading, and the disagreement controls"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresheafControls
#witness "D5 the agreement theorem" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresheafReading
  forces_sound forces_terminal_iff

/-! ## D6. The portfolio -/

#acceptance "D6 each strategy's controls answer through ask"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExploredControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.SearchControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CompletenessControls
  Mettapedia.OSLF.NativeTypes.Executable.BackwardBinderControls
  Mettapedia.OSLF.NativeTypes.Executable.FiniteModelKripkeControls
#witness "D6 fairness of the portfolio" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.Persistence
  ask_settled_of_evidence
#witness "D6 backward search" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.BackwardReach
  backwardEstablishes_sound backwardRefutes_sound
#witness "D6 explored graphs" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.ExploredDecider decides_exact
#witness "D6 the fair backward plans" in Mettapedia.OSLF.Framework.BackwardSearchPlans fair_complete

/-! ## D7. Native types of set languages -/

#acceptance "D7 every admitted native type of a hereditarily finite set decided, with kernel-checked controls"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSplitControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPointControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCrossingControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCountedControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPastProofControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTwoWayControls
#witness "D7 exactness of the practical stage" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipPracticalStage
  evalPractical_iff
#acceptance "D7 the set driver's verdicts at the front door"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetDriverControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.DeclaredHereditaryControls
#witness "D7 the set driver" in Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetDriver askHereditary_sound

/-! ## D8. The source construction -/

open Mettapedia.OSLF.Framework.FULLStatus in
/-- The status table's rows in D8's areas. -/
def sourceConstructionRows : List Milestone :=
  (tracker ++ strictTracker ++ paperParityTracker).filter fun row =>
    ["Context-Decorated Logic", "Generated Type Systems", "Generated Type System", "OSLF Paper Core",
      "Native Type Theory Core", "Native Type Theory Future Work"].contains row.area || row.area.startsWith "OSLF Core"

-- Every row of D8's areas is done, and there are rows in each of them.
#guard sourceConstructionRows.all (·.status == .done)
#guard sourceConstructionRows.length ≥ 20
#acceptance "D8 the labels used by ask for context-labelled modalities"
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartnerControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartnerControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabelControls

/-! ## D9. Instances and consumers -/

#acceptance "D9 λ and TinyML" Mettapedia.OSLF.NativeTypes.GeneratedLogic.InstanceControls
#acceptance "D9 π" Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerControls
#acceptance "D9 ρ" Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoDriverReadingControls
#acceptance "D9 ambients" Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuControls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextControls
#acceptance "D9 Petri nets" Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls
#acceptance "D9 Dedukti" Mettapedia.OSLF.NativeTypes.Instances.Dedukti.FrontDoorControls
#acceptance "D9 partial recursive functions" Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.PartrecDriverReadingControls
#acceptance "D9 the MeTTa dialects" Mettapedia.OSLF.NativeTypes.Instances.MeTTaDialectControls
  Mettapedia.OSLF.NativeTypes.Instances.PeTTa.FrontDoor Mettapedia.OSLF.NativeTypes.Instances.MeTTaHE.FrontDoor
  Mettapedia.OSLF.NativeTypes.Instances.MeTTaZero.FrontDoor
#witness "D9 PeTTa's step is the front door's" in Mettapedia.OSLF.NativeTypes.Instances.PeTTa.FrontDoor
  sat_step_iff sat_stuck_iff
#witness "D9 HE's step is the front door's" in Mettapedia.OSLF.NativeTypes.Instances.MeTTaHE.FrontDoor
  sat_step_iff sat_stuck_iff
#witness "D9 MeTTa Zero" in Mettapedia.OSLF.NativeTypes.Instances.MeTTaZero.FrontDoor sat_query_iff
#acceptance "D9 MeTTaSpace" Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceFrontDoor
  Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceControls
#witness "D9 MeTTaSpace's former decider" in Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceFrontDoor
  queryMember_iff_frontDoor checkOccurrence_iff_frontDoor
#acceptance "D9 MeTTaSpace, spatial" Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatialFrontDoor
  Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatialControls
#witness "D9 the spatial reading's former decider" in Mettapedia.OSLF.NativeTypes.Consumers.MeTTaSpaceSpatialFrontDoor
  occurrence_iff_frontDoor packet_iff_frontDoor
#acceptance "D9 PLN evidence" Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidenceFrontDoor
  Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidenceControls
#witness "D9 PLN evidence's former decider" in Mettapedia.OSLF.NativeTypes.Consumers.PLNEvidenceFrontDoor
  check_iff_frontDoor native_iff_frontDoor completes_iff_frontDoor
#acceptance "D9 MM0 admission" Mettapedia.OSLF.NativeTypes.Consumers.MM0AdmissionFrontDoor
  Mettapedia.OSLF.NativeTypes.Consumers.MM0AdmissionControls
#witness "D9 MM0 admission's former decider" in Mettapedia.OSLF.NativeTypes.Consumers.MM0AdmissionFrontDoor
  proofCheck_iff_frontDoor submissionCheck_iff_frontDoor
#acceptance "D9 MM2 batches" Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchFrontDoor
  Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchFrontDoorControls
#witness "D9 MM2 batches' former decider" in Mettapedia.OSLF.NativeTypes.Consumers.MM2BatchFrontDoor
  completesBy_iff transition_iff
#acceptance "D9 dependent checking" Mettapedia.OSLF.NativeTypes.Consumers.DependentCheckingFrontDoor
  Mettapedia.OSLF.NativeTypes.Consumers.DependentCheckingFrontDoorControls
#witness "D9 dependent checking's former decider" in Mettapedia.OSLF.NativeTypes.Consumers.DependentCheckingFrontDoor
  check_iff_frontDoor native_iff_frontDoor
#acceptance "D9 indexed append" Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppendFrontDoor
#witness "D9 indexed append's former decider" in Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppendFrontDoor
  check_iff_frontDoor append_length_iff_frontDoor
#acceptance "D9 executor qualification" Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualificationFrontDoor
  Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualification
#witness "D9 executor qualification's former decider" in
  Mettapedia.OSLF.NativeTypes.Consumers.ExecutorQualificationFrontDoor checkPackets_iff_frontDoor

/-! ## D10. The product -/

#witness "D10 what the executable establishes holds, what it refutes fails" in Mettapedia.OSLF.NativeTypes.Product.Query
  answerWith_proved answerWith_refuted askRecursive_proved askRecursive_refuted
#witness "D10 resumable: every resumed answer is the answer at its budget" in Mettapedia.OSLF.NativeTypes.Product.Query
  answers_eq answersRecursive_eq askKnown_eq
#witness "D10 speedups with the same answers: tables visited one at a time" in Mettapedia.OSLF.Framework.FiniteModels
  allTables_eq

end Mettapedia.OSLF.NativeTypes.AcceptanceLedger
