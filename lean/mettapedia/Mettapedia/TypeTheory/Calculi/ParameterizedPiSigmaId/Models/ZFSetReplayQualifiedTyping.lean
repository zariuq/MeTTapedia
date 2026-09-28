import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayResultQualification
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayUniverseModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIntroduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayElimination
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayNeutralCoherence

/-!
# Semantic typing with qualified result formations

The program may compute. Qualification concerns the result-type formations
throughout its retained typing tree, not normality of the program. Universe
closure and declared constants are explicit model assumptions. They do not
assert soundness of arbitrary terms or agreement of arbitrary certificates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment extend)
open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (tracePiSet traceApp)
open ZFSetDependentProducts (sigmaSet)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u
variable {Head : Type}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- Each declared constant has one chosen checked, qualified interpretation
of its closed declared type, containing the constant's set value. Other
accepted formation certificates are compared with this witness by a theorem.
This is a signature-model obligation, not whole-language soundness. -/
structure ConstantsModel : Prop where
  declared : ∀ name type, R.constantType name = some type →
    ∃ (level : Head) (formation : Code Head NoConversion 0) (meaning : Meaning.{u} 0),
      check R noConversionCheck .nil type (.head level) formation = true ∧
      formation.neutralEliminations type (.head level) = true ∧
      assemble heads constants formation type (.head level) = some meaning ∧
      constants name ∈ meaning.value Fin.elim0

theorem ConstantsModel.membership
    (model : ConstantsModel heads constants R)
    {name : DeclName} {type : Tm Head 0} {level : Head}
    {formation : Code Head NoConversion 0} {meaning : Meaning.{u} 0}
    (known : R.constantType name = some type)
    (checked : check R noConversionCheck .nil type (.head level) formation = true)
    (assembled : assemble heads constants formation type (.head level) = some meaning) :
    constants name ∈ meaning.value Fin.elim0 := by
  obtain ⟨chosenLevel, chosenCode, chosen, chosenChecked, qualified, atChosen, member⟩ :=
    model.declared name type known
  have agree := assemble_neutralEliminations_coherent heads constants R chosenCode
    chosenChecked qualified atChosen checked assembled (EqualOrHeads.heads chosenLevel level)
  exact agree ▸ member

variable (successor : Head → Head) (universes : FormationSensitive.UniverseRegularity R)
variable (successorQualified : ∀ level, R.isUniverse level →
  R.isUniverse (successor level) ∧ R.headTyping level (successor level))

include universes successorQualified in
/-- The qualified *extracted* formation controls an independently supplied
formation. The target formation need not itself pass the qualification. -/
theorem result_membership_transport {n : Nat}
    {context : Ctx Head n} {subject type : Tm Head n}
    (contextCode : ContextCode Head NoConversion n) (code : Code Head NoConversion n)
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (checked : check R noConversionCheck context subject type code = true)
    (qualified : code.resultFormationNeutral successor contextCode subject type = true)
    {level : Head} {formation : Code Head NoConversion n}
    (extracted : code.resultFormation noConversionRename noConversionSubstitute successor
      contextCode subject type = some (level, formation))
    (meaning : Meaning.{u} n)
    (atFormation : assemble heads constants formation type (.head level) = some meaning)
    {otherLevel : Head} {other : Code Head NoConversion n} (otherMeaning : Meaning.{u} n)
    (otherChecked : check R noConversionCheck context type (.head otherLevel) other = true)
    (atOther : assemble heads constants other type (.head otherLevel) = some otherMeaning)
    (env : Environment.{u} n) (value : ZFSet.{u})
    (member : value ∈ meaning.value env) : value ∈ otherMeaning.value env := by
  obtain ⟨actualLevel, actualCode, computed, _, formed⟩ := code.resultFormation_checked
    R noConversionCheck noConversionRename (fun _ impossible => nomatch impossible)
    noConversionSubstitute (fun _ impossible => nomatch impossible)
    successor universes successorQualified contextCode contextChecked checked
  rw [extracted] at computed
  cases Option.some.inj computed
  have normal : formation.neutralEliminations type (.head level) = true := by
    simpa [Code.resultFormationNeutral, extracted] using qualified
  have agree := assemble_neutralEliminations_coherent heads constants R formation
    formed normal atFormation otherChecked atOther (EqualOrHeads.heads level otherLevel)
  exact agree ▸ member

omit [DecidableEq Head] in
private theorem assembled_head_value {n : Nat} (code : Code Head NoConversion n)
    (head : Head) (type : Tm Head n) (meaning : Meaning.{u} n)
    (assembled : assemble heads constants code (.head head) type = some meaning)
    (env : Environment.{u} n) : meaning.value env = heads head :=
  agrees_with_type_expressions heads constants code (.head head) type meaning rfl assembled env

include universes successorQualified in
/-- Every accepted tree whose actual result formations are qualified has
semantic membership in every independently accepted formation of its type.
The induction follows the retained code, not evaluation or normalization.
No semantic typing of subterms is an input to this theorem. -/
theorem qualified_membership (model : UniverseModel R heads)
    (constantModel : ConstantsModel heads constants R) {n : Nat}
    (code : Code Head NoConversion n) :
    ∀ {context : Ctx Head n} {subject type : Tm Head n}
      (contextCode : ContextCode Head NoConversion n),
      checkContext R noConversionCheck context contextCode = true →
      check R noConversionCheck context subject type code = true →
      code.resultFormationsNeutral R successor contextCode subject type = true →
      ∀ (valid : Environment.{u} n → Prop) (meaning : Meaning.{u} n),
      assembleContext heads constants contextCode context = some valid →
      assemble heads constants code subject type = some meaning →
      ∀ (level : Head) (formation : Code Head NoConversion n) (typeMeaning : Meaning.{u} n),
      check R noConversionCheck context type (.head level) formation = true →
      assemble heads constants formation type (.head level) = some typeMeaning →
      ∀ env, valid env → meaning.value env ∈ typeMeaning.value env := by
  induction code <;>
    intro context subject type contextCode contextChecked checked qualified valid meaning
      atContext atSource level formation typeMeaning formationChecked atFormation env admitted
  all_goals
    have root := Code.resultFormationsNeutral_root R successor _ contextCode subject type qualified
    obtain ⟨ownLevel, ownCode, extracted, isOwn, ownChecked⟩ := Code.resultFormation_checked
      R noConversionCheck noConversionRename (fun _ impossible => nomatch impossible)
      noConversionSubstitute (fun _ impossible => nomatch impossible)
      successor universes successorQualified _ contextCode contextChecked checked
    obtain ⟨ownMeaning, atOwn, ownPi⟩ :=
      accepted_assembles heads constants R noConversionCheck ownCode ownChecked
    apply result_membership_transport heads constants R successor universes successorQualified
      contextCode _ contextChecked checked root extracted ownMeaning atOwn typeMeaning
      formationChecked atFormation env (meaning.value env)
  case headType =>
    cases subject <;> cases type <;>
      simp only [check, decide_eq_true_eq, Bool.false_eq_true] at checked
    rename_i head target
    rw [assembled_head_value heads constants _ head _ meaning atSource env,
      assembled_head_value heads constants _ target _ ownMeaning atOwn env]
    exact model.headTyping_mem checked
  case var =>
    cases subject <;> simp only [check, decide_eq_true_eq, Bool.false_eq_true] at checked
    rename_i index
    subst type
    obtain ⟨lookup, atLookup, member⟩ := lookupFormation_membership noConversionRename
      heads constants contextCode atContext index env admitted
    have exactResult := Option.some.inj extracted
    have exactLevel := congrArg Prod.fst exactResult
    have exactCode := congrArg Prod.snd exactResult
    dsimp only at exactLevel exactCode
    subst ownLevel ownCode
    rw [atOwn] at atLookup
    cases Option.some.inj atLookup
    simp only [assemble, Option.some.injEq] at atSource
    subst meaning
    exact member
  case const m declaredLevel declaredCode _ =>
    cases subject <;> simp only [check, Bool.false_eq_true] at checked
    rename_i name
    cases known : R.constantType name with
    | none => simp [known] at checked
    | some declared =>
      simp only [known, Bool.and_eq_true, decide_eq_true_eq] at checked
      obtain ⟨⟨_, declaredChecked⟩, rfl⟩ := checked
      obtain ⟨declaredMeaning, atDeclared, _⟩ :=
        accepted_assembles heads constants R noConversionCheck declaredCode declaredChecked
      have member := constantModel.membership heads constants R known declaredChecked atDeclared
      have atLift := assemble_rename noConversionRename heads constants declaredCode
        declared (.head declaredLevel) declaredMeaning atDeclared (Fin.elim0 : Ren 0 m)
      simp only [Code.resultFormation, Option.some.injEq, Prod.mk.injEq] at extracted
      rcases extracted with ⟨rfl, rfl⟩
      change assemble _ _ _ (liftClosed declared) (.head declaredLevel) = _ at atLift
      rw [atOwn] at atLift
      cases Option.some.inj atLift
      simp only [assemble, Option.some.injEq] at atSource
      subst meaning
      change constants name ∈ declaredMeaning.value (env ∘ Fin.elim0)
      rw [Subsingleton.elim (env ∘ Fin.elim0) (Fin.elim0 : Environment.{u} 0)]
      exact member
  case piForm domainLevel bodyLevel domainCode bodyCode ihDomain ihBody =>
    cases subject <;> cases type <;>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at checked
    rename_i A B target
    obtain ⟨⟨⟨⟨isDomain, isBody⟩, joined⟩, domainChecked⟩, bodyChecked⟩ := checked
    have quals := (Bool.and_eq_true_iff.mp qualified).2
    change (_ && _) = true at quals
    have quals := Bool.and_eq_true_iff.mp quals
    obtain ⟨domain, atDomain, _⟩ :=
      accepted_assembles heads constants R noConversionCheck domainCode domainChecked
    obtain ⟨body, atBody, _⟩ :=
      accepted_assembles heads constants R noConversionCheck bodyCode bodyChecked
    have domainMember := ihDomain contextCode contextChecked domainChecked quals.1 valid domain
      atContext atDomain (successor domainLevel) .headType (.plain (fun _ => heads domainLevel))
      (by simpa only [check, decide_eq_true_eq] using (successorQualified _ isDomain).2) rfl env admitted
    let extended : Environment.{u} (_ + 1) → Prop :=
      fun e => valid (e ∘ wk) ∧ e 0 ∈ domain.value (e ∘ wk)
    have extendedChecked : checkContext R noConversionCheck (.snoc context A)
        (.snoc contextCode domainLevel domainCode) = true := by
      simp only [checkContext, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨contextChecked, isDomain⟩, domainChecked⟩
    have atExtended : assembleContext heads constants (.snoc contextCode domainLevel domainCode)
        (.snoc context A) = some extended := by simp [assembleContext, atContext, atDomain, extended]
    have bodyMember : ∀ x ∈ domain.value env, body.value (extend env x) ∈ heads bodyLevel := by
      intro x inside
      exact ihBody _ extendedChecked bodyChecked quals.2 extended body atExtended atBody
        (successor bodyLevel) .headType (.plain (fun _ => heads bodyLevel))
        (by simpa only [check, decide_eq_true_eq] using (successorQualified _ isBody).2) rfl
        (extend env x) ⟨admitted, inside⟩
    simp only [assemble, atDomain, atBody, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.some.injEq] at atSource
    subst meaning
    rw [assembled_head_value heads constants _ target _ ownMeaning atOwn env]
    exact model.pi_mem joined domainMember _ bodyMember
  case sigmaForm domainLevel bodyLevel domainCode bodyCode ihDomain ihBody =>
    cases subject <;> cases type <;>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at checked
    rename_i A B target
    obtain ⟨⟨⟨⟨isDomain, isBody⟩, joined⟩, domainChecked⟩, bodyChecked⟩ := checked
    have quals := (Bool.and_eq_true_iff.mp qualified).2
    change (_ && _) = true at quals
    have quals := Bool.and_eq_true_iff.mp quals
    obtain ⟨domain, atDomain, _⟩ :=
      accepted_assembles heads constants R noConversionCheck domainCode domainChecked
    obtain ⟨body, atBody, _⟩ :=
      accepted_assembles heads constants R noConversionCheck bodyCode bodyChecked
    have domainMember := ihDomain contextCode contextChecked domainChecked quals.1 valid domain
      atContext atDomain (successor domainLevel) .headType (.plain (fun _ => heads domainLevel))
      (by simpa only [check, decide_eq_true_eq] using (successorQualified _ isDomain).2) rfl env admitted
    let extended : Environment.{u} (_ + 1) → Prop :=
      fun e => valid (e ∘ wk) ∧ e 0 ∈ domain.value (e ∘ wk)
    have extendedChecked : checkContext R noConversionCheck (.snoc context A)
        (.snoc contextCode domainLevel domainCode) = true := by
      simp only [checkContext, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨contextChecked, isDomain⟩, domainChecked⟩
    have atExtended : assembleContext heads constants (.snoc contextCode domainLevel domainCode)
        (.snoc context A) = some extended := by simp [assembleContext, atContext, atDomain, extended]
    have bodyMember : ∀ x ∈ domain.value env, body.value (extend env x) ∈ heads bodyLevel := by
      intro x inside
      exact ihBody _ extendedChecked bodyChecked quals.2 extended body atExtended atBody
        (successor bodyLevel) .headType (.plain (fun _ => heads bodyLevel))
        (by simpa only [check, decide_eq_true_eq] using (successorQualified _ isBody).2) rfl
        (extend env x) ⟨admitted, inside⟩
    simp only [assemble, atDomain, atBody, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.some.injEq] at atSource
    subst meaning
    rw [assembled_head_value heads constants _ target _ ownMeaning atOwn env]
    exact model.sigma_mem joined domainMember _ bodyMember
  case lamIntro lambdaLevel formationCode bodyCode _ ihBody =>
    cases subject <;> cases type <;>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at checked
    rename_i body A B
    obtain ⟨⟨_, formed⟩, bodyChecked⟩ := checked
    obtain ⟨domainLevel, bodyLevel, domainCode, codomainCode, parts, isDomain, _,
      domainChecked, codomainChecked⟩ := formationCode.piFormation_checked R noConversionCheck formed
    have quals := Code.resultFormationsNeutral_lamIntro R successor contextCode A B body
      lambdaLevel domainLevel bodyLevel formationCode domainCode bodyCode codomainCode parts qualified
    obtain ⟨domain, atDomain, _⟩ :=
      accepted_assembles heads constants R noConversionCheck domainCode domainChecked
    obtain ⟨codomain, atCodomain, _⟩ :=
      accepted_assembles heads constants R noConversionCheck codomainCode codomainChecked
    obtain ⟨bodyMeaning, atBody, _⟩ :=
      accepted_assembles heads constants R noConversionCheck bodyCode bodyChecked
    simp only [Code.resultFormation, Option.some.injEq, Prod.mk.injEq] at extracted
    rcases extracted with ⟨rfl, rfl⟩
    let extended : Environment.{u} (_ + 1) → Prop :=
      fun e => valid (e ∘ wk) ∧ e 0 ∈ domain.value (e ∘ wk)
    have extendedChecked : checkContext R noConversionCheck (.snoc context A)
        (.snoc contextCode domainLevel domainCode) = true := by
      simp only [checkContext, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨contextChecked, isDomain⟩, domainChecked⟩
    have atExtended : assembleContext heads constants (.snoc contextCode domainLevel domainCode)
        (.snoc context A) = some extended := by simp [assembleContext, atContext, atDomain, extended]
    exact (lambda_result_membership heads constants noConversionRename noConversionSubstitute
      successor context contextCode A B body formationCode domainCode codomainCode bodyCode
      lambdaLevel domainLevel bodyLevel ownMeaning domain meaning codomain bodyMeaning
      valid extended parts atOwn atDomain atCodomain atBody atContext atExtended atSource
      (fun e validE => ihBody _ extendedChecked bodyChecked quals.2 extended bodyMeaning
        atExtended atBody bodyLevel codomainCode codomain codomainChecked atCodomain e validE)
      env admitted).2
  case appElim A B functionCode argumentCode ihFunction ihArgument =>
    cases subject <;>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at checked
    rename_i function argument
    obtain ⟨⟨functionChecked, argumentChecked⟩, rfl⟩ := checked
    have quals := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp qualified).2
    obtain ⟨functionLevel, functionFormation, functionExtract, _, functionFormed⟩ :=
      functionCode.resultFormation_checked R noConversionCheck noConversionRename
        (fun _ impossible => nomatch impossible) noConversionSubstitute
        (fun _ impossible => nomatch impossible) successor universes successorQualified
        contextCode contextChecked functionChecked
    obtain ⟨domainLevel, bodyLevel, domainCode, codomainCode, parts, _, _,
      domainChecked, codomainChecked⟩ := functionFormation.piFormation_checked R noConversionCheck functionFormed
    obtain ⟨functionMeaning, atFunction, _⟩ := accepted_assembles heads constants R noConversionCheck functionCode functionChecked
    obtain ⟨arg, atArg, _⟩ := accepted_assembles heads constants R noConversionCheck argumentCode argumentChecked
    obtain ⟨formed, atFormed, _⟩ := accepted_assembles heads constants R noConversionCheck functionFormation functionFormed
    obtain ⟨domain, atDomain, _⟩ := accepted_assembles heads constants R noConversionCheck domainCode domainChecked
    obtain ⟨codomain, atCodomain, _⟩ := accepted_assembles heads constants R noConversionCheck codomainCode codomainChecked
    have functionMember := ihFunction contextCode contextChecked functionChecked quals.1 valid
      functionMeaning atContext atFunction functionLevel functionFormation formed functionFormed atFormed env admitted
    have argumentMember := ihArgument contextCode contextChecked argumentChecked quals.2 valid
      arg atContext atArg domainLevel domainCode domain domainChecked atDomain env admitted
    obtain ⟨resultType, actualExtract, atResultType, member⟩ := application_result_membership
      heads constants noConversionRename noConversionSubstitute successor R noConversionCheck
      context contextCode A function argument B functionCode argumentCode functionFormation
      domainCode codomainCode functionLevel domainLevel bodyLevel functionMeaning formed domain arg
      meaning codomain functionExtract parts codomainChecked atFormed atDomain atCodomain
      atFunction atArg atSource env functionMember argumentMember
    rw [extracted] at actualExtract
    cases Option.some.inj actualExtract
    rw [atOwn] at atResultType
    cases Option.some.inj atResultType
    exact member
  case pairIntro pairLevel formationCode firstCode secondCode _ ihFirst ihSecond =>
    cases subject <;> cases type <;>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at checked
    rename_i x y A B
    obtain ⟨⟨⟨_, formed⟩, firstChecked⟩, secondChecked⟩ := checked
    have quals := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp qualified).2
    have firstQual := (Bool.and_eq_true_iff.mp quals.1).2
    obtain ⟨domainLevel, bodyLevel, domainCode, codomainCode, parts, _, _,
      domainChecked, codomainChecked⟩ := formationCode.sigmaFormation_checked R noConversionCheck formed
    obtain ⟨first, atFirst, _⟩ := accepted_assembles heads constants R noConversionCheck firstCode firstChecked
    obtain ⟨second, atSecond, _⟩ := accepted_assembles heads constants R noConversionCheck secondCode secondChecked
    obtain ⟨domain, atDomain, _⟩ := accepted_assembles heads constants R noConversionCheck domainCode domainChecked
    obtain ⟨codomain, atCodomain, _⟩ := accepted_assembles heads constants R noConversionCheck codomainCode codomainChecked
    have secondTypeChecked := Code.instantiateFormation_checked R noConversionCheck
      noConversionRename (fun _ impossible => nomatch impossible) noConversionSubstitute
      (fun _ impossible => nomatch impossible) codomainChecked firstChecked
    obtain ⟨secondType, atSecondType, _⟩ := accepted_assembles heads constants R noConversionCheck _ secondTypeChecked
    have firstMember := ihFirst contextCode contextChecked firstChecked firstQual valid first
      atContext atFirst domainLevel domainCode domain domainChecked atDomain env admitted
    have secondMember := ihSecond contextCode contextChecked secondChecked quals.2 valid second
      atContext atSecond bodyLevel _ secondType secondTypeChecked atSecondType env admitted
    simp only [Code.resultFormation, Option.some.injEq, Prod.mk.injEq] at extracted
    rcases extracted with ⟨rfl, rfl⟩
    exact (pair_result_membership heads constants noConversionRename noConversionSubstitute
      successor R noConversionCheck context contextCode A x y B formationCode domainCode firstCode secondCode
      codomainCode pairLevel domainLevel bodyLevel ownMeaning domain first second secondType meaning
      codomain parts atOwn atDomain atCodomain codomainChecked atFirst atSecond atSecondType atSource
      env firstMember secondMember).2
  case fstElim B pairCode ihPair =>
    cases subject <;> simp only [check, Bool.false_eq_true] at checked
    rename_i pair
    have pairQual := (Bool.and_eq_true_iff.mp qualified).2
    obtain ⟨pairLevel, pairFormation, pairExtract, _, pairFormed⟩ :=
      pairCode.resultFormation_checked R noConversionCheck noConversionRename
        (fun _ impossible => nomatch impossible) noConversionSubstitute
        (fun _ impossible => nomatch impossible) successor universes successorQualified contextCode contextChecked checked
    obtain ⟨domainLevel, bodyLevel, domainCode, codomainCode, parts, _, _,
      domainChecked, _⟩ := pairFormation.sigmaFormation_checked R noConversionCheck pairFormed
    obtain ⟨pairMeaning, atPair, _⟩ := accepted_assembles heads constants R noConversionCheck pairCode checked
    obtain ⟨formed, atFormed, _⟩ := accepted_assembles heads constants R noConversionCheck pairFormation pairFormed
    obtain ⟨domain, atDomain, _⟩ := accepted_assembles heads constants R noConversionCheck domainCode domainChecked
    have pairMember := ihPair contextCode contextChecked checked pairQual valid pairMeaning
      atContext atPair pairLevel pairFormation formed pairFormed atFormed env admitted
    obtain ⟨actualExtract, member⟩ := first_result_membership heads constants noConversionRename
      noConversionSubstitute successor contextCode type pair B pairCode pairFormation domainCode
      codomainCode pairLevel domainLevel bodyLevel pairMeaning formed domain meaning pairExtract
      parts atFormed atDomain atPair atSource env pairMember
    rw [extracted] at actualExtract
    cases Option.some.inj actualExtract
    rw [atOwn] at atDomain
    cases Option.some.inj atDomain
    exact member
  case sndElim A B pairCode ihPair =>
    cases subject <;>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at checked
    rename_i pair
    obtain ⟨pairChecked, rfl⟩ := checked
    have pairQual := (Bool.and_eq_true_iff.mp qualified).2
    obtain ⟨pairLevel, pairFormation, pairExtract, _, pairFormed⟩ :=
      pairCode.resultFormation_checked R noConversionCheck noConversionRename
        (fun _ impossible => nomatch impossible) noConversionSubstitute
        (fun _ impossible => nomatch impossible) successor universes successorQualified contextCode contextChecked pairChecked
    obtain ⟨domainLevel, bodyLevel, domainCode, codomainCode, parts, _, _,
      _, codomainChecked⟩ := pairFormation.sigmaFormation_checked R noConversionCheck pairFormed
    obtain ⟨pairMeaning, atPair, _⟩ := accepted_assembles heads constants R noConversionCheck pairCode pairChecked
    obtain ⟨formed, atFormed, _⟩ := accepted_assembles heads constants R noConversionCheck pairFormation pairFormed
    obtain ⟨codomain, atCodomain, _⟩ := accepted_assembles heads constants R noConversionCheck codomainCode codomainChecked
    have pairMember := ihPair contextCode contextChecked pairChecked pairQual valid pairMeaning
      atContext atPair pairLevel pairFormation formed pairFormed atFormed env admitted
    obtain ⟨resultType, actualExtract, atResultType, member⟩ := second_result_membership
      heads constants noConversionRename noConversionSubstitute successor R noConversionCheck
      context contextCode A pair B pairCode pairFormation domainCode codomainCode pairLevel
      domainLevel bodyLevel pairMeaning formed meaning codomain pairExtract parts codomainChecked
      atFormed atCodomain atPair atSource env pairMember
    rw [extracted] at actualExtract
    cases Option.some.inj actualExtract
    rw [atOwn] at atResultType
    cases Option.some.inj atResultType
    exact member
  case idForm idLevel carrierCode leftCode rightCode _ _ _ =>
    cases subject <;> cases type <;>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at checked
    rename_i A x y target
    obtain ⟨⟨⟨⟨isLevel, _⟩, leftChecked⟩, rightChecked⟩, rfl⟩ := checked
    obtain ⟨left, atLeft, _⟩ := accepted_assembles heads constants R noConversionCheck leftCode leftChecked
    obtain ⟨right, atRight, _⟩ := accepted_assembles heads constants R noConversionCheck rightCode rightChecked
    simp only [assemble, atLeft, atRight, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, Option.some.injEq] at atSource
    subst meaning
    rw [assembled_head_value heads constants _ target _ ownMeaning atOwn env]
    exact model.identity_mem isLevel _
  case reflIntro A termCode _ =>
    cases subject <;>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at checked
    rename_i term
    obtain ⟨termChecked, rfl⟩ := checked
    obtain ⟨termLevel, termFormation, termExtract, _, _⟩ :=
      termCode.resultFormation_checked R noConversionCheck noConversionRename
        (fun _ impossible => nomatch impossible) noConversionSubstitute
        (fun _ impossible => nomatch impossible) successor universes successorQualified contextCode contextChecked termChecked
    obtain ⟨termMeaning, atTerm, _⟩ := accepted_assembles heads constants R noConversionCheck termCode termChecked
    obtain ⟨result, resultType, actualExtract, atResult, atResultType, member⟩ :=
      reflexivity_result_membership heads constants noConversionRename noConversionSubstitute
        successor contextCode A term termCode termFormation termLevel termMeaning termExtract atTerm
    rw [extracted] at actualExtract
    cases Option.some.inj actualExtract
    rw [atOwn] at atResultType
    cases Option.some.inj atResultType
    rw [atSource] at atResult
    cases Option.some.inj atResult
    exact member env
  case cumul lower sourceCode ih =>
    cases type <;>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at checked
    rename_i upper
    obtain ⟨sourceChecked, below⟩ := checked
    have sourceQual := (Bool.and_eq_true_iff.mp qualified).2
    obtain ⟨sourceLevel, sourceFormation, _, _, sourceFormed⟩ :=
      sourceCode.resultFormation_checked R noConversionCheck noConversionRename
        (fun _ impossible => nomatch impossible) noConversionSubstitute
        (fun _ impossible => nomatch impossible) successor universes successorQualified
        contextCode contextChecked sourceChecked
    obtain ⟨sourceTypeMeaning, atSourceType, _⟩ :=
      accepted_assembles heads constants R noConversionCheck sourceFormation sourceFormed
    have sourceMember := ih contextCode contextChecked sourceChecked sourceQual valid meaning
      atContext atSource sourceLevel sourceFormation sourceTypeMeaning sourceFormed atSourceType env admitted
    rw [assembled_head_value heads constants _ lower _ sourceTypeMeaning atSourceType env] at sourceMember
    rw [assembled_head_value heads constants _ upper _ ownMeaning atOwn env]
    exact model.cumulative_subset below sourceMember
  case convert _ _ _ _ impossible _ _ => exact nomatch impossible

#print axioms qualified_membership

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
