import Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsReflection
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationPresentations
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSubstitution
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationMultisets

/-!
# The π-calculus with sums: restriction blocks and steps

`piSumCalc` is a calculus with restriction and replication in the sense of the restriction-block theory
(`piSumReplicationLanguage`): parallel composition is a bare bag of processes with inaction as unit, the sum is a
named multiset of guards whose empty instance is inaction, `PiNu` binds a name over a process, `PiRep` replicates a
process, and its declared laws are exactly those of restriction, of the empty sum and of replication. Its canonical
form is the replication theory's (`canonR`): a sum reads as one component, its summands read canonically and sorted.

Its steps are reactions (`piSumReactions`): two sums side by side, an input among the summands of the first and an
output on its channel among those of the second, leave the reception and the output's continuation; a sum with a
silent summand leaves its continuation. The other summands are discarded. A redex records the summands before and
after the one that acts, so its parts are the sums as they stand.

Components read alike to the canonical forms of a redex's parts are sums whose summands read, one for one, as the
canonical summands of the parts (`plain_reads_alike`), so one of them is an input, an output or a silent prefix read
as the redex's, and they are a redex leaving equivalent processes (`Redex.alike`). A step reaches a block with a redex
at its front (`step_block`), so some unfolding of its canonical form steps to an equivalent contractum
(`simulation`), and so does a presentation of the canonical form (`presented`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsSteps

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Prenex
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (substitute_single_eq_instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_apply freeIn_lambda freeIn_collection)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv DerivedInstance derivedInstance_equivalent)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff isObjectPatternList_iff)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Sums (piSumCalc piSumRule piRecvRule piSendRule piTauRule
  PiSumRawStep)

/-! ## The π-calculus with sums is a calculus with restriction and replication -/

/-- The blocks of the π-calculus with sums: inaction, restriction, processes and names, and the sum as a multiset
whose empty instance is inaction. -/
abbrev piSumBlock : Block := ⟨"PiNil", "PiNu", "Proc", "Name", ["PiSum"], ["PiSum"]⟩

/-- Its blocks with replication of any process. -/
abbrev piSumRepBlock : ReplicationBlock := ⟨piSumBlock, "PiRep", true⟩

@[simp] theorem piSumRepBlock_toBlock : piSumRepBlock.toBlock = piSumBlock := rfl
@[simp] theorem piSumRepBlock_replicate : piSumRepBlock.replicate = "PiRep" := rfl

/-- The π-calculus with sums declares exactly the laws of restriction, of the empty sum and of replication. -/
theorem piSumCalc_equations : piSumCalc.equations = replicationBlockLaws piSumRepBlock := rfl

/-- The sum is a named multiset of guards. -/
theorem sum_namedMultiset : NamedMultiset piSumCalc.terms[2] "Proc" :=
  ⟨rfl, rfl, ⟨"gs", "Guard", rfl, by decide⟩⟩

/-- Parallel composition is a bare bag beside the sum. -/
theorem piSum_parallelBag : ParallelBag piSumCalc piSumCalc.terms[1] "PiNil" ["PiSum"] where
  bagAuthored := List.getElem_mem (by decide)
  bagShape := ⟨"ps", rfl⟩
  bagAlgebra := rfl
  representedBare := rfl
  unitAuthored := ⟨piSumCalc.terms[0], List.getElem_mem (by decide), rfl, rfl, rfl⟩
  otherParameters := by
    intro rule member notBag
    simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; simp [piCalc]
    · exact absurd rfl notBag
    · exact .inr ⟨by simp [piSumRule], sum_namedMultiset⟩
    all_goals left; simp [piCalc, piRecvRule, piSendRule, piTauRule, TermParam.typeExpr,
      Mettapedia.GSLT.LanguageDef.BagNormalForm.collectionFree]

/-- **The π-calculus with sums is a calculus with restriction and replication.** -/
instance piSumReplicationLanguage : ReplicationLanguage piSumCalc piSumRepBlock where
  bag := ⟨piSumCalc.terms[1], piSum_parallelBag, rfl⟩
  equations := rfl
  restrictAuthored := ⟨piSumCalc.terms[3], List.getElem_mem (by decide), rfl⟩
  restrictShape := by
    intro rule member labelIs
    simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [piCalc, piSumRule, piRecvRule, piSendRule, piTauRule]
  unitShape := by
    intro rule member labelIs
    simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [piCalc, piSumRule, piRecvRule, piSendRule, piTauRule]
  multisetShape := by
    intro rule member listed
    simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [piCalc, piSumRule, piRecvRule, piSendRule, piTauRule] at listed
    exact sum_namedMultiset
  emptyUnitShape := by
    intro label listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    subst listed
    refine ⟨by simp, fun rule member labelIs => ?_⟩
    simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [piCalc, piSumRule, piRecvRule, piSendRule, piTauRule]
  emptyUnitAuthored := by
    intro label listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    subst listed
    exact ⟨piSumCalc.terms[2], List.getElem_mem (by decide), rfl⟩
  labelsUnique := by decide
  params := by
    intro rule member notBare notMultiset parameter present
    simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [piCalc] at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    · simp [piSumRule] at notMultiset
    all_goals
      simp only [piCalc, piRecvRule, piSendRule, piTauRule, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl <;> simp [parameterType?]
  arrowsAbstract := by
    intro rule member notBare notMultiset parameter present domain sort found
    simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [piCalc] at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    · simp [piSumRule] at notMultiset
    all_goals
      simp only [piCalc, piRecvRule, piSendRule, piTauRule, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl <;> simp_all [parameterType?]
  replicateAuthored := ⟨piSumCalc.terms[4], List.getElem_mem (by decide), rfl⟩
  replicateShape := by
    intro rule member labelIs
    simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [piCalc, piSumRule, piRecvRule, piSendRule, piTauRule]
  replicateFresh := by decide

/-- **The signature of the π-calculus with sums is a restriction-block signature.** -/
instance piSumBlockSignature : BlockSignature piSumCalc piSumBlock := piSumReplicationLanguage.toBlockSignature

/-! ## Sums and guards -/

/-- A sum of guards. -/
def sum (guards : List Pattern) : Pattern := .apply "PiSum" [.collection .hashBag guards none]

/-- An input guard. -/
def recv (channel body : Pattern) : Pattern := .apply "PiRecv" [channel, .lambda none body]

/-- An output guard, followed by a process. -/
def send (channel datum continuation : Pattern) : Pattern := .apply "PiSend" [channel, datum, continuation]

/-- A silent guard. -/
def tau (continuation : Pattern) : Pattern := .apply "PiTau" [continuation]

/-- The parameters of the guards and of replication, by label. -/
theorem params_of_label {rule : GrammarRule} (member : rule ∈ piSumCalc.terms) :
    (rule.label = "PiRecv" →
      rule.params = [.simple "x" (.base "Name"), .abstraction "body" (.arrow (.base "Name") (.base "Proc"))]) ∧
    (rule.label = "PiSend" →
      rule.params = [.simple "x" (.base "Name"), .simple "z" (.base "Name"), .simple "k" (.base "Proc")]) ∧
    (rule.label = "PiTau" → rule.params = [.simple "k" (.base "Proc")]) ∧
    (rule.label = "PiRep" → rule.params = [.simple "p" (.base "Proc")]) := by
  simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [piCalc, piSumRule, piRecvRule, piSendRule, piTauRule]

/-- Every constructor makes a process or a guard. -/
theorem category_of_member {rule : GrammarRule} (member : rule ∈ piSumCalc.terms) :
    rule.category = "Proc" ∨ rule.category = "Guard" := by
  simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [piCalc, piSumRule, piRecvRule, piSendRule, piTauRule]

/-- **The summands of a typed sum are guards.** -/
theorem sum_guards {free : FreeTypeContext} {bound : List TypeExpr} {guards : List Pattern}
    (typed : HasType piSumCalc free bound (sum guards) (.base "Proc")) :
    ∀ guard ∈ guards, HasType piSumCalc free bound guard (.base "Guard") := by
  obtain ⟨rule, member, labelIs, -, -, parameterName, elementSort, argument, params, -, argumentsIs, argumentTyped⟩ :=
    multiset_argument (block := piSumBlock) typed (by simp)
  have sortIs : elementSort = "Guard" := by
    simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [piCalc, piSumRule, piRecvRule, piSendRule, piTauRule, TypeExpr.bag]
  subst sortIs
  simp only [List.cons.injEq, and_true] at argumentsIs
  subst argumentsIs
  rcases hasType_collection_inversion argumentTyped with ⟨elementType, typeIs, elementsTyped⟩ |
    ⟨rule', -, -, -, -, typeIs, -⟩
  · simp only [TypeExpr.collection.injEq, true_and] at typeIs
    subst typeIs
    exact elementsHaveType_iff.mp elementsTyped
  · cases typeIs

/-- **A typed input guard** listens on a name, with a process abstracted over the received name. -/
theorem recv_parts {free : FreeTypeContext} {bound : List TypeExpr} {channel body : Pattern} {binder : Option String}
    (typed : HasType piSumCalc free bound (.apply "PiRecv" [channel, .lambda binder body]) (.base "Guard")) :
    HasType piSumCalc free bound channel (.base "Name") ∧
      HasType piSumCalc free (.base "Name" :: bound) body (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  rw [(params_of_label member).1 labelIs.symm] at arguments
  cases arguments with
  | cons _ channelType channelTyped rest =>
      cases rest with
      | cons _ bodyType bodyTyped _ =>
          simp only [parameterType?, Option.some.injEq] at channelType bodyType
          subst channelType bodyType
          cases bodyTyped with
          | lambda inner => exact ⟨channelTyped, inner⟩

/-- **A typed output guard** sends a name on a name, followed by a process. -/
theorem send_parts {free : FreeTypeContext} {bound : List TypeExpr} {channel datum continuation : Pattern}
    (typed : HasType piSumCalc free bound (.apply "PiSend" [channel, datum, continuation]) (.base "Guard")) :
    HasType piSumCalc free bound channel (.base "Name") ∧ HasType piSumCalc free bound datum (.base "Name") ∧
      HasType piSumCalc free bound continuation (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  rw [(params_of_label member).2.1 labelIs.symm] at arguments
  cases arguments with
  | cons _ channelType channelTyped rest =>
      cases rest with
      | cons _ datumType datumTyped rest =>
          cases rest with
          | cons _ continuationType continuationTyped _ =>
              simp only [parameterType?, Option.some.injEq] at channelType datumType continuationType
              subst channelType datumType continuationType
              exact ⟨channelTyped, datumTyped, continuationTyped⟩

/-- **A typed silent guard** is followed by a process. -/
theorem tau_part {free : FreeTypeContext} {bound : List TypeExpr} {continuation : Pattern}
    (typed : HasType piSumCalc free bound (.apply "PiTau" [continuation]) (.base "Guard")) :
    HasType piSumCalc free bound continuation (.base "Proc") := by
  obtain ⟨rule, member, labelIs, -, -, arguments⟩ := hasType_apply_inversion typed
  rw [(params_of_label member).2.2.1 labelIs.symm] at arguments
  cases arguments with
  | cons _ continuationType continuationTyped _ =>
      simp only [parameterType?, Option.some.injEq] at continuationType
      subst continuationType
      exact continuationTyped

theorem object_of_sum {guards : List Pattern} (object : isObjectPattern (sum guards) = true) :
    ∀ guard ∈ guards, isObjectPattern guard = true := by
  simp only [sum, isObjectPattern, isObjectPatternList, Bool.and_true, Option.isNone_none,
    Bool.true_and] at object
  exact isObjectPatternList_iff.mp object

theorem binds_of_sum {guards : List Pattern} (binds : restrictionsBind piSumBlock (sum guards) = true) :
    ∀ guard ∈ guards, restrictionsBind piSumBlock guard = true := by
  simp only [sum, restrictionsBind, restrictionsBindList, Bool.and_true, Bool.and_eq_true] at binds
  rw [restrictionsBindList_eq_all, List.all_eq_true] at binds
  exact binds.2

/-! ## Redexes -/

open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)

/-- **A redex of the π-calculus with sums**: an input and an output on one channel, each a summand of a sum, with the
summands before and after each; or a silent summand of a sum, with the summands before and after it. -/
inductive Redex where
  | comm (channel body datum continuation : Pattern) (before after before' after' : List Pattern)
  | silent (continuation : Pattern) (before after : List Pattern)

namespace Redex

/-- The sums that react. -/
def parts : Redex → List Pattern
  | comm channel body datum continuation before after before' after' =>
      [sum (before ++ recv channel body :: after), sum (before' ++ send channel datum continuation :: after')]
  | silent continuation before after => [sum (before ++ tau continuation :: after)]

/-- What they leave: the reception beside the output's continuation, or the silent summand's continuation. -/
def result : Redex → List Pattern
  | comm _ body datum continuation _ _ _ _ => [instantiateBVar datum body, continuation]
  | silent continuation _ _ => [continuation]

/-- Rename a redex's variables. -/
def rename (relabel : Nat → Nat) : Redex → Redex
  | comm channel body datum continuation before after before' after' =>
      comm (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel channel)
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename (liftIndex 1 relabel) body)
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel datum)
        (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel continuation)
        (before.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
        (after.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
        (before'.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
        (after'.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
  | silent continuation before after =>
      silent (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel continuation)
        (before.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))
        (after.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel))

theorem parts_rename (relabel : Nat → Nat) (redex : Redex) :
    (redex.rename relabel).parts = redex.parts.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel) := by
  cases redex <;> simp [rename, parts, sum, recv, send, tau, rename_apply, rename_collection, rename_lambda]

theorem result_rename (relabel : Nat → Nat) (redex : Redex) :
    (redex.rename relabel).result = redex.result.map (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel) := by
  cases redex <;> simp [rename, result, rename_instantiate]

/-- **What a redex leaves are processes.** -/
theorem result_members {free : FreeTypeContext} {bound : List TypeExpr} (redex : Redex)
    (members : Members piSumCalc piSumBlock free bound redex.parts) :
    Members piSumCalc piSumBlock free bound redex.result := by
  cases redex with
  | comm channel body datum continuation before after before' after' =>
      have receiving := sum_guards (members _ (List.mem_cons_self)) (recv channel body) (by simp)
      have sending := sum_guards (members _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (send channel datum continuation) (by simp)
      obtain ⟨-, bodyTyped⟩ := recv_parts receiving
      obtain ⟨-, datumTyped, continuationTyped⟩ := send_parts sending
      intro element member
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · rw [← substitute_single_eq_instantiateBVar]
        refine HasType.substituteBoundOnSupport bodyTyped _ fun index type _ lookup => ?_
        cases index with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
            subst lookup
            exact datumTyped
        | succ index => exact HasType.bvar (by simpa using lookup)
      · exact continuationTyped
  | silent continuation before after =>
      have silentTyped := sum_guards (members _ List.mem_cons_self) (tau continuation) (by simp)
      intro element member
      simp only [result, List.mem_singleton] at member
      subst member
      exact tau_part silentTyped

theorem result_objects (redex : Redex) (objects : ∀ part ∈ redex.parts, isObjectPattern part = true) :
    ∀ element ∈ redex.result, isObjectPattern element = true := by
  cases redex with
  | comm channel body datum continuation before after before' after' =>
      have receiving := object_of_sum (objects _ List.mem_cons_self) (recv channel body) (by simp)
      have sending := object_of_sum (objects _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (send channel datum continuation) (by simp)
      simp only [recv, isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at receiving
      simp only [send, isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at sending
      intro element member
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · rw [← substitute_single_eq_instantiateBVar]
        refine isObject_substitute _ (fun index => ?_) receiving.2
        cases index with
        | zero => exact sending.2.1
        | succ => rfl
      · exact sending.2.2
  | silent continuation before after =>
      have silentObject := object_of_sum (objects _ List.mem_cons_self) (tau continuation) (by simp)
      intro element member
      simp only [result, List.mem_singleton] at member
      subst member
      simpa [tau, isObjectPattern, isObjectPatternList] using silentObject

/-- A variable of a summand is a variable of the sum. -/
theorem freeIn_sum {index : Nat} {guard : Pattern} {guards : List Pattern} (member : guard ∈ guards)
    (free : FreeIn index guard) : FreeIn index (sum guards) :=
  freeIn_apply.mpr ⟨.collection .hashBag guards none, by simp, freeIn_collection.mpr ⟨guard, member, free⟩⟩

theorem freeIn_result (redex : Redex) {index : Nat} {element : Pattern} (member : element ∈ redex.result)
    (free : FreeIn index element) : ∃ part ∈ redex.parts, FreeIn index part := by
  cases redex with
  | comm channel body datum continuation before after before' after' =>
      simp only [result, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · rcases freeIn_instantiate free with inBody | inDatum
        · exact ⟨_, List.mem_cons_self, freeIn_sum (guard := recv channel body) (by simp)
            (freeIn_apply.mpr ⟨.lambda none body, by simp, freeIn_lambda.mpr inBody⟩)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
            freeIn_sum (guard := send channel datum continuation) (by simp)
              (freeIn_apply.mpr ⟨datum, by simp, inDatum⟩)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
          freeIn_sum (guard := send channel datum element) (by simp) (freeIn_apply.mpr ⟨element, by simp, free⟩)⟩
  | silent continuation before after =>
      simp only [result, List.mem_singleton] at member
      subst member
      exact ⟨_, List.mem_cons_self, freeIn_sum (guard := tau element) (by simp)
        (freeIn_apply.mpr ⟨element, by simp, free⟩)⟩

end Redex

/-! ## Canonical guards and sums -/

theorem sumFresh : piSumRepBlock.replicate ∉ piSumRepBlock.emptyUnits :=
  replicate_not_emptyUnit (block := piSumRepBlock) (language := piSumCalc)

theorem sumRestrictFresh : piSumRepBlock.replicate ≠ piSumRepBlock.restrict :=
  replicate_ne_restrict (block := piSumRepBlock) (language := piSumCalc)

/-- A typed guard's constructor is an input, an output or a silent prefix. -/
theorem guard_label {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {arguments : List Pattern}
    (typed : HasType piSumCalc free bound (.apply label arguments) (.base "Guard")) :
    label = "PiRecv" ∨ label = "PiSend" ∨ label = "PiTau" := by
  obtain ⟨rule, member, labelIs, -, typeIs, -⟩ := hasType_apply_inversion typed
  simp only [TypeExpr.base.injEq] at typeIs
  subst labelIs
  simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd typeIs (by simp [piCalc])
  · exact absurd typeIs (by simp [piCalc])
  · exact absurd typeIs (by simp [piSumRule])
  · exact absurd typeIs (by simp [piCalc])
  · exact absurd typeIs (by simp [piCalc])
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- An application of one argument other than restriction and replication reads canonically as one component. -/
theorem canonP_single (label : String) (argument : Pattern) (notRestrict : label ≠ "PiNu")
    (notReplicate : label ≠ "PiRep") (notEmpty : label ≠ "PiSum") :
    canonP piSumRepBlock (.apply label [argument]) =
      Prenex.atom (.apply label [argumentOf piSumRepBlock label argument (canonP piSumRepBlock argument)]) := by
  rw [canonP_apply (by simp) (fun _ _ same => notRestrict same.1) (fun _ _ same => notReplicate same.1)
    (fun _ _ _ listed => absurd (by simpa using listed) notEmpty)]
  rw [canonsP, canonsP]
  rfl

theorem canonP_pair (label : String) (first second : Pattern) :
    canonP piSumRepBlock (.apply label [first, second]) =
      Prenex.atom (.apply label (List.zipWith (argumentOf piSumRepBlock label) [first, second]
        (canonsP piSumRepBlock [first, second]))) :=
  canonP_apply (by simp) (by simp) (by simp) (by simp)

theorem canonP_triple (label : String) (first second third : Pattern) :
    canonP piSumRepBlock (.apply label [first, second, third]) =
      Prenex.atom (.apply label (List.zipWith (argumentOf piSumRepBlock label) [first, second, third]
        (canonsP piSumRepBlock [first, second, third]))) :=
  canonP_apply (by simp) (by simp) (by simp) (by simp)

/-- **A typed guard is its own block, not replicated, and reads canonically as one component.** -/
theorem guard_facts {free : FreeTypeContext} {bound : List TypeExpr} {guard : Pattern}
    (typed : HasType piSumCalc free bound guard (.base "Guard")) (object : isObjectPattern guard = true) :
    decompose piSumBlock guard = Prenex.atom guard ∧ isReplicated piSumRepBlock guard = false ∧
      canonP piSumRepBlock guard = Prenex.atom (canonR piSumRepBlock guard) := by
  refine ⟨decompose_other typed (by simp), ?_, ?_⟩
  · cases replicated : isReplicated piSumRepBlock guard
    · rfl
    · obtain ⟨argument, rfl⟩ := isReplicated_shape replicated
      rcases guard_label typed with labelIs | labelIs | labelIs <;> simp at labelIs
  · cases guard with
    | bvar => rfl
    | fvar => rfl
    | apply label arguments =>
        have labels := guard_label typed
        unfold canonR
        rw [canonP_apply (fun same => by rcases labels with rfl | rfl | rfl <;> simp_all)
          (fun _ _ same => by rcases labels with rfl | rfl | rfl <;> simp_all)
          (fun _ _ same => by rcases labels with rfl | rfl | rfl <;> simp_all)
          (fun _ _ _ listed => by rcases labels with rfl | rfl | rfl <;> simp_all)]
        rfl
    | lambda => cases typed
    | multiLambda => cases typed
    | subst => simp [isObjectPattern] at object
    | collection =>
        have sortIs := (piSumBlockSignature.bag_members typed).2.1
        simp at sortIs

theorem canonsP_guards {free : FreeTypeContext} {bound : List TypeExpr} : ∀ {guards : List Pattern},
    (∀ guard ∈ guards, HasType piSumCalc free bound guard (.base "Guard")) →
    (∀ guard ∈ guards, isObjectPattern guard = true) →
    canonsP piSumRepBlock guards = (guards.map (canonR piSumRepBlock)).map Prenex.atom
  | [], _, _ => rfl
  | guard :: guards, typed, objects => by
      rw [canonsP, (guard_facts (typed guard List.mem_cons_self) (objects guard List.mem_cons_self)).2.2,
        canonsP_guards (fun other member => typed other (List.mem_cons_of_mem _ member))
          (fun other member => objects other (List.mem_cons_of_mem _ member))]
      rfl

/-- **A typed sum with a summand reads canonically as the sum of the canonical block of its summands read
canonically.** -/
theorem canonR_sum {free : FreeTypeContext} {bound : List TypeExpr} {guards : List Pattern}
    (typed : HasType piSumCalc free bound (sum guards) (.base "Proc")) (object : isObjectPattern (sum guards) = true)
    (nonempty : guards ≠ []) :
    canonR piSumRepBlock (sum guards) =
      sum (normal piSumRepBlock ⟨0, guards.map (canonR piSumRepBlock)⟩).components := by
  have guardsTyped := sum_guards typed
  have guardsObject := object_of_sum object
  have guardsBind := binds_of_sum (restrictionsBind_of_typed (block := piSumRepBlock) _ typed)
  have bagIs : canonP piSumRepBlock (.collection .hashBag guards none) =
      normal piSumRepBlock ⟨0, guards.map (canonR piSumRepBlock)⟩ := by
    simp only [canonP]
    rw [canonsP_guards guardsTyped guardsObject, foldr_par_atoms]
  obtain ⟨guard, member⟩ := List.exists_mem_of_ne_nil guards nonempty
  have bagNotNil : canonP piSumRepBlock (.collection .hashBag guards none) ≠ Prenex.nil :=
    canonP_bag_ne_nil sumFresh sumRestrictFresh guardsObject guardsBind
      ⟨guard, member, by
        rw [(guard_facts (guardsTyped guard member) (guardsObject guard member)).2.2]
        simp [Prenex.atom, Prenex.nil]⟩
  unfold canonR
  rw [sum, canonP_apply (by simp) (by simp) (by simp) (fun argument _ same _ => by
    simp only [List.cons.injEq, and_true] at same
    subst same
    exact bagNotNil)]
  simp only [canonsP, List.zipWith_cons_cons, List.zipWith_nil_right, argumentOf, bagIs]
  simp only [List.mem_singleton, if_true, multisetOf, normal_count_zero]
  rfl

/-- **A sum of atoms read again** is the sum of their canonical block. -/
theorem recanon_sum {guards : List Pattern} (atomic : ∀ guard ∈ guards, decompose piSumBlock guard = Prenex.atom guard) :
    recanon piSumRepBlock (sum guards) = sum (normal piSumRepBlock ⟨0, guards⟩).components := by
  rw [sum, recanon_apply_multiset (by decide) (by simp)]
  simp only [List.map_cons, List.map_nil]
  rw [multisetPart_other (by simp) (by simp), decompose_bag, decomposeList_atoms atomic]
  simp [multisetOf, normal_count_zero, sum]

theorem prenex_ext {first second : Prenex} (count : first.count = second.count)
    (components : first.components = second.components) : first = second := by
  cases first
  cases second
  simp_all

/-- Alike components read again alike. -/
theorem recanon_eq_of_alike {first second : Pattern} (alike : AlikeR piSumRepBlock first second) :
    recanon piSumRepBlock first = recanon piSumRepBlock second := by
  have read := alike.2.2.1 id Function.injective_id
  rwa [rename_id, rename_id] at read

/-- A typed argument of a collection type is a collection, its members as they stand. -/
theorem collection_of_typed {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {argument : Pattern} {kind : CollType} {elementType : TypeExpr}
    (typed : HasType piSumCalc free bound argument (.collection kind elementType))
    (object : isObjectPattern argument = true) : ∃ elements, argument = .collection kind elements none := by
  cases argument with
  | bvar index =>
      cases typed with
      | bvar lookup =>
          obtain ⟨sort, sortIs⟩ := context.bound _ (List.mem_of_getElem? lookup)
          cases sortIs
  | fvar name =>
      cases typed with
      | fvar lookup =>
          obtain ⟨sort, sortIs⟩ := context.free _ _ lookup
          cases sortIs
  | apply label arguments =>
      obtain ⟨rule, -, -, -, typeIs, -⟩ := hasType_apply_inversion typed
      cases typeIs
  | lambda => cases typed
  | multiLambda => cases typed
  | subst => simp [isObjectPattern] at object
  | collection kind' elements rest =>
      rcases hasType_collection_inversion typed with ⟨elementType', typeIs, -⟩ | ⟨rule, -, -, -, -, typeIs, -⟩
      · simp only [TypeExpr.collection.injEq] at typeIs
        obtain ⟨rfl, -⟩ := typeIs
        have restNone : rest = none := by
          simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
          exact object.1
        subst restNone
        exact ⟨elements, rfl⟩
      · cases typeIs

/-- **A typed process whose reading again is a sum is a sum.** -/
theorem sum_of_recanon {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {shown : Pattern} {guards : List Pattern} (typed : HasType piSumCalc free bound shown (.base "Proc"))
    (object : isObjectPattern shown = true) (read : recanon piSumRepBlock shown = sum guards) :
    ∃ shownGuards, shown = sum shownGuards := by
  cases shown with
  | apply label arguments =>
      by_cases isRestrict : label = piSumRepBlock.restrict
      · subst isRestrict
        rw [recanon_apply_restrict] at read
        simp [sum] at read
      by_cases listed : label ∈ piSumRepBlock.multisets
      · have labelIs : label = "PiSum" := by simpa using listed
        subst labelIs
        obtain ⟨rule, -, -, -, -, parameterName, elementSort, argument, -, -, argumentsIs, argumentTyped⟩ :=
          multiset_argument (block := piSumBlock) typed (by simp)
        subst argumentsIs
        have argumentObject : isObjectPattern argument = true := by
          simpa [isObjectPattern, isObjectPatternList] using object
        obtain ⟨elements, rfl⟩ := collection_of_typed context argumentTyped argumentObject
        exact ⟨elements, rfl⟩
      · rw [recanon_apply_other isRestrict listed] at read
        simp only [sum, Pattern.apply.injEq] at read
        exact absurd (by rw [read.1]; simp) listed
  | collection kind elements rest =>
      rw [recanon_collection] at read
      cases read
  | lambda binder body =>
      rw [recanon_lambda] at read
      cases read
  | bvar index =>
      rw [recanon_bvar] at read
      cases read
  | fvar name =>
      rw [recanon_fvar] at read
      cases read
  | subst body replacement =>
      rw [recanon_subst] at read
      cases read
  | multiLambda => cases typed

/-- **A component read alike to a typed sum's canonical form is a sum with a summand read again as each summand of
the sum read canonically.** -/
theorem matched_summand {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {shown : Pattern} {guards : List Pattern} {guard : Pattern}
    (shownTyped : HasType piSumCalc free bound shown (.base "Proc")) (shownObject : isObjectPattern shown = true)
    (sumTyped : HasType piSumCalc free bound (sum guards) (.base "Proc"))
    (sumObject : isObjectPattern (sum guards) = true) (member : guard ∈ guards)
    (alike : AlikeR piSumRepBlock shown (canonR piSumRepBlock (sum guards))) :
    ∃ shownGuards, shown = sum shownGuards ∧ ∃ shownGuard ∈ shownGuards,
      recanon piSumRepBlock shownGuard = recanon piSumRepBlock (canonR piSumRepBlock guard) := by
  have guardsTyped := sum_guards sumTyped
  have guardsObject := object_of_sum sumObject
  -- the canonical summands
  have canonIs := canonR_sum sumTyped sumObject (List.ne_nil_of_mem member)
  set canonical := (normal piSumRepBlock ⟨0, guards.map (canonR piSumRepBlock)⟩).components with canonicalIs
  have mappedFacts : ∀ component ∈ guards.map (canonR piSumRepBlock),
      decompose piSumBlock component = Prenex.atom component ∧ isReplicated piSumRepBlock component = false := by
    intro component inMapped
    obtain ⟨original, inGuards, rfl⟩ := List.mem_map.mp inMapped
    obtain ⟨atomic, plain, -⟩ := guard_facts (canonR_sound (block := piSumRepBlock) context
      (guardsTyped original inGuards)).1 (isObject_canonR (block := piSumRepBlock) (guardsObject original inGuards))
    exact ⟨atomic, plain⟩
  have mappedAtomic : (Prenex.mk 0 (guards.map (canonR piSumRepBlock))).Atomic piSumBlock :=
    fun component inMapped => (mappedFacts component inMapped).1
  have canonicalPerm : canonical.Perm ((guards.map (canonR piSumRepBlock)).map (recanon piSumRepBlock)) :=
    normal_plain_perm sumFresh sumRestrictFresh mappedAtomic fun component inMapped => (mappedFacts component inMapped).2
  have canonicalAtomic : (Prenex.mk 0 canonical).Atomic piSumBlock :=
    normal_atomic sumFresh sumRestrictFresh mappedAtomic
  have canonicalPlain : ∀ component ∈ canonical, isReplicated piSumRepBlock component = false := by
    intro component inCanonical
    obtain ⟨original, inMapped, rfl⟩ := List.mem_map.mp (canonicalPerm.subset inCanonical)
    rw [isReplicated_recanon]
    exact (mappedFacts original inMapped).2
  -- the shown component is a sum read as the canonical summands
  have readSame := recanon_eq_of_alike alike
  rw [canonIs, recanon_sum canonicalAtomic] at readSame
  obtain ⟨shownGuards, rfl⟩ := sum_of_recanon context shownTyped shownObject readSame
  have shownGuardsTyped := sum_guards shownTyped
  have shownGuardsObject := object_of_sum shownObject
  have shownAtomic : (Prenex.mk 0 shownGuards).Atomic piSumBlock := fun component inShown =>
    (guard_facts (shownGuardsTyped component inShown) (shownGuardsObject component inShown)).1
  have shownPlain : ∀ component ∈ shownGuards, isReplicated piSumRepBlock component = false :=
    fun component inShown => (guard_facts (shownGuardsTyped component inShown) (shownGuardsObject component inShown)).2.1
  rw [recanon_sum shownAtomic] at readSame
  have sameNormal : normal piSumRepBlock ⟨0, shownGuards⟩ = normal piSumRepBlock ⟨0, canonical⟩ :=
    prenex_ext (by rw [normal_count_zero, normal_count_zero]) (by simpa [sum] using readSame)
  have readPerm := plain_reads_alike sumFresh sumRestrictFresh shownAtomic canonicalAtomic shownPlain canonicalPlain
    sameNormal
  -- the summand read as the given one
  have inCanonical : recanon piSumRepBlock (canonR piSumRepBlock guard) ∈ canonical :=
    canonicalPerm.symm.subset (List.mem_map_of_mem (List.mem_map_of_mem member))
  obtain ⟨shownGuard, inShownGuards, readIs⟩ :=
    List.mem_map.mp (readPerm.symm.subset (List.mem_map_of_mem inCanonical))
  refine ⟨shownGuards, rfl, shownGuard, inShownGuards, ?_⟩
  rw [readIs, recanon_recanon sumFresh sumRestrictFresh (idemUpTo_all sumFresh sumRestrictFresh _)]

/-! ## Components alike to the canonical parts -/

/-- **A typed object name is a variable**: the π-calculus with sums has no constructor of names. -/
theorem name_cases {free : FreeTypeContext} {bound : List TypeExpr} {name : Pattern}
    (typed : HasType piSumCalc free bound name (.base "Name")) (object : isObjectPattern name = true) :
    (∃ index, name = .bvar index) ∨ ∃ name', name = .fvar name' := by
  cases name with
  | bvar index => exact .inl ⟨index, rfl⟩
  | fvar name' => exact .inr ⟨name', rfl⟩
  | lambda => cases typed
  | multiLambda => cases typed
  | subst => simp [isObjectPattern] at object
  | apply =>
      obtain ⟨rule, member, -, -, typeIs, -⟩ := hasType_apply_inversion typed
      simp only [TypeExpr.base.injEq] at typeIs
      rcases category_of_member member with categoryIs | categoryIs <;>
        exact absurd (typeIs.trans categoryIs) (by decide)
  | collection =>
      have sortIs := (piSumBlockSignature.bag_members typed).2.1
      exact absurd sortIs (by simp)

theorem canonP_name {name : Pattern} (isName : (∃ index, name = .bvar index) ∨ ∃ name', name = .fvar name') :
    canonP piSumRepBlock name = Prenex.atom name := by
  rcases isName with ⟨index, rfl⟩ | ⟨name', rfl⟩ <;> rfl

theorem canonArgument_var {name : Pattern} (isName : (∃ index, name = .bvar index) ∨ ∃ name', name = .fvar name') :
    canonArgument (canonicalOf piSumRepBlock) name = name := by
  rcases isName with ⟨index, rfl⟩ | ⟨name', rfl⟩ <;> rfl

theorem canonR_recv {channel body : Pattern}
    (channelName : (∃ index, channel = .bvar index) ∨ ∃ name', channel = .fvar name') :
    canonR piSumRepBlock (recv channel body) = .apply "PiRecv" [channel, .lambda none (canonR piSumRepBlock body)] := by
  unfold canonR
  rw [recv, canonP_pair]
  simp [canonsP, canonP_name channelName, canonP, argumentOf]
  rfl

theorem canonR_send {channel datum continuation : Pattern}
    (channelName : (∃ index, channel = .bvar index) ∨ ∃ name', channel = .fvar name')
    (datumName : (∃ index, datum = .bvar index) ∨ ∃ name', datum = .fvar name') :
    canonR piSumRepBlock (send channel datum continuation) =
      .apply "PiSend" [channel, datum, canonR piSumRepBlock continuation] := by
  unfold canonR
  rw [send, canonP_triple]
  simp [canonsP, canonP_name channelName, canonP_name datumName, argumentOf]
  rfl

theorem canonR_tau {continuation : Pattern} :
    canonR piSumRepBlock (tau continuation) = .apply "PiTau" [canonR piSumRepBlock continuation] := by
  unfold canonR
  rw [tau, canonP_single "PiTau" continuation (by decide) (by decide) (by decide)]
  simp [argumentOf]
  rfl

theorem recanon_recv {channel reading : Pattern}
    (channelName : (∃ index, channel = .bvar index) ∨ ∃ name', channel = .fvar name') :
    recanon piSumRepBlock (.apply "PiRecv" [channel, .lambda none reading]) =
      .apply "PiRecv" [channel, .lambda none (canonicalOf piSumRepBlock reading)] := by
  rw [recanon_apply_other (by simp) (by simp)]
  simp only [List.map_cons, List.map_nil]
  rw [canonArgument_var channelName]
  rfl

theorem recanon_send {channel datum reading : Pattern}
    (channelName : (∃ index, channel = .bvar index) ∨ ∃ name', channel = .fvar name')
    (datumName : (∃ index, datum = .bvar index) ∨ ∃ name', datum = .fvar name') :
    recanon piSumRepBlock (.apply "PiSend" [channel, datum, reading]) =
      .apply "PiSend" [channel, datum, canonArgument (canonicalOf piSumRepBlock) reading] := by
  rw [recanon_apply_other (by simp) (by simp)]
  simp only [List.map_cons, List.map_nil, canonArgument_var channelName, canonArgument_var datumName]

theorem recanon_tau (reading : Pattern) :
    recanon piSumRepBlock (.apply "PiTau" [reading]) =
      .apply "PiTau" [canonArgument (canonicalOf piSumRepBlock) reading] := by
  rw [recanon_apply_other (by simp) (by simp)]
  simp only [List.map_cons, List.map_nil]

/-- The label of a guard read again is its own. -/
theorem recanon_guard {free : FreeTypeContext} {bound : List TypeExpr} {label : String} {arguments : List Pattern}
    (typed : HasType piSumCalc free bound (.apply label arguments) (.base "Guard")) :
    recanon piSumRepBlock (.apply label arguments) =
      .apply label (arguments.map (canonArgument (canonicalOf piSumRepBlock))) := by
  have labels := guard_label typed
  exact recanon_apply_other (by rcases labels with rfl | rfl | rfl <;> simp)
    (by rcases labels with rfl | rfl | rfl <;> simp)

/-- **A guard read again as an input reads is an input on that channel**, its body read canonically as that input's
body. -/
theorem shown_recv {free : FreeTypeContext} {bound : List TypeExpr} {shown channel reading : Pattern}
    (typed : HasType piSumCalc free bound shown (.base "Guard")) (object : isObjectPattern shown = true)
    (read : recanon piSumRepBlock shown = .apply "PiRecv" [channel, .lambda none reading]) :
    ∃ body, shown = .apply "PiRecv" [channel, .lambda none body] ∧ canonicalOf piSumRepBlock body = reading := by
  cases shown with
  | apply label arguments =>
      rw [recanon_guard typed] at read
      simp only [Pattern.apply.injEq] at read
      obtain ⟨rfl, mapped⟩ := read
      have lengthTwo : arguments.length = 2 := by simpa using congrArg List.length mapped
      obtain ⟨first, second, rfl⟩ := List.length_eq_two.mp lengthTwo
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
      obtain ⟨channelIs, bodyIs⟩ := mapped
      obtain ⟨rule, member, labelIs, -, -, argumentsTyped⟩ := hasType_apply_inversion typed
      rw [(params_of_label member).1 labelIs.symm] at argumentsTyped
      cases argumentsTyped with
      | cons _ channelType channelTyped rest =>
          cases rest with
          | cons representation bodyType bodyTyped _ =>
              simp only [parameterType?, Option.some.injEq] at channelType bodyType
              subst channelType bodyType
              obtain ⟨inner, rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp representation
              have firstObject : isObjectPattern first = true := by
                simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true] at object
                exact object.1
              rw [canonArgument_var (name_cases channelTyped firstObject)] at channelIs
              subst channelIs
              simp only [canonArgument, Pattern.lambda.injEq] at bodyIs
              exact ⟨inner, rfl, bodyIs.2⟩
  | collection kind elements rest =>
      rw [recanon_collection] at read
      cases read
  | lambda binder body =>
      rw [recanon_lambda] at read
      cases read
  | bvar index =>
      rw [recanon_bvar] at read
      cases read
  | fvar name' =>
      rw [recanon_fvar] at read
      cases read
  | subst body replacement =>
      rw [recanon_subst] at read
      cases read
  | multiLambda => cases typed

/-- **A guard read again as an output reads is an output of that datum on that channel**, its continuation read
canonically as that output's continuation. -/
theorem shown_send {free : FreeTypeContext} {bound : List TypeExpr} {shown channel datum reading : Pattern}
    (typed : HasType piSumCalc free bound shown (.base "Guard")) (object : isObjectPattern shown = true)
    (read : recanon piSumRepBlock shown = .apply "PiSend" [channel, datum, reading]) :
    ∃ continuation, shown = .apply "PiSend" [channel, datum, continuation] ∧
      canonArgument (canonicalOf piSumRepBlock) continuation = reading := by
  cases shown with
  | apply label arguments =>
      rw [recanon_guard typed] at read
      simp only [Pattern.apply.injEq] at read
      obtain ⟨rfl, mapped⟩ := read
      have lengthThree : arguments.length = 3 := by simpa using congrArg List.length mapped
      obtain ⟨first, second, third, rfl⟩ := List.length_eq_three.mp lengthThree
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
      obtain ⟨channelIs, datumIs, continuationIs⟩ := mapped
      obtain ⟨channelTyped, datumTyped, -⟩ := send_parts typed
      simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at object
      rw [canonArgument_var (name_cases channelTyped object.1)] at channelIs
      rw [canonArgument_var (name_cases datumTyped object.2.1)] at datumIs
      subst channelIs datumIs
      exact ⟨third, rfl, continuationIs⟩
  | collection kind elements rest =>
      rw [recanon_collection] at read
      cases read
  | lambda binder body =>
      rw [recanon_lambda] at read
      cases read
  | bvar index =>
      rw [recanon_bvar] at read
      cases read
  | fvar name' =>
      rw [recanon_fvar] at read
      cases read
  | subst body replacement =>
      rw [recanon_subst] at read
      cases read
  | multiLambda => cases typed

/-- **A guard read again as a silent prefix reads is a silent prefix**, its continuation read canonically as that
prefix's continuation. -/
theorem shown_tau {free : FreeTypeContext} {bound : List TypeExpr} {shown reading : Pattern}
    (typed : HasType piSumCalc free bound shown (.base "Guard"))
    (read : recanon piSumRepBlock shown = .apply "PiTau" [reading]) :
    ∃ continuation, shown = .apply "PiTau" [continuation] ∧
      canonArgument (canonicalOf piSumRepBlock) continuation = reading := by
  cases shown with
  | apply label arguments =>
      rw [recanon_guard typed] at read
      simp only [Pattern.apply.injEq] at read
      obtain ⟨rfl, mapped⟩ := read
      have lengthOne : arguments.length = 1 := by simpa using congrArg List.length mapped
      obtain ⟨first, rfl⟩ := List.length_eq_one_iff.mp lengthOne
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
      exact ⟨first, rfl, mapped⟩
  | collection kind elements rest =>
      rw [recanon_collection] at read
      cases read
  | lambda binder body =>
      rw [recanon_lambda] at read
      cases read
  | bvar index =>
      rw [recanon_bvar] at read
      cases read
  | fvar name' =>
      rw [recanon_fvar] at read
      cases read
  | subst body replacement =>
      rw [recanon_subst] at read
      cases read
  | multiLambda => cases typed

/-- **A typed argument read canonically is equivalent to it.** -/
theorem canonArgument_canonicalOf_equivalent {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) {argument : Pattern} {sort : String}
    (typed : HasType piSumCalc free bound argument (.base sort)) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piSumCalc
      (canonArgument (canonicalOf piSumRepBlock) argument) argument := by
  cases argument with
  | lambda => cases typed
  | multiLambda => cases typed
  | bvar => exact .refl _
  | fvar => exact .refl _
  | subst => exact .refl _
  | apply => exact .symm _ _ (canonicalOf_sound (block := piSumRepBlock) context typed).2.toEquationEquiv
  | collection => exact .symm _ _ (canonicalOf_sound (block := piSumRepBlock) context typed).2.toEquationEquiv

/-- Processes whose canonical arguments read alike are equivalent. -/
theorem continuation_equivalent {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {shown original : Pattern} (shownTyped : HasType piSumCalc free bound shown (.base "Proc"))
    (originalTyped : HasType piSumCalc free bound original (.base "Proc"))
    (read : canonArgument (canonicalOf piSumRepBlock) shown =
      canonArgument (canonicalOf piSumRepBlock) (canonR piSumRepBlock original)) :
    EquationEquiv (engineBasePremises RelationEnv.empty) piSumCalc shown original := by
  obtain ⟨canonTyped, toCanon⟩ := canonR_sound (block := piSumRepBlock) context originalTyped
  have shownSide := canonArgument_canonicalOf_equivalent context shownTyped
  have originalSide := canonArgument_canonicalOf_equivalent context canonTyped
  rw [read] at shownSide
  exact .trans _ _ _ (.symm _ _ shownSide) (.trans _ _ _ originalSide (.symm _ _ toCanon.toEquationEquiv))

/-- A list split around its member at an index. -/
theorem split_at {α : Type} (elements : List α) (index : Nat) (inside : index < elements.length) :
    elements = elements.take index ++ elements[index] :: elements.drop (index + 1) := by
  rw [List.getElem_cons_drop inside, List.take_append_drop]

theorem getElem_split {α : Type} (before after : List α) (element : α) :
    (before ++ element :: after)[before.length]'(by simp) = element := by
  simp

/-- **Components read alike to the canonical forms of a redex's parts are a redex** leaving processes equivalent to
what the redex leaves. -/
theorem Redex.alike {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound) (redex : Redex)
    (shown : List Pattern) (partsMembers : Members piSumCalc piSumBlock free bound redex.parts)
    (partsObjects : ∀ part ∈ redex.parts, isObjectPattern part = true)
    (shownMembers : Members piSumCalc piSumBlock free bound shown)
    (shownObjects : ∀ part ∈ shown, isObjectPattern part = true)
    (related : List.Forall₂ (fun part original => AlikeR piSumRepBlock part (canonR piSumRepBlock original)) shown
      redex.parts) :
    ∃ redex' : Redex, redex'.parts = shown ∧
      List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) piSumCalc) redex'.result redex.result := by
  cases redex with
  | comm channel body datum continuation before after before' after' =>
      cases related with
      | cons firstAlike rest =>
          cases rest with
          | cons secondAlike last =>
              cases last
              rename_i firstShown secondShown
              have firstTyped := partsMembers _ List.mem_cons_self
              have secondTyped := partsMembers _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have firstObject := partsObjects _ List.mem_cons_self
              have secondObject := partsObjects _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have receiving := sum_guards firstTyped (recv channel body) (by simp)
              have sending := sum_guards secondTyped (send channel datum continuation) (by simp)
              have receivingObject := object_of_sum firstObject (recv channel body) (by simp)
              have sendingObject := object_of_sum secondObject (send channel datum continuation) (by simp)
              obtain ⟨channelTyped, bodyTyped⟩ := recv_parts receiving
              obtain ⟨-, datumTyped, continuationTyped⟩ := send_parts sending
              simp only [recv, isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true]
                at receivingObject
              simp only [send, isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at sendingObject
              have channelName := name_cases channelTyped receivingObject.1
              have datumName := name_cases datumTyped sendingObject.2.1
              -- the summands read as the input and the output
              have firstShownTyped := shownMembers _ List.mem_cons_self
              have secondShownTyped := shownMembers _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have firstShownObject := shownObjects _ List.mem_cons_self
              have secondShownObject := shownObjects _ (List.mem_cons_of_mem _ List.mem_cons_self)
              obtain ⟨firstGuards, rfl, receiver, receiverIn, receiverRead⟩ :=
                matched_summand context firstShownTyped firstShownObject firstTyped firstObject
                  (guard := recv channel body) (by simp) firstAlike
              obtain ⟨secondGuards, rfl, sender, senderIn, senderRead⟩ :=
                matched_summand context secondShownTyped secondShownObject secondTyped secondObject
                  (guard := send channel datum continuation) (by simp) secondAlike
              rw [canonR_recv channelName, recanon_recv channelName] at receiverRead
              rw [canonR_send channelName datumName, recanon_send channelName datumName] at senderRead
              have receiverTyped := sum_guards firstShownTyped receiver receiverIn
              have senderTyped := sum_guards secondShownTyped sender senderIn
              obtain ⟨body', rfl, bodyRead⟩ := shown_recv receiverTyped
                (object_of_sum firstShownObject _ receiverIn) receiverRead
              obtain ⟨continuation', rfl, continuationRead⟩ := shown_send senderTyped
                (object_of_sum secondShownObject _ senderIn) senderRead
              obtain ⟨before1, after1, firstSplit⟩ := List.append_of_mem receiverIn
              obtain ⟨before2, after2, secondSplit⟩ := List.append_of_mem senderIn
              refine ⟨.comm channel body' datum continuation' before1 after1 before2 after2, ?_, ?_⟩
              · rw [firstSplit, secondSplit]
                rfl
              -- the bodies are equivalent, and stay so once the datum is received
              obtain ⟨-, body'Typed⟩ := recv_parts receiverTyped
              obtain ⟨-, -, continuation'Typed⟩ := send_parts senderTyped
              have receiverObject := object_of_sum firstShownObject _ receiverIn
              have body'Object : isObjectPattern body' = true := by
                simp only [isObjectPattern, isObjectPatternList, Bool.and_eq_true, Bool.and_true] at receiverObject
                exact receiverObject.2
              have bodyContext := context.cons "Name"
              have toCanonical := (canonicalOf_sound (block := piSumRepBlock) bodyContext body'Typed).2.toEquationEquiv
              obtain ⟨canonRTyped, toCanonR⟩ := canonR_sound (block := piSumRepBlock) bodyContext bodyTyped
              have canonRCanonical :=
                (canonicalOf_sound (block := piSumRepBlock) bodyContext canonRTyped).2.toEquationEquiv
              rw [bodyRead] at toCanonical
              have chain : EquationEquiv (engineBasePremises RelationEnv.empty) piSumCalc body' body :=
                .trans _ _ _ toCanonical (.trans _ _ _ (.symm _ _ canonRCanonical) (.symm _ _ toCanonR.toEquationEquiv))
              exact .cons (sortedEquiv_instantiate_replication (block := piSumRepBlock) context datumTyped
                sendingObject.2.1 body'Typed bodyTyped body'Object receivingObject.2 chain)
                (.cons (continuation_equivalent context continuation'Typed continuationTyped continuationRead) .nil)
  | silent continuation before after =>
      cases related with
      | cons silentAlike last =>
          cases last
          rename_i silentShown
          have silentTyped := partsMembers _ List.mem_cons_self
          have silentObject := partsObjects _ List.mem_cons_self
          have continuationTyped := tau_part (sum_guards silentTyped (tau continuation) (by simp))
          have shownTyped := shownMembers _ List.mem_cons_self
          have shownObject := shownObjects _ List.mem_cons_self
          obtain ⟨guards, rfl, guard, guardIn, guardRead⟩ :=
            matched_summand context shownTyped shownObject silentTyped silentObject (guard := tau continuation)
              (by simp) silentAlike
          rw [canonR_tau, recanon_tau] at guardRead
          have guardTyped := sum_guards shownTyped guard guardIn
          obtain ⟨continuation', rfl, continuationRead⟩ := shown_tau guardTyped guardRead
          obtain ⟨before1, after1, split⟩ := List.append_of_mem guardIn
          refine ⟨.silent continuation' before1 after1, ?_, ?_⟩
          · rw [split]
            rfl
          exact .cons (continuation_equivalent context (tau_part guardTyped) continuationTyped continuationRead) .nil

/-! ## The reactions of the π-calculus with sums -/

theorem canonP_recv_ne_nil (channel body : Pattern) : canonP piSumRepBlock (recv channel body) ≠ Prenex.nil := by
  rw [recv, canonP_pair]
  simp [Prenex.atom, Prenex.nil]

theorem canonP_send_ne_nil (channel datum continuation : Pattern) :
    canonP piSumRepBlock (send channel datum continuation) ≠ Prenex.nil := by
  rw [send, canonP_triple]
  simp [Prenex.atom, Prenex.nil]

theorem canonP_tau_ne_nil (continuation : Pattern) : canonP piSumRepBlock (tau continuation) ≠ Prenex.nil := by
  rw [tau, canonP_single "PiTau" continuation (by decide) (by decide) (by decide)]
  simp [Prenex.atom, Prenex.nil]

/-- **A sum with a guard reading as one component is one component**, read canonically as itself. -/
theorem canonP_sum_atom {guards : List Pattern} {guard : Pattern} (member : guard ∈ guards)
    (guardNotNil : canonP piSumRepBlock guard ≠ Prenex.nil) (object : isObjectPattern (sum guards) = true)
    (binds : restrictionsBind piSumBlock (sum guards) = true) :
    canonP piSumRepBlock (sum guards) = Prenex.atom (canonR piSumRepBlock (sum guards)) ∧
      isReplicated piSumRepBlock (canonR piSumRepBlock (sum guards)) = false := by
  have bagNotNil := canonP_bag_ne_nil sumFresh sumRestrictFresh (object_of_sum object) (binds_of_sum binds)
    ⟨guard, member, guardNotNil⟩
  unfold canonR
  rw [sum, canonP_apply (by simp) (by simp) (by simp) (fun argument _ same _ => by
    simp only [List.cons.injEq, and_true] at same
    subst same
    exact bagNotNil)]
  refine ⟨rfl, ?_⟩
  simp only [canonsP, List.zipWith_cons_cons, List.zipWith_nil_right]
  rfl

theorem Redex.atoms (redex : Redex) : ∀ part ∈ redex.parts, isObjectPattern part = true →
    restrictionsBind piSumBlock part = true →
      canonP piSumRepBlock part = Prenex.atom (canonR piSumRepBlock part) ∧
        isReplicated piSumRepBlock (canonR piSumRepBlock part) = false := by
  intro part member object binds
  cases redex with
  | comm channel body datum continuation before after before' after' =>
      simp only [Redex.parts, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact canonP_sum_atom (guard := recv channel body) (by simp) (canonP_recv_ne_nil _ _) object binds
      · exact canonP_sum_atom (guard := send channel datum continuation) (by simp) (canonP_send_ne_nil _ _ _) object
          binds
  | silent continuation before after =>
      simp only [Redex.parts, List.mem_singleton] at member
      subst member
      exact canonP_sum_atom (guard := tau continuation) (by simp) (canonP_tau_ne_nil _) object binds

/-- **A redex reacts in any bag that holds its parts.** -/
theorem Redex.fires {free : FreeTypeContext} {bound : List TypeExpr} (redex : Redex) {components rest : List Pattern}
    (permutation : components.Perm (redex.parts ++ rest))
    (members : Members piSumCalc piSumBlock free bound components) :
    ∃ target, PiSumRawStep (Prenex.body piSumBlock components) target ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) piSumCalc target
        (.collection .hashBag (redex.result ++ rest) none) := by
  have released := redex.result_members fun part member => members part (permutation.mem_iff.mpr
    (List.mem_append_left _ member))
  cases redex with
  | comm channel body datum continuation before after before' after' =>
      simp only [Redex.parts, List.cons_append, List.nil_append] at permutation
      have long : 2 ≤ components.length := by rw [permutation.length_eq]; simp
      obtain ⟨i, hi, j, hj, firstAt, secondAt, restPerm⟩ := indices_of_perm_two permutation
      refine ⟨.collection .hashBag (instantiateBVar datum body :: continuation ::
        (components.eraseIdx i).eraseIdx j) none, ?_, ?_⟩
      · rw [body_of_long long]
        exact .comm i hi j hj before.length (by simp) before'.length (by simp) channel none body datum continuation
          firstAt secondAt (getElem_split _ _ _) (getElem_split _ _ _)
      · have contractumMembers : Members piSumCalc piSumBlock free bound
            (instantiateBVar datum body :: continuation :: (components.eraseIdx i).eraseIdx j) := by
          intro element member
          simp only [List.mem_cons] at member
          rcases member with rfl | rfl | inRest
          · exact released _ (by simp [Redex.result])
          · exact released _ (by simp [Redex.result])
          · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
        exact derivedInstance_equivalent (DerivedInstance.bagPerm_of_sorted
          ⟨free, bound, bag_typed (rest := none) contractumMembers⟩ ((restPerm.cons _).cons _))
  | silent continuation before after =>
      simp only [Redex.parts, List.cons_append, List.nil_append] at permutation
      have continuationTyped := released continuation (by simp [Redex.result])
      cases rest with
      | nil =>
          obtain rfl := List.perm_singleton.mp permutation
          refine ⟨continuation, .tau before.length (by simp) continuation (getElem_split _ _ _), ?_⟩
          exact .symm _ _ (derivedInstance_equivalent (piSumBlockSignature.singleton continuationTyped))
      | cons other others =>
          have long : 2 ≤ components.length := by rw [permutation.length_eq]; simp
          obtain ⟨i, hi, firstAt, restPerm⟩ := index_of_perm_one permutation
          refine ⟨.collection .hashBag (continuation :: components.eraseIdx i) none, ?_, ?_⟩
          · rw [body_of_long long]
            exact .par i hi (by rw [firstAt]; exact .tau before.length (by simp) continuation (getElem_split _ _ _))
          · have contractumMembers : Members piSumCalc piSumBlock free bound
                (continuation :: components.eraseIdx i) := by
              intro element member
              rcases List.mem_cons.mp member with rfl | inRest
              · exact continuationTyped
              · exact members element (List.mem_of_mem_eraseIdx inRest)
            exact derivedInstance_equivalent (DerivedInstance.bagPerm_of_sorted
              ⟨free, bound, bag_typed (rest := none) contractumMembers⟩ (restPerm.cons _))

/-- **The reactions of the π-calculus with sums, with replication**: an input and an output on one channel in two
sums, or a silent summand. -/
abbrev piSumReactions : ReplicationReactions piSumCalc piSumRepBlock PiSumRawStep where
  Redex := Redex
  parts := Redex.parts
  result := Redex.result
  rename := Redex.rename
  parts_rename := Redex.parts_rename
  result_rename := Redex.result_rename
  canonicalAtoms redex part member object binds := (redex.atoms part member object binds).1
  plain redex part member object binds := (redex.atoms part member object binds).2
  arity := 2
  arity_le redex := by cases redex <;> simp [Redex.parts]
  result_members redex members := redex.result_members members
  result_objects := Redex.result_objects
  freeIn_result := Redex.freeIn_result
  alike context redex shown members objects shownMembers shownObjects related :=
    Redex.alike context redex shown members objects shownMembers shownObjects related
  react redex _ _ permutation members _ := redex.fires permutation members
  restrict stepped := .res none stepped

/-- **A step is a reaction of the components of a block**, up to the static theory. -/
theorem step_block {source target : Pattern} (step : PiSumRawStep source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound →
      HasType piSumCalc free bound source (.base "Proc") → isObjectPattern source = true →
        ∃ count redex rest, ReplicationStepAt piSumReactions free bound source target count redex rest := by
  induction step with
  | @comm elements tail i hi j hj guards guards' sumTail sumTail' k hk l hl channel binder body datum continuation
      first second receiving sending =>
      intro free bound _ typed object
      cases bag_tail_none object
      have members := members_of_bag (block := piSumBlock) typed
      have objects := bag_objects object
      have firstObject := objects _ (List.getElem_mem hi)
      have secondObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      have firstTyped := members _ (List.getElem_mem hi)
      rw [first] at firstObject firstTyped
      rw [second] at secondObject
      cases bag_tail_none (kind := .hashBag) (elements := guards) (tail := sumTail)
        (by simpa [isObjectPattern, isObjectPatternList] using firstObject)
      cases bag_tail_none (kind := .hashBag) (elements := guards') (tail := sumTail')
        (by simpa [isObjectPattern, isObjectPatternList] using secondObject)
      have receiverTyped := sum_guards firstTyped _ (List.getElem_mem hk)
      have receiverObject := object_of_sum firstObject _ (List.getElem_mem hk)
      rw [receiving] at receiverTyped receiverObject
      have binderIs : binder = none := by
        have canonical := (metadata_of_typed (block := piSumBlock) _ receiverTyped receiverObject).1 ⟨_, rfl⟩
        simp only [Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList, Bool.and_true,
          Bool.and_eq_true, Option.isNone_iff_eq_none] at canonical
        exact canonical.2.1
      subst binderIs
      let redex : Redex := .comm channel body datum continuation (guards.take k) (guards.drop (k + 1))
        (guards'.take l) (guards'.drop (l + 1))
      have firstIs : elements[i] = sum (guards.take k ++ recv channel body :: guards.drop (k + 1)) := by
        rw [first, sum, recv, ← receiving, ← split_at guards k hk]
      have secondIs : (elements.eraseIdx i)[j] =
          sum (guards'.take l ++ send channel datum continuation :: guards'.drop (l + 1)) := by
        rw [second, sum, send, ← sending, ← split_at guards' l hl]
      have permutation := (perm_getElem_eraseIdx elements i hi).trans
        ((perm_getElem_eraseIdx (elements.eraseIdx i) j hj).cons _)
      rw [firstIs, secondIs] at permutation
      exact ⟨0, redex, (elements.eraseIdx i).eraseIdx j,
        ReactsAt.ofPerm typed members objects permutation (.refl _)⟩
  | @tau guards sumTail k hk continuation silent =>
      intro free bound _ typed object
      cases bag_tail_none (kind := .hashBag) (elements := guards) (tail := sumTail)
        (by simpa [isObjectPattern, isObjectPatternList] using object)
      let redex : Redex := .silent continuation (guards.take k) (guards.drop (k + 1))
      have sumIs : Pattern.apply "PiSum" [.collection .hashBag guards none] =
          sum (guards.take k ++ tau continuation :: guards.drop (k + 1)) := by
        rw [sum, tau, ← silent, ← split_at guards k hk]
      have continuationTyped := tau_part (sum_guards (sumIs ▸ typed) (tau continuation) (by simp))
      exact ⟨0, redex, [], ReactsAt.single (by simp [redex, Redex.parts, sumIs]) typed object
        (.symm _ _ (derivedInstance_equivalent (piSumBlockSignature.singleton continuationTyped)))⟩
  | @par elements tail i hi target inner recurse =>
      intro free bound context typed object
      cases bag_tail_none object
      have members := members_of_bag (block := piSumBlock) typed
      have objects := bag_objects object
      obtain ⟨count, redex, rest, stepBlock⟩ :=
        recurse context (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      exact ⟨count, redex, _, ReactsAt.inBag i hi (piSumReactions.result_members redex) typed objects stepBlock⟩
  | @res binder source target inner recurse =>
      intro free bound context typed object
      cases restriction_binder (block := piSumBlock) typed
      have bodyTyped := (piSumBlockSignature.restriction_typed typed).1
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      obtain ⟨count, redex, rest, stepBlock⟩ := recurse (context.cons "Name") bodyTyped bodyObject
      exact ⟨count + 1, redex, rest, ReactsAt.restrict stepBlock⟩

/-- **A step of a process is matched by a step of an unfolding of its canonical form**, within twice the ceiling read
off that form, to an equivalent contractum. -/
theorem simulation {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {source target : Pattern} (step : PiSumRawStep source target)
    (typed : HasType piSumCalc free bound source (.base "Proc")) (object : isObjectPattern source = true) :
    ∃ unfolded, UnfoldsWithin piSumRepBlock (2 * ceilingOf piSumRepBlock (canonP piSumRepBlock source))
        (canonP piSumRepBlock source) unfolded ∧
      ∃ target', PiSumRawStep (unfolded.toPattern piSumBlock) target' ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) piSumCalc target' target := by
  obtain ⟨count, redex, rest, reached⟩ := step_block step context typed object
  exact replication_simulation piSumReactions context reached typed object

/-- **A step of a process is matched by a step of a presentation of its canonical form**, to an equivalent
contractum: within two unfoldings when every replicated component of the canonical form copies one component. -/
theorem presented {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {source target : Pattern} (step : PiSumRawStep source target)
    (typed : HasType piSumCalc free bound source (.base "Proc")) (object : isObjectPattern source = true) :
    ∃ shown ∈ replicationPresentations piSumRepBlock 2 (canonR piSumRepBlock source), ∃ target',
      PiSumRawStep shown target' ∧ EquationEquiv (engineBasePremises RelationEnv.empty) piSumCalc target' target := by
  obtain ⟨count, redex, rest, reached⟩ := step_block step context typed object
  exact replication_presented piSumReactions context reached typed object

/-- **A step keeps a typed object process a typed object.** -/
theorem typed_of_raw {source target : Pattern} (step : PiSumRawStep source target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, HasType piSumCalc free bound source (.base "Proc") →
      isObjectPattern source = true →
        HasType piSumCalc free bound target (.base "Proc") ∧ isObjectPattern target = true := by
  induction step with
  | @comm elements tail i hi j hj guards guards' sumTail sumTail' k hk l hl channel binder body datum continuation
      first second receiving sending =>
      intro free bound typed object
      have members := members_of_bag (block := piSumBlock) typed
      have objects := bag_objects object
      have firstTyped := members _ (List.getElem_mem hi)
      have secondTyped := members _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      have firstObject := objects _ (List.getElem_mem hi)
      have secondObject := objects _ (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
      rw [first] at firstTyped firstObject
      rw [second] at secondTyped secondObject
      cases bag_tail_none (kind := .hashBag) (elements := guards) (tail := sumTail)
        (by simpa [isObjectPattern, isObjectPatternList] using firstObject)
      cases bag_tail_none (kind := .hashBag) (elements := guards') (tail := sumTail')
        (by simpa [isObjectPattern, isObjectPatternList] using secondObject)
      have receiverTyped := sum_guards firstTyped _ (List.getElem_mem hk)
      have senderTyped := sum_guards secondTyped _ (List.getElem_mem hl)
      have receiverObject := object_of_sum firstObject _ (List.getElem_mem hk)
      have senderObject := object_of_sum secondObject _ (List.getElem_mem hl)
      rw [receiving] at receiverTyped receiverObject
      rw [sending] at senderTyped senderObject
      obtain ⟨-, bodyTyped⟩ := recv_parts receiverTyped
      obtain ⟨-, datumTyped, continuationTyped⟩ := send_parts senderTyped
      simp only [isObjectPattern, isObjectPatternList, Bool.and_true, Bool.and_eq_true] at receiverObject senderObject
      have receivedTyped : HasType piSumCalc free bound (instantiateBVar datum body) (.base "Proc") := by
        rw [← substitute_single_eq_instantiateBVar]
        refine HasType.substituteBoundOnSupport bodyTyped _ fun index type _ lookup => ?_
        cases index with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
            subst lookup
            exact datumTyped
        | succ index => exact HasType.bvar (by simpa using lookup)
      have receivedObject : isObjectPattern (instantiateBVar datum body) = true := by
        rw [← substitute_single_eq_instantiateBVar]
        refine isObject_substitute _ (fun index => ?_) receiverObject.2
        cases index with
        | zero => exact senderObject.2.1
        | succ => rfl
      have contractumMembers : Members piSumCalc piSumBlock free bound
          (instantiateBVar datum body :: continuation :: (elements.eraseIdx i).eraseIdx j) := by
        intro element member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | inRest
        · exact receivedTyped
        · exact continuationTyped
        · exact members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
      refine ⟨bag_typed (rest := none) contractumMembers, ?_⟩
      rw [isObject_bag]
      intro element member
      simp only [List.mem_cons] at member
      rcases member with rfl | rfl | inRest
      · exact receivedObject
      · exact senderObject.2.2
      · exact objects element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest))
  | @tau guards sumTail k hk continuation silent =>
      intro free bound typed object
      cases bag_tail_none (kind := .hashBag) (elements := guards) (tail := sumTail)
        (by simpa [isObjectPattern, isObjectPatternList] using object)
      have guardTyped := sum_guards typed _ (List.getElem_mem hk)
      have guardObject := object_of_sum object _ (List.getElem_mem hk)
      rw [silent] at guardTyped guardObject
      exact ⟨tau_part guardTyped, by simpa [isObjectPattern, isObjectPatternList] using guardObject⟩
  | @par elements tail i hi target inner recurse =>
      intro free bound typed object
      have members := members_of_bag (block := piSumBlock) typed
      have objects := bag_objects object
      obtain ⟨targetTyped, targetObject⟩ :=
        recurse (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      have contractumMembers : Members piSumCalc piSumBlock free bound (target :: elements.eraseIdx i) := by
        intro element member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact targetTyped
        · exact members element (List.mem_of_mem_eraseIdx inRest)
      refine ⟨bag_typed (rest := none) contractumMembers, ?_⟩
      rw [isObject_bag]
      intro element member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact targetObject
      · exact objects element (List.mem_of_mem_eraseIdx inRest)
  | @res binder source target inner recurse =>
      intro free bound typed object
      have bodyTyped := (piSumBlockSignature.restriction_typed typed).1
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      obtain ⟨targetTyped, targetObject⟩ := recurse bodyTyped bodyObject
      exact ⟨restricts_typed (block := piSumBlock) 1 (by simpa [Prenex.restricts] using targetTyped),
        by rw [isObject_restriction]; exact targetObject⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsSteps
