import Mettapedia.GSLT.LanguageDef.ExtensionAlongMorphisms
import Mettapedia.GSLT.LanguageDef.ExtensionConservativity
import Mettapedia.GSLT.LanguageDef.ArithmeticTargetCoproductNTT

/-!
# Controls for layers along morphisms

Two small cores, numerals and booleans, a structural coproduct of them, and
proof calculi over each.  Every hypothesis of the transport, union and
conservativity theorems has a positive and a negative instance here.

* Positive: the numeral and boolean typing calculi glue over the coproduct;
  the union resolves each side's judgments as that side does, and restricted
  to the numeral judgment it is the transported numeral calculus, which is not
  the whole union.
* Renaming is needed: the numeral calculus moved without renaming its
  constructors is rejected over the coproduct.
* Freshness is needed: a calculus whose judgment head is a constructor label of
  the coproduct is admitted over its own core and rejected after transport.
* Compatibility is needed: two calculi that both declare the head `IsNat` have
  no union.
* Renaming unites them: with the boolean namespace prefixed, the union exists.
  A renaming whose rule identifiers collide, one that sends a head onto a
  constructor label, and one that merges two heads are each refused.
* Equal cores: two compatible calculi over one core glue, as the identity case.
* The premise square is needed: two evaluators that disagree on a rule's
  premise give different answers on one term.  The arithmetic target machines
  are a summand with relation-query premises that satisfies the square.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExtensionAlongMorphismsControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.ExtensionGluing
open Mettapedia.GSLT.LanguageDef.StructuralCoproduct
open Mettapedia.GSLT.LanguageDef.SourcePreservingCalculusCoproduct
open Mettapedia.GSLT.LanguageDef.ExtensionAlongMorphisms
open Mettapedia.GSLT.LanguageDef.ExtensionConservativity
open Mettapedia.Logic.Relation.ObservationTransport

/-! ## Two cores and their coproduct -/

private def tag (prefixText source : String) : String := prefixText ++ source

private theorem tag_injective (prefixText : String) :
    Function.Injective (tag prefixText) := by
  intro left right equality
  apply String.toList_inj.mp
  have listEquality := congrArg String.toList equality
  simp only [tag, String.toList_append] at listEquality
  exact (List.append_right_inj prefixText.toList).mp listEquality

private theorem nat_bool_disjoint :
    ∀ natName boolName, tag "N:" natName ≠ tag "B:" boolName := by
  intro natName boolName equality
  have listEquality := congrArg String.toList equality
  simp [tag] at listEquality

/-- Tag every numeral symbol with `N:`. -/
def natSymbols : LanguageDefSymbolMap where
  sort := tag "N:"
  constructor := tag "N:"
  relation := tag "N:"
  equation := tag "N:"
  rewrite := tag "N:"

/-- Tag every boolean symbol with `B:`. -/
def boolSymbols : LanguageDefSymbolMap where
  sort := tag "B:"
  constructor := tag "B:"
  relation := tag "B:"
  equation := tag "B:"
  rewrite := tag "B:"

/-- Numerals: `zero` and `succ`. -/
def natCore : LanguageDef where
  name := "numerals"
  types := [TypeDecl.plain "Nat"]
  terms :=
    [{ label := "zero", category := "Nat", params := [], syntaxPattern := [] },
     { label := "succ", category := "Nat", params := [.simple "n" (.base "Nat")],
       syntaxPattern := [] }]
  equations := []
  rewrites := []

/-- Booleans: `tt` and `ff`. -/
def boolCore : LanguageDef where
  name := "booleans"
  types := [TypeDecl.plain "Bool"]
  terms :=
    [{ label := "tt", category := "Bool", params := [], syntaxPattern := [] },
     { label := "ff", category := "Bool", params := [], syntaxPattern := [] }]
  equations := []
  rewrites := []

theorem natCore_validate : natCore.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;> decide

theorem boolCore_validate : boolCore.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;> decide

def natValidated : ValidatedLanguageDef := ⟨natCore, natCore_validate⟩

def boolValidated : ValidatedLanguageDef := ⟨boolCore, boolCore_validate⟩

theorem natBool_validate :
    (rawCoproduct "NatBool" natSymbols boolSymbols natCore boolCore).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    (unfold rawCoproduct renameLanguage natSymbols boolSymbols tag natCore boolCore
     decide +kernel)

/-- The structural coproduct of numerals and booleans. -/
theorem natBool : Compatibility "NatBool" natSymbols boolSymbols natValidated boolValidated where
  leftSymbolsInjective :=
    { sort := tag_injective _, constructor := tag_injective _, relation := tag_injective _,
      equation := tag_injective _, rewrite := tag_injective _ }
  rightSymbolsInjective :=
    { sort := tag_injective _, constructor := tag_injective _, relation := tag_injective _,
      equation := tag_injective _, rewrite := tag_injective _ }
  symbolImagesDisjoint :=
    { sort := nat_bool_disjoint, constructor := nat_bool_disjoint,
      relation := nat_bool_disjoint, equation := nat_bool_disjoint,
      rewrite := nat_bool_disjoint }
  leftRewritesRooted := by intro rewrite member; cases member
  rightRewritesRooted := by intro rewrite member; cases member
  typeNamesNodup := LanguageDef.typeNames_nodup_of_validate_eq_nil _ natBool_validate
  constructorNamesNodup :=
    LanguageDef.constructorLabels_nodup_of_validate_eq_nil _ natBool_validate
  equationNamesNodup := LanguageDef.equationNames_nodup_of_validate_eq_nil _ natBool_validate
  rewriteNamesNodup := LanguageDef.rewriteNames_nodup_of_validate_eq_nil _ natBool_validate
  leftTermsStable := by
    intro term member
    apply LanguageDef.validateTerm_eq_nil_of_validate_eq_nil _ natBool_validate
    exact List.mem_append_left _ (List.mem_map.mpr ⟨term, member, rfl⟩)
  rightTermsStable := by
    intro term member
    apply LanguageDef.validateTerm_eq_nil_of_validate_eq_nil _ natBool_validate
    exact List.mem_append_right _ (List.mem_map.mpr ⟨term, member, rfl⟩)
  leftEquationsStable := by intro equation member; cases member
  rightEquationsStable := by intro equation member; cases member
  leftRewritesStable := by intro rewrite member; cases member
  rightRewritesStable := by intro rewrite member; cases member

/-! ## Two typing calculi -/

/-- The numeral typing calculus: `IsNat(zero)` and `IsNat(n) ⊢ IsNat(succ n)`. -/
def natCalculus : ProofCalculus where
  judgments := [{ head := "IsNat", arity := 1 }]
  rules :=
    [{ id := ⟨"zeroNat"⟩, metavariables := [], premises := [],
       conclusion := .apply "IsNat" [.apply "zero" []] },
     { id := ⟨"succNat"⟩, metavariables := [("n", 0)],
       premises := [.apply "IsNat" [.fvar "n"]],
       conclusion := .apply "IsNat" [.apply "succ" [.fvar "n"]] }]

/-- The boolean typing calculus: `IsBool(tt)` and `IsBool(ff)`. -/
def boolCalculus : ProofCalculus where
  judgments := [{ head := "IsBool", arity := 1 }]
  rules :=
    [{ id := ⟨"ttBool"⟩, metavariables := [], premises := [],
       conclusion := .apply "IsBool" [.apply "tt" []] },
     { id := ⟨"ffBool"⟩, metavariables := [], premises := [],
       conclusion := .apply "IsBool" [.apply "ff" []] }]

theorem natCalculus_admitted :
    (CalculusLanguageDef.extend natCore natCalculus).isValid = true := by
  decide +kernel

theorem boolCalculus_admitted :
    (CalculusLanguageDef.extend boolCore boolCalculus).isValid = true := by
  decide +kernel

/-! ## Positive: the union over the coproduct -/

theorem natBool_conditions : UnionConditions natBool natCalculus boolCalculus where
  leftAdmitted := natCalculus_admitted
  rightAdmitted := boolCalculus_admitted
  leftFresh := by
    unfold HeadsFresh
    unfold Compatibility.combinedLanguage rawCoproduct renameLanguage natSymbols boolSymbols
      tag natValidated boolValidated natCore boolCore natCalculus
    decide +kernel
  rightFresh := by
    unfold HeadsFresh
    unfold Compatibility.combinedLanguage rawCoproduct renameLanguage natSymbols boolSymbols
      tag natValidated boolValidated natCore boolCore boolCalculus
    decide +kernel
  compatible := ⟨by decide +kernel, by decide +kernel, Or.inl rfl⟩

/-- **The numeral and boolean typing calculi glue over the coproduct.**  The
union contains the numeral rules with renamed constructors before the boolean
rules with renamed constructors. -/
theorem natBoolUnion_rules :
    (coproductUnion natBool_conditions).1.rules =
      [{ id := ⟨"zeroNat"⟩, metavariables := [], premises := [],
         conclusion := .apply "IsNat" [.apply "N:zero" []] },
       { id := ⟨"succNat"⟩, metavariables := [("n", 0)],
         premises := [.apply "IsNat" [.fvar "n"]],
         conclusion := .apply "IsNat" [.apply "N:succ" [.fvar "n"]] },
       { id := ⟨"ttBool"⟩, metavariables := [], premises := [],
         conclusion := .apply "IsBool" [.apply "B:tt" []] },
       { id := ⟨"ffBool"⟩, metavariables := [], premises := [],
         conclusion := .apply "IsBool" [.apply "B:ff" []] }] := by
  decide +kernel

/-- The union resolves the numeral judgment exactly as the numeral core does. -/
theorem natBoolUnion_resolves_IsNat :
    (coproductUnion natBool_conditions).1.lookupJudgment? "IsNat" 1 =
      some { head := "IsNat", arity := 1 } := by
  rw [coproductUnion_lookupJudgment_left natBool_conditions 1 (by decide)]
  decide

/-- Restricted to the numeral judgment, the union is the numeral calculus with
renamed constructors, and the boolean rows are not in it. -/
theorem natBoolUnion_restricts_to_nat :
    restrictToHeads ["IsNat"] (unionCalculus natSymbols boolSymbols natCalculus boolCalculus) =
        reindexProofCalculus (coreSymbols natSymbols) natCalculus ∧
      restrictToHeads ["IsNat"] (unionCalculus natSymbols boolSymbols natCalculus boolCalculus) ≠
        unionCalculus natSymbols boolSymbols natCalculus boolCalculus :=
  ⟨coproductUnion_restrict_left natBool_conditions, by decide +kernel⟩

/-- A raw proof of `IsNat(succ zero)` in the union's names. -/
def succZeroProof : InferenceChecker.RawProof :=
  .node ⟨⟨"succNat"⟩, [.apply "N:zero" []]⟩ [.node ⟨⟨"zeroNat"⟩, []⟩ []]

/-- **Positive: a left judgment is checked by the union as by the left side.** -/
theorem union_checks_succZero :
    InferenceChecker.checkRaw (coproductUnion natBool_conditions)
        (.apply "IsNat" [.apply "N:succ" [.apply "N:zero" []]]) succZeroProof = true ∧
      InferenceChecker.checkRaw (coproductLeftPart natBool_conditions)
        (.apply "IsNat" [.apply "N:succ" [.apply "N:zero" []]]) succZeroProof = true := by
  constructor <;> decide +kernel

/-- **Negative: the judgment shape is needed.**  A boolean judgment is checked by
the union and rejected by the left side alone, so derivation conservativity
holds only on goals shaped by the side's own judgments. -/
theorem union_checks_bool_left_rejects :
    InferenceChecker.checkRaw (coproductUnion natBool_conditions)
        (.apply "IsBool" [.apply "B:tt" []]) (.node ⟨⟨"ttBool"⟩, []⟩ []) = true ∧
      InferenceChecker.checkRaw (coproductLeftPart natBool_conditions)
        (.apply "IsBool" [.apply "B:tt" []]) (.node ⟨⟨"ttBool"⟩, []⟩ []) = false := by
  constructor <;> decide +kernel

/-! ## Negative: renaming is needed -/

/-- Moving the numeral calculus onto the coproduct without renaming its
constructors leaves `zero` and `succ` undeclared there. -/
theorem untransported_not_admitted :
    (CalculusLanguageDef.extend natBool.combinedLanguage.language natCalculus).isValid =
      false := by
  unfold Compatibility.combinedLanguage rawCoproduct renameLanguage natSymbols boolSymbols
    tag natValidated boolValidated natCore boolCore
  decide +kernel

/-! ## Negative: freshness is needed -/

/-- A numeral calculus whose judgment head happens to be the boolean
constructor label of the coproduct. -/
def collidingCalculus : ProofCalculus where
  judgments := [{ head := "B:tt", arity := 0 }]

theorem collidingCalculus_admitted :
    (CalculusLanguageDef.extend natCore collidingCalculus).isValid = true := by
  decide +kernel

theorem collidingCalculus_not_fresh :
    ¬ HeadsFresh natBool.combinedLanguage.language collidingCalculus := by
  intro fresh
  exact fresh { head := "B:tt", arity := 0 } (List.mem_singleton_self _)
    { label := "B:tt", category := "B:Bool", params := [], syntaxPattern := [] }
    (by
      unfold Compatibility.combinedLanguage rawCoproduct renameLanguage natSymbols
        boolSymbols tag natValidated boolValidated natCore boolCore
      decide +kernel)
    rfl

/-- **The collision is refused after transport**, although the calculus is
admitted over its own core. -/
theorem collidingCalculus_transport_refused :
    (CalculusLanguageDef.extend natBool.combinedLanguage.language
        (reindexProofCalculus (coreSymbols natSymbols) collidingCalculus)).isValid ≠ true :=
  fun admitted =>
    collidingCalculus_not_fresh
      ((admitted_reindex_iff natBool.leftInclusion.toTyping collidingCalculus_admitted).mp
        admitted)

/-! ## Negative: incompatible calculi are refused -/

/-- A boolean typing calculus that reuses the judgment head `IsNat`. -/
def boolCalculusSameHead : ProofCalculus where
  judgments := [{ head := "IsNat", arity := 1 }]
  rules :=
    [{ id := ⟨"ttBool"⟩, metavariables := [], premises := [],
       conclusion := .apply "IsNat" [.apply "tt" []] }]

theorem boolCalculusSameHead_admitted :
    (CalculusLanguageDef.extend boolCore boolCalculusSameHead).isValid = true := by
  decide +kernel

/-- **Two calculi sharing a judgment head have no union**, although each is
admitted over its core and both heads are fresh in the coproduct. -/
theorem sameHead_union_refused :
    ¬ ∃ merged,
      proofCalculusMonoid.op
          (reindexProofCalculus (coreSymbols natBool.leftInclusion.toTyping.symbols)
            natCalculus)
          (reindexProofCalculus (coreSymbols natBool.rightInclusion.toTyping.symbols)
            boolCalculusSameHead) = some merged ∧
        (CalculusLanguageDef.extend natBool.combinedLanguage.language merged).isValid =
          true := by
  rw [union_admitted_iff natBool.leftInclusion.toTyping natBool.rightInclusion.toTyping
    natCalculus_admitted boolCalculusSameHead_admitted natBool_conditions.leftFresh
    (by
      unfold HeadsFresh
      unfold Compatibility.combinedLanguage rawCoproduct renameLanguage natSymbols
        boolSymbols tag natValidated boolValidated natCore boolCore boolCalculusSameHead
      decide +kernel)]
  intro compatible
  exact compatible.judgmentHeads "IsNat" (by decide) (by decide)

/-! ## The identity case -/

/-- A second calculus over the numerals: parity. -/
def parityCalculus : ProofCalculus where
  judgments := [{ head := "Even", arity := 1 }]
  rules :=
    [{ id := ⟨"zeroEven"⟩, metavariables := [], premises := [],
       conclusion := .apply "Even" [.apply "zero" []] }]

theorem parityCalculus_admitted :
    (CalculusLanguageDef.extend natCore parityCalculus).isValid = true := by
  decide +kernel

/-- **Over one core the union is the equal-core gluing.** -/
theorem natParity_glue :
    ∃ merged, proofCalculusMonoid.op natCalculus parityCalculus = some merged ∧
      (CalculusLanguageDef.extend natCore merged).isValid = true :=
  (equalCore_union_iff natValidated natCalculus_admitted parityCalculus_admitted).mpr
    ⟨by decide +kernel, by decide +kernel, Or.inl rfl⟩

/-! ## Namespaces: a clash united after renaming -/

/-- Prefix the boolean side's judgment heads and rule identifiers. -/
def boolPrefix : NamespaceMap := ⟨fun head => "B." ++ head, fun id => "B." ++ id⟩

/-- The numeral side keeps its names, legally. -/
theorem natNames_legal : NamesValid natBool.combinedLanguage.language 1 natCalculus :=
  (namesValid_one_iff natCalculus_admitted).mpr natBool_conditions.leftFresh

/-- **Positive: the prefix is a legal renaming** of the boolean calculus that
declares `IsNat`. -/
theorem boolPrefix_legal :
    NamesValid natBool.combinedLanguage.language boolPrefix boolCalculusSameHead where
  headsApart := by decide
  idsApart := by decide
  idsNonempty := by decide
  headsLegal := by decide
  fresh := by
    unfold HeadsFresh
    unfold Compatibility.combinedLanguage rawCoproduct renameLanguage natSymbols boolSymbols
      tag natValidated boolValidated natCore boolCore boolCalculusSameHead boolPrefix
    decide +kernel

/-- **Renamed, the clash unites.**  As it stands, the boolean calculus that
declares `IsNat` has no union with the numeral calculus
(`sameHead_union_refused`).  With its namespace prefixed, the union over the
coproduct exists and is admitted. -/
theorem clash_united_after_renaming :
    ∃ merged,
      proofCalculusMonoid.op
          (reindexProofCalculus (layerSymbols natBool.leftInclusion.toTyping.symbols 1)
            natCalculus)
          (reindexProofCalculus (layerSymbols natBool.rightInclusion.toTyping.symbols boolPrefix)
            boolCalculusSameHead) = some merged ∧
        (CalculusLanguageDef.extend natBool.combinedLanguage.language merged).isValid =
          true :=
  (union_layer_admitted_iff natBool.leftInclusion.toTyping natBool.rightInclusion.toTyping 1
    boolPrefix natCalculus_admitted boolCalculusSameHead_admitted natNames_legal
    boolPrefix_legal).mpr ⟨by decide +kernel, by decide +kernel, Or.inl rfl⟩

/-- **Rename, then unite.**  After the renaming over its own core, the renamed
boolean calculus and the numeral calculus meet the union conditions over the
coproduct, so the whole coproduct package applies to them. -/
theorem renamedBool_conditions :
    UnionConditions natBool natCalculus
      (reindexProofCalculus (namespaceSymbols boolPrefix) boolCalculusSameHead) where
  leftAdmitted := natCalculus_admitted
  rightAdmitted := (admitted_rename_iff (core := boolValidated) boolPrefix
    boolCalculusSameHead_admitted).mpr
      ⟨by decide, by decide, by decide, by decide, by
        unfold HeadsFresh
        unfold boolValidated boolCore boolCalculusSameHead boolPrefix
        decide +kernel⟩
  leftFresh := natBool_conditions.leftFresh
  rightFresh := boolPrefix_legal.fresh
  compatible := ⟨by decide +kernel, by decide +kernel, Or.inl rfl⟩

/-- Restricted to the renamed boolean judgment, the union is the boolean
calculus moved along its renaming and the right injection together: the layer
morphism of the pair. -/
theorem renamedUnion_restricts_to_bool :
    restrictToHeads
        ((reindexProofCalculus (namespaceSymbols boolPrefix) boolCalculusSameHead).judgments.map
          JudgmentDecl.head)
        (unionCalculus natSymbols boolSymbols natCalculus
          (reindexProofCalculus (namespaceSymbols boolPrefix) boolCalculusSameHead)) =
      reindexProofCalculus (layerSymbols boolSymbols boolPrefix) boolCalculusSameHead := by
  rw [layerSymbols_eq_rename_comp, reindexProofCalculus_comp]
  exact coproductUnion_restrict_right renamedBool_conditions

/-- A renaming that prefixes the head but sends the rule identifier onto the
numeral calculus' `zeroNat`. -/
def collidingIds : NamespaceMap := ⟨fun head => "B." ++ head, fun _ => "zeroNat"⟩

theorem collidingIds_legal :
    NamesValid natBool.combinedLanguage.language collidingIds boolCalculusSameHead where
  headsApart := by decide
  idsApart := by decide
  idsNonempty := by decide
  headsLegal := by decide
  fresh := by
    unfold HeadsFresh
    unfold Compatibility.combinedLanguage rawCoproduct renameLanguage natSymbols boolSymbols
      tag natValidated boolValidated natCore boolCore boolCalculusSameHead collidingIds
    decide +kernel

/-- **Negative: a renaming whose rule identifiers collide is refused.**  The
renaming is legal on its own side, but the union has two rules named
`zeroNat`. -/
theorem colliding_ids_refused :
    ¬ ∃ merged,
      proofCalculusMonoid.op
          (reindexProofCalculus (layerSymbols natBool.leftInclusion.toTyping.symbols 1)
            natCalculus)
          (reindexProofCalculus (layerSymbols natBool.rightInclusion.toTyping.symbols
            collidingIds) boolCalculusSameHead) = some merged ∧
        (CalculusLanguageDef.extend natBool.combinedLanguage.language merged).isValid =
          true := by
  rw [union_layer_admitted_iff natBool.leftInclusion.toTyping natBool.rightInclusion.toTyping 1
    collidingIds natCalculus_admitted boolCalculusSameHead_admitted natNames_legal
    collidingIds_legal]
  intro compatible
  exact compatible.ruleIds ⟨"zeroNat"⟩ (by decide) (by decide)

/-- A renaming that sends the boolean head onto the constructor label `B:tt`
of the coproduct. -/
def ontoConstructor : NamespaceMap := ⟨fun _ => "B:tt", _root_.id⟩

/-- **Negative: a renaming onto a constructor label is refused** by
admission over the coproduct. -/
theorem onto_constructor_refused :
    (CalculusLanguageDef.extend natBool.combinedLanguage.language
        (reindexProofCalculus (layerSymbols natBool.rightInclusion.toTyping.symbols
          ontoConstructor) boolCalculusSameHead)).isValid ≠ true := fun admitted =>
  ((admitted_layer_iff natBool.rightInclusion.toTyping ontoConstructor
    boolCalculusSameHead_admitted).mp admitted).fresh { head := "B:tt", arity := 1 }
    (List.mem_singleton_self _)
    { label := "B:tt", category := "B:Bool", params := [], syntaxPattern := [] }
    (by
      unfold Compatibility.combinedLanguage rawCoproduct renameLanguage natSymbols
        boolSymbols tag natValidated boolValidated natCore boolCore
      decide +kernel)
    rfl

/-- A renaming that sends every judgment head to one head. -/
def mergeHeads : NamespaceMap := ⟨fun _ => "Same", _root_.id⟩

/-- The numeral and parity calculi glued over the numerals. -/
def natParityCalculus : ProofCalculus := mergeOf natCalculus parityCalculus

theorem natParityCalculus_admitted :
    (CalculusLanguageDef.extend natCore natParityCalculus).isValid = true := by
  decide +kernel

/-- **Negative: a renaming that merges two heads of one calculus is refused**,
already over its own core. -/
theorem merging_renaming_refused :
    (CalculusLanguageDef.extend natCore
        (reindexProofCalculus (namespaceSymbols mergeHeads) natParityCalculus)).isValid ≠
      true := fun admitted =>
  absurd
    (((admitted_rename_iff (core := natValidated) mergeHeads natParityCalculus_admitted).mp
      admitted).headsApart "IsNat" (by decide) "Even" (by decide) rfl)
    (by decide)

/-! ## The premise square -/

/-- A core with one rule `a ↦ b` guarded by a relation-query premise. -/
def gateCore : LanguageDef where
  name := "gate"
  types := [TypeDecl.plain "S"]
  terms :=
    [{ label := "a", category := "S", params := [], syntaxPattern := [] },
     { label := "b", category := "S", params := [], syntaxPattern := [] }]
  equations := []
  rewrites :=
    [{ name := "gate"
       typeContext := []
       premises := [.relationQuery "open" []]
       left := .apply "a" []
       right := .apply "b" [] }]

/-- An evaluator under which every premise holds. -/
def everyPremiseHolds : BasePremiseEvaluator := fun _ bindings _ => [bindings]

/-- An evaluator under which no premise holds. -/
def noPremiseHolds : BasePremiseEvaluator := fun _ _ _ => []

theorem gate_open :
    rewriteAt everyPremiseHolds gateCore 1 (.apply "a" []) = [.apply "b" []] := by
  decide +kernel

theorem gate_closed : rewriteAt noPremiseHolds gateCore 1 (.apply "a" []) = [] := by
  decide +kernel

/-- **The premise square is load-bearing.**  Two evaluators that disagree on
the rule's premise violate the square even along the identity symbol map, and
the may-observation "some answer is `b`" holds under one and fails under the
other. -/
theorem premise_square_needed :
    ¬ StructuralCoproductOperational.RulePremiseEvaluatorsCommute LanguageDefSymbolMap.id
        gateCore gateCore everyPremiseHolds noPremiseHolds ∧
      May (answerStep everyPremiseHolds gateCore 1) (fun next => next = .apply "b" [])
        (.apply "a" []) ∧
      ¬ May (answerStep noPremiseHolds gateCore 1) (fun next => next = .apply "b" [])
        (.apply "a" []) := by
  refine ⟨?_, ⟨.apply "b" [], by rw [answerStep, gate_open]; simp, rfl⟩, ?_⟩
  · intro commutes
    have square := commutes _ (List.mem_singleton_self _) _ (List.mem_singleton_self _) []
    simp [everyPremiseHolds, noPremiseHolds] at square
  · rintro ⟨next, stepped, _⟩
    rw [answerStep, gate_closed] at stepped
    cases stepped

/-- **A summand with relation-query premises that satisfies the square**: the
external-call machine in the coproduct of the arithmetic target machines. -/
noncomputable def externalSummand :
    LeftSummand (engineBasePremises ExternalCallMachine.externalCallDemoRelationEnv)
      ArithmeticTargetCoproduct.externalValidated where
  name := "ArithmeticTargetMachines"
  leftSymbols := ArithmeticTargetCoproduct.externalSymbols
  rightSymbols := ArithmeticTargetCoproduct.radixSymbols
  right := ArithmeticTargetCoproduct.radixValidated
  coproduct := ArithmeticTargetCoproduct.compatibility
  targetBase := ArithmeticTargetCoproductNTT.combinedOperationalBase
  commutes := ArithmeticTargetCoproductNTT.external_rule_premises_commute

#print axioms natBool
#print axioms natBoolUnion_rules
#print axioms natBoolUnion_restricts_to_nat
#print axioms union_checks_succZero
#print axioms union_checks_bool_left_rejects
#print axioms untransported_not_admitted
#print axioms collidingCalculus_transport_refused
#print axioms sameHead_union_refused
#print axioms clash_united_after_renaming
#print axioms renamedUnion_restricts_to_bool
#print axioms colliding_ids_refused
#print axioms onto_constructor_refused
#print axioms merging_renaming_refused
#print axioms natParity_glue
#print axioms premise_square_needed
#print axioms externalSummand

end Mettapedia.GSLT.LanguageDef.ExtensionAlongMorphismsControls
