import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingAgreement
import Mettapedia.GSLT.LanguageDef.TptpFofSkolemTermAgreement

/-!
# Semantic agreement of authored definitional naming

Typed Skolem FOF matrices induce executions of the authored linear naming
LanguageDef.  This module identifies the operational root, frontier, and both
ledgers with the independent postorder naming semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingSemanticAgreement

open LO FirstOrder
open scoped LO.FirstOrder
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingSemantics

namespace Operational

open Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingLanguageDef
open Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingAgreement

def encodeDefinitionPatterns : List Pattern → Pattern
  | [] => TptpFofDefinitionalCnfLanguageDef.definitionsNil
  | head :: tail =>
      TptpFofDefinitionalCnfLanguageDef.definitionsCons head
        (encodeDefinitionPatterns tail)

def encodeIntroducedPatterns : List Pattern → Pattern
  | [] => TptpFofDefinitionalCnfLanguageDef.introducedNil
  | head :: tail =>
      TptpFofDefinitionalCnfLanguageDef.introducedCons head
        (encodeIntroducedPatterns tail)

def variableTerms : Nat → Nat → Pattern
  | 0, _ => TptpFofSkolemLanguageDef.termsNil
  | remaining + 1, next =>
      TptpFofSkolemLanguageDef.termsCons
        (TptpFofSkolemLanguageDef.termVariable
          (TptpResolvedFofLanguageDef.encodeNatIndex next))
        (variableTerms remaining (next + 1))

@[simp] theorem encodeNatIndex_zero :
    TptpResolvedFofLanguageDef.encodeNatIndex 0 = indexZero := rfl

@[simp] theorem encodeNatIndex_succ (index : Nat) :
    TptpResolvedFofLanguageDef.encodeNatIndex (index + 1) =
      indexSucc (TptpResolvedFofLanguageDef.encodeNatIndex index) := rfl

@[simp] theorem naming_indexSucc_eq_skolem (index : Pattern) :
    TptpFofDefinitionalNamingLanguageDef.indexSucc index =
      TptpFofSkolemTermLanguageDef.indexSucc index := rfl

@[simp] theorem naming_indexZero_eq_skolem :
    TptpFofDefinitionalNamingLanguageDef.indexZero =
      TptpFofSkolemTermLanguageDef.indexZero := rfl

def variablesDerivation : (remaining next : Nat) →
    Derivation
      (variablesRequest
        (TptpResolvedFofLanguageDef.encodeNatIndex remaining)
        (TptpResolvedFofLanguageDef.encodeNatIndex next))
      (variablesResult
        (TptpResolvedFofLanguageDef.encodeNatIndex remaining)
        (TptpResolvedFofLanguageDef.encodeNatIndex next)
        (variableTerms remaining next))
  | 0, next => by
      simpa [variableTerms, encodeNatIndex_zero] using
        Derivation.variablesZero
          (TptpResolvedFofLanguageDef.encodeNatIndex next)
  | remaining + 1, next => by
      simpa [variableTerms, encodeNatIndex_succ] using
        Derivation.variablesSucc (variablesDerivation remaining (next + 1))

structure NamePatternOutput where
  root : Pattern
  next : Nat
  reverseDefinitions : List Pattern
  reverseIntroduced : List Pattern

noncomputable def namePattern {depth : Nat} :
    (source : Source.Formula depth) → QuantifierFree source → Nat →
    List Pattern → List Pattern → NamePatternOutput
  | .verum, _, frontier, definitions, introduced =>
      ⟨TptpFofDefinitionalCnfLanguageDef.refVerum, frontier,
        definitions, introduced⟩
  | .falsum, _, frontier, definitions, introduced =>
      ⟨TptpFofDefinitionalCnfLanguageDef.refFalsum, frontier,
        definitions, introduced⟩
  | .rel (.predicate predicate) arguments, _, frontier, definitions,
      introduced =>
      ⟨TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
          (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
          (TptpFofSkolemLanguageDef.encodeTerms (List.ofFn arguments)),
        frontier, definitions, introduced⟩
  | .rel .equality arguments, _, frontier, definitions, introduced =>
      ⟨TptpFofDefinitionalCnfLanguageDef.refEqual
          (TptpFofSkolemLanguageDef.encodeTerm (arguments 0))
          (TptpFofSkolemLanguageDef.encodeTerm (arguments 1)),
        frontier, definitions, introduced⟩
  | .nrel (.predicate predicate) arguments, _, frontier, definitions,
      introduced =>
      ⟨TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
          (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
          (TptpFofSkolemLanguageDef.encodeTerms (List.ofFn arguments)),
        frontier, definitions, introduced⟩
  | .nrel .equality arguments, _, frontier, definitions, introduced =>
      ⟨TptpFofDefinitionalCnfLanguageDef.refNotEqual
          (TptpFofSkolemLanguageDef.encodeTerm (arguments 0))
          (TptpFofSkolemLanguageDef.encodeTerm (arguments 1)),
        frontier, definitions, introduced⟩
  | .and left right, quantifierFree, frontier, definitions, introduced =>
      let leftOutput := namePattern left quantifierFree.1 frontier
        definitions introduced
      let rightOutput := namePattern right quantifierFree.2 leftOutput.next
        leftOutput.reverseDefinitions leftOutput.reverseIntroduced
      let id := TptpResolvedFofLanguageDef.encodeNatIndex rightOutput.next
      let source := TptpFofSkolemLanguageDef.and
        (TptpFofSkolemLanguageDef.encodeFormula left
          quantifierFree.1.existentialFree)
        (TptpFofSkolemLanguageDef.encodeFormula right
          quantifierFree.2.existentialFree)
      { root := TptpFofDefinitionalCnfLanguageDef.refDefinedPositive id
          (variableTerms depth 0)
        next := rightOutput.next + 1
        reverseDefinitions :=
          TptpFofDefinitionalCnfLanguageDef.definitionAnd id source
            leftOutput.root rightOutput.root :: rightOutput.reverseDefinitions
        reverseIntroduced :=
          TptpFofDefinitionalCnfLanguageDef.introducedPredicate id
            (TptpResolvedFofLanguageDef.encodeNatIndex depth) ::
            rightOutput.reverseIntroduced }
  | .or left right, quantifierFree, frontier, definitions, introduced =>
      let leftOutput := namePattern left quantifierFree.1 frontier
        definitions introduced
      let rightOutput := namePattern right quantifierFree.2 leftOutput.next
        leftOutput.reverseDefinitions leftOutput.reverseIntroduced
      let id := TptpResolvedFofLanguageDef.encodeNatIndex rightOutput.next
      let source := TptpFofSkolemLanguageDef.or
        (TptpFofSkolemLanguageDef.encodeFormula left
          quantifierFree.1.existentialFree)
        (TptpFofSkolemLanguageDef.encodeFormula right
          quantifierFree.2.existentialFree)
      { root := TptpFofDefinitionalCnfLanguageDef.refDefinedPositive id
          (variableTerms depth 0)
        next := rightOutput.next + 1
        reverseDefinitions :=
          TptpFofDefinitionalCnfLanguageDef.definitionOr id source
            leftOutput.root rightOutput.root :: rightOutput.reverseDefinitions
        reverseIntroduced :=
          TptpFofDefinitionalCnfLanguageDef.introducedPredicate id
            (TptpResolvedFofLanguageDef.encodeNatIndex depth) ::
            rightOutput.reverseIntroduced }
  | .all _, impossible, _, _, _ => False.elim impossible
  | .ex _, impossible, _, _, _ => False.elim impossible
termination_by source => sizeOf source

noncomputable def nameDerivation {depth : Nat} :
    (source : Source.Formula depth) → (quantifierFree : QuantifierFree source) →
    (frontier : Nat) → (definitions introduced : List Pattern) →
    let output := namePattern source quantifierFree frontier definitions introduced
    Derivation
      (nameRequest
        (TptpResolvedFofLanguageDef.encodeNatIndex depth)
        (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
        (TptpFofSkolemLanguageDef.encodeFormula source
          quantifierFree.existentialFree)
        (encodeDefinitionPatterns definitions)
        (encodeIntroducedPatterns introduced))
      (nameResult
        (TptpResolvedFofLanguageDef.encodeNatIndex depth)
        (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
        (TptpFofSkolemLanguageDef.encodeFormula source
          quantifierFree.existentialFree)
        output.root
        (TptpResolvedFofLanguageDef.encodeNatIndex output.next)
        (encodeDefinitionPatterns output.reverseDefinitions)
        (encodeIntroducedPatterns output.reverseIntroduced))
  | .verum, _, frontier, definitions, introduced => by
      simpa [namePattern, encodeDefinitionPatterns,
        encodeIntroducedPatterns, TptpFofSkolemLanguageDef.encodeFormula] using
        Derivation.nameVerum
          (TptpResolvedFofLanguageDef.encodeNatIndex depth)
          (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
          (encodeDefinitionPatterns definitions)
          (encodeIntroducedPatterns introduced)
  | .falsum, _, frontier, definitions, introduced => by
      simpa [namePattern, encodeDefinitionPatterns,
        encodeIntroducedPatterns, TptpFofSkolemLanguageDef.encodeFormula] using
        Derivation.nameFalsum
          (TptpResolvedFofLanguageDef.encodeNatIndex depth)
          (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
          (encodeDefinitionPatterns definitions)
          (encodeIntroducedPatterns introduced)
  | .rel (.predicate predicate) arguments, _, frontier, definitions,
      introduced => by
      simpa [namePattern, TptpFofSkolemLanguageDef.encodeFormula] using
        Derivation.namePositive
          (TptpResolvedFofLanguageDef.encodeNatIndex depth)
          (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
          (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
          (TptpFofSkolemLanguageDef.encodeTerms (List.ofFn arguments))
          (encodeDefinitionPatterns definitions)
          (encodeIntroducedPatterns introduced)
  | .rel .equality arguments, _, frontier, definitions, introduced => by
      simpa [namePattern, TptpFofSkolemLanguageDef.encodeFormula] using
        Derivation.nameEqual
          (TptpResolvedFofLanguageDef.encodeNatIndex depth)
          (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
          (TptpFofSkolemLanguageDef.encodeTerm (arguments 0))
          (TptpFofSkolemLanguageDef.encodeTerm (arguments 1))
          (encodeDefinitionPatterns definitions)
          (encodeIntroducedPatterns introduced)
  | .nrel (.predicate predicate) arguments, _, frontier, definitions,
      introduced => by
      simpa [namePattern, TptpFofSkolemLanguageDef.encodeFormula] using
        Derivation.nameNegative
          (TptpResolvedFofLanguageDef.encodeNatIndex depth)
          (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
          (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
          (TptpFofSkolemLanguageDef.encodeTerms (List.ofFn arguments))
          (encodeDefinitionPatterns definitions)
          (encodeIntroducedPatterns introduced)
  | .nrel .equality arguments, _, frontier, definitions, introduced => by
      simpa [namePattern, TptpFofSkolemLanguageDef.encodeFormula] using
        Derivation.nameNotEqual
          (TptpResolvedFofLanguageDef.encodeNatIndex depth)
          (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
          (TptpFofSkolemLanguageDef.encodeTerm (arguments 0))
          (TptpFofSkolemLanguageDef.encodeTerm (arguments 1))
          (encodeDefinitionPatterns definitions)
          (encodeIntroducedPatterns introduced)
  | .and left right, quantifierFree, frontier, definitions, introduced => by
      change QuantifierFree left ∧ QuantifierFree right at quantifierFree
      simpa [namePattern, variableTerms,
        encodeDefinitionPatterns, encodeIntroducedPatterns,
        TptpFofSkolemLanguageDef.encodeFormula,
        encodeNatIndex_succ] using
        Derivation.nameAnd
          (nameDerivation left quantifierFree.1 frontier definitions introduced)
          (nameDerivation right quantifierFree.2
            (namePattern left quantifierFree.1 frontier definitions introduced).next
            (namePattern left quantifierFree.1 frontier definitions introduced).reverseDefinitions
            (namePattern left quantifierFree.1 frontier definitions introduced).reverseIntroduced)
          (variablesDerivation depth 0)
  | .or left right, quantifierFree, frontier, definitions, introduced => by
      change QuantifierFree left ∧ QuantifierFree right at quantifierFree
      simpa [namePattern, variableTerms,
        encodeDefinitionPatterns, encodeIntroducedPatterns,
        TptpFofSkolemLanguageDef.encodeFormula,
        encodeNatIndex_succ] using
        Derivation.nameOr
          (nameDerivation left quantifierFree.1 frontier definitions introduced)
          (nameDerivation right quantifierFree.2
            (namePattern left quantifierFree.1 frontier definitions introduced).next
            (namePattern left quantifierFree.1 frontier definitions introduced).reverseDefinitions
            (namePattern left quantifierFree.1 frontier definitions introduced).reverseIntroduced)
          (variablesDerivation depth 0)
  | .all _, impossible, _, _, _ => False.elim impossible
  | .ex _, impossible, _, _, _ => False.elim impossible

def reverseDefinitionsDerivation : (source accumulator : List Pattern) →
    Derivation
      (reverseDefinitionsRequest (encodeDefinitionPatterns source)
        (encodeDefinitionPatterns accumulator))
      (reverseDefinitionsResult (encodeDefinitionPatterns source)
        (encodeDefinitionPatterns accumulator)
        (encodeDefinitionPatterns (source.reverse ++ accumulator)))
  | [], accumulator => by
      simpa [encodeDefinitionPatterns] using
        Derivation.reverseDefinitionsNil (encodeDefinitionPatterns accumulator)
  | head :: tail, accumulator => by
      simpa [encodeDefinitionPatterns, List.reverse_cons,
        List.append_assoc] using
        Derivation.reverseDefinitionsCons
          (reverseDefinitionsDerivation tail (head :: accumulator))

def reverseIntroducedDerivation : (source accumulator : List Pattern) →
    Derivation
      (reverseIntroducedRequest (encodeIntroducedPatterns source)
        (encodeIntroducedPatterns accumulator))
      (reverseIntroducedResult (encodeIntroducedPatterns source)
        (encodeIntroducedPatterns accumulator)
        (encodeIntroducedPatterns (source.reverse ++ accumulator)))
  | [], accumulator => by
      simpa [encodeIntroducedPatterns] using
        Derivation.reverseIntroducedNil (encodeIntroducedPatterns accumulator)
  | head :: tail, accumulator => by
      simpa [encodeIntroducedPatterns, List.reverse_cons,
        List.append_assoc] using
        Derivation.reverseIntroducedCons
          (reverseIntroducedDerivation tail (head :: accumulator))

/-! ## Agreement with the independent typed naming semantics -/

theorem variableIndexPatterns_exact (depth start : Nat) :
    List.ofFn (fun index : Fin depth =>
      TptpFofSkolemLanguageDef.termVariable
        (TptpResolvedFofLanguageDef.encodeNatIndex (start + index.val))) =
    (List.range depth).map (fun index =>
      TptpFofSkolemLanguageDef.termVariable
        (TptpResolvedFofLanguageDef.encodeNatIndex (start + index))) := by
  induction depth generalizing start with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [List.ofFn_succ, List.range_succ_eq_map]
      simp only [Fin.val_zero, Nat.add_zero, List.map_cons, List.cons.injEq,
        true_and]
      convert inductionHypothesis (start + 1) using 1
      · apply List.ofFn_inj.mpr
        funext index
        apply congrArg TptpFofSkolemLanguageDef.termVariable
        apply congrArg TptpResolvedFofLanguageDef.encodeNatIndex
        simp only [Fin.val_succ]
        omega
      · rw [List.map_map]
        apply List.map_congr_left
        intro index _
        apply congrArg TptpFofSkolemLanguageDef.termVariable
        apply congrArg TptpResolvedFofLanguageDef.encodeNatIndex
        omega

theorem variableTerms_range_exact (remaining next : Nat) :
    variableTerms remaining next =
      TptpFofSkolemLanguageDef.encodeTermPatterns
        ((List.range' next remaining).map fun index =>
          TptpFofSkolemLanguageDef.termVariable
            (TptpResolvedFofLanguageDef.encodeNatIndex index)) := by
  induction remaining generalizing next with
  | zero => rfl
  | succ remaining inductionHypothesis =>
      rw [variableTerms, List.range'_succ, List.map_cons,
        TptpFofSkolemLanguageDef.encodeTermPatterns]
      rw [inductionHypothesis]

theorem variableTerms_zero_exact (depth : Nat) :
    variableTerms depth 0 =
      TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms
        (fun index : Fin depth =>
          (.bvar index : TptpFofDefinitionalNamingSemantics.Term depth)) := by
  rw [variableTerms_range_exact]
  unfold TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms
  congr 1
  simpa [TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm,
    TptpResolvedFofLanguageDef.encodeIndex,
    List.range'_eq_map_range] using
    (variableIndexPatterns_exact depth 0).symm

theorem encodeNamedTerms_translate_exact {depth arity : Nat}
    (arguments : Fin arity → Source.Term depth) :
    TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms
        (fun index => translateTerm (arguments index)) =
      TptpFofSkolemLanguageDef.encodeTerms (List.ofFn arguments) := by
  unfold TptpFofDefinitionalCnfLanguageDef.encodeNamedTerms
    TptpFofSkolemLanguageDef.encodeTerms
  congr 1
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext index
  exact TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm_translateTerm_exact
    (arguments index)

noncomputable def encodeDefinitionList {depth : Nat} :
    (definitions : List (Definition depth)) →
    (∀ definition ∈ definitions, QuantifierFree definition.source) →
    List Pattern
  | [], _ => []
  | head :: tail, quantifierFree =>
      TptpFofDefinitionalCnfLanguageDef.encodeDefinition head
          (quantifierFree head (by simp)) ::
        encodeDefinitionList tail (fun definition membership =>
          quantifierFree definition (by simp [membership]))

theorem encodeDefinitionList_append {depth : Nat}
    (left right : List (Definition depth))
    (quantifierFree : ∀ definition ∈ left ++ right,
      QuantifierFree definition.source) :
    encodeDefinitionList (left ++ right) quantifierFree =
      encodeDefinitionList left (fun definition membership =>
        quantifierFree definition (by simp [membership])) ++
      encodeDefinitionList right (fun definition membership =>
        quantifierFree definition (by simp [membership])) := by
  induction left with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, encodeDefinitionList, List.cons.injEq,
        true_and]
      exact inductionHypothesis _

theorem encodeDefinitionPatterns_encodeDefinitionList_exact {depth : Nat}
    (definitions : List (Definition depth))
    (quantifierFree : ∀ definition ∈ definitions,
      QuantifierFree definition.source) :
    encodeDefinitionPatterns
        (encodeDefinitionList definitions quantifierFree) =
      TptpFofDefinitionalCnfLanguageDef.encodeDefinitions definitions
        quantifierFree := by
  induction definitions with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [encodeDefinitionList, encodeDefinitionPatterns,
        TptpFofDefinitionalCnfLanguageDef.encodeDefinitions]
      congr 1
      exact inductionHypothesis _

theorem encodeDefinitionList_reverse_exact {depth : Nat}
    (definitions : List (Definition depth))
    (quantifierFree : ∀ definition ∈ definitions,
      QuantifierFree definition.source) :
    (encodeDefinitionList definitions quantifierFree).reverse =
      encodeDefinitionList definitions.reverse
        (fun definition membership =>
          quantifierFree definition (by simpa using membership)) := by
  induction definitions with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [encodeDefinitionList, List.reverse_cons]
      simp [encodeDefinitionList_append, inductionHypothesis]
      congr 2

theorem encodeIntroducedPatterns_map_exact
    (introduced : List IntroducedPredicate) :
    encodeIntroducedPatterns
        (introduced.map
          TptpFofDefinitionalCnfLanguageDef.encodeIntroducedPredicate) =
      TptpFofDefinitionalCnfLanguageDef.encodeIntroduced introduced := by
  induction introduced with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [encodeIntroducedPatterns,
        TptpFofDefinitionalCnfLanguageDef.encodeIntroduced,
        inductionHypothesis]

theorem encodeReference_positive_source_exact {depth arity : Nat}
    (relation : Source.RelationSymbol arity)
    (arguments : Fin arity → Source.Term depth) :
    TptpFofDefinitionalCnfLanguageDef.encodeReference
        (.positive (.original relation) fun index =>
          translateTerm (arguments index)) =
      match relation with
      | .predicate predicate =>
          TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
            (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
            (TptpFofSkolemLanguageDef.encodeTerms (List.ofFn arguments))
      | .equality =>
          TptpFofDefinitionalCnfLanguageDef.refEqual
            (TptpFofSkolemLanguageDef.encodeTerm (arguments 0))
            (TptpFofSkolemLanguageDef.encodeTerm (arguments 1)) := by
  cases relation with
  | predicate predicate =>
      simp [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        encodeNamedTerms_translate_exact]
  | equality =>
      simp [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm_translateTerm_exact]

theorem encodeReference_negative_source_exact {depth arity : Nat}
    (relation : Source.RelationSymbol arity)
    (arguments : Fin arity → Source.Term depth) :
    TptpFofDefinitionalCnfLanguageDef.encodeReference
        (.negative (.original relation) fun index =>
          translateTerm (arguments index)) =
      match relation with
      | .predicate predicate =>
          TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
            (TptpFofSymbolLanguageDef.encodePredicateHead ⟨predicate.kind, predicate.name⟩)
            (TptpFofSkolemLanguageDef.encodeTerms (List.ofFn arguments))
      | .equality =>
          TptpFofDefinitionalCnfLanguageDef.refNotEqual
            (TptpFofSkolemLanguageDef.encodeTerm (arguments 0))
            (TptpFofSkolemLanguageDef.encodeTerm (arguments 1)) := by
  cases relation with
  | predicate predicate =>
      simp [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        encodeNamedTerms_translate_exact]
  | equality =>
      simp [TptpFofDefinitionalCnfLanguageDef.encodeReference,
        TptpFofDefinitionalCnfLanguageDef.encodeNamedTerm_translateTerm_exact]

theorem encodeReference_defined_exact (depth id : Nat) :
    TptpFofDefinitionalCnfLanguageDef.encodeReference
        (definedReference depth id) =
      TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
        (TptpResolvedFofLanguageDef.encodeNatIndex id)
        (variableTerms depth 0) := by
  simp [definedReference,
    TptpFofDefinitionalCnfLanguageDef.encodeReference,
    variableTerms_zero_exact]

theorem namePattern_exact {depth : Nat} (source : Source.Formula depth)
    (quantifierFree : QuantifierFree source) (frontier : Nat)
    (definitionPatterns introducedPatterns : List Pattern) :
    namePattern source quantifierFree frontier definitionPatterns
        introducedPatterns =
      let output := nameFrom source quantifierFree frontier
      { root :=
          TptpFofDefinitionalCnfLanguageDef.encodeReference output.root
        next := output.next
        reverseDefinitions :=
          encodeDefinitionList output.definitions.reverse
              (fun definition membership =>
                nameFrom_definition_sources_quantifierFree source
                  quantifierFree frontier definition (by simpa using membership)) ++
            definitionPatterns
        reverseIntroduced :=
          output.introduced.reverse.map
              TptpFofDefinitionalCnfLanguageDef.encodeIntroducedPredicate ++
            introducedPatterns } := by
  classical
  revert frontier definitionPatterns introducedPatterns
  induction source with
  | verum =>
      intro frontier definitionPatterns introducedPatterns
      simp [namePattern, nameFrom, leafOutput,
        TptpFofDefinitionalCnfLanguageDef.encodeReference,
        encodeDefinitionList]
  | falsum =>
      intro frontier definitionPatterns introducedPatterns
      simp [namePattern, nameFrom, leafOutput,
        TptpFofDefinitionalCnfLanguageDef.encodeReference,
        encodeDefinitionList]
  | rel relation arguments =>
      intro frontier definitionPatterns introducedPatterns
      cases relation with
      | predicate predicate =>
          simp [namePattern, nameFrom, leafOutput,
            encodeDefinitionList, encodeReference_positive_source_exact]
      | equality =>
          simp [namePattern, nameFrom, leafOutput,
            encodeDefinitionList, encodeReference_positive_source_exact]
  | nrel relation arguments =>
      intro frontier definitionPatterns introducedPatterns
      cases relation with
      | predicate predicate =>
          simp [namePattern, nameFrom, leafOutput,
            encodeDefinitionList, encodeReference_negative_source_exact]
      | equality =>
          simp [namePattern, nameFrom, leafOutput,
            encodeDefinitionList, encodeReference_negative_source_exact]
  | and left right leftHypothesis rightHypothesis =>
      intro frontier definitionPatterns introducedPatterns
      change QuantifierFree left ∧ QuantifierFree right at quantifierFree
      simp only [namePattern]
      rw [leftHypothesis quantifierFree.1 frontier definitionPatterns
        introducedPatterns]
      rw [rightHypothesis quantifierFree.2]
      simp [nameFrom, encodeReference_defined_exact,
        TptpFofDefinitionalCnfLanguageDef.encodeDefinition,
        TptpFofDefinitionalCnfLanguageDef.encodeIntroducedPredicate,
        TptpFofSkolemLanguageDef.encodeFormula,
        List.reverse_append, List.append_assoc, encodeDefinitionList,
        encodeDefinitionList_append]
  | or left right leftHypothesis rightHypothesis =>
      intro frontier definitionPatterns introducedPatterns
      change QuantifierFree left ∧ QuantifierFree right at quantifierFree
      simp only [namePattern]
      rw [leftHypothesis quantifierFree.1 frontier definitionPatterns
        introducedPatterns]
      rw [rightHypothesis quantifierFree.2]
      simp [nameFrom, encodeReference_defined_exact,
        TptpFofDefinitionalCnfLanguageDef.encodeDefinition,
        TptpFofDefinitionalCnfLanguageDef.encodeIntroducedPredicate,
        TptpFofSkolemLanguageDef.encodeFormula,
        List.reverse_append, List.append_assoc, encodeDefinitionList,
        encodeDefinitionList_append]
  | all body inductionHypothesis =>
      intro frontier definitionPatterns introducedPatterns
      contradiction
  | ex body inductionHypothesis =>
      intro frontier definitionPatterns introducedPatterns
      contradiction

noncomputable def matrixPattern {depth : Nat}
    (source : Source.Formula depth) (quantifierFree : QuantifierFree source) :
    MatrixPattern
      (TptpFofSkolemLanguageDef.encodeFormula source
        quantifierFree.existentialFree) := by
  cases source with
  | verum => exact .verum
  | falsum => exact .falsum
  | rel relation arguments =>
      cases relation with
      | predicate predicate => exact .positive _ _
      | equality => exact .equal _ _
  | nrel relation arguments =>
      cases relation with
      | predicate predicate => exact .negative _ _
      | equality => exact .notEqual _ _
  | and left right => exact .and _ _
  | or left right => exact .or _ _
  | all body => contradiction
  | ex body => contradiction

noncomputable def matrixDerivation {depth : Nat}
    (source : Source.Formula depth) (quantifierFree : QuantifierFree source)
    (frontier : Nat) :
    Derivation
      (openRequest
        (TptpResolvedFofLanguageDef.encodeNatIndex depth)
        (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
        (TptpFofSkolemLanguageDef.encodeFormula source
          quantifierFree.existentialFree))
      (openResult
        (TptpResolvedFofLanguageDef.encodeNatIndex depth)
        (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
        (TptpFofSkolemLanguageDef.encodeFormula source
          quantifierFree.existentialFree)
        (TptpFofDefinitionalCnfLanguageDef.encodeNameFrom source
          quantifierFree frontier)) := by
  let output := nameFrom source quantifierFree frontier
  let definitionQuantifierFree :
      ∀ definition ∈ output.definitions,
        QuantifierFree definition.source :=
    fun definition membership =>
      nameFrom_definition_sources_quantifierFree source quantifierFree
        frontier definition membership
  let reverseDefinitionQuantifierFree :
      ∀ definition ∈ output.definitions.reverse,
        QuantifierFree definition.source :=
    fun definition membership =>
      definitionQuantifierFree definition (by simpa using membership)
  have naming := nameDerivation source quantifierFree frontier [] []
  rw [namePattern_exact] at naming
  simp only [List.append_nil] at naming
  have definitions := reverseDefinitionsDerivation
    (encodeDefinitionList output.definitions.reverse
      reverseDefinitionQuantifierFree) []
  have introduced := reverseIntroducedDerivation
    (output.introduced.reverse.map
      TptpFofDefinitionalCnfLanguageDef.encodeIntroducedPredicate) []
  simpa [output, definitionQuantifierFree,
    reverseDefinitionQuantifierFree,
    TptpFofDefinitionalCnfLanguageDef.encodeNameFrom,
    TptpFofDefinitionalCnfLanguageDef.encodeNamedOutput,
    encodeDefinitionList_reverse_exact,
    encodeDefinitionPatterns_encodeDefinitionList_exact,
    encodeIntroducedPatterns_map_exact] using
      Derivation.openMatrix (matrixPattern source quantifierFree)
        naming definitions introduced

noncomputable def universalDerivation {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier : Nat) :
    Derivation
      (openRequest
        (TptpResolvedFofLanguageDef.encodeNatIndex depth)
        (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
        (TptpFofSkolemLanguageDef.encodeFormula source
          evidence.existentialFree))
      (openResult
        (TptpResolvedFofLanguageDef.encodeNatIndex depth)
        (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
        (TptpFofSkolemLanguageDef.encodeFormula source
          evidence.existentialFree)
        (TptpFofDefinitionalCnfLanguageDef.encodeNameFrom
          evidence.opened.formula evidence.opened.quantifierFree frontier)) := by
  induction evidence with
  | @matrix depth source quantifierFree =>
      simpa [UniversalPrefix.opened,
        UniversalPrefix.existentialFree] using
        matrixDerivation source quantifierFree frontier
  | @all depth body bodyEvidence inductionHypothesis =>
      simpa [UniversalPrefix.opened, UniversalPrefix.existentialFree,
        TptpFofSkolemLanguageDef.encodeFormula, encodeNatIndex_succ] using
        Derivation.openAll inductionHypothesis

theorem rewriteAt_universal_exact {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier fuel : Nat)
    (enough : (universalDerivation evidence frontier).height ≤ fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalNamingLanguageDef.language fuel
        (openRequest
          (TptpResolvedFofLanguageDef.encodeNatIndex depth)
          (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
          (TptpFofSkolemLanguageDef.encodeFormula source
            evidence.existentialFree)) =
      [openResult
        (TptpResolvedFofLanguageDef.encodeNatIndex depth)
        (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
        (TptpFofSkolemLanguageDef.encodeFormula source
          evidence.existentialFree)
        (TptpFofDefinitionalCnfLanguageDef.encodeNameFrom
          evidence.opened.formula evidence.opened.quantifierFree frontier)] :=
  (universalDerivation evidence frontier).rewriteAt_exact fuel enough

theorem universal_no_invention {depth : Nat}
    {source : Source.Formula depth} (evidence : UniversalPrefix source)
    (frontier fuel : Nat)
    (enough : (universalDerivation evidence frontier).height ≤ fuel)
    (target : Pattern)
    (membership : target ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalNamingLanguageDef.language fuel
      (openRequest
        (TptpResolvedFofLanguageDef.encodeNatIndex depth)
        (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
        (TptpFofSkolemLanguageDef.encodeFormula source
          evidence.existentialFree))) :
    target = openResult
      (TptpResolvedFofLanguageDef.encodeNatIndex depth)
      (TptpResolvedFofLanguageDef.encodeNatIndex frontier)
      (TptpFofSkolemLanguageDef.encodeFormula source
        evidence.existentialFree)
      (TptpFofDefinitionalCnfLanguageDef.encodeNameFrom
        evidence.opened.formula evidence.opened.quantifierFree frontier) :=
  (universalDerivation evidence frontier).no_invention fuel enough membership

namespace Canary

def universalSource : Source.Formula 0 :=
  .all (.or .verum .falsum)

def universalEvidence : UniversalPrefix universalSource := by
  refine .all (.matrix ?_)
  simp [QuantifierFree]

theorem universal_source_opens_at_depth_one :
    universalEvidence.opened.depth = 1 := rfl

theorem universal_source_has_one_canonical_reduct :
    (rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalNamingLanguageDef.language
      (universalDerivation universalEvidence 7).height
      (openRequest
        (TptpResolvedFofLanguageDef.encodeNatIndex 0)
        (TptpResolvedFofLanguageDef.encodeNatIndex 7)
        (TptpFofSkolemLanguageDef.encodeFormula universalSource
          universalEvidence.existentialFree))).length = 1 := by
  rw [rewriteAt_universal_exact universalEvidence 7 _ (le_refl _)]
  rfl

end Canary

#print axioms namePattern_exact
#print axioms rewriteAt_universal_exact
#print axioms universal_no_invention
#print axioms Canary.universal_source_has_one_canonical_reduct

end Operational

end Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingSemanticAgreement
