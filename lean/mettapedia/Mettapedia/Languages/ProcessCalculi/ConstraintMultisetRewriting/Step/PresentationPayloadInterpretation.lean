import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRuleGrammar
import Mathlib.Tactic.FinCases

/-! # Interpreting every authored payload constructor

The carrier family covers every sort declared by `Tcalc.Syntax`. Constructor
interpretation is indexed by the actual compiled row and its ordered child
sorts. Configuration syntax retains its occurrence list here; the existing
configuration reader subsequently checks distinct identities before forming
the occurrence set.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

def Carrier : String → Type
  | "TcIndex" => Nat
  | "TcHead" => Head
  | "TcTerm" => Term
  | "TcFields" => Fields
  | "TcTerms" => List Term
  | "TcEquation" => Equation Term
  | "TcEquations" => EquationStore Term
  | "TcCheck" => Check Term
  | "TcChecks" => List (Check Term)
  | "TcRule" => RuleInstance Term
  | "TcIndices" => List Nat
  | "TcSelection" => Selection Nat
  | "TcConfiguration" => EquationStore Term × List Nat
  | _ => Empty

def readConfigurationData : Pattern → Option (EquationStore Term × List Nat)
  | .apply "TcConfigurationData" [knowledge, occurrences] => do
      return (← readEquations knowledge, ← readIndices occurrences)
  | _ => none

def decode : (sort : String) → Pattern → Option (Carrier sort)
  | "TcIndex", pattern => readIndex pattern
  | "TcHead", pattern => readHead pattern
  | "TcTerm", pattern => readTerm pattern
  | "TcFields", pattern => readFields pattern
  | "TcTerms", pattern => readTerms pattern
  | "TcEquation", pattern => readEquation pattern
  | "TcEquations", pattern => readEquations pattern
  | "TcCheck", pattern => readCheck pattern
  | "TcChecks", pattern => readChecks pattern
  | "TcRule", pattern => readRule pattern
  | "TcIndices", pattern => readIndices pattern
  | "TcSelection", pattern => readSelection pattern
  | "TcConfiguration", pattern => readConfigurationData pattern
  | _, _ => none

def construct {inputs : List String} {output : String} (operation : Operation rules inputs output) :
    FamilyList Carrier inputs → Carrier output := by
  cases operation with
  | «at» index =>
    rcases index with ⟨n, valid⟩
    have range : n < 25 := valid
    match n with
    | 0 =>
      change FamilyList Carrier [] → Nat
      exact fun | .nil => 0
    | 1 =>
      change FamilyList Carrier ["TcIndex"] → Nat
      exact fun | .cons n (.nil) => Nat.succ n
    | 2 =>
      change FamilyList Carrier ["TcIndex"] → Head
      exact fun | .cons n (.nil) => Head.symbol n
    | 3 =>
      change FamilyList Carrier ["TcIndex"] → Head
      exact fun | .cons n (.nil) => Head.name n
    | 4 =>
      change FamilyList Carrier ["TcIndex"] → Head
      exact fun | .cons n (.nil) => Head.hole n
    | 5 =>
      change FamilyList Carrier ["TcIndex"] → Head
      exact fun | .cons n (.nil) => Head.quotedRule n
    | 6 =>
      change FamilyList Carrier ["TcIndex"] → Term
      exact fun | .cons n (.nil) => (.idx n : Term)
    | 7 =>
      change FamilyList Carrier ["TcHead", "TcFields"] → Term
      exact fun | .cons head (.cons fields (.nil)) => (.node head fields : Term)
    | 8 =>
      change FamilyList Carrier [] → Fields
      exact fun | .nil => (.nil : Fields)
    | 9 =>
      change FamilyList Carrier ["TcIndex", "TcTerm", "TcFields"] → Fields
      exact fun | .cons depth (.cons term (.cons rest (.nil))) => (.cons depth term rest : Fields)
    | 10 =>
      change FamilyList Carrier [] → List Term
      exact fun | .nil => ([] : List Term)
    | 11 =>
      change FamilyList Carrier ["TcTerm", "TcTerms"] → List Term
      exact fun | .cons term (.cons rest (.nil)) => term :: rest
    | 12 =>
      change FamilyList Carrier ["TcTerm", "TcTerm"] → Equation Term
      exact fun | .cons left (.cons right (.nil)) => (left, right)
    | 13 =>
      change FamilyList Carrier [] → EquationStore Term
      exact fun | .nil => ([] : EquationStore Term)
    | 14 =>
      change FamilyList Carrier ["TcEquation", "TcEquations"] → EquationStore Term
      exact fun | .cons equation (.cons rest (.nil)) => equation :: rest
    | 15 =>
      change FamilyList Carrier ["TcTerm", "TcTerm"] → Check Term
      exact fun | .cons left (.cons right (.nil)) => Check.equal left right
    | 16 =>
      change FamilyList Carrier ["TcTerm"] → Check Term
      exact fun | .cons term (.nil) => Check.absent term
    | 17 =>
      change FamilyList Carrier ["TcTerm", "TcIndex"] → Check Term
      exact fun | .cons term (.cons count (.nil)) => Check.count term count
    | 18 =>
      change FamilyList Carrier [] → List (Check Term)
      exact fun | .nil => ([] : List (Check Term))
    | 19 =>
      change FamilyList Carrier ["TcCheck", "TcChecks"] → List (Check Term)
      exact fun | .cons check (.cons rest (.nil)) => check :: rest
    | 20 =>
      change FamilyList Carrier ["TcTerms", "TcTerms", "TcEquations", "TcChecks", "TcTerms"] → RuleInstance Term
      exact fun | .cons take (.cons read (.cons tell (.cons checks (.cons make (.nil))))) => (⟨take, read, tell, checks, make⟩ : RuleInstance Term)
    | 21 =>
      change FamilyList Carrier [] → List Nat
      exact fun | .nil => ([] : List Nat)
    | 22 =>
      change FamilyList Carrier ["TcIndex", "TcIndices"] → List Nat
      exact fun | .cons index (.cons rest (.nil)) => index :: rest
    | 23 =>
      change FamilyList Carrier ["TcIndices", "TcIndices", "TcIndices"] → Selection Nat
      exact fun | .cons take (.cons read (.cons make (.nil))) => (⟨take, read, make⟩ : Selection Nat)
    | 24 =>
      change FamilyList Carrier ["TcEquations", "TcIndices"] → EquationStore Term × List Nat
      exact fun | .cons knowledge (.cons present (.nil)) => (knowledge, present)
    | k + 25 => exact False.elim (by omega)

def interpretation : Interpretation rules where
  Carrier := Carrier
  operation := construct

/-- The child evidence is ordered and sort-indexed; no head-name search or
untyped positional cast is hidden in the constructor law. -/
inductive ChildrenDecode : {sorts : List String} →
    FamilyList (fun _ : String => Observation) sorts → FamilyList Carrier sorts → Prop where
  | nil : ChildrenDecode .nil .nil
  | cons {sort : String} {sorts : List String} {observation : Observation} {value : Carrier sort}
      {observations : FamilyList (fun _ : String => Observation) sorts}
      {values : FamilyList Carrier sorts}
      (head : decode sort observation.tree = some value) (tail : ChildrenDecode observations values) :
      ChildrenDecode (.cons observation observations) (.cons value values)


theorem ChildrenDecode.head {sort : String} {sorts : List String}
    {observation : Observation} {value : Carrier sort}
    {observations : FamilyList (fun _ : String => Observation) sorts}
    {values : FamilyList Carrier sorts}
    (children : ChildrenDecode (.cons observation observations) (.cons value values)) :
    decode sort observation.tree = some value := by
  cases children with
  | cons head _ => exact head

theorem ChildrenDecode.tail {sort : String} {sorts : List String}
    {observation : Observation} {value : Carrier sort}
    {observations : FamilyList (fun _ : String => Observation) sorts}
    {values : FamilyList Carrier sorts}
    (children : ChildrenDecode (.cons observation observations) (.cons value values)) :
    ChildrenDecode observations values := by
  cases children with
  | cons _ tail => exact tail

/-- The total constructor interpretation agrees with the independent reader
for every authored row and every correctly interpreted ordered child list. -/
theorem decode_construct {inputs : List String} {output : String}
    (operation : Operation rules inputs output)
    (observations : FamilyList (fun _ : String => Observation) inputs)
    (values : FamilyList Carrier inputs) (children : ChildrenDecode observations values) :
    decode output (observeOperation rules operation observations).tree =
      some (construct operation values) := by
  cases operation with
  | «at» index =>
    fin_cases index
    · change FamilyList (fun _ : String => Observation) [] at observations
      change FamilyList Carrier [] at values
      cases observations
      cases values
      rfl
    · change FamilyList (fun _ : String => Observation) ["TcIndex"] at observations
      change FamilyList Carrier ["TcIndex"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0
          cases vs0
          have h0 := children.head
          change readIndex o0.tree = some v0 at h0
          change readIndex (.apply "TcSucc" [o0.tree]) = some (Nat.succ v0)
          rw [readIndex, h0]
          rfl
    · change FamilyList (fun _ : String => Observation) ["TcIndex"] at observations
      change FamilyList Carrier ["TcIndex"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0
          cases vs0
          have h0 := children.head
          change readIndex o0.tree = some v0 at h0
          change readHead (.apply "TcSymbol" [o0.tree]) = some (Head.symbol v0)
          rw [readHead, h0]
          rfl
    · change FamilyList (fun _ : String => Observation) ["TcIndex"] at observations
      change FamilyList Carrier ["TcIndex"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0
          cases vs0
          have h0 := children.head
          change readIndex o0.tree = some v0 at h0
          change readHead (.apply "TcName" [o0.tree]) = some (Head.name v0)
          rw [readHead, h0]
          rfl
    · change FamilyList (fun _ : String => Observation) ["TcIndex"] at observations
      change FamilyList Carrier ["TcIndex"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0
          cases vs0
          have h0 := children.head
          change readIndex o0.tree = some v0 at h0
          change readHead (.apply "TcHole" [o0.tree]) = some (Head.hole v0)
          rw [readHead, h0]
          rfl
    · change FamilyList (fun _ : String => Observation) ["TcIndex"] at observations
      change FamilyList Carrier ["TcIndex"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0
          cases vs0
          have h0 := children.head
          change readIndex o0.tree = some v0 at h0
          change readHead (.apply "TcQuotedRule" [o0.tree]) = some (Head.quotedRule v0)
          rw [readHead, h0]
          rfl
    · change FamilyList (fun _ : String => Observation) ["TcIndex"] at observations
      change FamilyList Carrier ["TcIndex"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0
          cases vs0
          have h0 := children.head
          change readIndex o0.tree = some v0 at h0
          change readTerm (.apply "TcVar" [o0.tree]) = some ((.idx v0 : Term))
          rw [readTerm, h0]
          rfl
    · change FamilyList (fun _ : String => Observation) ["TcHead", "TcFields"] at observations
      change FamilyList Carrier ["TcHead", "TcFields"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1
              cases vs1
              have h0 := children.head
              change readHead o0.tree = some v0 at h0
              have h1 := children.tail.head
              change readFields o1.tree = some v1 at h1
              change readTerm (.apply "TcNode" [o0.tree, o1.tree]) = some ((.node v0 v1 : Term))
              rw [readTerm, h0, h1]
              rfl
    · change FamilyList (fun _ : String => Observation) [] at observations
      change FamilyList Carrier [] at values
      cases observations
      cases values
      rfl
    · change FamilyList (fun _ : String => Observation) ["TcIndex", "TcTerm", "TcFields"] at observations
      change FamilyList Carrier ["TcIndex", "TcTerm", "TcFields"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1 with
              | cons o2 os2 =>
                cases vs1 with
                | cons v2 vs2 =>
                  cases os2
                  cases vs2
                  have h0 := children.head
                  change readIndex o0.tree = some v0 at h0
                  have h1 := children.tail.head
                  change readTerm o1.tree = some v1 at h1
                  have h2 := children.tail.tail.head
                  change readFields o2.tree = some v2 at h2
                  change readFields (.apply "TcFieldsCons" [o0.tree, o1.tree, o2.tree]) = some ((.cons v0 v1 v2 : Fields))
                  rw [readFields, h0, h1, h2]
                  rfl
    · change FamilyList (fun _ : String => Observation) [] at observations
      change FamilyList Carrier [] at values
      cases observations
      cases values
      rfl
    · change FamilyList (fun _ : String => Observation) ["TcTerm", "TcTerms"] at observations
      change FamilyList Carrier ["TcTerm", "TcTerms"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1
              cases vs1
              have h0 := children.head
              change readTerm o0.tree = some v0 at h0
              have h1 := children.tail.head
              change readTerms o1.tree = some v1 at h1
              dsimp only [readTerms] at h1
              change readTerms (.apply "TcTermsCons" [o0.tree, o1.tree]) = some (v0 :: v1)
              rw [readTerms, readList, h0, h1]
              rfl
    · change FamilyList (fun _ : String => Observation) ["TcTerm", "TcTerm"] at observations
      change FamilyList Carrier ["TcTerm", "TcTerm"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1
              cases vs1
              have h0 := children.head
              change readTerm o0.tree = some v0 at h0
              have h1 := children.tail.head
              change readTerm o1.tree = some v1 at h1
              change readEquation (.apply "TcEquationData" [o0.tree, o1.tree]) = some ((v0, v1))
              rw [readEquation, h0, h1]
              rfl
    · change FamilyList (fun _ : String => Observation) [] at observations
      change FamilyList Carrier [] at values
      cases observations
      cases values
      rfl
    · change FamilyList (fun _ : String => Observation) ["TcEquation", "TcEquations"] at observations
      change FamilyList Carrier ["TcEquation", "TcEquations"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1
              cases vs1
              have h0 := children.head
              change readEquation o0.tree = some v0 at h0
              have h1 := children.tail.head
              change readEquations o1.tree = some v1 at h1
              dsimp only [readEquations] at h1
              change readEquations (.apply "TcEquationsCons" [o0.tree, o1.tree]) = some (v0 :: v1)
              rw [readEquations, readList, h0, h1]
              rfl
    · change FamilyList (fun _ : String => Observation) ["TcTerm", "TcTerm"] at observations
      change FamilyList Carrier ["TcTerm", "TcTerm"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1
              cases vs1
              have h0 := children.head
              change readTerm o0.tree = some v0 at h0
              have h1 := children.tail.head
              change readTerm o1.tree = some v1 at h1
              change readCheck (.apply "TcEqual" [o0.tree, o1.tree]) = some (Check.equal v0 v1)
              rw [readCheck, h0, h1]
              rfl
    · change FamilyList (fun _ : String => Observation) ["TcTerm"] at observations
      change FamilyList Carrier ["TcTerm"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0
          cases vs0
          have h0 := children.head
          change readTerm o0.tree = some v0 at h0
          change readCheck (.apply "TcAbsent" [o0.tree]) = some (Check.absent v0)
          rw [readCheck, h0]
          rfl
    · change FamilyList (fun _ : String => Observation) ["TcTerm", "TcIndex"] at observations
      change FamilyList Carrier ["TcTerm", "TcIndex"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1
              cases vs1
              have h0 := children.head
              change readTerm o0.tree = some v0 at h0
              have h1 := children.tail.head
              change readIndex o1.tree = some v1 at h1
              change readCheck (.apply "TcCount" [o0.tree, o1.tree]) = some (Check.count v0 v1)
              rw [readCheck, h0, h1]
              rfl
    · change FamilyList (fun _ : String => Observation) [] at observations
      change FamilyList Carrier [] at values
      cases observations
      cases values
      rfl
    · change FamilyList (fun _ : String => Observation) ["TcCheck", "TcChecks"] at observations
      change FamilyList Carrier ["TcCheck", "TcChecks"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1
              cases vs1
              have h0 := children.head
              change readCheck o0.tree = some v0 at h0
              have h1 := children.tail.head
              change readChecks o1.tree = some v1 at h1
              dsimp only [readChecks] at h1
              change readChecks (.apply "TcChecksCons" [o0.tree, o1.tree]) = some (v0 :: v1)
              rw [readChecks, readList, h0, h1]
              rfl
    · change FamilyList (fun _ : String => Observation) ["TcTerms", "TcTerms", "TcEquations", "TcChecks", "TcTerms"] at observations
      change FamilyList Carrier ["TcTerms", "TcTerms", "TcEquations", "TcChecks", "TcTerms"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1 with
              | cons o2 os2 =>
                cases vs1 with
                | cons v2 vs2 =>
                  cases os2 with
                  | cons o3 os3 =>
                    cases vs2 with
                    | cons v3 vs3 =>
                      cases os3 with
                      | cons o4 os4 =>
                        cases vs3 with
                        | cons v4 vs4 =>
                          cases os4
                          cases vs4
                          have h0 := children.head
                          change readTerms o0.tree = some v0 at h0
                          have h1 := children.tail.head
                          change readTerms o1.tree = some v1 at h1
                          have h2 := children.tail.tail.head
                          change readEquations o2.tree = some v2 at h2
                          have h3 := children.tail.tail.tail.head
                          change readChecks o3.tree = some v3 at h3
                          have h4 := children.tail.tail.tail.tail.head
                          change readTerms o4.tree = some v4 at h4
                          change readRule (.apply "TcRuleData" [o0.tree, o1.tree, o2.tree, o3.tree, o4.tree]) = some ((⟨v0, v1, v2, v3, v4⟩ : RuleInstance Term))
                          rw [readRule, h0, h1, h2, h3, h4]
                          rfl
    · change FamilyList (fun _ : String => Observation) [] at observations
      change FamilyList Carrier [] at values
      cases observations
      cases values
      rfl
    · change FamilyList (fun _ : String => Observation) ["TcIndex", "TcIndices"] at observations
      change FamilyList Carrier ["TcIndex", "TcIndices"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1
              cases vs1
              have h0 := children.head
              change readIndex o0.tree = some v0 at h0
              have h1 := children.tail.head
              change readIndices o1.tree = some v1 at h1
              dsimp only [readIndices] at h1
              change readIndices (.apply "TcIndicesCons" [o0.tree, o1.tree]) = some (v0 :: v1)
              rw [readIndices, readList, h0, h1]
              rfl
    · change FamilyList (fun _ : String => Observation) ["TcIndices", "TcIndices", "TcIndices"] at observations
      change FamilyList Carrier ["TcIndices", "TcIndices", "TcIndices"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1 with
              | cons o2 os2 =>
                cases vs1 with
                | cons v2 vs2 =>
                  cases os2
                  cases vs2
                  have h0 := children.head
                  change readIndices o0.tree = some v0 at h0
                  have h1 := children.tail.head
                  change readIndices o1.tree = some v1 at h1
                  have h2 := children.tail.tail.head
                  change readIndices o2.tree = some v2 at h2
                  change readSelection (.apply "TcSelectionData" [o0.tree, o1.tree, o2.tree]) = some ((⟨v0, v1, v2⟩ : Selection Nat))
                  rw [readSelection, h0, h1, h2]
                  rfl
    · change FamilyList (fun _ : String => Observation) ["TcEquations", "TcIndices"] at observations
      change FamilyList Carrier ["TcEquations", "TcIndices"] at values
      cases observations with
      | cons o0 os0 =>
        cases values with
        | cons v0 vs0 =>
          cases os0 with
          | cons o1 os1 =>
            cases vs0 with
            | cons v1 vs1 =>
              cases os1
              cases vs1
              have h0 := children.head
              change readEquations o0.tree = some v0 at h0
              have h1 := children.tail.head
              change readIndices o1.tree = some v1 at h1
              change readConfigurationData (.apply "TcConfigurationData" [o0.tree, o1.tree]) = some ((v0, v1))
              rw [readConfigurationData, h0, h1]
              rfl

mutual
  /-- Every typed route of the authored grammar decodes to its structural
  interpretation, including routes not produced by the canonical printer. -/
  theorem decode_route {sort : String} (route : Route sort) :
      decode sort ((syntaxAlgebra rules).evaluate route).tree =
        some (interpret interpretation route) := by
    match route with
    | .source impossible => exact Empty.elim impossible
    | .apply operation arguments =>
        exact decode_construct operation _ _ (decode_arguments arguments)
    termination_by structural route

  theorem decode_arguments {sorts : List String}
      (arguments : ConstructionArguments (syntaxAlgebra rules) sorts) :
      ChildrenDecode ((syntaxAlgebra rules).evaluateArguments arguments)
        (interpretArguments interpretation arguments) := by
    match arguments with
    | .nil => exact .nil
    | .cons head tail => exact .cons (decode_route head) (decode_arguments tail)
    termination_by structural arguments
end

/-- The existing compiler's reflection/completeness result connects an
arbitrary authored derivation to the actual transform data interpretation. -/
theorem source_has_interpreted_route {sort : String} {tokens : List String} {tree : Pattern}
    (derivation : GrammarDerives.Derives dataLanguage sort tokens tree) :
    ∃ route : Route sort, (syntaxAlgebra rules).evaluate route = ⟨tokens, tree⟩ ∧
      decode sort tree = some (interpret interpretation route) := by
  obtain ⟨route, observed⟩ := (source_derives_iff_route data_compiles sort tokens tree).mp derivation
  refine ⟨route, observed, ?_⟩
  have decoded := decode_route route
  simpa only [observed] using decoded

/-- Authored grammar derivations cannot produce a structurally undecodable
value. Configuration occurrence distinctness remains a later semantic check. -/
theorem source_decodes {sort : String} {tokens : List String} {tree : Pattern}
    (derivation : GrammarDerives.Derives dataLanguage sort tokens tree) :
    ∃ value : Carrier sort, decode sort tree = some value := by
  obtain ⟨route, _, decoded⟩ := source_has_interpreted_route derivation
  exact ⟨interpret interpretation route, decoded⟩

/-- The data observation forgets route identity only when their actual
structural trees agree. This does not assert uniqueness of parsing. -/
theorem interpretation_of_same_tree {sort : String} (first second : Route sort)
    (same : ((syntaxAlgebra rules).evaluate first).tree =
      ((syntaxAlgebra rules).evaluate second).tree) :
    interpret interpretation first = interpret interpretation second := by
  have decoded := decode_route first
  rw [same, decode_route second] at decoded
  exact (Option.some.inj decoded).symm

/-- A head constructor cannot be invented as a term constructor by a source
parser, even though both carry an index. -/
theorem wrong_sort_not_derivable (tokens : List String) (index : Nat) :
    ¬ GrammarDerives.Derives dataLanguage "TcTerm" tokens (headPattern (.name index)) := by
  intro derivation
  obtain ⟨value, decoded⟩ := source_decodes derivation
  change readTerm (.apply "TcName" [indexPattern index]) = some value at decoded
  simp only [readTerm] at decoded
  cases decoded

#print axioms decode_construct
#print axioms decode_route
#print axioms source_has_interpreted_route
#print axioms source_decodes
#print axioms interpretation_of_same_tree
#print axioms wrong_sort_not_derivable


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads
