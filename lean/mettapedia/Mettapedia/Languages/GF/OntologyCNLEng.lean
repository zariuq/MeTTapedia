/-
# Ontology CNL — English Linearization

Deterministic linearization of OntologyCNL abstract trees to English strings.
Each tree produces exactly one string. No ambiguity.

## Design

Uses direct string assembly rather than the full GF English Syntax engine,
because ontology English has fixed patterns that don't need tense/aspect
variation. This keeps the linearization simple and provably deterministic.

The full Syntax engine (linPredVP, mkClause, etc.) is available for future
modules (Instruction, Paper) that need richer linguistic structure.
-/

import Mettapedia.Languages.GF.OntologyCNL

namespace Mettapedia.Languages.GF.OntologyCNLEng

open Mettapedia.Languages.GF.OntologyCNL

/-! ## Helpers -/

private def strengthStr : Strength → String
  | .strong => "strong"
  | .moderate => "moderate"
  | .weak => "weak"

private def sourceStr (s : SourceLoc) : String :=
  s.file ++ ":" ++ toString s.line

private def articleFor (name : String) : String :=
  match name.toList.head? with
  | some c => if c ∈ ['A', 'E', 'I', 'O', 'U', 'a', 'e', 'i', 'o', 'u']
              then "an" else "a"
  | none => "a"

/-! ## Core Linearization -/

/-- Linearize an ontology statement to English -/
def linOntStmt : OntStmt → String
  | .isSubclassOf sub sup =>
    sub.name ++ " is a subclass of " ++ sup.name
  | .isInstanceOf inst cls =>
    inst.name ++ " is an instance of " ++ cls.name
  | .domainAt rel pos cls =>
    "the domain of " ++ rel.name ++ " at position " ++ toString pos ++ " is " ++ cls.name
  | .rangeIs rel cls =>
    "the range of " ++ rel.name ++ " is " ++ cls.name
  | .forAll cls body =>
    "for every " ++ cls.name ++ ", " ++ linOntStmt body
  | .exists_ cls body =>
    "there exists " ++ articleFor cls.name ++ " " ++ cls.name ++ " such that " ++ linOntStmt body
  | .ifThen hyp concl =>
    "if " ++ linOntStmt hyp ++ " then " ++ linOntStmt concl
  | .and_ left right =>
    linOntStmt left ++ " and " ++ linOntStmt right
  | .or_ left right =>
    linOntStmt left ++ " or " ++ linOntStmt right
  | .not_ body =>
    "it is not the case that " ++ linOntStmt body
  | .relatesTo subj rel obj =>
    subj.name ++ " " ++ rel.name ++ " " ++ obj.name
  | .disjointFrom a b =>
    a.name ++ " is disjoint from " ++ b.name
  | .relArity rel n =>
    rel.name ++ " is " ++ articleFor (arityWord n) ++ " " ++ arityWord n
where
  arityWord : Nat → String
    | 1 => "UnaryPredicate"
    | 2 => "BinaryPredicate"
    | 3 => "TernaryPredicate"
    | n => toString n ++ "-ary predicate"

/-- Linearize an evidence statement to English -/
def linEvidenceStmt : EvidenceStmt → String
  | .cite item =>
    let base := sourceStr item.source ++ " supports " ++ item.supports.name
                ++ " (" ++ strengthStr item.strength ++ ")"
    if item.note == "" then base else base ++ " — " ++ item.note
  | .usageCount concept role count =>
    toString count ++ " axioms use " ++ concept.name ++ " as " ++
    articleFor role ++ " " ++ role
  | .recommendation concept cls =>
    "the recommended classification of " ++ concept.name ++ " is " ++ cls.name

/-- Linearize a document block to English -/
def linOntDoc : OntDoc → String
  | .stmt s => linOntStmt s
  | .evidence e => linEvidenceStmt e
  | .seq first rest => linOntDoc first ++ ". " ++ linOntDoc rest
  | .empty => ""

/-! ## Determinism Proof

The linearization is structurally recursive on the inductive type,
with no case analysis on external state. Each constructor maps to
exactly one string template. This is trivially deterministic.
-/

/-- Linearization is a function (trivially true by construction, but stated
    explicitly for documentation: same tree always produces same string) -/
theorem linOntStmt_deterministic (s : OntStmt) :
    linOntStmt s = linOntStmt s := rfl

theorem linEvidenceStmt_deterministic (e : EvidenceStmt) :
    linEvidenceStmt e = linEvidenceStmt e := rfl

/-! ## Test Examples

Concrete examples showing abstract trees and their English linearizations.
These serve as the Phase A verification corpus.
-/

-- Example 1: Subclass declaration
private def ex_pain_subclass : OntStmt :=
  .isSubclassOf "Pain" "StateOfMind"

#eval linOntStmt ex_pain_subclass
-- "Pain is a subclass of StateOfMind"

-- Example 2: Instance declaration
private def ex_accountant_instance : OntStmt :=
  .isInstanceOf "Accountant" "Profession"

#eval linOntStmt ex_accountant_instance
-- "Accountant is an instance of Profession"

-- Example 3: Domain declaration
private def ex_attribute_domain : OntStmt :=
  .domainAt "attribute" 1 "Object"

#eval linOntStmt ex_attribute_domain
-- "the domain of attribute at position 1 is Object"

-- Example 4: Universal quantification
private def ex_forall : OntStmt :=
  .forAll "Process" (.relatesTo "it" "causes" "Effect")

#eval linOntStmt ex_forall
-- "for every Process, it causes Effect"

-- Example 5: Conditional
private def ex_ifthen : OntStmt :=
  .ifThen
    (.isSubclassOf "X" "PhysicalProcess")
    (.relatesTo "X" "hasParticipant" "PhysicalEntity")

#eval linOntStmt ex_ifthen
-- "if X is a subclass of PhysicalProcess then X hasParticipant PhysicalEntity"

-- Example 6: BinaryEvidence citation
private def ex_evidence : EvidenceStmt :=
  .cite {
    source := SourceLoc.mk "Merge.kif" 925
    supports := "Object"
    strength := .strong
    note := "domain declaration for part relation"
  }

#eval linEvidenceStmt ex_evidence
-- "Merge.kif:925 supports Object (strong) — domain declaration for part relation"

-- Example 7: Usage count
private def ex_usage : EvidenceStmt :=
  .usageCount "Pain" "Process" 5

#eval linEvidenceStmt ex_usage
-- "5 axioms use Pain as a Process"

-- Example 8: Recommendation
private def ex_recommend : EvidenceStmt :=
  .recommendation "Pain" "StateOfMind"

#eval linEvidenceStmt ex_recommend
-- "the recommended classification of Pain is StateOfMind"

-- Example 9: Disjointness
private def ex_disjoint : OntStmt :=
  .disjointFrom "Physical" "Abstract"

#eval linOntStmt ex_disjoint
-- "Physical is disjoint from Abstract"

-- Example 10: Relation arity
private def ex_arity : OntStmt :=
  .relArity "subAttribute" 2

#eval linOntStmt ex_arity
-- "subAttribute is a BinaryPredicate"

-- Example 11: Existential
private def ex_exists : OntStmt :=
  .exists_ "Agent" (.relatesTo "it" "performs" "Action")

#eval linOntStmt ex_exists
-- "there exists an Agent such that it performs Action"

-- Example 12: Negation
private def ex_not : OntStmt :=
  .not_ (.isSubclassOf "Pain" "PhysicalProcess")

#eval linOntStmt ex_not
-- "it is not the case that Pain is a subclass of PhysicalProcess"

-- Example 13: Conjunction
private def ex_and : OntStmt :=
  .and_
    (.isSubclassOf "Pain" "StateOfMind")
    (.isSubclassOf "StateOfMind" "InternalAttribute")

#eval linOntStmt ex_and
-- "Pain is a subclass of StateOfMind and StateOfMind is a subclass of InternalAttribute"

-- Example 14: Document block (multi-sentence)
private def ex_doc : OntDoc :=
  .seq
    (.stmt (.isSubclassOf "Pain" "StateOfMind"))
    (.seq
      (.evidence (.usageCount "Pain" "Process" 5))
      (.evidence (.recommendation "Pain" "StateOfMind")))

#eval linOntDoc ex_doc
-- "Pain is a subclass of StateOfMind. 5 axioms use Pain as a Process. the recommended classification of Pain is StateOfMind"

-- Example 15: Nested quantification
private def ex_nested : OntStmt :=
  .forAll "Agent"
    (.ifThen
      (.relatesTo "Agent" "desires" "Formula")
      (.exists_ "Action" (.relatesTo "Agent" "performs" "Action")))

#eval linOntStmt ex_nested
-- "for every Agent, if Agent desires Formula then there exists an Action such that Agent performs Action"

end Mettapedia.Languages.GF.OntologyCNLEng
