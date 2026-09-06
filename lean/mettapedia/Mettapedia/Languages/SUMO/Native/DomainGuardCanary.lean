import Mettapedia.Languages.SUMO.Native.DomainGuardElaboration

/-!
# Executable canaries for native SUMO domain guards

These examples cover both guard polarities, `KappaFn`, subclass-domain
restrictions, inherited domains, variable arity, redundancy elimination, and
scope-safe guards for denoted operators and exact row tails.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native.DomainGuardCanary

open Mettapedia.Languages.SUMO.Native
open Mettapedia.Languages.SUMO.Native.SourceElaboration
open Mettapedia.Languages.SUMO.Native.DomainGuardElaboration

private def agentSignature : SourceSignature :=
  { domainRestrictions :=
      [⟨"loves", 1, .object, "CognitiveAgent"⟩,
       ⟨"works", 1, .object, "Entity"⟩,
       ⟨"partition", 1, .class, "Class"⟩,
       ⟨"partition", 2, .class, "Class"⟩,
       ⟨"related", 1, .object, "Object"⟩]
    subclassEdges := [("Human", "CognitiveAgent"),
      ("CognitiveAgent", "Entity")]
    subrelationEdges := [("likes", "related")]
    operatorClasses := [("partition", "VariableArityRelation")] }

private def sourceResult (source : String) :
    Option DomainGuardElaboration.Result :=
  match SourceElaboration.elaborateSource agentSignature source with
  | .ok sentence => some (DomainGuardElaboration.apply agentSignature sentence)
  | .error _ => none

private def heterogeneousRowSignature : SourceSignature :=
  { domainRestrictions :=
      [⟨"mixed", 1, .object, "Human"⟩,
       ⟨"mixed", 2, .class, "Class"⟩]
    operatorClasses := [("mixed", "VariableArityRelation")] }

private def gappedSignature : SourceSignature :=
  { domainRestrictions :=
      [⟨"gapped", 1, .object, "Entity"⟩,
       ⟨"gapped", 3, .object, "Entity"⟩] }

private def objectGuard
    {ordinary rows : Nat} (className : String) (index : Fin ordinary) :
    Formula String String ordinary rows :=
  .atom (.constant "instance")
    (.term (.var index) (.term (.constant className) .nil))

private def classGuard
    {ordinary rows : Nat} (className : String) (index : Fin ordinary) :
    Formula String String ordinary rows :=
  .atom (.constant "subclass")
    (.term (.var index) (.term (.constant className) .nil))

private def lovesBody : Formula String String 1 0 :=
  .atom (.constant "loves")
    (.term (.var 0) (.term (.constant "Mary") .nil))

private def partitionThirdBody : Formula String String 1 0 :=
  .atom (.constant "partition")
    (.term (.constant "Whole")
      (.term (.constant "Other") (.term (.var 0) .nil)))

private def checks : List (String × Bool) :=
  [ ("minimum arity follows the consecutive domain sequence",
      decide (agentSignature.declaredArity "partition" = 2 &&
        gappedSignature.declaredArity "gapped" = 1)),
    ("universal guard is an antecedent",
      decide (sourceResult "(forall (?X) (loves ?X Mary))" =
        some ⟨.allObject (.implies (objectGuard "CognitiveAgent" 0) lovesBody), []⟩)),
    ("existential guard is a conjunct",
      decide (sourceResult "(exists (?X) (loves ?X Mary))" =
        some ⟨.someObject (.and (objectGuard "CognitiveAgent" 0) lovesBody), []⟩)),
    ("KappaFn guard is a conjunct",
      match sourceResult
          "(equal (KappaFn ?X (loves ?X Mary)) LovingThings)" with
      | some
          { sentence := .equal (.kappa (.and guard body)) (.constant "LovingThings")
            issues := [] } =>
          decide (guard = objectGuard "CognitiveAgent" 0 && body = lovesBody)
      | _ => false),
    ("domainSubclass becomes subclass",
      match sourceResult "(forall (?C) (partition ?C Whole))" with
      | some { sentence := .allObject (.implies guard _), issues := [] } =>
          decide (guard = classGuard "Class" 0)
      | _ => false),
    ("variable arity repeats the final domain",
      decide (sourceResult "(forall (?C) (partition Whole Other ?C))" =
        some ⟨.allObject (.implies (classGuard "Class" 0) partitionThirdBody), []⟩)),
    ("subrelation inherits domain",
      match sourceResult "(forall (?X) (likes ?X Mary))" with
      | some { sentence := .allObject (.implies guard _), issues := [] } =>
          decide (guard = objectGuard "Object" 0)
      | _ => false),
    ("explicit stronger guard is not duplicated",
      match SourceElaboration.elaborateSource agentSignature
          "(forall (?X) (=> (instance ?X Human) (works ?X)))" with
      | .ok sentence =>
          decide ((DomainGuardElaboration.apply agentSignature sentence).sentence = sentence)
      | .error _ => false),
    ("denoted relation domain is explicit",
      decide (sourceResult "(forall (?REL ?X) (?REL ?X))" =
        some ⟨
          .allObject (.allObject
            (.implies
              (.inOperatorDomain (.var 1) 0 (.var 0))
              (.atom (.var 1) (.term (.var 0) .nil)))),
          []⟩)),
    ("denoted function domain is explicit",
      decide (sourceResult
          "(forall (?FUNCTION ?X) (equal (?FUNCTION ?X) Result))" =
        some ⟨
          .allObject (.allObject
            (.implies
              (.inOperatorDomain (.var 1) 0 (.var 0))
              (.equal
                (.application (.var 1) (.term (.var 0) .nil))
                (.constant "Result")))),
          []⟩)),
    ("dependent guard is consumed at the closest referenced binder",
      decide (sourceResult "(forall (?X ?REL) (?REL ?X))" =
        some ⟨
          .allObject (.allObject
            (.implies
              (.inOperatorDomain (.var 0) 0 (.var 1))
              (.atom (.var 0) (.term (.var 1) .nil)))),
          []⟩)),
    ("dependent guard crosses an unused binder",
      decide (sourceResult "(forall (?REL ?X ?UNUSED) (?REL ?X))" =
        some ⟨
          .allObject (.allObject
            (.implies
              (.inOperatorDomain (.var 1) 0 (.var 0))
              (.allObject
                (.atom (.var 2) (.term (.var 1) .nil))))),
          []⟩)),
    ("existential denoted-domain guard is conjunctive",
      decide (sourceResult "(forall (?REL) (exists (?X) (?REL ?X)))" =
        some ⟨
          .allObject (.someObject
            (.and
              (.inOperatorDomain (.var 1) 0 (.var 0))
              (.atom (.var 1) (.term (.var 0) .nil)))),
          []⟩)),
    ("denoted relation row receives an exact-tail guard",
      decide (sourceResult "(forall (?REL @ROW) (?REL @ROW))" =
        some ⟨
          .allObject (.allRow
            (.implies
              (.tailInOperatorDomain (.var 0) 0 (.row 0 .nil))
              (.atom (.var 0) (.row 0 .nil)))),
          []⟩)),
    ("uniform row domain becomes a bounded universal",
      match sourceResult "(forall (@ROW) (partition @ROW))" with
      | some
          { sentence := .allRow
              (.implies
                (.tailInOperatorDomain (.constant "partition") 0
                  (.row 0 .nil))
                (.implies (.allInSpine (.row 0 .nil) guard) _))
            issues := [] } =>
          decide (guard = classGuard "Class" 0)
      | _ => false),
    ("heterogeneous row receives a native exact-tail guard",
      match SourceElaboration.elaborateSource heterogeneousRowSignature
          "(forall (@ROW) (mixed @ROW))" with
      | .ok sentence =>
          match DomainGuardElaboration.apply heterogeneousRowSignature sentence with
          | { sentence := .allRow
                (.implies
                  (.tailInOperatorDomain (.constant "mixed") 0 (.row 0 .nil))
                  (.atom (.constant "mixed") (.row 0 .nil)))
              issues := [] } => true
          | _ => false
      | _ => false),
    ("row tail includes every trailing argument",
      match SourceElaboration.elaborateSource heterogeneousRowSignature
          "(forall (@ROW) (mixed @ROW Suffix))" with
      | .ok sentence =>
          match DomainGuardElaboration.apply heterogeneousRowSignature sentence with
          | { sentence := .allRow
                (.implies
                  (.tailInOperatorDomain (.constant "mixed") 0
                    (.row 0 (.term (.constant "Suffix") .nil)))
                  (.atom (.constant "mixed")
                    (.row 0 (.term (.constant "Suffix") .nil))))
              issues := [] } => true
          | _ => false
      | _ => false) ]

def run : IO UInt32 := do
  let mut failed := 0
  for (name, passed) in checks do
    if passed then
      IO.println s!"PASS: {name}"
    else
      failed := failed + 1
      IO.eprintln s!"FAIL: {name}"
  IO.println s!"domain guard canaries: {checks.length - failed}/{checks.length}"
  pure (if failed = 0 then 0 else 1)

end Mettapedia.Languages.SUMO.Native.DomainGuardCanary

def main : IO UInt32 :=
  Mettapedia.Languages.SUMO.Native.DomainGuardCanary.run
