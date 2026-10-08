import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedDeduction
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphBoundedFormulaRealization
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedSetTheory

/-!
# A shared first-order material-set law calculus

The adoption syntax is stated independently of its interpretations. It uses
the existing equality/membership formulas and occurrence-indexed logical
proof trees. Bounded Separation retains its authored bounded formula.
Strong Collection and Subset Collection have separate extension constructors;
neither their availability nor a logic or anti-foundation profile is inferred
from the core signature.

The dependency trace records free hypothesis occurrences in a proof tree,
including repeated uses and both branches of a case analysis. It is a
syntactic dependency ledger, rather than a trace of one evaluation branch.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.CommonCore

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula substitute weakenFormula instantiate)
open ContextualMaterialSetTheory (emptyAxiom pairingAxiom unionAxiom infinityAxiom
  extensionalityAxiom separationAxiom strongCollectionAxiom)
open GraphBoundedFormulaRealization (BoundedFormula toFormula)
open GraphRealizedDeduction (Proof)

inductive LawName where
  | empty | pairing | union | infinity | extensionality | boundedSeparation
  | strongCollection | subsetCollection
  deriving DecidableEq, Repr

/-- Adoption of an independently stated law instance. -/
inductive Axiom : {count : Nat} → Formula count → Type where
  | empty : Axiom emptyAxiom
  | pairing : Axiom pairingAxiom
  | union : Axiom unionAxiom
  | infinity : Axiom infinityAxiom
  | extensionality : Axiom extensionalityAxiom
  | boundedSeparation {count : Nat} (body : BoundedFormula (count+1)) :
      Axiom (separationAxiom (toFormula body))
  | substitution {count other : Nat} {body : Formula count}
      (indices : Fin count → Fin other) (adopted : Axiom body) :
      Axiom (substitute indices body)

def Axiom.name {count : Nat} {body : Formula count} : Axiom body → LawName
  | .empty => .empty
  | .pairing => .pairing
  | .union => .union
  | .infinity => .infinity
  | .extensionality => .extensionality
  | .boundedSeparation _ => .boundedSeparation
  | .substitution _ adopted => adopted.name

theorem Axiom.substitution_name {count other : Nat} {body : Formula count}
    (indices : Fin count → Fin other) (adopted : Axiom body) :
    (Axiom.substitution indices adopted).name = adopted.name := rfl

/-- Extensions are explicit, even when a particular model validates them. -/
inductive Extension : {count : Nat} → Formula count → Type where
  | core {count : Nat} {body : Formula count} (adopted : Axiom body) : Extension body
  | strongCollection {count : Nat} (body : Formula (count+2)) :
      Extension (strongCollectionAxiom body)
  | subsetCollection {count : Nat} (body : Formula (count+3)) :
      Extension (GraphRealizedSetTheory.subsetCollectionAxiom body)
  | substitution {count other : Nat} {body : Formula count}
      (indices : Fin count → Fin other) (adopted : Extension body) :
      Extension (substitute indices body)

def Extension.name {count : Nat} {body : Formula count} : Extension body → LawName
  | .core adopted => adopted.name
  | .strongCollection _ => .strongCollection
  | .subsetCollection _ => .subsetCollection
  | .substitution _ adopted => adopted.name

theorem core_extension_injective {count : Nat} {body : Formula count} :
    Function.Injective (Extension.core (count := count) (body := body)) := by
  intro first second same
  cases same
  rfl

/-- Discharge the newest local hypothesis without erasing older positions. -/
def dropHead {length : Nat} : Fin (length+1) → Option (Fin length) :=
  Fin.cases none some

/-- Free hypothesis occurrences used by the authored deduction tree. -/
def freeHypotheses {count : Nat} {assumptions : List (Formula count)}
    {conclusion : Formula count} (proof : Proof assumptions conclusion) :
    List (Fin assumptions.length) :=
  match proof with
  | .hypothesis index => [index]
  | .weakening previous positions _ => (freeHypotheses previous).map positions
  | .bottomElim previous => freeHypotheses previous
  | .bothIntro left right => freeHypotheses left ++ freeHypotheses right
  | .bothLeft previous => freeHypotheses previous
  | .bothRight previous => freeHypotheses previous
  | .eitherLeft previous => freeHypotheses previous
  | .eitherRight previous => freeHypotheses previous
  | .eitherElim previous left right =>
      freeHypotheses previous ++ (freeHypotheses left).filterMap dropHead ++
        (freeHypotheses right).filterMap dropHead
  | .implyIntro previous => (freeHypotheses previous).filterMap dropHead
  | .implyElim previous premise => freeHypotheses previous ++ freeHypotheses premise
  | .allIntro previous => (freeHypotheses previous).map (fun index =>
      ⟨index.val, by simpa using index.isLt⟩)
  | .allElim previous _ => freeHypotheses previous
  | .existIntro _ previous => freeHypotheses previous
  | .existElim previous branch => freeHypotheses previous ++
      ((freeHypotheses branch).filterMap dropHead).map (fun index =>
        ⟨index.val, by simpa using index.isLt⟩)
  | .equalRefl _ => []
  | .equalElim same previous => freeHypotheses same ++ freeHypotheses previous

theorem hypothesis_trace {count : Nat} (assumptions : List (Formula count))
    (index : Fin assumptions.length) :
    freeHypotheses (Proof.hypothesis index) = [index] := rfl

theorem repeated_use_trace {count : Nat} (body : Formula count) :
    freeHypotheses (Proof.bothIntro
      (Proof.hypothesis (assumptions := [body]) 0)
      (Proof.hypothesis (assumptions := [body]) 0)) = [0, 0] := rfl

theorem discharged_hypothesis_trace {count : Nat} (body : Formula count) :
    freeHypotheses (Proof.implyIntro (Proof.hypothesis (assumptions := [body]) 0)) = [] := rfl

/-- A deduction from precisely indexed core law occurrences. -/
structure Derivation {count : Nat} (conclusion : Formula count) where
  assumptions : List (Formula count)
  adopted : (index : Fin assumptions.length) → Axiom assumptions[index.val]
  proof : Proof assumptions conclusion

def Derivation.usedLaws {count : Nat} {conclusion : Formula count}
    (derivation : Derivation conclusion) : List LawName :=
  (freeHypotheses derivation.proof).map (fun index => (derivation.adopted index).name)

def Derivation.assumptionLedger {count : Nat} {conclusion : Formula count}
    (derivation : Derivation conclusion) : List LawName :=
  (List.finRange derivation.assumptions.length).map (fun index => (derivation.adopted index).name)

def Derivation.ofAxiom {count : Nat} {body : Formula count} (adopted : Axiom body) :
    Derivation body where
  assumptions := [body]
  adopted := Fin.cases adopted (fun index => False.elim (Nat.not_lt_zero _ index.isLt))
  proof := .hypothesis (assumptions := [body]) 0

theorem Derivation.ofAxiom_usedLaws {count : Nat} {body : Formula count} (adopted : Axiom body) :
    (Derivation.ofAxiom adopted).usedLaws = [adopted.name] := rfl

structure ExtensionDerivation {count : Nat} (conclusion : Formula count) where
  assumptions : List (Formula count)
  adopted : (index : Fin assumptions.length) → Extension assumptions[index.val]
  proof : Proof assumptions conclusion

def Derivation.toExtension {count : Nat} {conclusion : Formula count}
    (derivation : Derivation conclusion) : ExtensionDerivation conclusion :=
  ⟨derivation.assumptions, fun index => .core (derivation.adopted index), derivation.proof⟩

def ExtensionDerivation.usedLaws {count : Nat} {conclusion : Formula count}
    (derivation : ExtensionDerivation conclusion) : List LawName :=
  (freeHypotheses derivation.proof).map (fun index => (derivation.adopted index).name)

theorem Derivation.extension_usedLaws {count : Nat} {conclusion : Formula count}
    (derivation : Derivation conclusion) :
    derivation.toExtension.usedLaws = derivation.usedLaws := rfl

/-- Regularity, stated for comparison rather than adopted by the core. -/
def foundationAxiom : Formula 0 :=
  .all (.imply (.exist (.member 0 1))
    (.exist (.both (.member 0 1)
      (.all (.imply (.member 0 1) (.imply (.member 0 2) .bottom))))))

/-- Pairing implies that every value belongs to some set. -/
def containmentTheorem : Formula 0 := .all (.exist (.member 1 0))

def containmentProof : Proof [pairingAxiom] containmentTheorem := by
  apply Proof.allIntro
  have first : Proof ([pairingAxiom].map weakenFormula)
      (.all (.exist (.all (ContextualMaterialSetTheory.equivalent (.member 0 1)
        (.either (.equal 0 3) (.equal 0 2)))))) := by
    exact Proof.allElim
      (Proof.hypothesis (assumptions := [pairingAxiom].map weakenFormula) ⟨0, by decide⟩) 0
  have pairSelf : Proof ([pairingAxiom].map weakenFormula)
      (.exist (.all (ContextualMaterialSetTheory.equivalent (.member 0 1)
        (.either (.equal 0 2) (.equal 0 2))))) := by
    exact Proof.allElim first 0
  apply Proof.existElim pairSelf
  apply Proof.existIntro 0
  have pairLaw : Proof
      ((.all (ContextualMaterialSetTheory.equivalent (.member 0 1)
        (.either (.equal 0 2) (.equal 0 2)))) ::
        ([pairingAxiom].map weakenFormula).map weakenFormula)
      (ContextualMaterialSetTheory.equivalent (.member 1 0)
        (.either (.equal 1 1) (.equal 1 1))) := by
    exact Proof.allElim
      (Proof.hypothesis (assumptions :=
        ((.all (ContextualMaterialSetTheory.equivalent (.member 0 1)
          (.either (.equal 0 2) (.equal 0 2)))) ::
          ([pairingAxiom].map weakenFormula).map weakenFormula)) 0) 1
  exact Proof.implyElim (Proof.bothRight pairLaw) (Proof.eitherLeft (Proof.equalRefl 1))

def containmentDerivation : Derivation containmentTheorem where
  assumptions := [pairingAxiom]
  adopted := Fin.cases .pairing (fun index => False.elim (Nat.not_lt_zero _ index.isLt))
  proof := containmentProof

theorem containment_uses_only_pairing : containmentDerivation.usedLaws = [.pairing] := rfl

end Mettapedia.SetTheory.Profiles.CommonCore
