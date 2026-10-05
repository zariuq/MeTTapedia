import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialFormulaSemantics
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogicSoundness

/-!
# An explicit intuitionistic material-set theory signature

The first-order signature contains equality and membership. The adopted
sentences and formula schemata below are stated independently of any model.
Foundation, Choice, excluded middle and identity reflection are absent from
this theory. Anti-foundation interpretations require their separate graph
class and decoration theorem; they are not inferred from this signature.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSetTheory

open _root_.CategoryTheory ContextualMaterialLogic
open ContextualMaterialFormulaSemantics
universe u v

def equivalent {n : Nat} (first second : Formula n) : Formula n :=
  .both (.imply first second) (.imply second first)

def emptyAxiom : Formula 0 := .exist (.all (.imply (.member 0 1) .bottom))

def pairingAxiom : Formula 0 :=
  .all (.all (.exist (.all (equivalent (.member 0 1) (.either (.equal 0 3) (.equal 0 2))))))

def unionAxiom : Formula 0 :=
  .all (.exist (.all (equivalent (.member 0 1)
    (.exist (.both (.member 0 3) (.member 1 0))))))

def powersetAxiom : Formula 0 :=
  .all (.exist (.all (equivalent (.member 0 1)
    (.all (.imply (.member 0 1) (.member 0 3))))))

def emptyProperty {n : Nat} (value : Fin n) : Formula n :=
  .all (.imply (.member 0 value.succ) .bottom)

def successorProperty {n : Nat} (first second : Fin n) : Formula n :=
  .all (equivalent (.member 0 second.succ) (.either (.member 0 first.succ) (.equal 0 first.succ)))

def infinityAxiom : Formula 0 :=
  .exist (.both (.exist (.both (emptyProperty 0) (.member 0 1)))
    (.all (.imply (.member 0 1) (.exist (.both (successorProperty 1 0) (.member 0 2))))))

def separationAxiom {n : Nat} (formula : Formula (n+1)) : Formula n :=
  .all (.exist (.all (equivalent (.member 0 1)
    (.both (.member 0 2) (substitute behindHeadTwo formula)))))

def collectionPremise {n : Nat} (formula : Formula (n+2)) : Formula (n+1) :=
  .all (.imply (.member 0 1) (.exist (substitute behindTwoOne formula)))

def collectionFirst {n : Nat} (formula : Formula (n+2)) : Formula (n+2) :=
  .all (.imply (.member 0 2) (.exist (.both (.member 0 2) (substitute behindTwoTwo formula))))

def collectionSecond {n : Nat} (formula : Formula (n+2)) : Formula (n+2) :=
  .all (.imply (.member 0 1) (.exist (.both (.member 0 3) (substitute swappedBehindTwoTwo formula))))

def strongCollectionAxiom {n : Nat} (formula : Formula (n+2)) : Formula n :=
  .all (.imply (collectionPremise formula) (.exist (.both (collectionFirst formula) (collectionSecond formula))))

def extensionalityAxiom : Formula 2 :=
  .imply (.all (equivalent (.member 0 1) (.member 0 2))) (.equal 0 1)

/-- These are object-theory sentences, not primitive host axioms. -/
inductive Axiom : {n : Nat} → Formula n → Prop where
  | empty : Axiom emptyAxiom
  | pairing : Axiom pairingAxiom
  | union : Axiom unionAxiom
  | powerset : Axiom powersetAxiom
  | infinity : Axiom infinityAxiom
  | extensionality : Axiom extensionalityAxiom
  | separation {n : Nat} (formula : Formula (n+1)) : Axiom (separationAxiom formula)
  | strongCollection {n : Nat} (formula : Formula (n+2)) : Axiom (strongCollectionAxiom formula)
  | substitution {n m : Nat} {formula : Formula n} (indices : Fin n → Fin m)
      (adopted : Axiom formula) : Axiom (substitute indices formula)

variable {D : Type u} [Category.{u} D] {values : D ⥤ Type v}

/-- A model must validate each named sentence and every schema instance
at every world and assignment. -/
def ValidTheory (model : Model values) : Prop :=
  ∀ {n : Nat} {formula : Formula n}, Axiom formula →
    ∀ (point : D) (environment : Environment values n point), force values model formula point environment

/-- Deduction from adopted set axioms is sound in each actual validating
model. Every assumption is checked as an axiom instance. -/
theorem derivation_valid (model : Model values) (valid : ValidTheory model)
    {n : Nat} {assumptions : List (Formula n)} {conclusion : Formula n}
    (derivation : Derivation assumptions conclusion)
    (adopted : ∀ formula ∈ assumptions, Axiom formula)
    (point : D) (environment : Environment values n point) :
    force values model conclusion point environment :=
  derivation_sound model derivation point environment
    (fun formula available => valid (adopted formula available) point environment)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSetTheory
