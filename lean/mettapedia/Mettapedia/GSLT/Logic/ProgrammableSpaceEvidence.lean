import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceFinite

/-!
# Derivations with authored rule occurrences and input origins

A source contains an ordered list of definite rules and its input facts indexed
by their origins. A derivation records the actual position of every rule used,
and one typed subderivation for each premise position. Equal clauses at distinct
source positions remain distinct occurrences. Input origins are retained even
when two derivations have the same conclusion.

The lists of rule and input occurrences are computed from the derivation itself.
Origin support removes repeated uses of an origin; neither derivation counts nor
origin disjointness asserts statistical independence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceEvidence

attribute [local instance] Finite.membership

open Core.AnnotatedHorn

universe u v w

structure Source (Atom : Type u) (Origin : Type v) where
  input : Origin → Atom
  rules : List (DefiniteRule Atom)

variable {Atom : Type u} {Origin : Type v}

namespace Source

abbrev RuleIndex (source : Source Atom Origin) := Fin source.rules.length

def rule (source : Source Atom Origin) (index : source.RuleIndex) : DefiniteRule Atom :=
  source.rules.get index

abbrev PremiseIndex (source : Source Atom Origin) (index : source.RuleIndex) :=
  Fin (source.rule index).body.length

def premise (source : Source Atom Origin) (index : source.RuleIndex)
    (position : source.PremiseIndex index) : Atom :=
  (source.rule index).body.get position

end Source

/-- Every rule node names a position in the authored rule list. -/
inductive Derivation (source : Source Atom Origin) : Atom → Type (max u v) where
  | input (origin : Origin) : Derivation source (source.input origin)
  | rule (index : source.RuleIndex)
      (premises : (position : source.PremiseIndex index) →
        Derivation source (source.premise index position)) :
      Derivation source (source.rule index).head

namespace Derivation

variable {source : Source Atom Origin} {atom : Atom}

/-- Input occurrences in premise order, including repeated uses. -/
def origins : {atom : Atom} → Derivation source atom → List Origin
  | _, .input origin => [origin]
  | _, .rule _ premises => (List.ofFn fun position => origins (premises position)).flatten

/-- Authored rule occurrences in preorder. -/
def rules : {atom : Atom} → Derivation source atom → List source.RuleIndex
  | _, .input _ => []
  | _, .rule index premises =>
      index :: (List.ofFn fun position => rules (premises position)).flatten

def root : {atom : Atom} → Derivation source atom → Option source.RuleIndex
  | _, .input _ => none
  | _, .rule index _ => some index

@[simp] theorem origins_input (origin : Origin) :
    (Derivation.input (source := source) origin).origins = [origin] := rfl

@[simp] theorem origins_rule (index : source.RuleIndex)
    (premises : (position : source.PremiseIndex index) →
      Derivation source (source.premise index position)) :
    (Derivation.rule index premises).origins =
      (List.ofFn fun position => (premises position).origins).flatten := rfl

@[simp] theorem root_rule (index : source.RuleIndex)
    (premises : (position : source.PremiseIndex index) →
      Derivation source (source.premise index position)) :
    (Derivation.rule index premises).root = some index := rfl

def originSupport [DecidableEq Origin] (proof : Derivation source atom) : Finset Origin :=
  Finite.support proof.origins

@[simp] theorem mem_originSupport [DecidableEq Origin]
    (proof : Derivation source atom) (origin : Origin) :
    origin ∈ proof.originSupport ↔ origin ∈ proof.origins := Finite.mem_support _ _

/-- Ordinary semantic soundness of the retained, typed proof tree. -/
theorem sound (interpret : Atom → Prop)
    (inputs : ∀ origin, interpret (source.input origin))
    (rules : ∀ index, (∀ position, interpret (source.premise index position)) →
      interpret (source.rule index).head)
    (proof : Derivation source atom) : interpret atom := by
  induction proof with
  | input origin => exact inputs origin
  | rule index premises inductionHypothesis => exact rules index inductionHypothesis

end Derivation

/-- A retained answer carries both its conclusion and its actual derivation. -/
abbrev Receipt (source : Source Atom Origin) := Sigma (Derivation source)

namespace Receipt

variable {source : Source Atom Origin}

def fact (receipt : Receipt source) : Atom := receipt.1

def origins (receipt : Receipt source) : List Origin := receipt.2.origins

def rules (receipt : Receipt source) : List source.RuleIndex := receipt.2.rules

def root (receipt : Receipt source) : Option source.RuleIndex := receipt.2.root

def originSupport [DecidableEq Origin] (receipt : Receipt source) : Finset Origin :=
  receipt.2.originSupport

/-- No input occurrence is used by both receipts. This is only a provenance
condition, not a probability-theoretic independence assertion. -/
def OriginSeparated [DecidableEq Origin] (first second : Receipt source) : Prop :=
  ∀ origin, origin ∈ first.originSupport → origin ∈ second.originSupport → False

theorem not_originSeparated_of_shared [DecidableEq Origin]
    (first second : Receipt source) (origin : Origin)
    (left : origin ∈ first.origins) (right : origin ∈ second.origins) :
    ¬ OriginSeparated first second := by
  intro separated
  exact separated origin ((Finite.mem_support _ _).mpr left) ((Finite.mem_support _ _).mpr right)

end Receipt

end Mettapedia.GSLT.ProgrammableSpaceEvidence
