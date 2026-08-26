import Mettapedia.GSLT.LanguageDef.CertificateGSLTMuCalculusBoundary
import Mettapedia.GSLT.LanguageDef.CertificateGSLTParityAuthority
import Mathlib.Data.Fintype.Prod

/-!
# Finite evaluation games for the modal mu-calculus

This module compiles one modal mu-calculus formula to a finite graph of formula
occurrences.  Ambient variables become observations interpreted by the finite
model.  Bound-variable nodes retain the exact occurrence of their binder, so
fixed points produce graph cycles without unfolding syntax.  The graph and
finite labelled model form the standard verifier/falsifier evaluation game.

The compiler is structural and independent of the denotational satisfaction
relation.  Adequacy of the resulting parity game is a subsequent theorem: this
file establishes the finite arena, its validation laws, the positivity gate,
and executable positive and negative controls.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.EvaluationGame

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity

universe uState uAction uObservation

variable {Action : Type uAction} {State : Type uState}
  {Observation : Type uObservation}

/-! ## Formula-occurrence bytecode -/

inductive FixedPointKind where
  | least
  | greatest
deriving Repr, DecidableEq

namespace FixedPointKind

/-- Negation exchanges least and greatest fixed points. -/
def dual : FixedPointKind → FixedPointKind
  | .least => .greatest
  | .greatest => .least

/-- The fixed-point kind observed at a game position.  Negative polarity
dually exchanges least and greatest. -/
def atPolarity (kind : FixedPointKind) (polarity : Bool) : FixedPointKind :=
  if polarity then kind else kind.dual

@[simp] theorem atPolarity_true (kind : FixedPointKind) :
    kind.atPolarity true = kind := rfl

@[simp] theorem atPolarity_false (kind : FixedPointKind) :
    kind.atPolarity false = kind.dual := rfl

@[simp] theorem dual_dual (kind : FixedPointKind) : kind.dual.dual = kind := by
  cases kind <;> rfl

end FixedPointKind

/-- A formula variable is either an ambient observation supplied by the model
or a back-edge to a fixed-point binder allocated during compilation. -/
inductive VariableReference (Observation : Type uObservation) where
  | observation (label : Observation)
  | binder (address : Nat)
deriving Repr, DecidableEq

/-- One formula occurrence.  Every numeric target is an absolute node index
in the compiled program. -/
inductive Node (Action : Type uAction) (Observation : Type uObservation) where
  | truth (value : Bool)
  | observation (label : Observation)
  | negation (child : Nat)
  | conjunction (left right : Nat)
  | disjunction (left right : Nat)
  | diamond (action : Action) (child : Nat)
  | box (action : Action) (child : Nat)
  | fixedPoint (kind : FixedPointKind) (depth child : Nat)
  | variable (binder : Nat)
deriving Repr, DecidableEq

namespace Node

/-- All graph targets mentioned by one node. -/
def targets : Node Action Observation → List Nat
  | .truth _ => []
  | .observation _ => []
  | .negation child => [child]
  | .conjunction left right | .disjunction left right => [left, right]
  | .diamond _ child | .box _ child => [child]
  | .fixedPoint _ _ child => [child]
  | .variable binder => [binder]

end Node

/-- Extend the de Bruijn binder-address environment underneath one fixed-point
binder.  Index zero points to the newly allocated binder occurrence. -/
def extendVariableReferences {n : Nat}
    (references : Fin n → VariableReference Observation) (current : Nat) :
    Fin (n + 1) → VariableReference Observation :=
  Fin.cases (.binder current) references

/-- Structural preorder compilation.  `offset` is the absolute address of the
current formula occurrence and `depth` is its fixed-point nesting depth. -/
def compileAt {n : Nat} (offset depth : Nat)
    (references : Fin n → VariableReference Observation) :
    Formula Action n → List (Node Action Observation)
  | .tt => [.truth true]
  | .ff => [.truth false]
  | .neg formula =>
      .negation (offset + 1) :: compileAt (offset + 1) depth references formula
  | .conj left right =>
      .conjunction (offset + 1) (offset + 1 + left.size) ::
        (compileAt (offset + 1) depth references left ++
          compileAt (offset + 1 + left.size) depth references right)
  | .disj left right =>
      .disjunction (offset + 1) (offset + 1 + left.size) ::
        (compileAt (offset + 1) depth references left ++
          compileAt (offset + 1 + left.size) depth references right)
  | .diamond action formula =>
      .diamond action (offset + 1) ::
        compileAt (offset + 1) depth references formula
  | .box action formula =>
      .box action (offset + 1) ::
        compileAt (offset + 1) depth references formula
  | .mu body =>
      .fixedPoint .least depth (offset + 1) ::
        compileAt (offset + 1) (depth + 1)
          (extendVariableReferences references offset) body
  | .nu body =>
      .fixedPoint .greatest depth (offset + 1) ::
        compileAt (offset + 1) (depth + 1)
          (extendVariableReferences references offset) body
  | .var index =>
      match references index with
      | .observation label => [.observation label]
      | .binder address => [.variable address]

theorem compileAt_length {n : Nat} (offset depth : Nat)
    (references : Fin n → VariableReference Observation)
    (formula : Formula Action n) :
    (compileAt offset depth references formula).length = formula.size := by
  induction formula generalizing offset depth with
  | tt => rfl
  | ff => rfl
  | neg formula inductionHypothesis =>
      simp [compileAt, Formula.size, inductionHypothesis, Nat.add_comm]
  | conj left right leftHypothesis rightHypothesis =>
      simp [compileAt, Formula.size, leftHypothesis, rightHypothesis,
        Nat.add_comm, Nat.add_assoc]
  | disj left right leftHypothesis rightHypothesis =>
      simp [compileAt, Formula.size, leftHypothesis, rightHypothesis,
        Nat.add_comm, Nat.add_assoc]
  | diamond action formula inductionHypothesis =>
      simp [compileAt, Formula.size, inductionHypothesis, Nat.add_comm]
  | box action formula inductionHypothesis =>
      simp [compileAt, Formula.size, inductionHypothesis, Nat.add_comm]
  | mu body inductionHypothesis =>
      simp [compileAt, Formula.size, inductionHypothesis, Nat.add_comm]
  | nu body inductionHypothesis =>
      simp [compileAt, Formula.size, inductionHypothesis, Nat.add_comm]
  | var index =>
      cases reference : references index <;>
        simp [compileAt, reference, Formula.size]

theorem formula_size_positive {n : Nat} (formula : Formula Action n) :
    0 < formula.size := by
  cases formula <;> simp [Formula.size]

/-- Every binder back-edge inherited by a recursive compilation lies before
the current formula occurrence.  Ambient observations carry no address. -/
def ReferencesBelow {n : Nat}
    (references : Fin n → VariableReference Observation)
    (offset : Nat) : Prop :=
  ∀ index, match references index with
    | .observation _ => True
    | .binder address => address < offset

theorem extendVariableReferences_below {n : Nat}
    (references : Fin n → VariableReference Observation)
    (offset : Nat) (below : ReferencesBelow references offset) :
    ReferencesBelow (extendVariableReferences references offset) (offset + 1) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · simp [extendVariableReferences]
  · intro previous
    cases reference : references previous with
    | observation label => simp [extendVariableReferences, reference]
    | binder address =>
        simpa [extendVariableReferences, reference] using
          Nat.lt_succ_of_lt (by simpa [reference] using below previous)

/-- Every binder reference in a compiler environment points to an actual
fixed-point node in the already-emitted prefix.  This is strictly stronger
than the numeric `ReferencesBelow` invariant. -/
def ReferencesPointToFixedPoints {n : Nat}
    (emitted : List (Node Action Observation))
    (references : Fin n → VariableReference Observation) : Prop :=
  ∀ index, match references index with
    | .observation _ => True
    | .binder address =>
        ∃ kind depth child,
          emitted[address]? = some (.fixedPoint kind depth child)

theorem ReferencesPointToFixedPoints.append {n : Nat}
    {emitted : List (Node Action Observation)}
    {references : Fin n → VariableReference Observation}
    (valid : ReferencesPointToFixedPoints emitted references)
    (suffix : List (Node Action Observation)) :
    ReferencesPointToFixedPoints (emitted ++ suffix) references := by
  intro index
  cases reference : references index with
  | observation label => trivial
  | binder address =>
      obtain ⟨kind, depth, child, lookup⟩ := by
        simpa [ReferencesPointToFixedPoints, reference] using valid index
      refine ⟨kind, depth, child, ?_⟩
      rw [List.getElem?_append_left
        (List.getElem?_eq_some_iff.mp lookup).1]
      exact lookup

theorem ReferencesPointToFixedPoints.extend {n : Nat}
    {emitted : List (Node Action Observation)}
    {references : Fin n → VariableReference Observation}
    (valid : ReferencesPointToFixedPoints emitted references)
    (kind : FixedPointKind) (depth child : Nat) :
    ReferencesPointToFixedPoints
      (emitted ++ [.fixedPoint kind depth child])
      (extendVariableReferences references emitted.length) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · simp [extendVariableReferences]
  · intro previous
    cases reference : references previous with
    | observation label =>
        simp [extendVariableReferences, reference]
    | binder address =>
        simpa [ReferencesPointToFixedPoints, extendVariableReferences,
          reference] using (valid.append [.fixedPoint kind depth child]) previous

/-- Structural compilation preserves the stronger binder invariant: every
emitted variable back-edge resolves to a fixed-point node in the complete
table, including across sibling subtrees and nested binders. -/
theorem compileAt_variable_target_fixedPoint {n : Nat}
    (offset depth : Nat)
    (references : Fin n → VariableReference Observation)
    (formula : Formula Action n)
    (emitted suffix : List (Node Action Observation))
    (offsetEq : emitted.length = offset)
    (referencesValid : ReferencesPointToFixedPoints emitted references)
    (binder : Nat)
    (member : .variable binder ∈ compileAt offset depth references formula) :
    ∃ kind binderDepth child,
      (emitted ++ (compileAt offset depth references formula ++ suffix))[binder]? =
        some (.fixedPoint kind binderDepth child) := by
  induction formula generalizing offset depth emitted suffix binder with
  | tt => simp [compileAt] at member
  | ff => simp [compileAt] at member
  | neg formula inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      · rw [show emitted ++
              (compileAt offset depth references (.neg formula) ++ suffix) =
            (emitted ++ [.negation (offset + 1)]) ++
              (compileAt (offset + 1) depth references formula ++ suffix) by
            simp [compileAt, List.append_assoc]]
        exact inductionHypothesis (offset := offset + 1) (depth := depth)
            (references := references)
            (emitted := emitted ++ [.negation (offset + 1)])
            (suffix := suffix) (binder := binder)
            (offsetEq := by simp [offsetEq])
            (referencesValid :=
              referencesValid.append [.negation (offset + 1)])
            (member := member)
  | conj left right leftHypothesis rightHypothesis =>
      simp only [compileAt, List.mem_cons, List.mem_append] at member
      rcases member with impossible | member | member
      · cases impossible
      · rw [show emitted ++
              (compileAt offset depth references (.conj left right) ++ suffix) =
            (emitted ++
              [.conjunction (offset + 1) (offset + 1 + left.size)]) ++
              (compileAt (offset + 1) depth references left ++
                (compileAt (offset + 1 + left.size) depth references right ++
                  suffix)) by
            simp [compileAt, List.append_assoc]]
        exact leftHypothesis (offset := offset + 1) (depth := depth)
            (references := references)
            (emitted := emitted ++
              [.conjunction (offset + 1) (offset + 1 + left.size)])
            (suffix := compileAt (offset + 1 + left.size) depth references right ++
              suffix)
            (binder := binder) (offsetEq := by simp [offsetEq])
            (referencesValid := referencesValid.append
              [.conjunction (offset + 1) (offset + 1 + left.size)])
            (member := member)
      · rw [show emitted ++
              (compileAt offset depth references (.conj left right) ++ suffix) =
            (emitted ++
                [.conjunction (offset + 1) (offset + 1 + left.size)] ++
                  compileAt (offset + 1) depth references left) ++
              (compileAt (offset + 1 + left.size) depth references right ++
                suffix) by
            simp [compileAt, List.append_assoc]]
        exact rightHypothesis (offset := offset + 1 + left.size) (depth := depth)
            (references := references)
            (emitted := emitted ++
              [.conjunction (offset + 1) (offset + 1 + left.size)] ++
                compileAt (offset + 1) depth references left)
            (suffix := suffix) (binder := binder)
            (offsetEq := by
              simp [compileAt_length, offsetEq, Nat.add_comm, Nat.add_assoc])
            (referencesValid := (referencesValid.append
              [.conjunction (offset + 1) (offset + 1 + left.size)]).append
                (compileAt (offset + 1) depth references left))
            (member := member)
  | disj left right leftHypothesis rightHypothesis =>
      simp only [compileAt, List.mem_cons, List.mem_append] at member
      rcases member with impossible | member | member
      · cases impossible
      · rw [show emitted ++
              (compileAt offset depth references (.disj left right) ++ suffix) =
            (emitted ++
              [.disjunction (offset + 1) (offset + 1 + left.size)]) ++
              (compileAt (offset + 1) depth references left ++
                (compileAt (offset + 1 + left.size) depth references right ++
                  suffix)) by
            simp [compileAt, List.append_assoc]]
        exact leftHypothesis (offset := offset + 1) (depth := depth)
            (references := references)
            (emitted := emitted ++
              [.disjunction (offset + 1) (offset + 1 + left.size)])
            (suffix := compileAt (offset + 1 + left.size) depth references right ++
              suffix)
            (binder := binder) (offsetEq := by simp [offsetEq])
            (referencesValid := referencesValid.append
              [.disjunction (offset + 1) (offset + 1 + left.size)])
            (member := member)
      · rw [show emitted ++
              (compileAt offset depth references (.disj left right) ++ suffix) =
            (emitted ++
                [.disjunction (offset + 1) (offset + 1 + left.size)] ++
                  compileAt (offset + 1) depth references left) ++
              (compileAt (offset + 1 + left.size) depth references right ++
                suffix) by
            simp [compileAt, List.append_assoc]]
        exact rightHypothesis (offset := offset + 1 + left.size) (depth := depth)
            (references := references)
            (emitted := emitted ++
              [.disjunction (offset + 1) (offset + 1 + left.size)] ++
                compileAt (offset + 1) depth references left)
            (suffix := suffix) (binder := binder)
            (offsetEq := by
              simp [compileAt_length, offsetEq, Nat.add_comm, Nat.add_assoc])
            (referencesValid := (referencesValid.append
              [.disjunction (offset + 1) (offset + 1 + left.size)]).append
                (compileAt (offset + 1) depth references left))
            (member := member)
  | diamond action formula inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      · rw [show emitted ++
              (compileAt offset depth references (.diamond action formula) ++
                suffix) =
            (emitted ++ [.diamond action (offset + 1)]) ++
              (compileAt (offset + 1) depth references formula ++ suffix) by
            simp [compileAt, List.append_assoc]]
        exact inductionHypothesis (offset := offset + 1) (depth := depth)
            (references := references)
            (emitted := emitted ++ [.diamond action (offset + 1)])
            (suffix := suffix) (binder := binder)
            (offsetEq := by simp [offsetEq])
            (referencesValid :=
              referencesValid.append [.diamond action (offset + 1)])
            (member := member)
  | box action formula inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      · rw [show emitted ++
              (compileAt offset depth references (.box action formula) ++ suffix) =
            (emitted ++ [.box action (offset + 1)]) ++
              (compileAt (offset + 1) depth references formula ++ suffix) by
            simp [compileAt, List.append_assoc]]
        exact inductionHypothesis (offset := offset + 1) (depth := depth)
            (references := references)
            (emitted := emitted ++ [.box action (offset + 1)])
            (suffix := suffix) (binder := binder)
            (offsetEq := by simp [offsetEq])
            (referencesValid := referencesValid.append [.box action (offset + 1)])
            (member := member)
  | mu body inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      · rw [show emitted ++
              (compileAt offset depth references (.mu body) ++ suffix) =
            (emitted ++ [.fixedPoint .least depth (offset + 1)]) ++
              (compileAt (offset + 1) (depth + 1)
                (extendVariableReferences references offset) body ++ suffix) by
            simp [compileAt, List.append_assoc]]
        exact inductionHypothesis (offset := offset + 1) (depth := depth + 1)
            (references := extendVariableReferences references offset)
            (emitted := emitted ++ [.fixedPoint .least depth (offset + 1)])
            (suffix := suffix) (binder := binder)
            (offsetEq := by simp [offsetEq])
            (referencesValid := by
              simpa [offsetEq] using
                referencesValid.extend .least depth (offset + 1))
            (member := member)
  | nu body inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      · rw [show emitted ++
              (compileAt offset depth references (.nu body) ++ suffix) =
            (emitted ++ [.fixedPoint .greatest depth (offset + 1)]) ++
              (compileAt (offset + 1) (depth + 1)
                (extendVariableReferences references offset) body ++ suffix) by
            simp [compileAt, List.append_assoc]]
        exact inductionHypothesis (offset := offset + 1) (depth := depth + 1)
            (references := extendVariableReferences references offset)
            (emitted := emitted ++ [.fixedPoint .greatest depth (offset + 1)])
            (suffix := suffix) (binder := binder)
            (offsetEq := by simp [offsetEq])
            (referencesValid := by
              simpa [offsetEq] using
                referencesValid.extend .greatest depth (offset + 1))
            (member := member)
  | var index =>
      cases reference : references index with
      | observation label => simp [compileAt, reference] at member
      | binder address =>
          simp [compileAt, reference] at member
          subst binder
          obtain ⟨kind, binderDepth, child, lookup⟩ := by
            simpa [ReferencesPointToFixedPoints, reference] using
              referencesValid index
          refine ⟨kind, binderDepth, child, ?_⟩
          rw [List.getElem?_append_left
            (List.getElem?_eq_some_iff.mp lookup).1]
          exact lookup

/-- Every pointer emitted by structural compilation remains within the
compiled formula's contiguous node interval. -/
theorem compileAt_references_below {n : Nat} (offset depth : Nat)
    (references : Fin n → VariableReference Observation)
    (formula : Formula Action n)
    (referencesBelow : ReferencesBelow references offset)
    {node : Node Action Observation}
    (nodeMember : node ∈ compileAt offset depth references formula)
    {target : Nat} (targetMember : target ∈ node.targets) :
    target < offset + formula.size := by
  induction formula generalizing offset depth node target with
  | tt =>
      simp [compileAt] at nodeMember
      subst node
      simp [Node.targets] at targetMember
  | ff =>
      simp [compileAt] at nodeMember
      subst node
      simp [Node.targets] at targetMember
  | neg formula inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at nodeMember
      rcases nodeMember with rfl | nodeMember
      · simp [Node.targets] at targetMember
        subst target
        have sizePositive := formula_size_positive formula
        simp [Formula.size] at ⊢
        omega
      · have belowChild := inductionHypothesis (offset := offset + 1)
            (depth := depth) references
            (fun index => by
              cases reference : references index with
              | observation label => simp
              | binder address =>
                  simpa [reference] using Nat.lt_succ_of_lt
                    (by simpa [reference] using referencesBelow index))
            nodeMember targetMember
        simp [Formula.size] at ⊢
        omega
  | conj left right leftHypothesis rightHypothesis =>
      simp only [compileAt, List.mem_cons, List.mem_append] at nodeMember
      rcases nodeMember with rfl | nodeMember | nodeMember
      · simp [Node.targets] at targetMember
        rcases targetMember with rfl | rfl
        · have leftPositive := formula_size_positive left
          simp [Formula.size]
          omega
        · have rightPositive := formula_size_positive right
          simp [Formula.size]
          omega
      · have belowLeft := leftHypothesis (offset := offset + 1)
            (depth := depth) references
            (fun index => by
              cases reference : references index with
              | observation label => simp
              | binder address =>
                  simpa [reference] using Nat.lt_succ_of_lt
                    (by simpa [reference] using referencesBelow index))
            nodeMember targetMember
        simp [Formula.size] at ⊢
        omega
      · have belowRight := rightHypothesis
            (offset := offset + 1 + left.size) (depth := depth) references
            (fun index => by
              cases reference : references index with
              | observation label => simp
              | binder address =>
                  exact lt_of_lt_of_le
                    (by simpa [reference] using referencesBelow index) (by omega))
            nodeMember targetMember
        simp [Formula.size] at ⊢
        omega
  | disj left right leftHypothesis rightHypothesis =>
      simp only [compileAt, List.mem_cons, List.mem_append] at nodeMember
      rcases nodeMember with rfl | nodeMember | nodeMember
      · simp [Node.targets] at targetMember
        rcases targetMember with rfl | rfl
        · have leftPositive := formula_size_positive left
          simp [Formula.size]
          omega
        · have rightPositive := formula_size_positive right
          simp [Formula.size]
          omega
      · have belowLeft := leftHypothesis (offset := offset + 1)
            (depth := depth) references
            (fun index => by
              cases reference : references index with
              | observation label => simp
              | binder address =>
                  simpa [reference] using Nat.lt_succ_of_lt
                    (by simpa [reference] using referencesBelow index))
            nodeMember targetMember
        simp [Formula.size] at ⊢
        omega
      · have belowRight := rightHypothesis
            (offset := offset + 1 + left.size) (depth := depth) references
            (fun index => by
              cases reference : references index with
              | observation label => simp
              | binder address =>
                  exact lt_of_lt_of_le
                    (by simpa [reference] using referencesBelow index) (by omega))
            nodeMember targetMember
        simp [Formula.size] at ⊢
        omega
  | diamond action formula inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at nodeMember
      rcases nodeMember with rfl | nodeMember
      · simp [Node.targets] at targetMember
        subst target
        have sizePositive := formula_size_positive formula
        simp [Formula.size]
        omega
      · have belowChild := inductionHypothesis (offset := offset + 1)
            (depth := depth) references
            (fun index => by
              cases reference : references index with
              | observation label => simp
              | binder address =>
                  simpa [reference] using Nat.lt_succ_of_lt
                    (by simpa [reference] using referencesBelow index))
            nodeMember targetMember
        simp [Formula.size] at ⊢
        omega
  | box action formula inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at nodeMember
      rcases nodeMember with rfl | nodeMember
      · simp [Node.targets] at targetMember
        subst target
        have sizePositive := formula_size_positive formula
        simp [Formula.size]
        omega
      · have belowChild := inductionHypothesis (offset := offset + 1)
            (depth := depth) references
            (fun index => by
              cases reference : references index with
              | observation label => simp
              | binder address =>
                  simpa [reference] using Nat.lt_succ_of_lt
                    (by simpa [reference] using referencesBelow index))
            nodeMember targetMember
        simp [Formula.size] at ⊢
        omega
  | mu body inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at nodeMember
      rcases nodeMember with rfl | nodeMember
      · simp [Node.targets] at targetMember
        subst target
        have sizePositive := formula_size_positive body
        simp [Formula.size]
        omega
      · have belowChild := inductionHypothesis (offset := offset + 1)
            (depth := depth + 1) (extendVariableReferences references offset)
            (extendVariableReferences_below references offset referencesBelow)
            nodeMember targetMember
        simp [Formula.size] at ⊢
        omega
  | nu body inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at nodeMember
      rcases nodeMember with rfl | nodeMember
      · simp [Node.targets] at targetMember
        subst target
        have sizePositive := formula_size_positive body
        simp [Formula.size]
        omega
      · have belowChild := inductionHypothesis (offset := offset + 1)
            (depth := depth + 1) (extendVariableReferences references offset)
            (extendVariableReferences_below references offset referencesBelow)
            nodeMember targetMember
        simp [Formula.size] at ⊢
        omega
  | var index =>
      cases reference : references index with
      | observation label =>
          simp [compileAt, reference] at nodeMember
          subst node
          simp [Node.targets] at targetMember
      | binder address =>
          simp [compileAt, reference] at nodeMember
          subst node
          simp [Node.targets] at targetMember
          subst target
          simp [Formula.size]
          exact Nat.lt_succ_of_lt
            (by simpa [reference] using referencesBelow index)

/-- Every fixed-point depth emitted by structural compilation lies below the
initial depth plus the source formula's fixed-point nesting depth. -/
theorem compileAt_fixedPoint_depth_lt {n : Nat} (offset depth : Nat)
    (references : Fin n → VariableReference Observation)
    (formula : Formula Action n) (kind : FixedPointKind)
    (binderDepth child : Nat)
    (member : .fixedPoint kind binderDepth child ∈
      compileAt offset depth references formula) :
    binderDepth < depth + formula.altDepth := by
  induction formula generalizing offset depth binderDepth child with
  | tt => simp [compileAt] at member
  | ff => simp [compileAt] at member
  | neg formula inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      · simpa [Formula.altDepth] using
          inductionHypothesis (offset + 1) depth references
            binderDepth child member
  | conj left right leftHypothesis rightHypothesis =>
      simp only [compileAt, List.mem_cons, List.mem_append] at member
      rcases member with impossible | member | member
      · cases impossible
      · exact (leftHypothesis (offset + 1) depth references
          binderDepth child member).trans_le
          (Nat.add_le_add_left (Nat.le_max_left _ _) depth)
      · exact (rightHypothesis (offset + 1 + left.size) depth references
          binderDepth child member).trans_le
            (Nat.add_le_add_left (Nat.le_max_right _ _) depth)
  | disj left right leftHypothesis rightHypothesis =>
      simp only [compileAt, List.mem_cons, List.mem_append] at member
      rcases member with impossible | member | member
      · cases impossible
      · exact (leftHypothesis (offset + 1) depth references
          binderDepth child member).trans_le
          (Nat.add_le_add_left (Nat.le_max_left _ _) depth)
      · exact (rightHypothesis (offset + 1 + left.size) depth references
          binderDepth child member).trans_le
            (Nat.add_le_add_left (Nat.le_max_right _ _) depth)
  | diamond action formula inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      · simpa [Formula.altDepth] using
          inductionHypothesis (offset + 1) depth references
            binderDepth child member
  | box action formula inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at member
      rcases member with impossible | member
      · cases impossible
      · simpa [Formula.altDepth] using
          inductionHypothesis (offset + 1) depth references
            binderDepth child member
  | mu body inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at member
      rcases member with member | member
      · cases member
        simp [Formula.altDepth]
      · have bound := inductionHypothesis (offset + 1) (depth + 1)
          (extendVariableReferences references offset) binderDepth child member
        simpa [Formula.altDepth, Nat.add_assoc] using bound
  | nu body inductionHypothesis =>
      simp only [compileAt, List.mem_cons] at member
      rcases member with member | member
      · cases member
        simp [Formula.altDepth]
      · have bound := inductionHypothesis (offset + 1) (depth + 1)
          (extendVariableReferences references offset) binderDepth child member
        simpa [Formula.altDepth, Nat.add_assoc] using bound
  | var index =>
      cases reference : references index <;>
        simp [compileAt, reference] at member

/-- A compiled closed formula.  Positivity is retained as an admission bit,
not inferred from the existence of graph nodes. -/
structure Program (Action : Type uAction) (Observation : Type uObservation) where
  variableCount : Nat
  formula : Formula Action variableCount
  observation : Fin variableCount → Observation
  positive : fixedPointsPositive formula = true

namespace Program

def nodes (program : Program Action Observation) : List (Node Action Observation) :=
  compileAt 0 0 (fun index => .observation (program.observation index))
    program.formula

theorem nodes_length (program : Program Action Observation) :
    program.nodes.length = program.formula.size :=
  compileAt_length 0 0
    (fun index => .observation (program.observation index)) program.formula

/-- Executable validation for the semantic kind of every variable back-edge.
Bounds checking alone cannot distinguish a binder from an arbitrary in-range
node. -/
def binderTargetsValidNodes (nodes : List (Node Action Observation)) : Bool :=
  nodes.all fun node =>
    match node with
    | .variable binder =>
        match nodes[binder]? with
        | some (.fixedPoint _ _ _) => true
        | _ => false
    | _ => true

def binderTargetsValid (program : Program Action Observation) : Bool :=
  binderTargetsValidNodes program.nodes

/-- Every back-edge emitted for a generated program resolves to a real
fixed-point occurrence in the same node table. -/
theorem variable_target_fixedPoint (program : Program Action Observation)
    (binder : Nat) (member : .variable binder ∈ program.nodes) :
    ∃ kind depth child,
      program.nodes[binder]? = some (.fixedPoint kind depth child) := by
  simpa [nodes] using
    compileAt_variable_target_fixedPoint 0 0
      (fun index => .observation (program.observation index)) program.formula
      [] [] rfl (fun _ => trivial) binder member

/-- Every generated binder depth lies within the reverse-depth priority
ceiling derived from the source formula. -/
theorem fixedPoint_depth_le_priorityCeiling
    (program : Program Action Observation)
    (kind : FixedPointKind) (depth child : Nat)
    (member : .fixedPoint kind depth child ∈ program.nodes) :
    depth ≤ program.formula.altDepth - 1 := by
  have strict : depth < program.formula.altDepth := by
    simpa [nodes] using compileAt_fixedPoint_depth_lt 0 0
      (fun index => .observation (program.observation index))
      program.formula kind depth child member
  omega

/-- The generated compiler always passes the stronger binder-target gate. -/
theorem binderTargetsValid_eq_true (program : Program Action Observation) :
    program.binderTargetsValid = true := by
  simp only [binderTargetsValid, binderTargetsValidNodes, List.all_eq_true]
  intro node member
  cases node with
  | «variable» binder =>
      obtain ⟨kind, depth, child, lookup⟩ :=
        program.variable_target_fixedPoint binder member
      simp [lookup]
  | _ => rfl

def root (program : Program Action Observation) : Fin program.nodes.length :=
  ⟨0, by rw [nodes_length]; exact formula_size_positive program.formula⟩

/-- Executable graph well-formedness: every referenced address lies inside
the compiled node table and every variable back-edge targets a fixed-point
node. -/
def graphValid (program : Program Action Observation) : Bool :=
  (program.nodes.all fun node =>
    node.targets.all fun target => decide (target < program.nodes.length)) &&
      program.binderTargetsValid

/-- Structural compilation cannot emit a dangling pointer or a semantically
ill-kinded binder back-edge. -/
theorem graphValid_eq_true (program : Program Action Observation) :
    program.graphValid = true := by
  rw [graphValid, Bool.and_eq_true]
  constructor
  · simp only [List.all_eq_true, decide_eq_true_eq]
    intro node nodeMember target targetMember
    rw [nodes_length]
    simpa using compileAt_references_below 0 0
      (fun index => .observation (program.observation index)) program.formula
      (fun _ => trivial) nodeMember targetMember
  · exact program.binderTargetsValid_eq_true

end Program

/-! ## Finite labelled transition systems -/

/-- The evaluation-game compiler consumes the executable finite presentation
of an LTS.  Its propositional shadow is an ordinary `LTS`. -/
structure FiniteLTS (State : Type uState) (Action : Type uAction)
    [Fintype State] where
  edge : State → Action → State → Bool

namespace FiniteLTS

variable {State : Type uState} {Action : Type uAction} [Fintype State]

def toLTS (system : FiniteLTS State Action) : LTS State Action where
  trans source action target := system.edge source action target = true

def hasSuccessor (system : FiniteLTS State Action)
    (state : State) (action : Action) : Bool :=
  decide (∃ target, system.edge state action target = true)

theorem hasSuccessor_eq_true_iff (system : FiniteLTS State Action)
    (state : State) (action : Action) :
    system.hasSuccessor state action = true ↔
      ∃ target, system.edge state action target = true := by
  simp [hasSuccessor]

theorem hasSuccessor_eq_false_iff (system : FiniteLTS State Action)
    (state : State) (action : Action) :
    system.hasSuccessor state action = false ↔
      ∀ target, system.edge state action target = false := by
  simp [hasSuccessor]

end FiniteLTS

/-- A finite model is an executable LTS together with the valuation of ambient
observations.  Fixed-point variables never enter this valuation: the compiler
turns them into graph back-edges. -/
structure FiniteModel (State : Type uState) (Action : Type uAction)
    (Observation : Type uObservation) [Fintype State] where
  system : FiniteLTS State Action
  holds : State → Observation → Bool

namespace FiniteModel

variable {State : Type uState} {Action : Type uAction}
  {Observation : Type uObservation} [Fintype State]

/-- Propositional interpretation of one executable observation label. -/
def observationSet (model : FiniteModel State Action Observation)
    (label : Observation) : Set State :=
  {state | model.holds state label = true}

end FiniteModel

/-! ## Evaluation-game realization -/

/-- A game position records an LTS state, a formula occurrence, and semantic
polarity.  `true` polarity asks the verifier to establish the formula;
`false` asks it to establish its negation. -/
structure Position (State : Type uState) [Fintype State]
    (Action : Type uAction) (Observation : Type uObservation)
    (program : Program Action Observation) where
  state : State
  address : Fin program.nodes.length
  polarity : Bool

def positionEquiv (State : Type uState) [Fintype State]
    (Action : Type uAction) (Observation : Type uObservation)
    (program : Program Action Observation) :
    Position State Action Observation program ≃
      State × Fin program.nodes.length × Bool where
  toFun position := (position.state, position.address, position.polarity)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv position := by cases position; rfl
  right_inv data := by rcases data with ⟨state, address, polarity⟩; rfl

instance positionDecidableEq (State : Type uState) [Fintype State]
    [DecidableEq State] (Action : Type uAction) (Observation : Type uObservation)
    (program : Program Action Observation) :
    DecidableEq (Position State Action Observation program) := fun left right =>
  if equal : positionEquiv State Action Observation program left =
      positionEquiv State Action Observation program right then
    isTrue ((positionEquiv State Action Observation program).injective equal)
  else
    isFalse fun positionsEqual => equal (congrArg _ positionsEqual)

instance positionFintype (State : Type uState) [Fintype State]
    (Action : Type uAction) (Observation : Type uObservation)
    (program : Program Action Observation) :
    Fintype (Position State Action Observation program) :=
  Fintype.ofEquiv _ (positionEquiv State Action Observation program).symm

namespace Program

variable {State : Type uState} {Action : Type uAction}
  {Observation : Type uObservation}
  [Fintype State] [DecidableEq State]

def initial (program : Program Action Observation) (state : State) :
    Position State Action Observation program :=
  ⟨state, program.root, true⟩

/-- Denotational environment induced by the executable model's observation
table. -/
def semanticEnv (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    Env State program.variableCount :=
  fun index => model.observationSet (program.observation index)

/-- Denotational meaning against the same finite presentation used to build
the parity arena. -/
def Denotes (program : Program Action Observation)
    (model : FiniteModel State Action Observation) (state : State) : Prop :=
  satisfies model.system.toLTS (program.semanticEnv model) program.formula state

def nodeAt (program : Program Action Observation)
    (position : Position State Action Observation program) :
    Node Action Observation :=
  program.nodes.get position.address

omit [DecidableEq State] in
/-- Every target of the node selected by a game position is a valid address
in the same compiled program. -/
theorem target_lt_nodes_length (program : Program Action Observation)
    (position : Position State Action Observation program) (target : Nat)
    (member : target ∈ (program.nodeAt position).targets) :
    target < program.nodes.length := by
  have nodeMember : program.nodeAt position ∈ program.nodes := by
    exact List.get_mem program.nodes position.address
  rw [program.nodes_length]
  simpa [EvaluationGame.Program.nodes] using
    compileAt_references_below 0 0
      (fun index => .observation (program.observation index)) program.formula
      (fun _ => trivial) nodeMember member

def addressIs {program : Program Action Observation}
    (position : Position State Action Observation program) (address : Nat) : Bool :=
  position.address.val == address

def sameStateAndPolarity
    {program : Program Action Observation}
    (source target : Position State Action Observation program) : Bool :=
  decide (target.state = source.state) && decide (target.polarity = source.polarity)

def toggledStateAndPolarity
    {program : Program Action Observation}
    (source target : Position State Action Observation program) : Bool :=
  decide (target.state = source.state) && decide (target.polarity = !source.polarity)

def modalEdge {program : Program Action Observation}
    (system : FiniteLTS State Action)
    (source target : Position State Action Observation program)
    (action : Action) (child : Nat) : Bool :=
  if system.hasSuccessor source.state action then
    system.edge source.state action target.state &&
      addressIs target child && decide (target.polarity = source.polarity)
  else
    decide (target = source)

/-- Totalized evaluation-game edge relation.  Terminals and dead modalities
self-loop; their priorities below distinguish truthful/vacuous endings from
failure. -/
def gameEdge (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source target : Position State Action Observation program) : Bool :=
  match program.nodeAt source with
  | .truth _ | .observation _ => decide (target = source)
  | .negation child =>
      toggledStateAndPolarity source target && addressIs target child
  | .conjunction left right | .disjunction left right =>
      sameStateAndPolarity source target &&
        (addressIs target left || addressIs target right)
  | .diamond action child | .box action child =>
      modalEdge model.system source target action child
  | .fixedPoint _ _ child =>
      sameStateAndPolarity source target && addressIs target child
  | .variable binder =>
      sameStateAndPolarity source target && addressIs target binder

def ownerForChoice (positiveVerifier : Bool) : Player :=
  if positiveVerifier then .verifier else .falsifier

def gameOwner (program : Program Action Observation)
    (position : Position State Action Observation program) : Player :=
  match program.nodeAt position with
  | .conjunction _ _ => ownerForChoice (!position.polarity)
  | .disjunction _ _ => ownerForChoice position.polarity
  | .diamond _ _ => ownerForChoice position.polarity
  | .box _ _ => ownerForChoice (!position.polarity)
  | _ => .verifier

def terminalWins (truth polarity : Bool) : Bool := truth == polarity

def deadModalWins (node : Node Action Observation) (polarity : Bool) : Bool :=
  match node with
  | .diamond _ _ => !polarity
  | .box _ _ => polarity
  | _ => false

/-- Priority of a recursive variable back-edge.  Under the maximum-priority
convention, outer lexical binders must dominate inner binders because an outer
unfolding resets all inner approximations. -/
def binderPriority (maximumDepth : Nat) (kind : FixedPointKind) (depth : Nat)
    (polarity : Bool) : Nat :=
  let reverseDepth := maximumDepth - depth
  match kind.atPolarity polarity with
  | .least => 2 * reverseDepth + 1
  | .greatest => 2 * reverseDepth + 2

/-- Odd binder priorities are exactly least fixed points at the current
semantic polarity. -/
theorem binderPriority_odd_iff (maximumDepth : Nat)
    (kind : FixedPointKind) (depth : Nat)
    (polarity : Bool) :
    Odd (binderPriority maximumDepth kind depth polarity) ↔
      kind.atPolarity polarity = .least := by
  cases kind <;> cases polarity <;>
    simp [binderPriority, FixedPointKind.atPolarity, FixedPointKind.dual,
      parity_simps]

/-- Even binder priorities are exactly greatest fixed points at the current
semantic polarity. -/
theorem binderPriority_even_iff (maximumDepth : Nat)
    (kind : FixedPointKind) (depth : Nat)
    (polarity : Bool) :
    Even (binderPriority maximumDepth kind depth polarity) ↔
      kind.atPolarity polarity = .greatest := by
  cases kind <;> cases polarity <;>
    simp [binderPriority, FixedPointKind.atPolarity, FixedPointKind.dual,
      parity_simps]

/-- Within the declared depth ceiling, a strictly deeper binder receives a
strictly smaller priority.  Thus the maximum recurring priority selects the
outermost recursive binder visited infinitely often. -/
theorem binderPriority_strict_anti_depth
    (maximumDepth : Nat)
    (shallowerKind deeperKind : FixedPointKind)
    (shallowerPolarity deeperPolarity : Bool)
    {shallowerDepth deeperDepth : Nat}
    (deeper : shallowerDepth < deeperDepth)
    (within : deeperDepth ≤ maximumDepth) :
    binderPriority maximumDepth deeperKind deeperDepth deeperPolarity <
      binderPriority maximumDepth shallowerKind shallowerDepth
        shallowerPolarity := by
  cases shallowerKind <;> cases deeperKind <;> cases shallowerPolarity <;>
    cases deeperPolarity <;>
      simp [binderPriority, FixedPointKind.atPolarity, FixedPointKind.dual] <;>
      omega

/-- Maximum-priority-even assignment.  Priority is charged when a bound
variable returns to its introducing binder, not whenever execution merely
passes through fixed-point syntax.  Outer binders receive larger priorities,
and negation polarity swaps least and greatest fixed points. -/
def gamePriority (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (position : Position State Action Observation program) : Nat :=
  let node := program.nodeAt position
  match node with
  | .truth value => if terminalWins value position.polarity then 0 else 1
  | .observation label =>
      if terminalWins (model.holds position.state label) position.polarity then 0
      else 1
  | .diamond action _ | .box action _ =>
      if model.system.hasSuccessor position.state action then 0
      else if deadModalWins node position.polarity then 0 else 1
  | .fixedPoint _ _ _ => 0
  | .variable binder =>
      match program.nodes[binder]? with
      | some (.fixedPoint kind depth _) =>
          binderPriority (program.formula.altDepth - 1)
            kind depth position.polarity
      | _ => 0
  | _ => 0

def game (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    Parity.Game (Position State Action Observation program) where
  edge := program.gameEdge model
  owner := program.gameOwner
  priority := program.gamePriority model

/-- The totalized evaluation game has a legal successor at every position.
Dead modalities and terminals use their explicit self-loops. -/
theorem exists_gameEdge
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source : Position State Action Observation program) :
    ∃ target, program.gameEdge model source target = true := by
  generalize sourceNode : program.nodeAt source = node
  cases node with
  | truth value =>
      exact ⟨source, by simp [gameEdge, sourceNode]⟩
  | observation label =>
      exact ⟨source, by simp [gameEdge, sourceNode]⟩
  | negation child =>
      have childBound : child < program.nodes.length :=
        program.target_lt_nodes_length source child (by
          simp [sourceNode, Node.targets])
      let target : Position State Action Observation program :=
        ⟨source.state, ⟨child, childBound⟩, !source.polarity⟩
      refine ⟨target, ?_⟩
      simp [gameEdge, sourceNode, toggledStateAndPolarity, addressIs, target]
  | conjunction left right =>
      have leftBound : left < program.nodes.length :=
        program.target_lt_nodes_length source left (by
          simp [sourceNode, Node.targets])
      let target : Position State Action Observation program :=
        ⟨source.state, ⟨left, leftBound⟩, source.polarity⟩
      refine ⟨target, ?_⟩
      simp [gameEdge, sourceNode, sameStateAndPolarity, addressIs, target]
  | disjunction left right =>
      have leftBound : left < program.nodes.length :=
        program.target_lt_nodes_length source left (by
          simp [sourceNode, Node.targets])
      let target : Position State Action Observation program :=
        ⟨source.state, ⟨left, leftBound⟩, source.polarity⟩
      refine ⟨target, ?_⟩
      simp [gameEdge, sourceNode, sameStateAndPolarity, addressIs, target]
  | diamond action child =>
      by_cases successor :
          model.system.hasSuccessor source.state action = true
      · obtain ⟨targetState, transition⟩ :=
          (FiniteLTS.hasSuccessor_eq_true_iff model.system source.state action).1
            successor
        have childBound : child < program.nodes.length :=
          program.target_lt_nodes_length source child (by
            simp [sourceNode, Node.targets])
        let target : Position State Action Observation program :=
          ⟨targetState, ⟨child, childBound⟩, source.polarity⟩
        refine ⟨target, ?_⟩
        simp [gameEdge, sourceNode, modalEdge, successor, addressIs,
          target, transition]
      · have noSuccessor :
            model.system.hasSuccessor source.state action = false :=
          Bool.eq_false_of_not_eq_true successor
        exact ⟨source, by simp [gameEdge, sourceNode, modalEdge, noSuccessor]⟩
  | box action child =>
      by_cases successor :
          model.system.hasSuccessor source.state action = true
      · obtain ⟨targetState, transition⟩ :=
          (FiniteLTS.hasSuccessor_eq_true_iff model.system source.state action).1
            successor
        have childBound : child < program.nodes.length :=
          program.target_lt_nodes_length source child (by
            simp [sourceNode, Node.targets])
        let target : Position State Action Observation program :=
          ⟨targetState, ⟨child, childBound⟩, source.polarity⟩
        refine ⟨target, ?_⟩
        simp [gameEdge, sourceNode, modalEdge, successor, addressIs,
          target, transition]
      · have noSuccessor :
            model.system.hasSuccessor source.state action = false :=
          Bool.eq_false_of_not_eq_true successor
        exact ⟨source, by simp [gameEdge, sourceNode, modalEdge, noSuccessor]⟩
  | fixedPoint kind depth child =>
      have childBound : child < program.nodes.length :=
        program.target_lt_nodes_length source child (by
          simp [sourceNode, Node.targets])
      let target : Position State Action Observation program :=
        ⟨source.state, ⟨child, childBound⟩, source.polarity⟩
      refine ⟨target, ?_⟩
      simp [gameEdge, sourceNode, sameStateAndPolarity, addressIs, target]
  | «variable» binder =>
      have binderBound : binder < program.nodes.length :=
        program.target_lt_nodes_length source binder (by
          simp [sourceNode, Node.targets])
      let target : Position State Action Observation program :=
        ⟨source.state, ⟨binder, binderBound⟩, source.polarity⟩
      refine ⟨target, ?_⟩
      simp [gameEdge, sourceNode, sameStateAndPolarity, addressIs, target]

/-- Following a compiled variable back-edge reaches the fixed-point node that
introduced it, preserving the model state and semantic polarity. -/
theorem variable_edge_enters_fixedPoint
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source target : Position State Action Observation program)
    (binder : Nat)
    (sourceNode : program.nodeAt source = .variable binder)
    (edge : program.gameEdge model source target = true) :
    ∃ kind depth child,
      program.nodeAt target = .fixedPoint kind depth child ∧
        target.state = source.state ∧ target.polarity = source.polarity := by
  have sourceMember : (.variable binder : Node Action Observation) ∈
      program.nodes := by
    rw [← sourceNode]
    exact List.get_mem program.nodes source.address
  obtain ⟨kind, depth, child, binderLookup⟩ :=
    program.variable_target_fixedPoint binder sourceMember
  have edgeFacts :
      (target.state = source.state ∧ target.polarity = source.polarity) ∧
        target.address.val = binder := by
    simpa [gameEdge, sourceNode, sameStateAndPolarity, addressIs,
      Bool.and_eq_true] using edge
  refine ⟨kind, depth, child, ?_, edgeFacts.1.1, edgeFacts.1.2⟩
  obtain ⟨_binderInBounds, binderValue⟩ :=
    List.getElem?_eq_some_iff.mp binderLookup
  unfold nodeAt
  simpa [edgeFacts.2] using binderValue

/-- A variable occurrence carries exactly the priority of its introducing
binder, while the binder target itself remains neutral.  Charging the
back-edge occurrence distinguishes genuine recursion from merely passing
through nested fixed-point syntax. -/
theorem variable_edge_priority
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source target : Position State Action Observation program)
    (binder : Nat)
    (sourceNode : program.nodeAt source = .variable binder)
    (edge : program.gameEdge model source target = true) :
    ∃ kind depth child,
      program.nodeAt target = .fixedPoint kind depth child ∧
        program.gamePriority model source =
          binderPriority (program.formula.altDepth - 1)
            kind depth source.polarity ∧
        program.gamePriority model target = 0 := by
  obtain ⟨kind, depth, child, targetNode, _, _⟩ :=
    program.variable_edge_enters_fixedPoint model source target binder
      sourceNode edge
  have binderLookup : program.nodes[binder]? =
      some (.fixedPoint kind depth child) := by
    have targetAddress : target.address.val = binder := by
      have edgeFacts := edge
      simp [gameEdge, sourceNode, sameStateAndPolarity, addressIs,
        Bool.and_eq_true] at edgeFacts
      exact edgeFacts.2
    have targetValue : program.nodes[target.address.val] =
        .fixedPoint kind depth child := by
      simpa [nodeAt] using targetNode
    rw [List.getElem?_eq_some_iff]
    exact ⟨by simpa [targetAddress] using target.address.isLt,
      by simpa [targetAddress] using targetValue⟩
  exact ⟨kind, depth, child, targetNode, by
    simp [gamePriority, sourceNode, binderLookup], by
    simp [gamePriority, targetNode]⟩

end Program

/-! ## Structural compiler checks -/

/-- A formula accepted by the positivity boundary produces an admitted
evaluation-game program. -/
def compilePositive {n : Nat} (formula : Formula Action n)
    (observation : Fin n → Observation)
    (accepted : fixedPointsPositive formula = true) :
    Program Action Observation :=
  ⟨n, formula, observation, accepted⟩

def negativeFormula : Formula Unit 0 :=
  .mu (.neg (.var 0))

theorem negativeFormula_rejected :
    fixedPointsPositive negativeFormula = false := by
  rfl

theorem no_negativeProgram :
    ¬ ∃ _ : fixedPointsPositive negativeFormula = true, True := by
  rintro ⟨_accepted, _⟩
  cases _accepted

/-! ## Executable separating fixtures -/

namespace Canary

def singletonModel : FiniteModel Unit Unit Unit where
  system.edge _ _ _ := false
  holds _ _ := false

def topProgram : Program Unit Unit :=
  compilePositive .tt Fin.elim0 rfl

def bottomProgram : Program Unit Unit :=
  compilePositive .ff Fin.elim0 rfl

/-- Minimal generated fixed-point cycle. -/
def leastLoopProgram : Program Unit Unit :=
  compilePositive (.mu (.var 0)) Fin.elim0 rfl

theorem leastLoopProgram_nodes :
    leastLoopProgram.nodes =
      [.fixedPoint .least 0 1, .variable 0] := by
  rfl

theorem leastLoopProgram_binders_valid :
    leastLoopProgram.binderTargetsValid = true := by
  exact leastLoopProgram.binderTargetsValid_eq_true

/-- An in-range pointer to a non-binder is rejected by the stronger gate even
though a plain bounds check would accept it. -/
def malformedBinderNodes : List (Node Unit Unit) :=
  [.truth true, .variable 0]

theorem malformedBinderNodes_rejected :
    Program.binderTargetsValidNodes malformedBinderNodes = false := by
  rfl

/-- One ambient variable compiles to a model observation, not a spurious
fixed-point back-edge. -/
def observationProgram : Program Unit Unit :=
  compilePositive (Formula.var 0 : Formula Unit 1) (fun _ : Fin 1 => ()) rfl

theorem observationProgram_nodes :
    observationProgram.nodes = [.observation ()] := by
  rfl

def observingModel (value : Bool) : FiniteModel Unit Unit Unit where
  system.edge _ _ _ := false
  holds _ _ := value

theorem observed_true_has_even_priority :
    (observationProgram.game (observingModel true)).priority
      (observationProgram.initial ()) = 0 := by
  rfl

theorem observed_false_has_odd_priority :
    (observationProgram.game (observingModel false)).priority
      (observationProgram.initial ()) = 1 := by
  rfl

theorem top_graph_valid : topProgram.graphValid = true := by
  decide

theorem bottom_graph_valid : bottomProgram.graphValid = true := by
  decide

def topRoot : Position Unit Unit Unit topProgram := topProgram.initial ()
def bottomRoot : Position Unit Unit Unit bottomProgram := bottomProgram.initial ()

def topStrategy : Parity.Strategy (Position Unit Unit Unit topProgram) where
  active position := decide (position = topRoot)
  next _ := topRoot

def topMeasure : Parity.ProgressMeasure (topProgram.game singletonModel) where
  rank _ _ := 0

theorem topCertificate :
    topMeasure.check (topProgram.game singletonModel) topStrategy topRoot = true := by
  decide

def bottomStrategy : Parity.Strategy (Position Unit Unit Unit bottomProgram) where
  active position := decide (position = bottomRoot)
  next _ := bottomRoot

def bottomPlay :
    Parity.Strategy.Play (bottomProgram.game singletonModel)
      bottomStrategy bottomRoot where
  state _ := bottomRoot
  starts := rfl
  follows _ := by
    simp [Parity.Strategy.ControlledEdge, Program.game, Program.gameEdge,
      Program.gameOwner, Program.nodeAt, bottomProgram, compilePositive, Program.nodes,
      compileAt, bottomRoot, bottomStrategy, Program.initial, Program.root]

theorem bottomBad :
    Parity.Strategy.BadOddDominant (bottomProgram.game singletonModel)
      bottomPlay.state := by
  refine ⟨1, ⟨0, by omega⟩, ?_, 0, ?_⟩
  · have infiniteRange : Set.Infinite (Set.range (fun index : Nat => index)) :=
      Set.infinite_range_of_injective Function.injective_id
    simpa [bottomPlay, Program.game, Program.gamePriority, Program.nodeAt,
      bottomProgram, compilePositive, Program.nodes, compileAt, bottomRoot,
      Program.initial, Program.root, Program.terminalWins, Set.range_id] using
      infiniteRange
  · intro index _
    simp [bottomPlay, Program.game, Program.gamePriority, Program.nodeAt,
      bottomProgram, compilePositive, Program.nodes, compileAt, bottomRoot,
      Program.initial, Program.root, Program.terminalWins]

theorem bottomStrategy_not_winning :
    ¬ bottomStrategy.ParityWinning
      (bottomProgram.game singletonModel) bottomRoot := by
  intro winning
  exact winning.2 bottomPlay bottomBad

end Canary

end Mettapedia.Logic.ModalMuCalculus.EvaluationGame
