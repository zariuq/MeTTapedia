import Mettapedia.TypeTheory.JudgmentPresentationTransport
import Mathlib.Data.List.Basic

/-!
# Proof choices, equation authority and omitted premise positions

The binary source rule reads both separately indexed premises. A unary
target rule reads only the first. Their rule map is valid, but identifies
proofs whose second premises differ. An independent ordered readout both
detects the difference and excludes identification without an equation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.JudgmentPresentationControls

open JudgmentDerivation JudgmentEquationInitiality JudgmentPresentationTransport

inductive SourceRule : PUnit → Type where
  | leaf (label : Bool) : SourceRule .unit
  | fork : SourceRule .unit

abbrev source : Signature where
  Judgment := PUnit
  Rule := SourceRule
  Premise r := match r with | .leaf _ => Fin 0 | .fork => Fin 2
  hypothesis _ _ := .unit

inductive TargetRule : PUnit → Type where
  | leaf (label : Bool) : TargetRule .unit
  | branch : TargetRule .unit

abbrev target : Signature where
  Judgment := PUnit
  Rule := TargetRule
  Premise r := match r with | .leaf _ => Fin 0 | .branch => Fin 1
  hypothesis _ _ := .unit

def firstPremise : SignatureMap source target where
  judgment := id
  rule r := match r with | .leaf label => .leaf label | .fork => .branch
  position r := match r with | .leaf _ => Fin.elim0 | .fork => fun _ => 0
  hypothesis _ _ := rfl

def leaf (label : Bool) : Derivation source .unit :=
  .node (.leaf label) (fun p => nomatch p)

def fork (first second : Bool) : Derivation source .unit :=
  .node .fork (Fin.cases (leaf first) (fun _ => leaf second))

def ledger : Algebra source where
  Carrier _ := List Bool
  conclude r premises := match r with
    | .leaf label => [label]
    | .fork => premises 0 ++ premises 1

@[simp] theorem interpret_leaf (label : Bool) : interpret ledger (leaf label) = [label] := rfl
@[simp] theorem interpret_fork (first second : Bool) :
    interpret ledger (fork first second) = [first, second] := rfl

theorem supplied_proofs_distinct : fork false false ≠ fork false true := by
  intro erased
  have readout := congrArg (interpret ledger) erased
  have different : ([false, false] : List Bool) ≠ [false, true] := by decide
  exact different readout

/-- The source occurrence at position one has no target position. -/
theorem firstPremise_not_surjective :
    ¬ Function.Surjective (firstPremise.position SourceRule.fork) := by
  intro covers
  obtain ⟨p, equal⟩ := covers 1
  have indices : (0 : Fin 2) = 1 := equal
  exact Bool.noConfusion (congrArg (fun p : Fin 2 => p.val == 0) indices)

/-- This is a computation of the actual recursive proof translation. -/
theorem translation_omits_second_premise :
    firstPremise.translate (fork false false) = firstPremise.translate (fork false true) := rfl

theorem translation_not_injective :
    ¬ Function.Injective (fun d : Derivation source .unit => firstPremise.translate d) :=
  fun injective => supplied_proofs_distinct (injective translation_omits_second_premise)

def noEquations : Equations source := fun _ _ => False

theorem ledger_satisfies_noEquations : Satisfies noEquations ledger := by
  intro j left right impossible
  exact False.elim impossible

theorem no_equation_identifies_second_premises :
    ¬ Congruence noEquations (fork false false) (fork false true) := by
  apply separated_not_congruent noEquations ledger ledger_satisfies_noEquations
  change ([false, false] : List Bool) ≠ [false, true]
  decide

/-- The actual presented algebra retains these proofs without an imposed
equation. This is distinctness in the quotient, not just raw syntax. -/
theorem presented_proofs_distinct :
    (Quotient.mk (derivationSetoid noEquations .unit) (fork false false)) ≠
      Quotient.mk (derivationSetoid noEquations .unit) (fork false true) :=
  fun equal => no_equation_identifies_second_premises (Quotient.exact equal)

/-- An explicit equation can authorize that identification. -/
def eraseSecond : Equations source := fun {_j} left right =>
  ∃ first second other : Bool,
    HEq left (fork first second) ∧ HEq right (fork first other)

theorem eraseSecond_identifies :
    Congruence eraseSecond (fork false false) (fork false true) :=
  Congruence.equation ⟨false, false, true, HEq.rfl, HEq.rfl⟩

/-- The ordered readout cannot descend through that explicit erasure. -/
theorem ledger_does_not_satisfy_eraseSecond : ¬ Satisfies eraseSecond ledger := by
  intro sound
  have erased := sound (left := fork false false) (right := fork false true)
    ⟨false, false, true, HEq.rfl, HEq.rfl⟩
  have different : ([false, false] : List Bool) ≠ [false, true] := by decide
  exact different erased

/-- A readout that deliberately observes only the first premise does model
the erasure equations. The two observer contracts are different. -/
def firstLabel : Algebra source where
  Carrier _ := Bool
  conclude r premises := match r with | .leaf label => label | .fork => premises 0

theorem firstLabel_satisfies_eraseSecond : Satisfies eraseSecond firstLabel := by
  intro j left right imposed
  cases j
  obtain ⟨first, second, other, equalLeft, equalRight⟩ := imposed
  have leftEq := eq_of_heq equalLeft
  have rightEq := eq_of_heq equalRight
  rw [leftEq, rightEq]
  rfl

/-- All compatible observers agree exactly when the generated equations
permit the identification. -/
theorem all_eraseSecond_models_agree :
    ∀ (A : Algebra source), Satisfies eraseSecond A →
      interpret A (fork false false) = interpret A (fork false true) :=
  fun A laws => interpretation_respects_congruence eraseSecond A laws eraseSecond_identifies

end Mettapedia.TypeTheory.JudgmentPresentationControls
