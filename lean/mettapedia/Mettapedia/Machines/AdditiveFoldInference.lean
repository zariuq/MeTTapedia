import Mettapedia.Machines.ModeAggregation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Proof-producing inference of an additive fold regime

A finite pure counter-update syntax is normalized into state coefficients and
input-only weights. The classifier computes whether the coefficient matrix is
the identity. On acceptance it constructs a transition certificate; list and
bag homomorphism laws then follow for every input, not from sampled traces.

This is a restricted typed intermediate language, not a parser or equivalence
decider for arbitrary MeTTa. Effects, errors and declaration-sensitive calls
must be excluded by a source-to-IR refinement before using its certificates.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdditiveFoldInference

inductive Weight
  | constant (value : Nat)
  | inputValue
  | indicator (label : Nat)
  | add (left right : Weight)
  | scale (factor : Nat) (body : Weight)
  deriving DecidableEq

def Weight.eval : Weight → Nat → Nat
  | .constant n, _ => n
  | .inputValue, input => input
  | .indicator label, input => if input = label then 1 else 0
  | .add left right, input => left.eval input + right.eval input
  | .scale factor body, input => factor * body.eval input

inductive Expr (n : Nat)
  | register (index : Fin n)
  | weight (body : Weight)
  | add (left right : Expr n)
  | scale (factor : Nat) (body : Expr n)
  deriving DecidableEq

def Expr.eval {n : Nat} : Expr n → (Fin n → Nat) → Nat → Nat
  | .register index, state, _ => state index
  | .weight body, _, input => body.eval input
  | .add left right, state, input => left.eval state input + right.eval state input
  | .scale factor body, state, input => factor * body.eval state input

structure Normal (n : Nat) where
  coefficients : Fin n → Nat
  weight : Weight

def normalize {n : Nat} : Expr n → Normal n
  | .register index => ⟨fun j => if j = index then 1 else 0, .constant 0⟩
  | .weight body => ⟨fun _ => 0, body⟩
  | .add left right =>
      let a := normalize left
      let b := normalize right
      ⟨fun j => a.coefficients j + b.coefficients j, .add a.weight b.weight⟩
  | .scale factor body =>
      let a := normalize body
      ⟨fun j => factor * a.coefficients j, .scale factor a.weight⟩

theorem normalize_sound {n : Nat} (expression : Expr n) (state : Fin n → Nat) (input : Nat) :
    expression.eval state input =
      (∑ j, (normalize expression).coefficients j * state j) + (normalize expression).weight.eval input := by
  induction expression with
  | register index => simp [Expr.eval, normalize, Weight.eval]
  | weight body => simp [Expr.eval, normalize]
  | add left right ihl ihr =>
    simp only [Expr.eval, normalize, Weight.eval, ihl, ihr, Nat.add_mul, Finset.sum_add_distrib]
    omega
  | scale factor body ih =>
    simp [Expr.eval, normalize, Weight.eval, ih, Nat.mul_add, Finset.mul_sum, Nat.mul_assoc]

abbrev Program (n : Nat) := Fin n → Expr n

def sourceStep {n : Nat} (program : Program n) (state : Fin n → Nat) (input : Nat) : Fin n → Nat :=
  fun i => (program i).eval state input

def Admitted {n : Nat} (program : Program n) : Prop :=
  ∀ i j, (normalize (program i)).coefficients j = if j = i then 1 else 0

instance {n : Nat} (program : Program n) : Decidable (Admitted program) := by
  unfold Admitted
  infer_instance

def infer {n : Nat} (program : Program n) : Option (Fin n → Weight) :=
  if Admitted program then some (fun i => (normalize (program i)).weight) else none

/-- The matrix test is complete for this semantic regime within the declared
affine syntax. Necessity is recovered by probing zero and basis states. -/
theorem admitted_iff_translation {n : Nat} (program : Program n) :
    Admitted program ↔ ∀ state input,
      sourceStep program state input = state + sourceStep program 0 input := by
  constructor
  · intro admitted state input
    funext i
    simp only [sourceStep, Pi.add_apply]
    rw [normalize_sound, normalize_sound]
    simp [admitted i]
  · intro translation i j
    let basis : Fin n → Nat := fun k => if k = j then 1 else 0
    have equation := congrFun (translation basis 0) i
    simp only [sourceStep, Pi.add_apply] at equation
    rw [normalize_sound, normalize_sound] at equation
    simp [basis, mul_ite] at equation
    by_cases same : j = i
    · subst j
      simpa using equation
    · simpa [same, Ne.symm same] using equation

theorem infer_admits_iff {n : Nat} (program : Program n) :
    (infer program).isSome = true ↔ ∀ state input,
      sourceStep program state input = state + sourceStep program 0 input := by
  rw [← admitted_iff_translation]
  simp [infer]

/-- Equivalent spellings within this IR cannot cross the admission boundary.
This statement concerns admission, not identity of the generated weight AST. -/
theorem equivalent_programs_same_admission {n : Nat} (left right : Program n)
    (equivalent : ∀ state input, sourceStep left state input = sourceStep right state input) :
    (infer left).isSome = (infer right).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [infer_admits_iff, infer_admits_iff]
  simp only [equivalent]

theorem accepted_transition {n : Nat} (program : Program n) (weights : Fin n → Weight)
    (accepted : infer program = some weights) (state : Fin n → Nat) (input : Nat) :
    sourceStep program state input = state + fun i => (weights i).eval input := by
  by_cases admitted : Admitted program
  · have output : (fun i => (normalize (program i)).weight) = weights := by
      simpa [infer, admitted] using accepted
    rw [← output]
    funext i
    rw [sourceStep, normalize_sound]
    simp only [admitted i]
    simp
  · simp [infer, admitted] at accepted

structure Certificate {n : Nat} (program : Program n) where
  weights : Fin n → Weight
  transition : ∀ state input,
    sourceStep program state input = state + fun i => (weights i).eval input

/-- The returned proof is constructed from normalization and the computed
matrix check; callers do not provide the target transition equality. -/
def inferCertified {n : Nat} (program : Program n) : Option (Certificate program) :=
  match accepted : infer program with
  | none => none
  | some weights => some ⟨weights, accepted_transition program weights accepted⟩

def summary {n : Nat} (weights : Fin n → Weight) (inputs : List Nat) : Fin n → Nat :=
  fun i => (inputs.map (weights i).eval).sum

def sourceRun {n : Nat} (program : Program n) (inputs : List Nat) (initial : Fin n → Nat) : Fin n → Nat :=
  inputs.foldl (sourceStep program) initial

theorem accepted_run {n : Nat} (program : Program n) (weights : Fin n → Weight)
    (accepted : infer program = some weights) (inputs : List Nat) (initial : Fin n → Nat) :
    sourceRun program inputs initial = initial + summary weights inputs := by
  induction inputs generalizing initial with
  | nil => funext i; simp [sourceRun, summary]
  | cons input rest ih =>
    rw [sourceRun, List.foldl_cons]
    change sourceRun program rest (sourceStep program initial input) = _
    rw [ih, accepted_transition program weights accepted]
    funext i
    simp [summary, Nat.add_assoc]

/-- Refusal selects ordinary execution; it is neither an error nor an empty
answer. Accepted execution uses the extracted input-only summary. -/
def runInferred {n : Nat} (program : Program n) (inputs : List Nat) (initial : Fin n → Nat) : Fin n → Nat :=
  match infer program with
  | none => sourceRun program inputs initial
  | some weights => initial + summary weights inputs

theorem runInferred_exact {n : Nat} (program : Program n) (inputs : List Nat) (initial : Fin n → Nat) :
    runInferred program inputs initial = sourceRun program inputs initial := by
  cases result : infer program with
  | none => simp [runInferred, result]
  | some weights =>
    simpa only [runInferred, result] using (accepted_run program weights result inputs initial).symm

theorem runInferred_composes {n : Nat} (program : Program n) (left right : List Nat) (initial : Fin n → Nat) :
    runInferred program (left ++ right) initial = runInferred program right (runInferred program left initial) := by
  simp only [runInferred_exact, sourceRun, List.foldl_append]

theorem summary_append {n : Nat} (weights : Fin n → Weight) (left right : List Nat) :
    summary weights (left ++ right) = summary weights left + summary weights right := by
  funext i
  simp [summary]

theorem summary_perm {n : Nat} (weights : Fin n → Weight) {left right : List Nat}
    (permutation : left.Perm right) : summary weights left = summary weights right := by
  funext i
  exact (permutation.map _).sum_eq

/-- Any pure readout of the inferred summary inherits the same input-order
independence. Readout itself need not be a homomorphism, as mode demonstrates. -/
theorem accepted_readout_perm {n : Nat} {Answer : Type} (program : Program n) (weights : Fin n → Weight)
    (accepted : infer program = some weights) (readout : (Fin n → Nat) → Answer)
    (initial : Fin n → Nat) {left right : List Nat} (permutation : left.Perm right) :
    readout (sourceRun program left initial) = readout (sourceRun program right initial) := by
  rw [accepted_run program weights accepted, accepted_run program weights accepted, summary_perm weights permutation]

def histogramProgram (n : Nat) : Program n := fun i =>
  .add (.register i) (.weight (.indicator i.val))

theorem infer_histogram (n : Nat) :
    infer (histogramProgram n) = some (fun i => .add (.constant 0) (.indicator i.val)) := by
  have admitted : Admitted (histogramProgram n) := by simp [Admitted, histogramProgram, normalize]
  simp [infer, admitted, histogramProgram, normalize]

theorem inferred_histogram_counts (n : Nat) (inputs : List Nat) (i : Fin n) :
    sourceRun (histogramProgram n) inputs 0 i = inputs.count i.val := by
  rw [accepted_run _ _ (infer_histogram n)]
  simp only [Pi.add_apply, Pi.zero_apply, Nat.zero_add, summary]
  simp only [Weight.eval, Nat.zero_add]
  change (inputs.map (fun input => if input = i.val then 1 else 0)).sum = inputs.count i.val
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    by_cases same : input = i.val
    · simp [same, ih, Nat.add_comm]
    · simp [same, ih]

namespace Controls

def disguisedCounter : Program 1 := fun i =>
  .add (.scale 0 (.register i))
    (.add (.weight (.constant 0)) (.add (.weight (.indicator 7)) (.register i)))

theorem normalization_admits_disguised_counter : (inferCertified disguisedCounter).isSome = true := by decide

def doublesState : Program 1 := fun i => .add (.register i) (.register i)
theorem state_scaling_declines : (infer doublesState).isNone = true := by decide

def orderedDecimal : Program 1 := fun i => .add (.scale 10 (.register i)) (.weight .inputValue)
theorem order_sensitive_declines : (infer orderedDecimal).isNone = true := by decide
theorem order_sensitive_distinguishes :
    sourceRun orderedDecimal [1, 2] 0 0 = 12 ∧ sourceRun orderedDecimal [2, 1] 0 0 = 21 := by decide

theorem accepted_execution : runInferred disguisedCounter [7, 8, 7] 0 0 = 2 := by decide
theorem refusal_executes_source : runInferred orderedDecimal [1, 2] 0 0 = 12 := by decide

end Controls
end Mettapedia.Machines.AdditiveFoldInference
