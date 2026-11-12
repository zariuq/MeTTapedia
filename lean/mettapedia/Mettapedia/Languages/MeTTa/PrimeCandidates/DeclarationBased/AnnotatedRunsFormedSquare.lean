import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AnnotatedRunsFormedJoined

/-!
# The square of the two axes: substitution in the context and execution

Two routes lead from a formed source in a context `Γ` and a substitution `τ : Δ ⟶ Γ`:

* **substitute, then run**: execute in the substituted context;
* **run, then substitute**: execute in `Γ`, check the result, and substitute it.

## For every run (`run_square`, `substitution_square`)

Executing in the substituted context means starting with the substitution's equations
(`closedStart`): each context variable is told its image. For every check-free, query-free run
whose result is checked, the run executes from the closed start as soon as its closed store is
consistent, and its closed store observes the substituted answer, which reads back as the
substituted result (`readback_applyTerm`: readback commutes with substitution of values). On the
formed side, the substituted evidence (`FormedEvidence.reindex`) ends at the same substituted
term and relates the substituted source to it. The readback is taken at the substituted context's
arity; the statement is about every solution of the closed store, which also constrains any run
variable that coincides with a variable of the substituted context.

## For append, with the compiled program (`closed_certified`, `certified_square`)

Substituting `a ↦ 0, b ↦ 1`:

* result checking of the closed start (`closed_square`): the instance of the square for the run
  of append;
* **certifying execution of the substituted source**: the compiler reads the substituted source,
  its compiled run executes, and the run's own certificate certifies `[0, 1]`
  (`closed_certified`). The substituted Flower evidence ends at the same value, in the same class
  (`certified_square`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
namespace Square

open _root_.CategoryTheory
open Mettapedia.Logic.LP
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation (Tm Sub subst)
open Presentation.FormationSensitiveContextual (Context TypeOver Term TotalTerm QTerm empty)
open Presentation.StructuralConversionCode (RootDecoder Certificate Code)
open AnnotatedRuns

/-! ## The closed start -/

section Closing

variable {n : Nat}

/-- The substitution of the context's variables by the images `q`, on transform terms. -/
def closingSubst (q : Fin n → Pattern) : Subst signature :=
  fun v => if h : v < n then q ⟨v, h⟩ else .var v

/-- The substitution's equations: each context variable is told its image. -/
def closingStore (q : Fin n → Pattern) : EquationStore Pattern :=
  (List.finRange n).map fun i => (.var i.val, q i)

/-- **The start in the substituted context**: the substitution's equations before the start's. -/
def closedStart (q : Fin n → Pattern) (C : Configuration Pattern Nat) : Configuration Pattern Nat :=
  ⟨closingStore q ++ C.equations, C.present⟩

theorem result_closedStart (label : Nat → Pattern) (q : Fin n → Pattern)
    (f : Firing Pattern (Subst signature) Nat) (C : Configuration Pattern Nat) :
    f.result label (closedStart q C) = closedStart q (f.result label C) := by
  simp only [Firing.result, Selection.result, closedStart, Selection.problem, List.append_assoc]

/-- A run from the closed start leaves the closed configuration of the run. -/
theorem follow_closedStart (label : Nat → Pattern) (q : Fin n → Pattern) :
    ∀ (C : Configuration Pattern Nat) (w : List (Firing Pattern (Subst signature) Nat)),
      follow label (closedStart q C) w = closedStart q (follow label C w)
  | _, [] => rfl
  | C, f :: rest => by
      change follow label (f.result label (closedStart q C)) rest = _
      rw [result_closedStart]
      exact follow_closedStart label q (f.result label C) rest

/-- **A check-free, query-free run executes from the closed start** when its closed store is
consistent. -/
theorem executable_closedStart (label : Nat → Pattern) (q : Fin n → Pattern) :
    ∀ {C : Configuration Pattern Nat} {w : List (Firing Pattern (Subst signature) Nat)},
      Executable action label C w → (∀ f ∈ w, f.rule.checks = [] ∧ f.queries = []) →
      action.Consistent (follow label (closedStart q C) w).equations →
      Executable action label (closedStart q C) w
  | _, [], _, _, consistent => consistent
  | C, f :: rest, run, plain, consistent => by
      have restConsistent :
          action.Consistent (follow label (closedStart q (f.result label C)) rest).equations := by
        rw [← result_closedStart]
        exact consistent
      obtain ⟨⟨firing, _⟩, restRun⟩ := run
      refine ⟨⟨⟨firing.take_distinct, firing.output_distinct, firing.take_length,
        firing.read_length, firing.outputs, firing.occurrences, ?_, ?_⟩, ?_⟩, ?_⟩
      · obtain ⟨σ, solved⟩ := consistent
        refine ⟨σ, ?_⟩
        rw [follow_closedStart] at solved
        change action.Models σ (closingStore q ++ (follow label C (f :: rest)).equations) at solved
        rw [follow_equations, List.flatMap_cons] at solved
        simp only [action.models_append] at solved
        rw [Firing.problem_eq']
        simp only [closedStart, action.models_append]
        exact ⟨⟨solved.1, solved.2.1⟩, solved.2.2.1⟩
      · intro check member
        rw [(plain f List.mem_cons_self).1] at member
        cases member
      · intro query member
        rw [(plain f List.mem_cons_self).2] at member
        cases member
      · rw [result_closedStart]
        exact executable_closedStart label q restRun
          (fun g member => plain g (List.mem_cons_of_mem _ member)) restConsistent

variable {Head : Type} [DecidableEq Head] (canonical : Presentation.DeclName → Bool)

omit [DecidableEq Head] in
/-- A transform term that reads back mentions only the context's variables: substitutions that
agree there agree on it. -/
theorem applyTerm_congr_of_readback :
    ∀ {p : Pattern} {t : Tm Head n}, readback canonical p = some t →
      ∀ {σ σ' : Subst signature}, (∀ i : Fin n, σ i.val = σ' i.val) → σ.applyTerm p = σ'.applyTerm p
  | .var v, t, read, σ, σ', agree => by
      unfold readback at read
      split at read
      · rename_i inside
        exact agree ⟨v, inside⟩
      · cases read
  | .const name, t, read, σ, σ', agree => rfl
  | .app .application arguments, t, read, σ, σ', agree => by
      cases hf : (readback canonical (arguments ⟨0, by decide⟩) : Option (Tm Head n)) with
      | none => simp [readback, hf] at read
      | some f =>
          cases ha : (readback canonical (arguments ⟨1, by decide⟩) : Option (Tm Head n)) with
          | none => simp [readback, hf, ha] at read
          | some a =>
              have first := applyTerm_congr_of_readback hf agree
              have second := applyTerm_congr_of_readback ha agree
              change Term.app _ (fun i => σ.applyTerm (arguments i)) =
                Term.app _ (fun i => σ'.applyTerm (arguments i))
              congr 1
              funext i
              exact Fin.cases first (fun j => Fin.cases second (fun k => k.elim0) j) i
  | .app .pair arguments, t, read, σ, σ', agree => by
      cases hf : (readback canonical (arguments ⟨0, by decide⟩) : Option (Tm Head n)) with
      | none => simp [readback, hf] at read
      | some f =>
          cases ha : (readback canonical (arguments ⟨1, by decide⟩) : Option (Tm Head n)) with
          | none => simp [readback, hf, ha] at read
          | some a =>
              have first := applyTerm_congr_of_readback hf agree
              have second := applyTerm_congr_of_readback ha agree
              change Term.app _ (fun i => σ.applyTerm (arguments i)) =
                Term.app _ (fun i => σ'.applyTerm (arguments i))
              congr 1
              funext i
              exact Fin.cases first (fun j => Fin.cases second (fun k => k.elim0) j) i
  | .app .second _, t, read, _, _, _ => by simp [readback] at read
  | .app .evaluate _, t, read, _, _, _ => by simp [readback] at read
  | .app (.operation _ _) _, t, read, _, _, _ => by simp [readback] at read

omit [DecidableEq Head] in
/-- **The closed store observes the substituted answer.** -/
theorem observes_closed {store : EquationStore Pattern} {r : Nat} {answer : Pattern}
    {t : Tm Head n} (q : Fin n → Pattern) (observed : Observes action store (.var r) answer)
    (read : readback canonical answer = some t) :
    Observes action (closingStore q ++ store) (.var r) ((closingSubst q).applyTerm answer) := by
  intro σ solved
  obtain ⟨closing, final⟩ := (action.models_append σ _ _).mp solved
  have resultIs := observed σ final
  change σ.applyTerm (.var r) = σ.applyTerm answer at resultIs
  change σ.applyTerm (.var r) = σ.applyTerm ((closingSubst q).applyTerm answer)
  rw [resultIs, ← Subst.applyTerm_comp]
  apply applyTerm_congr_of_readback canonical read
  intro i
  have equation := closing (.var i.val, q i) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  change σ.applyTerm (.var i.val) = σ.applyTerm (q i) at equation
  change σ i.val = σ.applyTerm (closingSubst q i.val)
  rw [show closingSubst q i.val = q i from by simp [closingSubst]]
  exact equation

/-- **The square of the two axes, for every check-free, query-free run.** Substituting in the
context and then running executes, and the closed store observes an answer that reads back as the
substituted checked result. -/
theorem run_square {label : Nat → Pattern} {C : Configuration Pattern Nat}
    {w : List (Firing Pattern (Subst signature) Nat)} (run : Executable action label C w)
    (plain : ∀ f ∈ w, f.rule.checks = [] ∧ f.queries = []) {fuel r : Nat} {target : Tm Head n}
    (checked : checkResult canonical fuel (follow label C w).equations r target = true)
    {m : Nat} (q : Fin n → Pattern) (τ : Sub Head n m)
    (images : ∀ i, readback canonical (q i) = some (τ i))
    (consistent : action.Consistent (closingStore q ++ (follow label C w).equations)) :
    Executable action label (closedStart q C) w ∧
      ∃ answer, readback canonical answer = some (subst τ target) ∧
        Observes action (follow label (closedStart q C) w).equations (.var r) answer := by
  obtain ⟨_, answer, read, observed⟩ := checkResult_sound checked
  have closedEquations : (follow label (closedStart q C) w).equations =
      closingStore q ++ (follow label C w).equations := by
    rw [follow_closedStart]
    rfl
  refine ⟨executable_closedStart label q run plain (by rw [closedEquations]; exact consistent),
    (closingSubst q).applyTerm answer, ?_, ?_⟩
  · refine readback_applyTerm canonical (closingSubst q) τ (fun i => ?_) answer read
    rw [show closingSubst q i.val = q i from by simp [closingSubst]]
    exact images i
  · rw [closedEquations]
    exact observes_closed canonical q observed read

variable {R : Presentation.Rules Head} [DecidableRel R.headEq]

/-- **The square with the formed side.** Substitute, then run: the closed run observes an answer
reading back as the substituted result. Run, then substitute: the substituted formed evidence
ends at the same term, and relates the substituted source to it. -/
theorem substitution_square {decoder : RootDecoder R.computation} (rootAction : RootAction decoder)
    {context other : Context R} (morphism : other ⟶ context) (q : Fin context.arity → Pattern)
    (images : ∀ i, readback canonical (q i) = some (morphism.substitution i))
    {source : TotalTerm context} {label : Nat → Pattern} {C : Configuration Pattern Nat}
    {w : List (Firing Pattern (Subst signature) Nat)} (run : Executable action label C w)
    (plain : ∀ f ∈ w, f.rule.checks = [] ∧ f.queries = []) {fuel r : Nat}
    {target : Tm Head context.arity}
    (checked : checkResult canonical fuel (follow label C w).equations r target = true)
    (evidence : FormedEvidence decoder context source target)
    (consistent : action.Consistent (closingStore q ++ (follow label C w).equations)) :
    Executable action label (closedStart q C) w ∧
      (∃ answer, readback canonical answer = some (subst morphism.substitution target) ∧
        Observes action (follow label (closedStart q C) w).equations (.var r) answer) ∧
      (evidence.reindex rootAction morphism).targetTerm.code = subst morphism.substitution target ∧
      QTerm.mk (TotalTerm.reindex source morphism).2 =
        QTerm.mk (evidence.reindex rootAction morphism).targetTerm :=
  ⟨(run_square canonical run plain checked q morphism.substitution images consistent).1,
    (run_square canonical run plain checked q morphism.substitution images consistent).2,
    (evidence.reindex rootAction morphism).target_code,
    (evidence.reindex rootAction morphism).class_eq⟩

end Closing

/-! ## The instances for append -/

namespace AppendSquare

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed.Append
open NativeNaturalVectorFamilies

/-- The images of `a ↦ 0, b ↦ 1`, quoted: variable `0` is `b`, variable `1` is `a`. -/
def closingImages : Fin 2 → Pattern := ![succP zeroP, zeroP]

theorem closing_images :
    ∀ i : Fin 2, readback vectorCanonical (closingImages i) = some (closing.substitution i) := by
  decide +kernel

theorem run_plain : ∀ f ∈ run, f.rule.checks = [] ∧ f.queries = [] := by
  intro f member
  simp only [run, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    exact ⟨rfl, rfl⟩

theorem closed_consistent :
    action.Consistent (closingStore closingImages ++ (follow label start run).equations) :=
  consistent_of_unified (fuel := 64) (by decide +kernel)

/-- **The square for the run of append, with result checking**: executing with the closing
equations in the start store checks `[0, 1]`, the target of the substituted evidence. -/
theorem closed_square :
    Executable action label (closedStart closingImages start) run ∧
      (∃ answer, readback vectorCanonical answer = some (subst closing.substitution value) ∧
        Observes action (follow label (closedStart closingImages start) run).equations
          (.var resultVar) answer) ∧
      closedEvidence.targetTerm.code = subst closing.substitution value ∧
      QTerm.mk (TotalTerm.reindex appendSource closing).2 = QTerm.mk closedEvidence.targetTerm :=
  substitution_square vectorCanonical vectorRootAction closing closingImages closing_images
    append_executes run_plain append_certified appendEvidence closed_consistent

/-! ### Certifying execution of the substituted source -/

/-- The compiled term of the substituted source: the compiled append on `Nat, 1, 1, [0], [1]`. -/
def closedCompiledTerm : Pattern :=
  appendP natP (succP zeroP) (succP zeroP) (vconsP natP zeroP zeroP (vnilP natP))
    (vconsP natP zeroP (succP zeroP) (vnilP natP))

/-- **The compiler reads the substituted source.** -/
theorem closed_compile :
    compile vectorCanonical appendProgram.callables (TotalTerm.reindex appendSource closing).2.code =
      some closedCompiledTerm := by
  decide +kernel

/-- The labels of the substituted program: its compiled term at `0`, the cons rule's outputs at
`1` and `2`. -/
def closedLabel : Nat → Pattern
  | 0 => evaluate closedCompiledTerm (.var resultVar)
  | 1 => evaluate (addP (.var 4) (.var 5)) (.var 10)
  | 2 => evaluate (appendP (.var 3) (.var 4) (.var 5) (.var 7) (.var 8)) (.var 11)
  | _ => .const .anonymous

theorem closed_cons_valid : consFiring.Valid action closedLabel start :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    consistent_of_unified (fuel := 64) (by decide +kernel), by simp [consFiring, appendConsInstance]⟩,
    by simp [consFiring]⟩

theorem closed_add_valid : addFiring.Valid action closedLabel (consFiring.result closedLabel start) :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    consistent_of_unified (fuel := 64) (by decide +kernel), by simp [addFiring, addZeroInstance]⟩,
    by simp [addFiring]⟩

theorem closed_nil_valid :
    nilFiring.Valid action closedLabel (addFiring.result closedLabel (consFiring.result closedLabel start)) :=
  ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    consistent_of_unified (fuel := 64) (by decide +kernel), by simp [nilFiring, appendNilInstance]⟩,
    by simp [nilFiring]⟩

/-- The compiled steps of append run from the substituted program's start. -/
theorem closed_executes : Executable action closedLabel start run :=
  ⟨closed_cons_valid, closed_add_valid, closed_nil_valid,
    consistent_of_unified (fuel := 64) (by decide +kernel)⟩

theorem closed_checked :
    checkResult vectorCanonical 64 (follow closedLabel start run).equations resultVar
      (subst closing.substitution value) = true := by
  decide +kernel

/-- **Certifying execution of the substituted source**: the compiled program of `a ↦ 0, b ↦ 1`
applied to append's source runs as the same compiled steps, and its own certificate certifies
`[0, 1]`. -/
theorem closed_certified :
    CertifiedConclusion Programs.decoder vectorDiscipline appendProgram vectorRootAction
      (empty Append.rules) (TotalTerm.reindex appendSource closing) closedLabel 0 unitConfiguration
      steps []
      64 resultVar (subst closing.substitution value) := by
  refine formed_certified_execution vectorDiscipline appendProgram vectorRootAction closed_compile
    rfl ?_ ?_ ?_ closedEvidence.targetType closedEvidence.targetTerm closedEvidence.target_code
    closedEvidence.typeCertificate
  · rw [steps_firing]
    exact separated_alone closed_executes
  · rw [steps_firing]
    exact closed_checked
  · decide +kernel

/-- **The certifying square for append**: substitute, then compile, run and certify, reaches the
term at which run, then substitute, arrives: the substituted Flower evidence ends at `[0, 1]`, and
the certified evidence of the substituted run lies in its class. -/
theorem certified_square :
    CertifiedConclusion Programs.decoder vectorDiscipline appendProgram vectorRootAction
        (empty Append.rules) (TotalTerm.reindex appendSource closing) closedLabel 0 unitConfiguration
      steps []
        64 resultVar closedEvidence.targetTerm.code ∧
      ∀ evidence : FormedEvidence Programs.decoder (empty Append.rules)
          (TotalTerm.reindex appendSource closing)
          closedEvidence.targetTerm.code,
        QTerm.mk evidence.targetTerm = QTerm.mk closedEvidence.targetTerm := by
  refine ⟨closed_certified, fun evidence => ?_⟩
  exact evidence.class_eq.symm.trans closedEvidence.class_eq

end AppendSquare

#print axioms result_closedStart
#print axioms follow_closedStart
#print axioms executable_closedStart
#print axioms applyTerm_congr_of_readback
#print axioms observes_closed
#print axioms run_square
#print axioms substitution_square
#print axioms AppendSquare.closing_images
#print axioms AppendSquare.closed_square
#print axioms AppendSquare.closed_compile
#print axioms AppendSquare.closed_executes
#print axioms AppendSquare.closed_checked
#print axioms AppendSquare.closed_certified
#print axioms AppendSquare.certified_square

end Square
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
