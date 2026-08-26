import Mettapedia.Logic.ModalMuCalculusEvaluationGame
import Mettapedia.Logic.ModalQuantaleSemantics

/-!
# Semantic annotations for modal μ-calculus evaluation games

This module is the denotational side of the evaluation-game adequacy proof.
It annotates every structurally compiled formula occurrence with its Boolean
denotation under the environment active at that occurrence.  Fixed-point
bodies are annotated under the denotation of their introducing binder.

The table is proof-side data only.  It is aligned with the compiled node table
by construction and is not carried by the executable game.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.EvaluationGame.Adequacy

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.ModalMuCalculus.EvaluationGame
open Mettapedia.Logic.ModalQuantaleSemantics.Boolean
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open Mettapedia.Order.FiniteSetFixedPoints

universe uState uAction uObservation

variable {State : Type uState} {Action : Type uAction}
  {Observation : Type uObservation}

/-- Source-side data retained for one compiled formula occurrence.  This is a
dependent proof annotation: the environment and compiler references share the
same variable scope as the formula. -/
structure SourceOccurrence (State : Type uState) (Action : Type uAction)
    (Observation : Type uObservation) where
  variableCount : Nat
  environment : Env State variableCount
  references : Fin variableCount → VariableReference Observation
  formula : Formula Action variableCount
  /-- Enclosing fixed-point addresses, innermost first.  This is proof-side
  lexical information already implicit in `references`; it is not emitted in
  the executable game. -/
  binderStack : List Nat

namespace SourceOccurrence

/-- Denotation of a retained source occurrence. -/
def denotation (lts : LTS State Action)
    (occurrence : SourceOccurrence State Action Observation) : Set State :=
  sat lts occurrence.environment occurrence.formula

/-- The compiled node has the same outer constructor and variable-reference
kind as its retained source occurrence.  A fixed-point node's depth is the
length of the occurrence's lexical binder stack; numeric child addresses are
checked separately by the compiler's graph invariants. -/
def MatchesNode (occurrence : SourceOccurrence State Action Observation) :
    Node Action Observation → Prop
  | .truth true => match occurrence.formula with | .tt => True | _ => False
  | .truth false => match occurrence.formula with | .ff => True | _ => False
  | .observation label => match occurrence.formula with
      | .var index => occurrence.references index = .observation label
      | _ => False
  | .negation _ => match occurrence.formula with | .neg _ => True | _ => False
  | .conjunction _ _ => match occurrence.formula with
      | .conj _ _ => True
      | _ => False
  | .disjunction _ _ => match occurrence.formula with
      | .disj _ _ => True
      | _ => False
  | .diamond action _ => match occurrence.formula with
      | .diamond sourceAction _ => sourceAction = action
      | _ => False
  | .box action _ => match occurrence.formula with
      | .box sourceAction _ => sourceAction = action
      | _ => False
  | .fixedPoint .least depth _ => match occurrence.formula with
      | .mu _ => occurrence.binderStack.length = depth
      | _ => False
  | .fixedPoint .greatest depth _ => match occurrence.formula with
      | .nu _ => occurrence.binderStack.length = depth
      | _ => False
  | .variable binder => match occurrence.formula with
      | .var index => occurrence.references index = .binder binder
      | _ => False

/-- Every fixed-point source occurrence has a positive body. -/
def BinderPositive
    (occurrence : SourceOccurrence State Action Observation) : Prop :=
  match occurrence.formula with
  | .mu body | .nu body => body.isPositive = true
  | _ => True

end SourceOccurrence

/-- The compiler reference environment consists exactly of the active binder
stack, in innermost-first order, followed by ambient observations. -/
def BinderStackAligned {n : Nat}
    (references : Fin n → VariableReference Observation)
    (binderStack : List Nat) : Prop :=
  ∃ suffix,
    List.ofFn references =
        binderStack.map VariableReference.binder ++ suffix ∧
      ∀ reference ∈ suffix,
        ∃ label, reference = VariableReference.observation label

/-- A reference environment containing only observations agrees with the empty
lexical binder stack. -/
theorem binderStackAligned_observations {n : Nat}
    (observation : Fin n → Observation) :
    BinderStackAligned
      (fun index => VariableReference.observation (observation index)) [] := by
  refine ⟨List.ofFn (fun index =>
    VariableReference.observation (observation index)), by simp, ?_⟩
  intro reference member
  rw [List.mem_ofFn] at member
  obtain ⟨index, rfl⟩ := member
  exact ⟨observation index, rfl⟩

/-- Extending the compiler reference environment and the lexical binder stack
with the same address preserves their exact prefix agreement. -/
theorem BinderStackAligned.extend {n : Nat}
    (references : Fin n → VariableReference Observation)
    (binderStack : List Nat) (address : Nat)
    (aligned : BinderStackAligned references binderStack) :
    BinderStackAligned (extendVariableReferences references address)
      (address :: binderStack) := by
  rcases aligned with ⟨suffix, aligned, observations⟩
  refine ⟨suffix, ?_, observations⟩
  simpa [BinderStackAligned, List.ofFn_succ, extendVariableReferences] using
    congrArg (List.cons (VariableReference.binder address)) aligned

/-- Every binder-valued compiler reference names one of the lexically active
binders; ambient observations cannot manufacture a back-edge. -/
theorem BinderStackAligned.binder_mem {n : Nat}
    {references : Fin n → VariableReference Observation}
    {binderStack : List Nat} (aligned : BinderStackAligned references binderStack)
    {index : Fin n} {address : Nat}
    (reference : references index = .binder address) :
    address ∈ binderStack := by
  rcases aligned with ⟨suffix, tableEq, observations⟩
  have member : VariableReference.binder address ∈ List.ofFn references :=
    List.mem_ofFn.mpr ⟨index, reference⟩
  rw [tableEq, List.mem_append] at member
  rcases member with binderMember | suffixMember
  · simpa using binderMember
  · obtain ⟨label, impossible⟩ := observations _ suffixMember
    cases impossible

/-! ## Finite semantic signatures

The ordinary denotation records whether a position is true at the completed
fixed points.  A parity proof needs the more precise finite stage at which an
effective least fixed point becomes true.  The following proof-only semantics
keeps exactly that information.  `rank depth` bounds the effective least fixed
point at lexical `depth`; effective greatest fixed points use the canonical
finite descending iteration.  Negative polarity dualizes the connectives and
stores a candidate winning set as the complement of the raw bound variable.

This is not another executable game.  It is the finite-approximant refinement
of Boolean satisfaction from which the existing parity progress certificate
will be generated. -/

/-- Verifier-winning states at a finite fixed-point signature.  The definition
is structural in the formula; every fixed-point transformer recursively
evaluates only its proper body subformula. -/
noncomputable def boundedWinningSet [Finite State]
    (lts : LTS State Action) (rank : Nat → Nat) (depth : Nat)
    (polarity : Bool) : {n : Nat} → Env State n → Formula Action n → Set State
  | _, _, .tt => if polarity then Set.univ else ∅
  | _, _, .ff => if polarity then ∅ else Set.univ
  | _, environment, .neg child =>
      boundedWinningSet lts rank depth (!polarity) environment child
  | _, environment, .conj left right =>
      if polarity then
        boundedWinningSet lts rank depth polarity environment left ∩
          boundedWinningSet lts rank depth polarity environment right
      else
        boundedWinningSet lts rank depth polarity environment left ∪
          boundedWinningSet lts rank depth polarity environment right
  | _, environment, .disj left right =>
      if polarity then
        boundedWinningSet lts rank depth polarity environment left ∪
          boundedWinningSet lts rank depth polarity environment right
      else
        boundedWinningSet lts rank depth polarity environment left ∩
          boundedWinningSet lts rank depth polarity environment right
  | _, environment, .diamond action child =>
      if polarity then
        {source | ∃ target, target ∈ lts.successors source action ∧
          target ∈ boundedWinningSet lts rank depth polarity environment child}
      else
        {source | ∀ target, target ∈ lts.successors source action →
          target ∈ boundedWinningSet lts rank depth polarity environment child}
  | _, environment, .box action child =>
      if polarity then
        {source | ∀ target, target ∈ lts.successors source action →
          target ∈ boundedWinningSet lts rank depth polarity environment child}
      else
        {source | ∃ target, target ∈ lts.successors source action ∧
          target ∈ boundedWinningSet lts rank depth polarity environment child}
  | _, environment, .mu body =>
      let step := fun candidate =>
        boundedWinningSet lts rank (depth + 1) polarity
          (environment.extend (if polarity then candidate else candidateᶜ)) body
      match FixedPointKind.least.atPolarity polarity with
      | .least => step^[rank depth] ∅
      | .greatest => step^[Nat.card State] Set.univ
  | _, environment, .nu body =>
      let step := fun candidate =>
        boundedWinningSet lts rank (depth + 1) polarity
          (environment.extend (if polarity then candidate else candidateᶜ)) body
      match FixedPointKind.greatest.atPolarity polarity with
      | .least => step^[rank depth] ∅
      | .greatest => step^[Nat.card State] Set.univ
  | _, environment, .var index =>
      if polarity then environment index else (environment index)ᶜ

@[simp] theorem boundedWinningSet_truth [Finite State]
    (lts : LTS State Action) (rank : Nat → Nat) (depth : Nat)
    {n : Nat} (polarity value : Bool) (environment : Env State n) :
    boundedWinningSet lts rank depth polarity environment
        (if value then (.tt : Formula Action n) else .ff) =
      if value == polarity then Set.univ else ∅ := by
  cases value <;> cases polarity <;> rfl

/-- A recursive variable is interpreted by the candidate winning set supplied
to its binder, at either semantic polarity. -/
@[simp] theorem boundedWinningSet_boundVariable [Finite State]
    (lts : LTS State Action) (rank : Nat → Nat) (depth : Nat)
    {n : Nat} (polarity : Bool) (environment : Env State n)
    (candidate : Set State) :
    boundedWinningSet lts rank depth polarity
        (environment.extend (if polarity then candidate else candidateᶜ))
        (.var 0 : Formula Action (n + 1)) = candidate := by
  cases polarity <;> ext state <;>
    simp [boundedWinningSet, Env.extend]

/-- A positive least fixed point at successor rank unfolds once and supplies
the preceding approximation to its body. -/
theorem boundedWinningSet_mu_succ [Finite State]
    (lts : LTS State Action) (rank : Nat → Nat) (depth previous : Nat)
    {n : Nat} (environment : Env State n) (body : Formula Action (n + 1))
    (rankEq : rank depth = previous + 1) :
    boundedWinningSet lts rank depth true environment (.mu body) =
      boundedWinningSet lts rank (depth + 1) true
        (environment.extend
          ((fun candidate => boundedWinningSet lts rank (depth + 1) true
              (environment.extend candidate) body)^[previous] ∅)) body := by
  simp [boundedWinningSet, rankEq, Function.iterate_succ_apply']

/-- Refuting a greatest fixed point is the dual successor approximation: the
body is checked under the complement of the preceding winning set. -/
theorem boundedWinningSet_nu_refutation_succ [Finite State]
    (lts : LTS State Action) (rank : Nat → Nat) (depth previous : Nat)
    {n : Nat} (environment : Env State n) (body : Formula Action (n + 1))
    (rankEq : rank depth = previous + 1) :
    boundedWinningSet lts rank depth false environment (.nu body) =
      boundedWinningSet lts rank (depth + 1) false
        (environment.extend
          (((fun candidate => boundedWinningSet lts rank (depth + 1) false
              (environment.extend candidateᶜ) body)^[previous] ∅)ᶜ)) body := by
  simp [boundedWinningSet, rankEq, Function.iterate_succ_apply',
    FixedPointKind.atPolarity, FixedPointKind.dual]

/-- Finite-signature winning semantics is monotone (or antitone) in one raw
environment component according to syntactic and game polarity.  Positivity
of every nested binder is consumed in the fixed-point cases, where it proves
monotonicity of the iterated transformer rather than assuming it. -/
theorem boundedWinningSet_mono_env [Finite State]
    (lts : LTS State Action) (rank : Nat → Nat)
    {n : Nat} (formula : Formula Action n) (index : Fin n)
    (syntacticPolarity gamePolarity : Bool)
    (positive : formula.isPositiveIn index syntacticPolarity = true)
    (admitted : fixedPointsPositive formula = true)
    (environment₁ environment₂ : Env State n)
    (equalAway : ∀ other state, other ≠ index →
      environment₁ other state = environment₂ other state)
    (componentLe : environment₁ index ≤ environment₂ index)
    (depth : Nat) :
    if syntacticPolarity == gamePolarity then
      boundedWinningSet lts rank depth gamePolarity environment₁ formula ⊆
        boundedWinningSet lts rank depth gamePolarity environment₂ formula
    else
      boundedWinningSet lts rank depth gamePolarity environment₂ formula ⊆
        boundedWinningSet lts rank depth gamePolarity environment₁ formula := by
  induction formula generalizing syntacticPolarity gamePolarity depth with
  | tt => cases syntacticPolarity <;> cases gamePolarity <;>
      simp [boundedWinningSet]
  | ff => cases syntacticPolarity <;> cases gamePolarity <;>
      simp [boundedWinningSet]
  | neg child inductionHypothesis =>
      simp only [Formula.isPositiveIn] at positive
      simp only [fixedPointsPositive] at admitted
      have childResult := inductionHypothesis index (!syntacticPolarity)
        (!gamePolarity) positive admitted environment₁ environment₂
        equalAway componentLe depth
      cases syntacticPolarity <;> cases gamePolarity <;>
        simpa [boundedWinningSet] using childResult
  | conj left right leftHypothesis rightHypothesis =>
      simp only [Formula.isPositiveIn, Bool.and_eq_true] at positive
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      have leftResult := leftHypothesis index syntacticPolarity gamePolarity
        positive.1 admitted.1 environment₁ environment₂ equalAway componentLe depth
      have rightResult := rightHypothesis index syntacticPolarity gamePolarity
        positive.2 admitted.2 environment₁ environment₂ equalAway componentLe depth
      cases syntacticPolarity <;> cases gamePolarity
      · simpa [boundedWinningSet] using sup_le_sup leftResult rightResult
      · simpa [boundedWinningSet] using inf_le_inf leftResult rightResult
      · simpa [boundedWinningSet] using sup_le_sup leftResult rightResult
      · simpa [boundedWinningSet] using inf_le_inf leftResult rightResult
  | disj left right leftHypothesis rightHypothesis =>
      simp only [Formula.isPositiveIn, Bool.and_eq_true] at positive
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      have leftResult := leftHypothesis index syntacticPolarity gamePolarity
        positive.1 admitted.1 environment₁ environment₂ equalAway componentLe depth
      have rightResult := rightHypothesis index syntacticPolarity gamePolarity
        positive.2 admitted.2 environment₁ environment₂ equalAway componentLe depth
      cases syntacticPolarity <;> cases gamePolarity
      · simpa [boundedWinningSet] using inf_le_inf leftResult rightResult
      · simpa [boundedWinningSet] using sup_le_sup leftResult rightResult
      · simpa [boundedWinningSet] using inf_le_inf leftResult rightResult
      · simpa [boundedWinningSet] using sup_le_sup leftResult rightResult
  | diamond action child inductionHypothesis =>
      simp only [Formula.isPositiveIn] at positive
      simp only [fixedPointsPositive] at admitted
      have childResult := inductionHypothesis index syntacticPolarity gamePolarity
        positive admitted environment₁ environment₂ equalAway componentLe depth
      have existsMonotone {first second : Set State} (included : first ⊆ second) :
          {source | ∃ target, target ∈ lts.successors source action ∧
            target ∈ first} ⊆
          {source | ∃ target, target ∈ lts.successors source action ∧
            target ∈ second} := by
        rintro source ⟨target, transition, member⟩
        exact ⟨target, transition, included member⟩
      have forallMonotone {first second : Set State} (included : first ⊆ second) :
          {source | ∀ target, target ∈ lts.successors source action →
            target ∈ first} ⊆
          {source | ∀ target, target ∈ lts.successors source action →
            target ∈ second} := by
        intro source sourceMember target transition
        exact included (sourceMember target transition)
      cases syntacticPolarity <;> cases gamePolarity
      · simpa [boundedWinningSet] using forallMonotone childResult
      · simpa [boundedWinningSet] using existsMonotone childResult
      · simpa [boundedWinningSet] using forallMonotone childResult
      · simpa [boundedWinningSet] using existsMonotone childResult
  | box action child inductionHypothesis =>
      simp only [Formula.isPositiveIn] at positive
      simp only [fixedPointsPositive] at admitted
      have childResult := inductionHypothesis index syntacticPolarity gamePolarity
        positive admitted environment₁ environment₂ equalAway componentLe depth
      have existsMonotone {first second : Set State} (included : first ⊆ second) :
          {source | ∃ target, target ∈ lts.successors source action ∧
            target ∈ first} ⊆
          {source | ∃ target, target ∈ lts.successors source action ∧
            target ∈ second} := by
        rintro source ⟨target, transition, member⟩
        exact ⟨target, transition, included member⟩
      have forallMonotone {first second : Set State} (included : first ⊆ second) :
          {source | ∀ target, target ∈ lts.successors source action →
            target ∈ first} ⊆
          {source | ∀ target, target ∈ lts.successors source action →
            target ∈ second} := by
        intro source sourceMember target transition
        exact included (sourceMember target transition)
      cases syntacticPolarity <;> cases gamePolarity
      · simpa [boundedWinningSet] using existsMonotone childResult
      · simpa [boundedWinningSet] using forallMonotone childResult
      · simpa [boundedWinningSet] using existsMonotone childResult
      · simpa [boundedWinningSet] using forallMonotone childResult
  | var other =>
      simp only [Formula.isPositiveIn] at positive
      by_cases same : other = index
      · subst other
        simp at positive
        subst syntacticPolarity
        cases gamePolarity with
        | false =>
            simp only [boundedWinningSet]
            intro state outside₂ inside₁
            exact outside₂ (componentLe inside₁)
        | true =>
            simpa [boundedWinningSet] using componentLe
      · have equal := equalAway other
        have setEq : environment₁ other = environment₂ other := by
          ext state
          exact Iff.of_eq (equal state same)
        cases syntacticPolarity <;> cases gamePolarity <;>
          simp [boundedWinningSet, setEq]
  | mu body inductionHypothesis =>
      simp only [Formula.isPositiveIn] at positive
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      let step₁ : Set State → Set State := fun candidate =>
        boundedWinningSet lts rank (depth + 1) gamePolarity
          (environment₁.extend
            (if gamePolarity then candidate else candidateᶜ)) body
      let step₂ : Set State → Set State := fun candidate =>
        boundedWinningSet lts rank (depth + 1) gamePolarity
          (environment₂.extend
            (if gamePolarity then candidate else candidateᶜ)) body
      have stepMonotone (environment : Env State _) : Monotone
          (fun candidate : Set State =>
            boundedWinningSet lts rank (depth + 1) gamePolarity
              (environment.extend
                (if gamePolarity then candidate else candidateᶜ)) body) := by
        intro first second firstLe
        cases gamePolarity with
        | true =>
            apply inductionHypothesis 0 true true admitted.1 admitted.2
              (environment.extend first) (environment.extend second)
            · intro other state notZero
              obtain ⟨previous, rfl⟩ := Fin.eq_succ_of_ne_zero notZero
              rfl
            · simpa [Env.extend] using firstLe
        | false =>
            apply inductionHypothesis 0 true false admitted.1 admitted.2
              (environment.extend secondᶜ) (environment.extend firstᶜ)
            · intro other state notZero
              obtain ⟨previous, rfl⟩ := Fin.eq_succ_of_ne_zero notZero
              rfl
            · simpa [Env.extend] using
                Set.compl_subset_compl_of_subset firstLe
      have step₁Monotone : Monotone step₁ := stepMonotone environment₁
      have step₂Monotone : Monotone step₂ := stepMonotone environment₂
      have stepComparison :
          if syntacticPolarity == gamePolarity then step₁ ≤ step₂
          else step₂ ≤ step₁ := by
        by_cases polarities : syntacticPolarity == gamePolarity
        · simp only [polarities]
          intro candidate
          have compared := inductionHypothesis index.succ syntacticPolarity
            gamePolarity positive admitted.2
              (environment₁.extend
                (if gamePolarity then candidate else candidateᶜ))
              (environment₂.extend
                (if gamePolarity then candidate else candidateᶜ))
              (by
                intro other state notIndex
                by_cases zero : other = 0
                · subst other
                  rfl
                obtain ⟨previous, rfl⟩ := Fin.eq_succ_of_ne_zero zero
                apply equalAway previous state
                intro previousEq
                apply notIndex
                exact congrArg Fin.succ previousEq)
              (by simpa [Env.extend] using componentLe) (depth + 1)
          simpa [polarities] using compared
        · simp only [polarities]
          intro candidate
          have compared := inductionHypothesis index.succ syntacticPolarity
            gamePolarity positive admitted.2
              (environment₁.extend
                (if gamePolarity then candidate else candidateᶜ))
              (environment₂.extend
                (if gamePolarity then candidate else candidateᶜ))
              (by
                intro other state notIndex
                by_cases zero : other = 0
                · subst other
                  rfl
                obtain ⟨previous, rfl⟩ := Fin.eq_succ_of_ne_zero zero
                apply equalAway previous state
                intro previousEq
                apply notIndex
                exact congrArg Fin.succ previousEq)
              (by simpa [Env.extend] using componentLe) (depth + 1)
          simpa [polarities] using compared
      cases syntacticPolarity <;> cases gamePolarity
      all_goals simp at stepComparison ⊢
      · simpa [boundedWinningSet, step₁, step₂,
          FixedPointKind.atPolarity, FixedPointKind.dual] using
          step₁Monotone.iterate_le_of_le stepComparison (Nat.card State)
            (Set.univ : Set State)

      · simpa [boundedWinningSet, step₁, step₂,
          FixedPointKind.atPolarity, FixedPointKind.dual] using
          step₂Monotone.iterate_le_of_le stepComparison (rank depth)
            (∅ : Set State)
      · simpa [boundedWinningSet, step₁, step₂,
          FixedPointKind.atPolarity, FixedPointKind.dual] using
          step₂Monotone.iterate_le_of_le stepComparison (Nat.card State)
            (Set.univ : Set State)
      · simpa [boundedWinningSet, step₁, step₂,
          FixedPointKind.atPolarity, FixedPointKind.dual] using
          step₁Monotone.iterate_le_of_le stepComparison (rank depth)
            (∅ : Set State)
  | nu body inductionHypothesis =>
      simp only [Formula.isPositiveIn] at positive
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      let step₁ : Set State → Set State := fun candidate =>
        boundedWinningSet lts rank (depth + 1) gamePolarity
          (environment₁.extend
            (if gamePolarity then candidate else candidateᶜ)) body
      let step₂ : Set State → Set State := fun candidate =>
        boundedWinningSet lts rank (depth + 1) gamePolarity
          (environment₂.extend
            (if gamePolarity then candidate else candidateᶜ)) body
      have stepMonotone (environment : Env State _) : Monotone
          (fun candidate : Set State =>
            boundedWinningSet lts rank (depth + 1) gamePolarity
              (environment.extend
                (if gamePolarity then candidate else candidateᶜ)) body) := by
        intro first second firstLe
        cases gamePolarity with
        | true =>
            apply inductionHypothesis 0 true true admitted.1 admitted.2
              (environment.extend first) (environment.extend second)
            · intro other state notZero
              obtain ⟨previous, rfl⟩ := Fin.eq_succ_of_ne_zero notZero
              rfl
            · simpa [Env.extend] using firstLe
        | false =>
            apply inductionHypothesis 0 true false admitted.1 admitted.2
              (environment.extend secondᶜ) (environment.extend firstᶜ)
            · intro other state notZero
              obtain ⟨previous, rfl⟩ := Fin.eq_succ_of_ne_zero notZero
              rfl
            · simpa [Env.extend] using
                Set.compl_subset_compl_of_subset firstLe
      have step₁Monotone : Monotone step₁ := stepMonotone environment₁
      have step₂Monotone : Monotone step₂ := stepMonotone environment₂
      have stepComparison :
          if syntacticPolarity == gamePolarity then step₁ ≤ step₂
          else step₂ ≤ step₁ := by
        by_cases polarities : syntacticPolarity == gamePolarity
        · simp only [polarities]
          intro candidate
          have compared := inductionHypothesis index.succ syntacticPolarity
            gamePolarity positive admitted.2
              (environment₁.extend
                (if gamePolarity then candidate else candidateᶜ))
              (environment₂.extend
                (if gamePolarity then candidate else candidateᶜ))
              (by
                intro other state notIndex
                by_cases zero : other = 0
                · subst other
                  rfl
                obtain ⟨previous, rfl⟩ := Fin.eq_succ_of_ne_zero zero
                apply equalAway previous state
                intro previousEq
                apply notIndex
                exact congrArg Fin.succ previousEq)
              (by simpa [Env.extend] using componentLe) (depth + 1)
          simpa [polarities] using compared
        · simp only [polarities]
          intro candidate
          have compared := inductionHypothesis index.succ syntacticPolarity
            gamePolarity positive admitted.2
              (environment₁.extend
                (if gamePolarity then candidate else candidateᶜ))
              (environment₂.extend
                (if gamePolarity then candidate else candidateᶜ))
              (by
                intro other state notIndex
                by_cases zero : other = 0
                · subst other
                  rfl
                obtain ⟨previous, rfl⟩ := Fin.eq_succ_of_ne_zero zero
                apply equalAway previous state
                intro previousEq
                apply notIndex
                exact congrArg Fin.succ previousEq)
              (by simpa [Env.extend] using componentLe) (depth + 1)
          simpa [polarities] using compared
      cases syntacticPolarity <;> cases gamePolarity
      all_goals simp at stepComparison ⊢
      · simpa [boundedWinningSet, step₁, step₂,
          FixedPointKind.atPolarity, FixedPointKind.dual] using
          step₁Monotone.iterate_le_of_le stepComparison (rank depth)
            (∅ : Set State)
      · simpa [boundedWinningSet, step₁, step₂,
          FixedPointKind.atPolarity, FixedPointKind.dual] using
          step₂Monotone.iterate_le_of_le stepComparison (Nat.card State)
            (Set.univ : Set State)
      · simpa [boundedWinningSet, step₁, step₂,
          FixedPointKind.atPolarity, FixedPointKind.dual] using
          step₂Monotone.iterate_le_of_le stepComparison (rank depth)
            (∅ : Set State)
      · simpa [boundedWinningSet, step₁, step₂,
          FixedPointKind.atPolarity, FixedPointKind.dual] using
          step₁Monotone.iterate_le_of_le stepComparison (Nat.card State)
            (Set.univ : Set State)

/-- The candidate transformer used at any admitted binder is genuinely
monotone under either game polarity.  At negative polarity candidates are
stored complemented in the raw semantic environment, so the two order
reversals cancel. -/
theorem boundedWinningSet_transformer_monotone [Finite State]
    (lts : LTS State Action) (rank : Nat → Nat) (depth : Nat)
    {n : Nat} (polarity : Bool) (environment : Env State n)
    (body : Formula Action (n + 1))
    (positive : body.isPositive = true)
    (admitted : fixedPointsPositive body = true) :
    Monotone (fun candidate : Set State =>
      boundedWinningSet lts rank (depth + 1) polarity
        (environment.extend (if polarity then candidate else candidateᶜ)) body) := by
  intro first second firstLe
  cases polarity with
  | true =>
      apply boundedWinningSet_mono_env lts rank body 0 true true positive admitted
        (environment.extend first) (environment.extend second)
      · intro other state notZero
        obtain ⟨previous, rfl⟩ := Fin.eq_succ_of_ne_zero notZero
        rfl
      · simpa [Env.extend] using firstLe
  | false =>
      apply boundedWinningSet_mono_env lts rank body 0 true false positive admitted
        (environment.extend secondᶜ) (environment.extend firstᶜ)
      · intro other state notZero
        obtain ⟨previous, rfl⟩ := Fin.eq_succ_of_ne_zero notZero
        rfl
      · simpa [Env.extend] using Set.compl_subset_compl_of_subset firstLe

/-- Increasing every effective least-fixed-point approximation rank can only
enlarge the verifier's finite winning set.  This is the order-theoretic fact
needed before selecting minimal nested approximation signatures: it reuses
the existing monotone-transformer proof and Mathlib's iteration lemmas rather
than introducing a second fixed-point construction. -/
theorem boundedWinningSet_mono_rank [Finite State]
    (lts : LTS State Action) {rank₁ rank₂ : Nat → Nat}
    (rankLe : rank₁ ≤ rank₂) (depth : Nat) (polarity : Bool)
    {n : Nat} (environment : Env State n) (formula : Formula Action n)
    (admitted : fixedPointsPositive formula = true) :
    boundedWinningSet lts rank₁ depth polarity environment formula ⊆
      boundedWinningSet lts rank₂ depth polarity environment formula := by
  induction formula generalizing depth polarity with
  | tt => cases polarity <;> simp [boundedWinningSet]
  | ff => cases polarity <;> simp [boundedWinningSet]
  | var index => cases polarity <;> simp [boundedWinningSet]
  | neg child inductionHypothesis =>
      simp only [fixedPointsPositive] at admitted
      simpa [boundedWinningSet] using
        inductionHypothesis depth (!polarity) environment admitted
  | conj left right leftHypothesis rightHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      have leftResult := leftHypothesis depth polarity environment admitted.1
      have rightResult := rightHypothesis depth polarity environment admitted.2
      cases polarity
      · simpa [boundedWinningSet] using sup_le_sup leftResult rightResult
      · simpa [boundedWinningSet] using inf_le_inf leftResult rightResult
  | disj left right leftHypothesis rightHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      have leftResult := leftHypothesis depth polarity environment admitted.1
      have rightResult := rightHypothesis depth polarity environment admitted.2
      cases polarity
      · simpa [boundedWinningSet] using inf_le_inf leftResult rightResult
      · simpa [boundedWinningSet] using sup_le_sup leftResult rightResult
  | diamond action child inductionHypothesis =>
      simp only [fixedPointsPositive] at admitted
      have childResult := inductionHypothesis depth polarity environment admitted
      cases polarity with
      | false =>
          intro source sourceMember target transition
          exact childResult (sourceMember target transition)
      | true =>
          rintro source ⟨target, transition, targetMember⟩
          exact ⟨target, transition, childResult targetMember⟩
  | box action child inductionHypothesis =>
      simp only [fixedPointsPositive] at admitted
      have childResult := inductionHypothesis depth polarity environment admitted
      cases polarity with
      | false =>
          rintro source ⟨target, transition, targetMember⟩
          exact ⟨target, transition, childResult targetMember⟩
      | true =>
          intro source sourceMember target transition
          exact childResult (sourceMember target transition)
  | mu body inductionHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      let step₁ : Set State → Set State := fun candidate =>
        boundedWinningSet lts rank₁ (depth + 1) polarity
          (environment.extend (if polarity then candidate else candidateᶜ)) body
      let step₂ : Set State → Set State := fun candidate =>
        boundedWinningSet lts rank₂ (depth + 1) polarity
          (environment.extend (if polarity then candidate else candidateᶜ)) body
      have step₁Monotone : Monotone step₁ := by
        simpa [step₁] using boundedWinningSet_transformer_monotone
          lts rank₁ depth polarity environment body admitted.1 admitted.2
      have step₂Monotone : Monotone step₂ := by
        simpa [step₂] using boundedWinningSet_transformer_monotone
          lts rank₂ depth polarity environment body admitted.1 admitted.2
      have stepComparison : step₁ ≤ step₂ := by
        intro candidate
        exact inductionHypothesis (depth + 1) polarity
          (environment.extend (if polarity then candidate else candidateᶜ))
          admitted.2
      cases polarity with
      | false =>
          simpa [boundedWinningSet, step₁, step₂,
            FixedPointKind.atPolarity, FixedPointKind.dual] using
            step₁Monotone.iterate_le_of_le stepComparison (Nat.card State)
              (Set.univ : Set State)
      | true =>
          have sameRank := step₁Monotone.iterate_le_of_le stepComparison
            (rank₁ depth) (∅ : Set State)
          have moreSteps :=
            (step₂Monotone.monotone_iterate_of_le_map bot_le) (rankLe depth)
          simpa [boundedWinningSet, step₁, step₂,
            FixedPointKind.atPolarity] using sameRank.trans moreSteps
  | nu body inductionHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      let step₁ : Set State → Set State := fun candidate =>
        boundedWinningSet lts rank₁ (depth + 1) polarity
          (environment.extend (if polarity then candidate else candidateᶜ)) body
      let step₂ : Set State → Set State := fun candidate =>
        boundedWinningSet lts rank₂ (depth + 1) polarity
          (environment.extend (if polarity then candidate else candidateᶜ)) body
      have step₁Monotone : Monotone step₁ := by
        simpa [step₁] using boundedWinningSet_transformer_monotone
          lts rank₁ depth polarity environment body admitted.1 admitted.2
      have step₂Monotone : Monotone step₂ := by
        simpa [step₂] using boundedWinningSet_transformer_monotone
          lts rank₂ depth polarity environment body admitted.1 admitted.2
      have stepComparison : step₁ ≤ step₂ := by
        intro candidate
        exact inductionHypothesis (depth + 1) polarity
          (environment.extend (if polarity then candidate else candidateᶜ))
          admitted.2
      cases polarity with
      | false =>
          have sameRank := step₁Monotone.iterate_le_of_le stepComparison
            (rank₁ depth) (∅ : Set State)
          have moreSteps :=
            (step₂Monotone.monotone_iterate_of_le_map bot_le) (rankLe depth)
          simpa [boundedWinningSet, step₁, step₂,
            FixedPointKind.atPolarity, FixedPointKind.dual] using
            sameRank.trans moreSteps
      | true =>
          simpa [boundedWinningSet, step₁, step₂,
            FixedPointKind.atPolarity] using
            step₁Monotone.iterate_le_of_le stepComparison (Nat.card State)
              (Set.univ : Set State)

/-- Giving every lexical level the finite carrier bound recovers the ordinary
Boolean denotation exactly.  Thus finite signatures refine the existing
semantics; they do not define a competing meaning for formulas. -/
theorem boundedWinningSet_card_eq [Finite State]
    (lts : LTS State Action) (depth : Nat) (polarity : Bool)
    {n : Nat} (environment : Env State n) (formula : Formula Action n)
    (admitted : fixedPointsPositive formula = true) :
    boundedWinningSet lts (fun _ => Nat.card State) depth polarity
        environment formula =
      if polarity then sat lts environment formula
      else (sat lts environment formula)ᶜ := by
  classical
  induction formula generalizing depth polarity with
  | tt => cases polarity <;> ext state <;>
      simp [boundedWinningSet, sat, satisfies]
  | ff => cases polarity <;> ext state <;>
      simp [boundedWinningSet, sat, satisfies]
  | var index => cases polarity <;> ext state <;>
      simp [boundedWinningSet, sat, satisfies]
  | neg child inductionHypothesis =>
      simp only [fixedPointsPositive] at admitted
      have childFalse := inductionHypothesis depth false environment admitted
      have childTrue := inductionHypothesis depth true environment admitted
      cases polarity <;> ext state <;>
        simp [boundedWinningSet, sat, satisfies, childFalse, childTrue]
  | conj left right leftHypothesis rightHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      have leftFalse := leftHypothesis depth false environment admitted.1
      have leftTrue := leftHypothesis depth true environment admitted.1
      have rightFalse := rightHypothesis depth false environment admitted.2
      have rightTrue := rightHypothesis depth true environment admitted.2
      cases polarity with
      | false =>
          ext state
          simp [boundedWinningSet, sat, satisfies, leftFalse, rightFalse]
          tauto
      | true =>
          ext state
          simp [boundedWinningSet, sat, satisfies, leftTrue, rightTrue]
  | disj left right leftHypothesis rightHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      have leftFalse := leftHypothesis depth false environment admitted.1
      have leftTrue := leftHypothesis depth true environment admitted.1
      have rightFalse := rightHypothesis depth false environment admitted.2
      have rightTrue := rightHypothesis depth true environment admitted.2
      cases polarity <;> ext state <;>
        simp [boundedWinningSet, sat, satisfies, leftFalse, leftTrue,
          rightFalse, rightTrue]
  | diamond action child inductionHypothesis =>
      simp only [fixedPointsPositive] at admitted
      have childFalse := inductionHypothesis depth false environment admitted
      have childTrue := inductionHypothesis depth true environment admitted
      cases polarity <;> ext state <;>
        simp [boundedWinningSet, sat, satisfies, LTS.successors,
          childFalse, childTrue]
  | box action child inductionHypothesis =>
      simp only [fixedPointsPositive] at admitted
      have childFalse := inductionHypothesis depth false environment admitted
      have childTrue := inductionHypothesis depth true environment admitted
      cases polarity <;> ext state <;>
        simp [boundedWinningSet, sat, satisfies, LTS.successors,
          childFalse, childTrue]
  | mu body inductionHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      let original : Set State → Set State := fun candidate =>
        sat lts (environment.extend candidate) body
      let dual : Set State → Set State := fun candidate =>
        boundedWinningSet lts (fun _ => Nat.card State) (depth + 1) false
          (environment.extend candidateᶜ) body
      have positiveStepEq :
          (fun candidate : Set State =>
            boundedWinningSet lts (fun _ => Nat.card State) (depth + 1) true
              (environment.extend candidate) body) = original := by
        funext candidate
        simpa [original] using
          inductionHypothesis (depth + 1) true (environment.extend candidate) admitted.2
      have dualEq : ∀ candidate, dual candidate = (original candidateᶜ)ᶜ := by
        intro candidate
        simpa [dual, original] using
          inductionHypothesis (depth + 1) false (environment.extend candidateᶜ) admitted.2
      have originalIterate :
          original^[Nat.card State] (∅ : Set State) =
            sat lts environment (.mu body) := by
        ext state
        symm
        simpa [original, bodyOrderHom, sat] using
          satisfies_mu_iff_mem_iterate_empty lts environment body admitted.1 state
      cases polarity with
      | true =>
          simpa [boundedWinningSet, FixedPointKind.atPolarity,
            positiveStepEq, original] using originalIterate
      | false =>
          have dualIterate := Mettapedia.Order.FiniteSetFixedPoints.iterate_dual
            original dual dualEq
            (Nat.card State) (∅ : Set State)
          rw [Set.compl_empty] at dualIterate
          rw [originalIterate] at dualIterate
          simpa [boundedWinningSet, FixedPointKind.atPolarity,
            FixedPointKind.dual, dual] using dualIterate
  | nu body inductionHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      let original : Set State → Set State := fun candidate =>
        sat lts (environment.extend candidate) body
      let dual : Set State → Set State := fun candidate =>
        boundedWinningSet lts (fun _ => Nat.card State) (depth + 1) false
          (environment.extend candidateᶜ) body
      have positiveStepEq :
          (fun candidate : Set State =>
            boundedWinningSet lts (fun _ => Nat.card State) (depth + 1) true
              (environment.extend candidate) body) = original := by
        funext candidate
        simpa [original] using
          inductionHypothesis (depth + 1) true (environment.extend candidate) admitted.2
      have dualEq : ∀ candidate, dual candidate = (original candidateᶜ)ᶜ := by
        intro candidate
        simpa [dual, original] using
          inductionHypothesis (depth + 1) false (environment.extend candidateᶜ) admitted.2
      have originalIterate :
          original^[Nat.card State] Set.univ =
            sat lts environment (.nu body) := by
        ext state
        symm
        simpa [original, bodyOrderHom, sat] using
          satisfies_nu_iff_mem_iterate_univ lts environment body admitted.1 state
      cases polarity with
      | true =>
          simpa [boundedWinningSet, FixedPointKind.atPolarity,
            positiveStepEq, original] using originalIterate
      | false =>
          have dualIterate := Mettapedia.Order.FiniteSetFixedPoints.iterate_dual
            original dual dualEq
            (Nat.card State) Set.univ
          rw [Set.compl_univ] at dualIterate
          rw [originalIterate] at dualIterate
          simpa [boundedWinningSet, FixedPointKind.atPolarity,
            FixedPointKind.dual, dual] using dualIterate

/-- Source occurrences in the same preorder as `compileAt`.  Fixed-point
bodies retain the environment in which the newly bound variable denotes the
fixed point itself. -/
noncomputable def sourceTableAt (lts : LTS State Action) :
    {n : Nat} → Nat → Env State n →
      (Fin n → VariableReference Observation) → List Nat → Formula Action n →
      List (SourceOccurrence State Action Observation)
  | n, _, environment, references, binderStack, formula@.tt =>
      [⟨n, environment, references, formula, binderStack⟩]
  | n, _, environment, references, binderStack, formula@.ff =>
      [⟨n, environment, references, formula, binderStack⟩]
  | n, offset, environment, references, binderStack, formula@(.neg child) =>
      ⟨n, environment, references, formula, binderStack⟩ ::
        sourceTableAt lts (offset + 1) environment references binderStack child
  | n, offset, environment, references, binderStack, formula@(.conj left right) =>
      ⟨n, environment, references, formula, binderStack⟩ ::
        (sourceTableAt lts (offset + 1) environment references binderStack left ++
          sourceTableAt lts (offset + 1 + left.size) environment references
            binderStack right)
  | n, offset, environment, references, binderStack, formula@(.disj left right) =>
      ⟨n, environment, references, formula, binderStack⟩ ::
        (sourceTableAt lts (offset + 1) environment references binderStack left ++
          sourceTableAt lts (offset + 1 + left.size) environment references
            binderStack right)
  | n, offset, environment, references, binderStack, formula@(.diamond _ child) =>
      ⟨n, environment, references, formula, binderStack⟩ ::
        sourceTableAt lts (offset + 1) environment references binderStack child
  | n, offset, environment, references, binderStack, formula@(.box _ child) =>
      ⟨n, environment, references, formula, binderStack⟩ ::
        sourceTableAt lts (offset + 1) environment references binderStack child
  | n, offset, environment, references, binderStack, formula@(.mu body) =>
      let fixedPoint := sat lts environment formula
      ⟨n, environment, references, formula, binderStack⟩ ::
        sourceTableAt lts (offset + 1) (environment.extend fixedPoint)
          (extendVariableReferences references offset) (offset :: binderStack) body
  | n, offset, environment, references, binderStack, formula@(.nu body) =>
      let fixedPoint := sat lts environment formula
      ⟨n, environment, references, formula, binderStack⟩ ::
        sourceTableAt lts (offset + 1) (environment.extend fixedPoint)
          (extendVariableReferences references offset) (offset :: binderStack) body
  | n, _, environment, references, binderStack, formula@(.var _) =>
      [⟨n, environment, references, formula, binderStack⟩]

/-- Every retained occurrence preserves the exact correspondence between its
lexical binder stack and the binder prefix of its variable references. -/
theorem sourceTableAt_binderStackAligned {n : Nat} (lts : LTS State Action)
    (offset : Nat) (environment : Env State n)
    (references : Fin n → VariableReference Observation)
    (binderStack : List Nat) (formula : Formula Action n)
    (aligned : BinderStackAligned references binderStack) :
    (sourceTableAt lts offset environment references binderStack formula).Forall
      (fun occurrence =>
        BinderStackAligned occurrence.references occurrence.binderStack) := by
  induction formula generalizing offset binderStack with
  | tt => simp [sourceTableAt, aligned]
  | ff => simp [sourceTableAt, aligned]
  | neg formula inductionHypothesis =>
      simp [sourceTableAt, aligned,
        inductionHypothesis (offset + 1) environment references binderStack aligned]
  | conj left right leftHypothesis rightHypothesis =>
      simp [sourceTableAt, aligned,
        leftHypothesis (offset + 1) environment references binderStack aligned,
        rightHypothesis (offset + 1 + left.size) environment references binderStack aligned]
  | disj left right leftHypothesis rightHypothesis =>
      simp [sourceTableAt, aligned,
        leftHypothesis (offset + 1) environment references binderStack aligned,
        rightHypothesis (offset + 1 + left.size) environment references binderStack aligned]
  | diamond action formula inductionHypothesis =>
      simp [sourceTableAt, aligned,
        inductionHypothesis (offset + 1) environment references binderStack aligned]
  | box action formula inductionHypothesis =>
      simp [sourceTableAt, aligned,
        inductionHypothesis (offset + 1) environment references binderStack aligned]
  | mu body inductionHypothesis =>
      have extended := BinderStackAligned.extend references binderStack offset aligned
      simp [sourceTableAt, aligned,
        inductionHypothesis (offset + 1)
          (environment.extend (sat lts environment (.mu body)))
          (extendVariableReferences references offset) (offset :: binderStack) extended]
  | nu body inductionHypothesis =>
      have extended := BinderStackAligned.extend references binderStack offset aligned
      simp [sourceTableAt, aligned,
        inductionHypothesis (offset + 1)
          (environment.extend (sat lts environment (.nu body)))
          (extendVariableReferences references offset) (offset :: binderStack) extended]
  | var index => simp [sourceTableAt, aligned]

/-- The source-occurrence table is aligned constructor-for-constructor with
the existing executable compiler. -/
theorem sourceTableAt_matchesNodes {n : Nat} (lts : LTS State Action)
    (offset depth : Nat) (environment : Env State n)
    (references : Fin n → VariableReference Observation)
    (binderStack : List Nat)
    (formula : Formula Action n)
    (stackDepth : binderStack.length = depth) :
    List.Forall₂ (fun node occurrence => occurrence.MatchesNode node)
      (compileAt offset depth references formula)
      (sourceTableAt lts offset environment references binderStack formula) := by
  induction formula generalizing offset depth binderStack with
  | tt => exact .cons trivial .nil
  | ff => exact .cons trivial .nil
  | neg formula inductionHypothesis =>
      exact .cons trivial
        (inductionHypothesis (offset + 1) depth environment references binderStack
          stackDepth)
  | conj left right leftHypothesis rightHypothesis =>
      exact .cons trivial (List.rel_append
        (leftHypothesis (offset + 1) depth environment references binderStack stackDepth)
        (rightHypothesis (offset + 1 + left.size) depth environment references binderStack
          stackDepth))
  | disj left right leftHypothesis rightHypothesis =>
      exact .cons trivial (List.rel_append
        (leftHypothesis (offset + 1) depth environment references binderStack stackDepth)
        (rightHypothesis (offset + 1 + left.size) depth environment references binderStack
          stackDepth))
  | diamond action formula inductionHypothesis =>
      exact .cons rfl
        (inductionHypothesis (offset + 1) depth environment references binderStack
          stackDepth)
  | box action formula inductionHypothesis =>
      exact .cons rfl
        (inductionHypothesis (offset + 1) depth environment references binderStack
          stackDepth)
  | mu body inductionHypothesis =>
      exact .cons stackDepth (inductionHypothesis (offset + 1) (depth + 1)
        (environment.extend (sat lts environment (.mu body)))
        (extendVariableReferences references offset) (offset :: binderStack)
        (by simpa using congrArg Nat.succ stackDepth))
  | nu body inductionHypothesis =>
      exact .cons stackDepth (inductionHypothesis (offset + 1) (depth + 1)
        (environment.extend (sat lts environment (.nu body)))
        (extendVariableReferences references offset) (offset :: binderStack)
        (by simpa using congrArg Nat.succ stackDepth))
  | var index =>
      cases reference : references index with
      | observation label =>
          rw [compileAt, reference, sourceTableAt]
          exact .cons (by simp [SourceOccurrence.MatchesNode, reference]) .nil
      | binder address =>
          rw [compileAt, reference, sourceTableAt]
          exact .cons (by simp [SourceOccurrence.MatchesNode, reference]) .nil

/-- Global fixed-point positivity implies positivity at every retained binder
occurrence, including nested binders. -/
theorem sourceTableAt_binderPositive {n : Nat} (lts : LTS State Action)
    (offset : Nat) (environment : Env State n)
    (references : Fin n → VariableReference Observation)
    (binderStack : List Nat)
    (formula : Formula Action n)
    (positive : fixedPointsPositive formula = true) :
    (sourceTableAt lts offset environment references binderStack formula).Forall
      SourceOccurrence.BinderPositive := by
  induction formula generalizing offset binderStack with
  | tt => simp [sourceTableAt, SourceOccurrence.BinderPositive]
  | ff => simp [sourceTableAt, SourceOccurrence.BinderPositive]
  | neg formula inductionHypothesis =>
      simp only [fixedPointsPositive] at positive
      simp [sourceTableAt, SourceOccurrence.BinderPositive,
        inductionHypothesis (offset + 1) environment references binderStack positive]
  | conj left right leftHypothesis rightHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      simp [sourceTableAt, SourceOccurrence.BinderPositive,
        leftHypothesis (offset + 1) environment references binderStack positive.1,
        rightHypothesis (offset + 1 + left.size) environment references binderStack positive.2]
  | disj left right leftHypothesis rightHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      simp [sourceTableAt, SourceOccurrence.BinderPositive,
        leftHypothesis (offset + 1) environment references binderStack positive.1,
        rightHypothesis (offset + 1 + left.size) environment references binderStack positive.2]
  | diamond action formula inductionHypothesis =>
      simp only [fixedPointsPositive] at positive
      simp [sourceTableAt, SourceOccurrence.BinderPositive,
        inductionHypothesis (offset + 1) environment references binderStack positive]
  | box action formula inductionHypothesis =>
      simp only [fixedPointsPositive] at positive
      simp [sourceTableAt, SourceOccurrence.BinderPositive,
        inductionHypothesis (offset + 1) environment references binderStack positive]
  | mu body inductionHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      simp [sourceTableAt, SourceOccurrence.BinderPositive, positive.1,
        inductionHypothesis (offset + 1)
          (environment.extend (sat lts environment (.mu body)))
          (extendVariableReferences references offset) (offset :: binderStack) positive.2]
  | nu body inductionHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      simp [sourceTableAt, SourceOccurrence.BinderPositive, positive.1,
        inductionHypothesis (offset + 1)
          (environment.extend (sat lts environment (.nu body)))
          (extendVariableReferences references offset) (offset :: binderStack) positive.2]
  | var index => simp [sourceTableAt, SourceOccurrence.BinderPositive]

/-- Preorder semantic annotations aligned with `compileAt`.  The head of
every recursively compiled segment is the denotation of that segment's source
formula. -/
noncomputable def semanticTableAt (lts : LTS State Action) :
    {n : Nat} → Env State n → Formula Action n → List (Set State)
  | _, environment, formula@.tt => [sat lts environment formula]
  | _, environment, formula@.ff => [sat lts environment formula]
  | _, environment, formula@(.neg child) =>
      sat lts environment formula :: semanticTableAt lts environment child
  | _, environment, formula@(.conj left right) =>
      sat lts environment formula ::
        (semanticTableAt lts environment left ++
          semanticTableAt lts environment right)
  | _, environment, formula@(.disj left right) =>
      sat lts environment formula ::
        (semanticTableAt lts environment left ++
          semanticTableAt lts environment right)
  | _, environment, formula@(.diamond _ child) =>
      sat lts environment formula :: semanticTableAt lts environment child
  | _, environment, formula@(.box _ child) =>
      sat lts environment formula :: semanticTableAt lts environment child
  | _, environment, formula@(.mu body) =>
      let fixedPoint := sat lts environment formula
      fixedPoint :: semanticTableAt lts (environment.extend fixedPoint) body
  | _, environment, formula@(.nu body) =>
      let fixedPoint := sat lts environment formula
      fixedPoint :: semanticTableAt lts (environment.extend fixedPoint) body
  | _, environment, formula@(.var _) => [sat lts environment formula]

/-- Erasing retained source syntax and compiler references yields exactly the
pre-existing denotation table; the occurrence table is therefore an
informative refinement, not a second semantics. -/
theorem sourceTableAt_denotations {n : Nat} (lts : LTS State Action)
    (offset : Nat) (environment : Env State n)
    (references : Fin n → VariableReference Observation)
    (binderStack : List Nat)
    (formula : Formula Action n) :
    (sourceTableAt lts offset environment references binderStack formula).map
        (SourceOccurrence.denotation lts) =
      semanticTableAt lts environment formula := by
  induction formula generalizing offset binderStack with
  | tt => rfl
  | ff => rfl
  | neg formula inductionHypothesis =>
      simp [sourceTableAt, semanticTableAt, SourceOccurrence.denotation,
        inductionHypothesis]
  | conj left right leftHypothesis rightHypothesis =>
      simp [sourceTableAt, semanticTableAt, SourceOccurrence.denotation,
        leftHypothesis, rightHypothesis]
  | disj left right leftHypothesis rightHypothesis =>
      simp [sourceTableAt, semanticTableAt, SourceOccurrence.denotation,
        leftHypothesis, rightHypothesis]
  | diamond action formula inductionHypothesis =>
      simp [sourceTableAt, semanticTableAt, SourceOccurrence.denotation,
        inductionHypothesis]
  | box action formula inductionHypothesis =>
      simp [sourceTableAt, semanticTableAt, SourceOccurrence.denotation,
        inductionHypothesis]
  | mu body inductionHypothesis =>
      simp [sourceTableAt, semanticTableAt, SourceOccurrence.denotation,
        inductionHypothesis]
  | nu body inductionHypothesis =>
      simp [sourceTableAt, semanticTableAt, SourceOccurrence.denotation,
        inductionHypothesis]
  | var index => rfl

/-- The semantic table has exactly one entry per source constructor. -/
theorem semanticTableAt_length {n : Nat} (lts : LTS State Action)
    (environment : Env State n) (formula : Formula Action n) :
    (semanticTableAt lts environment formula).length = formula.size := by
  induction formula with
  | tt => rfl
  | ff => rfl
  | neg formula inductionHypothesis =>
      simp [semanticTableAt, Formula.size, inductionHypothesis, Nat.add_comm]
  | conj left right leftHypothesis rightHypothesis =>
      simp [semanticTableAt, Formula.size, leftHypothesis, rightHypothesis,
        Nat.add_comm, Nat.add_assoc]
  | disj left right leftHypothesis rightHypothesis =>
      simp [semanticTableAt, Formula.size, leftHypothesis, rightHypothesis,
        Nat.add_comm, Nat.add_assoc]
  | diamond action formula inductionHypothesis =>
      simp [semanticTableAt, Formula.size, inductionHypothesis, Nat.add_comm]
  | box action formula inductionHypothesis =>
      simp [semanticTableAt, Formula.size, inductionHypothesis, Nat.add_comm]
  | mu body inductionHypothesis =>
      simp [semanticTableAt, Formula.size, inductionHypothesis, Nat.add_comm]
  | nu body inductionHypothesis =>
      simp [semanticTableAt, Formula.size, inductionHypothesis, Nat.add_comm]
  | var index => rfl

/-- The first annotation of a compiled segment is exactly the denotation of
its source formula. -/
theorem semanticTableAt_head {n : Nat} (lts : LTS State Action)
    (environment : Env State n) (formula : Formula Action n) :
    (semanticTableAt lts environment formula)[0]? =
      some (sat lts environment formula) := by
  cases formula <;> rfl

/-- Lookup of the root denotation of a semantic compiler segment inside a
larger complete table. -/
theorem semanticTableAt_root_lookup {n : Nat} (lts : LTS State Action)
    (offset : Nat) (environment : Env State n) (formula : Formula Action n)
    (table emitted suffix : List (Set State))
    (tableEq : table = emitted ++ semanticTableAt lts environment formula ++ suffix)
    (offsetEq : emitted.length = offset) :
    table[offset]? = some (sat lts environment formula) := by
  rw [tableEq, List.append_assoc, ← offsetEq,
    List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self]
  rw [List.getElem?_append_left]
  · exact semanticTableAt_head lts environment formula
  · rw [semanticTableAt_length]
    exact formula_size_positive formula

/-! ## Semantic integrity of compiled variable references -/

variable [Fintype State]

/-- A compiler reference denotes the predicate stored in its semantic
environment.  Observation references use the model valuation; binder
references use the semantic table entry at the introducing address. -/
def ReferencesDenote {n : Nat}
    (model : FiniteModel State Action Observation)
    (table : List (Set State))
    (references : Fin n → VariableReference Observation)
    (environment : Env State n) : Prop :=
  ∀ index, match references index with
    | .observation label => environment index = model.observationSet label
    | .binder address => table[address]? = some (environment index)

/-- Extending both reference environments at a table entry preserves their
semantic agreement. -/
theorem ReferencesDenote.extend {n : Nat}
    (model : FiniteModel State Action Observation)
    (table : List (Set State))
    (references : Fin n → VariableReference Observation)
    (environment : Env State n) (address : Nat) (denotation : Set State)
    (valid : ReferencesDenote model table references environment)
    (lookup : table[address]? = some denotation) :
    ReferencesDenote model table
      (extendVariableReferences references address)
      (environment.extend denotation) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · simpa [extendVariableReferences, Env.extend] using lookup
  · intro previous
    cases reference : references previous with
    | observation label =>
        simpa [extendVariableReferences, Env.extend, reference] using
          valid previous
    | binder binder =>
        simpa [extendVariableReferences, Env.extend, reference] using
          valid previous

/-- The part of node/denotation alignment needed for binder soundness.
Observation nodes denote their model valuation, and variable nodes denote the
semantic table entry at their introducing binder. -/
def VariableDenotationAligned
    (model : FiniteModel State Action Observation)
    (table : List (Set State)) :
    Node Action Observation → Set State → Prop
  | .observation label, denotation =>
      denotation = model.observationSet label
  | .variable binder, denotation =>
      table[binder]? = some denotation
  | _, _ => True

/-- A fixed-point node and its compiled body denote the same predicate.  This
is the local unfolding equation consumed when the evaluation game enters a
fixed-point body. -/
def FixedPointDenotationAligned (table : List (Set State)) :
    Node Action Observation → Set State → Prop
  | .fixedPoint _ _ child, denotation => table[child]? = some denotation
  | _, _ => True

/-- Local denotational equations for ordinary formula constructors.  Binder
and variable equalities are kept in their focused relations above because
they refer backwards or consume positivity; this relation covers the
non-cyclic constructors uniformly. -/
def ConstructorDenotationAligned
    (model : FiniteModel State Action Observation)
    (table : List (Set State)) :
    Node Action Observation → Set State → Prop
  | .truth value, denotation =>
      denotation = if value then Set.univ else ∅
  | .negation child, denotation =>
      ∃ childDenotation,
        table[child]? = some childDenotation ∧
          denotation = childDenotationᶜ
  | .conjunction left right, denotation =>
      ∃ leftDenotation rightDenotation,
        table[left]? = some leftDenotation ∧
          table[right]? = some rightDenotation ∧
          denotation = leftDenotation ∩ rightDenotation
  | .disjunction left right, denotation =>
      ∃ leftDenotation rightDenotation,
        table[left]? = some leftDenotation ∧
          table[right]? = some rightDenotation ∧
          denotation = leftDenotation ∪ rightDenotation
  | .diamond action child, denotation =>
      ∃ childDenotation,
        table[child]? = some childDenotation ∧
          denotation = {source | ∃ target,
            model.system.edge source action target = true ∧
              target ∈ childDenotation}
  | .box action child, denotation =>
      ∃ childDenotation,
        table[child]? = some childDenotation ∧
          denotation = {source | ∀ target,
            model.system.edge source action target = true →
              target ∈ childDenotation}
  | _, _ => True

/-- Structural compilation and semantic annotation agree at every ambient or
bound variable occurrence.  The theorem keeps one shared complete semantic
table while recursively moving through compiler segments, so a binder address
continues to mean the same predicate across nested and sibling subformulas. -/
theorem compileAt_variableDenotations {n : Nat}
    (model : FiniteModel State Action Observation)
    (offset depth : Nat)
    (references : Fin n → VariableReference Observation)
    (environment : Env State n) (formula : Formula Action n)
    (table emitted suffix : List (Set State))
    (tableEq : table = emitted ++
      semanticTableAt model.system.toLTS environment formula ++ suffix)
    (offsetEq : emitted.length = offset)
    (referencesDenote : ReferencesDenote model table references environment) :
    List.Forall₂ (VariableDenotationAligned model table)
      (compileAt offset depth references formula)
      (semanticTableAt model.system.toLTS environment formula) := by
  induction formula generalizing offset depth emitted suffix with
  | tt => exact .cons trivial .nil
  | ff => exact .cons trivial .nil
  | neg formula inductionHypothesis =>
      apply List.Forall₂.cons trivial
      apply inductionHypothesis (offset := offset + 1) (depth := depth)
        (emitted := emitted ++ [sat model.system.toLTS environment (.neg formula)])
        (suffix := suffix)
      · simpa [semanticTableAt, List.append_assoc] using tableEq
      · simp [offsetEq]
      · exact referencesDenote
  | conj left right leftHypothesis rightHypothesis =>
      apply List.Forall₂.cons trivial
      apply List.rel_append
      · apply leftHypothesis (offset := offset + 1) (depth := depth)
          (emitted := emitted ++
            [sat model.system.toLTS environment (.conj left right)])
          (suffix := semanticTableAt model.system.toLTS environment right ++ suffix)
        · simpa [semanticTableAt, List.append_assoc] using tableEq
        · simp [offsetEq]
        · exact referencesDenote
      · apply rightHypothesis
          (offset := offset + 1 + left.size) (depth := depth)
          (emitted := emitted ++
            [sat model.system.toLTS environment (.conj left right)] ++
              semanticTableAt model.system.toLTS environment left)
          (suffix := suffix)
        · simpa [semanticTableAt, List.append_assoc] using tableEq
        · simp [semanticTableAt_length, offsetEq, Nat.add_comm, Nat.add_assoc]
        · exact referencesDenote
  | disj left right leftHypothesis rightHypothesis =>
      apply List.Forall₂.cons trivial
      apply List.rel_append
      · apply leftHypothesis (offset := offset + 1) (depth := depth)
          (emitted := emitted ++
            [sat model.system.toLTS environment (.disj left right)])
          (suffix := semanticTableAt model.system.toLTS environment right ++ suffix)
        · simpa [semanticTableAt, List.append_assoc] using tableEq
        · simp [offsetEq]
        · exact referencesDenote
      · apply rightHypothesis
          (offset := offset + 1 + left.size) (depth := depth)
          (emitted := emitted ++
            [sat model.system.toLTS environment (.disj left right)] ++
              semanticTableAt model.system.toLTS environment left)
          (suffix := suffix)
        · simpa [semanticTableAt, List.append_assoc] using tableEq
        · simp [semanticTableAt_length, offsetEq, Nat.add_comm, Nat.add_assoc]
        · exact referencesDenote
  | diamond action formula inductionHypothesis =>
      apply List.Forall₂.cons trivial
      apply inductionHypothesis (offset := offset + 1) (depth := depth)
        (emitted := emitted ++
          [sat model.system.toLTS environment (.diamond action formula)])
        (suffix := suffix)
      · simpa [semanticTableAt, List.append_assoc] using tableEq
      · simp [offsetEq]
      · exact referencesDenote
  | box action formula inductionHypothesis =>
      apply List.Forall₂.cons trivial
      apply inductionHypothesis (offset := offset + 1) (depth := depth)
        (emitted := emitted ++
          [sat model.system.toLTS environment (.box action formula)])
        (suffix := suffix)
      · simpa [semanticTableAt, List.append_assoc] using tableEq
      · simp [offsetEq]
      · exact referencesDenote
  | mu body inductionHypothesis =>
      let fixedPoint := sat model.system.toLTS environment (.mu body)
      have rootLookup : table[offset]? = some fixedPoint := by
        rw [tableEq, ← offsetEq]
        simp [semanticTableAt, fixedPoint]
      apply List.Forall₂.cons trivial
      apply inductionHypothesis (offset := offset + 1) (depth := depth + 1)
        (references := extendVariableReferences references offset)
        (environment := environment.extend fixedPoint)
        (emitted := emitted ++ [fixedPoint]) (suffix := suffix)
      · simpa [semanticTableAt, fixedPoint, List.append_assoc] using tableEq
      · simp [offsetEq]
      · exact referencesDenote.extend model table references environment offset
          fixedPoint rootLookup
  | nu body inductionHypothesis =>
      let fixedPoint := sat model.system.toLTS environment (.nu body)
      have rootLookup : table[offset]? = some fixedPoint := by
        rw [tableEq, ← offsetEq]
        simp [semanticTableAt, fixedPoint]
      apply List.Forall₂.cons trivial
      apply inductionHypothesis (offset := offset + 1) (depth := depth + 1)
        (references := extendVariableReferences references offset)
        (environment := environment.extend fixedPoint)
        (emitted := emitted ++ [fixedPoint]) (suffix := suffix)
      · simpa [semanticTableAt, fixedPoint, List.append_assoc] using tableEq
      · simp [offsetEq]
      · exact referencesDenote.extend model table references environment offset
          fixedPoint rootLookup
  | var index =>
      cases reference : references index with
      | observation label =>
          rw [compileAt, reference, semanticTableAt]
          apply List.Forall₂.cons
          · simpa [VariableDenotationAligned, sat, satisfies, reference] using
              referencesDenote index
          · exact .nil
      | binder address =>
          rw [compileAt, reference, semanticTableAt]
          apply List.Forall₂.cons
          · simpa [VariableDenotationAligned, sat, satisfies, reference] using
              referencesDenote index
          · exact .nil

omit [Fintype State] in
/-- Every admitted fixed-point node is aligned with an equal-denotation body
entry in the complete semantic table.  Positivity is used exactly at the μ/ν
unfolding steps. -/
theorem compileAt_fixedPointDenotations {n : Nat}
    (lts : LTS State Action) (offset depth : Nat)
    (references : Fin n → VariableReference Observation)
    (environment : Env State n) (formula : Formula Action n)
    (table emitted suffix : List (Set State))
    (tableEq : table = emitted ++ semanticTableAt lts environment formula ++ suffix)
    (offsetEq : emitted.length = offset)
    (positive : fixedPointsPositive formula = true) :
    List.Forall₂ (FixedPointDenotationAligned table)
      (compileAt offset depth references formula)
      (semanticTableAt lts environment formula) := by
  induction formula generalizing offset depth emitted suffix with
  | tt => exact .cons trivial .nil
  | ff => exact .cons trivial .nil
  | neg formula inductionHypothesis =>
      simp only [fixedPointsPositive] at positive
      apply List.Forall₂.cons trivial
      apply inductionHypothesis (offset := offset + 1) (depth := depth)
        (emitted := emitted ++ [sat lts environment (.neg formula)])
        (suffix := suffix)
      · simpa [semanticTableAt, List.append_assoc] using tableEq
      · simp [offsetEq]
      · exact positive
  | conj left right leftHypothesis rightHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      apply List.Forall₂.cons trivial
      apply List.rel_append
      · apply leftHypothesis (offset := offset + 1) (depth := depth)
          (emitted := emitted ++ [sat lts environment (.conj left right)])
          (suffix := semanticTableAt lts environment right ++ suffix)
        · simpa [semanticTableAt, List.append_assoc] using tableEq
        · simp [offsetEq]
        · exact positive.1
      · apply rightHypothesis
          (offset := offset + 1 + left.size) (depth := depth)
          (emitted := emitted ++ [sat lts environment (.conj left right)] ++
            semanticTableAt lts environment left)
          (suffix := suffix)
        · simpa [semanticTableAt, List.append_assoc] using tableEq
        · simp [semanticTableAt_length, offsetEq, Nat.add_comm, Nat.add_assoc]
        · exact positive.2
  | disj left right leftHypothesis rightHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      apply List.Forall₂.cons trivial
      apply List.rel_append
      · apply leftHypothesis (offset := offset + 1) (depth := depth)
          (emitted := emitted ++ [sat lts environment (.disj left right)])
          (suffix := semanticTableAt lts environment right ++ suffix)
        · simpa [semanticTableAt, List.append_assoc] using tableEq
        · simp [offsetEq]
        · exact positive.1
      · apply rightHypothesis
          (offset := offset + 1 + left.size) (depth := depth)
          (emitted := emitted ++ [sat lts environment (.disj left right)] ++
            semanticTableAt lts environment left)
          (suffix := suffix)
        · simpa [semanticTableAt, List.append_assoc] using tableEq
        · simp [semanticTableAt_length, offsetEq, Nat.add_comm, Nat.add_assoc]
        · exact positive.2
  | diamond action formula inductionHypothesis =>
      simp only [fixedPointsPositive] at positive
      apply List.Forall₂.cons trivial
      apply inductionHypothesis (offset := offset + 1) (depth := depth)
        (emitted := emitted ++ [sat lts environment (.diamond action formula)])
        (suffix := suffix)
      · simpa [semanticTableAt, List.append_assoc] using tableEq
      · simp [offsetEq]
      · exact positive
  | box action formula inductionHypothesis =>
      simp only [fixedPointsPositive] at positive
      apply List.Forall₂.cons trivial
      apply inductionHypothesis (offset := offset + 1) (depth := depth)
        (emitted := emitted ++ [sat lts environment (.box action formula)])
        (suffix := suffix)
      · simpa [semanticTableAt, List.append_assoc] using tableEq
      · simp [offsetEq]
      · exact positive
  | mu body inductionHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      let fixedPoint := sat lts environment (.mu body)
      have unfoldEq :
          fixedPoint = sat lts (environment.extend fixedPoint) body := by
        ext state
        exact satisfies_mu_unfold_iff lts environment body positive.1 state
      have childLookup : table[offset + 1]? = some fixedPoint := by
        have expanded : table =
            (emitted ++ [fixedPoint]) ++
              (semanticTableAt lts (environment.extend fixedPoint) body ++
                suffix) := by
          simpa [semanticTableAt, fixedPoint, List.append_assoc] using tableEq
        rw [expanded]
        have prefixLength : (emitted ++ [fixedPoint]).length = offset + 1 := by
          simp [offsetEq]
        rw [← prefixLength, List.getElem?_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self]
        rw [List.getElem?_append_left]
        · simpa [← unfoldEq] using
            semanticTableAt_head lts (environment.extend fixedPoint) body
        · rw [semanticTableAt_length]
          exact formula_size_positive body
      apply List.Forall₂.cons
      · exact childLookup
      · apply inductionHypothesis (offset := offset + 1) (depth := depth + 1)
          (references := extendVariableReferences references offset)
          (environment := environment.extend fixedPoint)
          (emitted := emitted ++ [fixedPoint]) (suffix := suffix)
        · simpa [semanticTableAt, fixedPoint, List.append_assoc] using tableEq
        · simp [offsetEq]
        · exact positive.2
  | nu body inductionHypothesis =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      let fixedPoint := sat lts environment (.nu body)
      have unfoldEq :
          fixedPoint = sat lts (environment.extend fixedPoint) body := by
        ext state
        exact satisfies_nu_unfold_iff lts environment body positive.1 state
      have childLookup : table[offset + 1]? = some fixedPoint := by
        have expanded : table =
            (emitted ++ [fixedPoint]) ++
              (semanticTableAt lts (environment.extend fixedPoint) body ++
                suffix) := by
          simpa [semanticTableAt, fixedPoint, List.append_assoc] using tableEq
        rw [expanded]
        have prefixLength : (emitted ++ [fixedPoint]).length = offset + 1 := by
          simp [offsetEq]
        rw [← prefixLength, List.getElem?_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self]
        rw [List.getElem?_append_left]
        · simpa [← unfoldEq] using
            semanticTableAt_head lts (environment.extend fixedPoint) body
        · rw [semanticTableAt_length]
          exact formula_size_positive body
      apply List.Forall₂.cons
      · exact childLookup
      · apply inductionHypothesis (offset := offset + 1) (depth := depth + 1)
          (references := extendVariableReferences references offset)
          (environment := environment.extend fixedPoint)
          (emitted := emitted ++ [fixedPoint]) (suffix := suffix)
        · simpa [semanticTableAt, fixedPoint, List.append_assoc] using tableEq
        · simp [offsetEq]
        · exact positive.2
  | var index =>
      cases reference : references index <;>
        simp [compileAt, semanticTableAt, reference,
          FixedPointDenotationAligned]

/-- The executable compiler and semantic table satisfy the ordinary
constructor equations at every nested occurrence. -/
theorem compileAt_constructorDenotations {n : Nat}
    (model : FiniteModel State Action Observation)
    (offset depth : Nat)
    (references : Fin n → VariableReference Observation)
    (environment : Env State n) (formula : Formula Action n)
    (table emitted suffix : List (Set State))
    (tableEq : table = emitted ++
      semanticTableAt model.system.toLTS environment formula ++ suffix)
    (offsetEq : emitted.length = offset) :
    List.Forall₂ (ConstructorDenotationAligned model table)
      (compileAt offset depth references formula)
      (semanticTableAt model.system.toLTS environment formula) := by
  induction formula generalizing offset depth emitted suffix with
  | tt =>
      apply List.Forall₂.cons
      · ext state
        simp [sat, satisfies]
      · exact .nil
  | ff =>
      apply List.Forall₂.cons
      · ext state
        simp [sat, satisfies]
      · exact .nil
  | neg formula inductionHypothesis =>
      let root := sat model.system.toLTS environment (.neg formula)
      have childTableEq : table = (emitted ++ [root]) ++
          semanticTableAt model.system.toLTS environment formula ++ suffix := by
        simpa [semanticTableAt, root, List.append_assoc] using tableEq
      have childLookup := semanticTableAt_root_lookup model.system.toLTS
        (offset + 1) environment formula table (emitted ++ [root]) suffix
        childTableEq (by simp [offsetEq])
      apply List.Forall₂.cons
      · refine ⟨sat model.system.toLTS environment formula, childLookup, ?_⟩
        ext state
        simp [sat, satisfies]
      · exact inductionHypothesis (offset := offset + 1) (depth := depth)
          (references := references) (environment := environment)
          (emitted := emitted ++ [root]) (suffix := suffix)
          childTableEq (by simp [offsetEq])
  | conj left right leftHypothesis rightHypothesis =>
      let root := sat model.system.toLTS environment (.conj left right)
      have leftTableEq : table = (emitted ++ [root]) ++
          semanticTableAt model.system.toLTS environment left ++
            (semanticTableAt model.system.toLTS environment right ++ suffix) := by
        simpa [semanticTableAt, root, List.append_assoc] using tableEq
      have rightTableEq : table =
          (emitted ++ [root] ++
            semanticTableAt model.system.toLTS environment left) ++
          semanticTableAt model.system.toLTS environment right ++ suffix := by
        simpa [semanticTableAt, root, List.append_assoc] using tableEq
      have leftLookup := semanticTableAt_root_lookup model.system.toLTS
        (offset + 1) environment left table (emitted ++ [root])
        (semanticTableAt model.system.toLTS environment right ++ suffix)
        leftTableEq (by simp [offsetEq])
      have rightLookup := semanticTableAt_root_lookup model.system.toLTS
        (offset + 1 + left.size) environment right table
        (emitted ++ [root] ++ semanticTableAt model.system.toLTS environment left)
        suffix rightTableEq (by
          simp [semanticTableAt_length, offsetEq, Nat.add_comm, Nat.add_assoc])
      apply List.Forall₂.cons
      · refine ⟨sat model.system.toLTS environment left,
          sat model.system.toLTS environment right,
          leftLookup, rightLookup, ?_⟩
        ext state
        simp [sat, satisfies]
      · apply List.rel_append
        · exact leftHypothesis (offset := offset + 1) (depth := depth)
            (references := references) (environment := environment)
            (emitted := emitted ++ [root])
            (suffix := semanticTableAt model.system.toLTS environment right ++
              suffix) leftTableEq (by simp [offsetEq])
        · exact rightHypothesis
            (offset := offset + 1 + left.size) (depth := depth)
            (references := references) (environment := environment)
            (emitted := emitted ++ [root] ++
              semanticTableAt model.system.toLTS environment left)
            (suffix := suffix) rightTableEq (by
              simp [semanticTableAt_length, offsetEq, Nat.add_comm, Nat.add_assoc])
  | disj left right leftHypothesis rightHypothesis =>
      let root := sat model.system.toLTS environment (.disj left right)
      have leftTableEq : table = (emitted ++ [root]) ++
          semanticTableAt model.system.toLTS environment left ++
            (semanticTableAt model.system.toLTS environment right ++ suffix) := by
        simpa [semanticTableAt, root, List.append_assoc] using tableEq
      have rightTableEq : table =
          (emitted ++ [root] ++
            semanticTableAt model.system.toLTS environment left) ++
          semanticTableAt model.system.toLTS environment right ++ suffix := by
        simpa [semanticTableAt, root, List.append_assoc] using tableEq
      have leftLookup := semanticTableAt_root_lookup model.system.toLTS
        (offset + 1) environment left table (emitted ++ [root])
        (semanticTableAt model.system.toLTS environment right ++ suffix)
        leftTableEq (by simp [offsetEq])
      have rightLookup := semanticTableAt_root_lookup model.system.toLTS
        (offset + 1 + left.size) environment right table
        (emitted ++ [root] ++ semanticTableAt model.system.toLTS environment left)
        suffix rightTableEq (by
          simp [semanticTableAt_length, offsetEq, Nat.add_comm, Nat.add_assoc])
      apply List.Forall₂.cons
      · refine ⟨sat model.system.toLTS environment left,
          sat model.system.toLTS environment right,
          leftLookup, rightLookup, ?_⟩
        ext state
        simp [sat, satisfies]
      · apply List.rel_append
        · exact leftHypothesis (offset := offset + 1) (depth := depth)
            (references := references) (environment := environment)
            (emitted := emitted ++ [root])
            (suffix := semanticTableAt model.system.toLTS environment right ++
              suffix) leftTableEq (by simp [offsetEq])
        · exact rightHypothesis
            (offset := offset + 1 + left.size) (depth := depth)
            (references := references) (environment := environment)
            (emitted := emitted ++ [root] ++
              semanticTableAt model.system.toLTS environment left)
            (suffix := suffix) rightTableEq (by
              simp [semanticTableAt_length, offsetEq, Nat.add_comm, Nat.add_assoc])
  | diamond action formula inductionHypothesis =>
      let root := sat model.system.toLTS environment (.diamond action formula)
      have childTableEq : table = (emitted ++ [root]) ++
          semanticTableAt model.system.toLTS environment formula ++ suffix := by
        simpa [semanticTableAt, root, List.append_assoc] using tableEq
      have childLookup := semanticTableAt_root_lookup model.system.toLTS
        (offset + 1) environment formula table (emitted ++ [root]) suffix
        childTableEq (by simp [offsetEq])
      apply List.Forall₂.cons
      · refine ⟨sat model.system.toLTS environment formula, childLookup, ?_⟩
        ext state
        simp [sat, satisfies, LTS.successors, FiniteLTS.toLTS]
      · exact inductionHypothesis (offset := offset + 1) (depth := depth)
          (references := references) (environment := environment)
          (emitted := emitted ++ [root]) (suffix := suffix)
          childTableEq (by simp [offsetEq])
  | box action formula inductionHypothesis =>
      let root := sat model.system.toLTS environment (.box action formula)
      have childTableEq : table = (emitted ++ [root]) ++
          semanticTableAt model.system.toLTS environment formula ++ suffix := by
        simpa [semanticTableAt, root, List.append_assoc] using tableEq
      have childLookup := semanticTableAt_root_lookup model.system.toLTS
        (offset + 1) environment formula table (emitted ++ [root]) suffix
        childTableEq (by simp [offsetEq])
      apply List.Forall₂.cons
      · refine ⟨sat model.system.toLTS environment formula, childLookup, ?_⟩
        ext state
        simp [sat, satisfies, LTS.successors, FiniteLTS.toLTS]
      · exact inductionHypothesis (offset := offset + 1) (depth := depth)
          (references := references) (environment := environment)
          (emitted := emitted ++ [root]) (suffix := suffix)
          childTableEq (by simp [offsetEq])
  | mu body inductionHypothesis =>
      let root := sat model.system.toLTS environment (.mu body)
      have childTableEq : table = (emitted ++ [root]) ++
          semanticTableAt model.system.toLTS (environment.extend root) body ++
            suffix := by
        simpa [semanticTableAt, root, List.append_assoc] using tableEq
      apply List.Forall₂.cons trivial
      exact inductionHypothesis (offset := offset + 1) (depth := depth + 1)
        (references := extendVariableReferences references offset)
        (environment := environment.extend root)
        (emitted := emitted ++ [root]) (suffix := suffix)
        childTableEq (by simp [offsetEq])
  | nu body inductionHypothesis =>
      let root := sat model.system.toLTS environment (.nu body)
      have childTableEq : table = (emitted ++ [root]) ++
          semanticTableAt model.system.toLTS (environment.extend root) body ++
            suffix := by
        simpa [semanticTableAt, root, List.append_assoc] using tableEq
      apply List.Forall₂.cons trivial
      exact inductionHypothesis (offset := offset + 1) (depth := depth + 1)
        (references := extendVariableReferences references offset)
        (environment := environment.extend root)
        (emitted := emitted ++ [root]) (suffix := suffix)
        childTableEq (by simp [offsetEq])
  | var index =>
      cases reference : references index <;>
        simp [compileAt, semanticTableAt, reference,
          ConstructorDenotationAligned]

end Mettapedia.Logic.ModalMuCalculus.EvaluationGame.Adequacy

namespace Mettapedia.Logic.ModalMuCalculus.EvaluationGame.Program

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.ModalMuCalculus.EvaluationGame.Adequacy
open Mettapedia.Logic.ModalQuantaleSemantics.Boolean
open Mettapedia.Order.FiniteSetFixedPoints

universe uState uAction uObservation

variable {State : Type uState} {Action : Type uAction}
  {Observation : Type uObservation}

variable [Fintype State]

/-- Semantic annotations for the same model and observation environment used
by the executable evaluation game. -/
noncomputable def semanticTable (program : Program Action Observation)
    (model : FiniteModel State Action Observation) : List (Set State) :=
  semanticTableAt model.system.toLTS (program.semanticEnv model)
    program.formula

/-- Retained source occurrences aligned with the program's executable node
table. -/
noncomputable def sourceTable (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    List (SourceOccurrence State Action Observation) :=
  sourceTableAt model.system.toLTS 0 (program.semanticEnv model)
    (fun index => .observation (program.observation index)) [] program.formula

/-- Erasing the retained source information yields the semantic table. -/
theorem sourceTable_denotations (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    (program.sourceTable model).map
        (SourceOccurrence.denotation model.system.toLTS) =
      program.semanticTable model := by
  exact sourceTableAt_denotations model.system.toLTS 0
    (program.semanticEnv model)
    (fun index => .observation (program.observation index)) [] program.formula

/-- The retained source and executable node tables have identical length. -/
theorem sourceTable_length (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    (program.sourceTable model).length = program.nodes.length := by
  have denotations := congrArg List.length (program.sourceTable_denotations model)
  rw [EvaluationGame.Program.nodes_length]
  simpa [List.length_map, semanticTable, semanticTableAt_length] using denotations

/-- The retained source constructor at every address matches the executable
node at that address. -/
theorem sourceTable_matchesNodes (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    List.Forall₂ (fun node occurrence => occurrence.MatchesNode node)
      program.nodes (program.sourceTable model) := by
  exact sourceTableAt_matchesNodes model.system.toLTS 0 0
    (program.semanticEnv model)
    (fun index => .observation (program.observation index)) [] program.formula rfl

/-- Positivity admission applies to every nested binder occurrence retained by
the proof table. -/
theorem sourceTable_binderPositive (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    (program.sourceTable model).Forall SourceOccurrence.BinderPositive := by
  exact sourceTableAt_binderPositive model.system.toLTS 0
    (program.semanticEnv model)
    (fun index => .observation (program.observation index)) [] program.formula
    program.positive

/-- Every retained source occurrence has a lexical binder stack equal to the
binder prefix of its compiler reference environment. -/
theorem sourceTable_binderStackAligned (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    (program.sourceTable model).Forall (fun occurrence =>
      BinderStackAligned occurrence.references occurrence.binderStack) := by
  exact sourceTableAt_binderStackAligned model.system.toLTS 0
    (program.semanticEnv model)
    (fun index => .observation (program.observation index)) [] program.formula
    (binderStackAligned_observations program.observation)

theorem semanticTable_length (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    (program.semanticTable model).length = program.nodes.length := by
  rw [semanticTable, semanticTableAt_length, EvaluationGame.Program.nodes_length]

/-- The closed program's initial compiler environments agree with the model:
every ambient reference denotes exactly its observation set. -/
theorem rootReferencesDenote (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    ReferencesDenote model (program.semanticTable model)
      (fun index => .observation (program.observation index))
      (program.semanticEnv model) := by
  intro index
  rfl

/-- Every generated observation or binder node is paired with the predicate
denoted by its compiler environment. -/
theorem variableDenotationsAligned (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    List.Forall₂
      (VariableDenotationAligned model (program.semanticTable model))
      program.nodes (program.semanticTable model) := by
  unfold EvaluationGame.Program.nodes semanticTable
  apply compileAt_variableDenotations model 0 0
    (fun index => .observation (program.observation index))
    (program.semanticEnv model) program.formula
    (semanticTableAt model.system.toLTS (program.semanticEnv model)
      program.formula) [] []
  · simp
  · rfl
  · exact program.rootReferencesDenote model

/-- Every generated fixed-point node is paired with an equal-denotation body
entry at its child address. -/
theorem fixedPointDenotationsAligned (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    List.Forall₂
      (FixedPointDenotationAligned (program.semanticTable model))
      program.nodes (program.semanticTable model) := by
  unfold EvaluationGame.Program.nodes semanticTable
  apply compileAt_fixedPointDenotations model.system.toLTS 0 0
    (fun index => .observation (program.observation index))
    (program.semanticEnv model) program.formula
    (semanticTableAt model.system.toLTS (program.semanticEnv model)
      program.formula) [] []
  · simp
  · rfl
  · exact program.positive

/-- Every ordinary compiled constructor satisfies its local denotational
equation in the complete semantic table. -/
theorem constructorDenotationsAligned (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    List.Forall₂
      (ConstructorDenotationAligned model (program.semanticTable model))
      program.nodes (program.semanticTable model) := by
  unfold EvaluationGame.Program.nodes semanticTable
  apply compileAt_constructorDenotations model 0 0
    (fun index => .observation (program.observation index))
    (program.semanticEnv model) program.formula
    (semanticTableAt model.system.toLTS (program.semanticEnv model)
      program.formula) [] []
  · simp
  · rfl

/-- Denotation attached to one compiled formula address. -/
noncomputable def semanticSet (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (address : Fin program.nodes.length) : Set State :=
  (program.semanticTable model)[address.val]'(by
    rw [program.semanticTable_length model]
    exact address.isLt)

/-- A successful semantic-table lookup identifies the semantic set at the
corresponding executable address. -/
theorem semanticSet_eq_of_getElem?_eq_some
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (address : Nat) (denotation : Set State)
    (lookup : (program.semanticTable model)[address]? = some denotation)
    (bound : address < program.nodes.length) :
    program.semanticSet model ⟨address, bound⟩ = denotation := by
  obtain ⟨_tableBound, value⟩ := List.getElem?_eq_some_iff.mp lookup
  unfold semanticSet
  simpa using value

/-- Retained source occurrence at one executable address. -/
noncomputable def sourceAt (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (address : Fin program.nodes.length) :
    SourceOccurrence State Action Observation :=
  (program.sourceTable model).get ⟨address.val, by
    rw [program.sourceTable_length model]
    exact address.isLt⟩

/-- The source occurrence selected by an address matches the executable node
selected by the same address. -/
theorem sourceAt_matchesNode (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (position : Position State Action Observation program) :
    (program.sourceAt model position.address).MatchesNode
      (program.nodeAt position) := by
  have aligned := program.sourceTable_matchesNodes model
  have sourceBound : position.address.val <
      (program.sourceTable model).length := by
    rw [program.sourceTable_length model]
    exact position.address.isLt
  have relation := aligned.get position.address.isLt sourceBound
  simpa [sourceAt, EvaluationGame.Program.nodeAt] using relation

/-- Every source occurrence selected from an admitted program satisfies the
binder-positivity condition. -/
theorem sourceAt_binderPositive (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (address : Fin program.nodes.length) :
    (program.sourceAt model address).BinderPositive := by
  have allPositive := program.sourceTable_binderPositive model
  apply (List.forall_iff_forall_mem.mp allPositive)
  exact List.get_mem (program.sourceTable model)
    ⟨address.val, by
      rw [program.sourceTable_length model]
      exact address.isLt⟩

/-- The lexical stack selected at any executable address agrees exactly with
the binder prefix of that occurrence's compiler references. -/
theorem sourceAt_binderStackAligned (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (address : Fin program.nodes.length) :
    BinderStackAligned (program.sourceAt model address).references
      (program.sourceAt model address).binderStack := by
  have allAligned := program.sourceTable_binderStackAligned model
  apply (List.forall_iff_forall_mem.mp allAligned)
  exact List.get_mem (program.sourceTable model)
    ⟨address.val, by
      rw [program.sourceTable_length model]
      exact address.isLt⟩

/-- A compiled fixed-point depth is exactly the lexical binder depth of its
retained source occurrence. -/
theorem sourceAt_fixedPoint_depth
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (position : Position State Action Observation program)
    (kind : FixedPointKind) (depth child : Nat)
    (sourceNode : program.nodeAt position = .fixedPoint kind depth child) :
    (program.sourceAt model position.address).binderStack.length = depth := by
  have nodeMatches := program.sourceAt_matchesNode model position
  rw [sourceNode] at nodeMatches
  generalize formulaEq :
    (program.sourceAt model position.address).formula = formula at nodeMatches
  cases kind <;> cases formula <;>
    simp [SourceOccurrence.MatchesNode, formulaEq] at nodeMatches ⊢
  all_goals exact nodeMatches

/-- Every executable variable back-edge returns to an enclosing binder in the
retained lexical stack. -/
theorem sourceAt_variable_binder_mem
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (position : Position State Action Observation program) (binder : Nat)
    (sourceNode : program.nodeAt position = .variable binder) :
    binder ∈ (program.sourceAt model position.address).binderStack := by
  let occurrence := program.sourceAt model position.address
  have nodeMatches := program.sourceAt_matchesNode model position
  rw [sourceNode] at nodeMatches
  have aligned := program.sourceAt_binderStackAligned model position.address
  change BinderStackAligned occurrence.references occurrence.binderStack at aligned
  change occurrence.MatchesNode (.variable binder) at nodeMatches
  generalize formulaEq : occurrence.formula = formula at nodeMatches
  cases formula with
  | var index =>
      apply aligned.binder_mem
      simpa [SourceOccurrence.MatchesNode, formulaEq] using nodeMatches
  | tt | ff | neg | conj | disj | diamond | box | mu | nu =>
      simp [SourceOccurrence.MatchesNode, formulaEq] at nodeMatches

/-- Merely entering fixed-point syntax carries no parity charge.  Recursion is
charged at the bound-variable occurrence that returns to the binder. -/
theorem sourceAt_fixedPoint_priority_zero
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (position : Position State Action Observation program)
    (kind : FixedPointKind) (depth child : Nat)
    (sourceNode : program.nodeAt position = .fixedPoint kind depth child) :
    program.gamePriority model position = 0 := by
  simp [EvaluationGame.Program.gamePriority, sourceNode]

/-- The denotation retained with a source occurrence is exactly the semantic
set selected by the same executable address. -/
theorem sourceAt_denotation (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (address : Fin program.nodes.length) :
    (program.sourceAt model address).denotation model.system.toLTS =
      program.semanticSet model address := by
  have tableEq := program.sourceTable_denotations model
  have sourceBound : address.val < (program.sourceTable model).length := by
    rw [program.sourceTable_length model]
    exact address.isLt
  have semanticBound : address.val < (program.semanticTable model).length := by
    rw [program.semanticTable_length model]
    exact address.isLt
  have atAddress := congrArg
    (fun table => table[address.val]?) tableEq
  have sourceLookup :
      ((program.sourceTable model).map
        (SourceOccurrence.denotation model.system.toLTS))[address.val]? =
        some ((program.sourceAt model address).denotation
          model.system.toLTS) := by
    simp [sourceAt, sourceBound]
  have semanticLookup :
      (program.semanticTable model)[address.val]? =
        some (program.semanticSet model address) := by
    simp [semanticSet, semanticBound]
  rw [sourceLookup, semanticLookup] at atAddress
  exact Option.some.inj atAddress

/-- At a variable occurrence, the current semantic set is exactly the table
entry of its introducing binder. -/
theorem variable_semanticSet_lookup
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source : Position State Action Observation program) (binder : Nat)
    (sourceNode : program.nodeAt source = .variable binder) :
    (program.semanticTable model)[binder]? =
      some (program.semanticSet model source.address) := by
  have aligned := program.variableDenotationsAligned model
  have semanticBound : source.address.val <
      (program.semanticTable model).length := by
    rw [program.semanticTable_length model]
    exact source.address.isLt
  have relation := aligned.get source.address.isLt semanticBound
  have nodeEq : program.nodes.get source.address = .variable binder := by
    simpa [EvaluationGame.Program.nodeAt] using sourceNode
  rw [nodeEq] at relation
  simpa [VariableDenotationAligned, semanticSet] using relation

/-- Local observation/binder denotation equation at one game position. -/
theorem variableDenotationAt
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source : Position State Action Observation program) :
    VariableDenotationAligned model (program.semanticTable model)
      (program.nodeAt source) (program.semanticSet model source.address) := by
  have aligned := program.variableDenotationsAligned model
  have semanticBound : source.address.val <
      (program.semanticTable model).length := by
    rw [program.semanticTable_length model]
    exact source.address.isLt
  have relation := aligned.get source.address.isLt semanticBound
  simpa [EvaluationGame.Program.nodeAt, semanticSet] using relation

/-- At a fixed-point occurrence, the compiled body child has exactly the same
semantic set as the binder occurrence. -/
theorem fixedPoint_semanticSet_lookup
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source : Position State Action Observation program)
    (kind : FixedPointKind) (depth child : Nat)
    (sourceNode : program.nodeAt source = .fixedPoint kind depth child) :
    (program.semanticTable model)[child]? =
      some (program.semanticSet model source.address) := by
  have aligned := program.fixedPointDenotationsAligned model
  have semanticBound : source.address.val <
      (program.semanticTable model).length := by
    rw [program.semanticTable_length model]
    exact source.address.isLt
  have relation := aligned.get source.address.isLt semanticBound
  have nodeEq : program.nodes.get source.address =
      .fixedPoint kind depth child := by
    simpa [EvaluationGame.Program.nodeAt] using sourceNode
  rw [nodeEq] at relation
  simpa [FixedPointDenotationAligned, semanticSet] using relation

/-- Local constructor equation at one game position. -/
theorem constructorDenotationAt
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source : Position State Action Observation program) :
    ConstructorDenotationAligned model (program.semanticTable model)
      (program.nodeAt source) (program.semanticSet model source.address) := by
  have aligned := program.constructorDenotationsAligned model
  have semanticBound : source.address.val <
      (program.semanticTable model).length := by
    rw [program.semanticTable_length model]
    exact source.address.isLt
  have relation := aligned.get source.address.isLt semanticBound
  simpa [EvaluationGame.Program.nodeAt, semanticSet] using relation

/-- A legal variable back-edge preserves not only the binder address, state,
and polarity, but also the exact denotational predicate attached to the game
position. -/
theorem variable_edge_semanticSet
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source target : Position State Action Observation program)
    (binder : Nat)
    (sourceNode : program.nodeAt source = .variable binder)
    (edge : program.gameEdge model source target = true) :
    program.semanticSet model target.address =
      program.semanticSet model source.address := by
  have edgeFacts :
      (target.state = source.state ∧ target.polarity = source.polarity) ∧
        target.address.val = binder := by
    simpa [EvaluationGame.Program.gameEdge, sourceNode,
      EvaluationGame.Program.sameStateAndPolarity,
      EvaluationGame.Program.addressIs, Bool.and_eq_true] using edge
  have lookup := program.variable_semanticSet_lookup model source binder sourceNode
  obtain ⟨binderBound, binderValue⟩ := List.getElem?_eq_some_iff.mp lookup
  change (program.semanticTable model).get
      ⟨target.address.val, by
        rw [program.semanticTable_length model]
        exact target.address.isLt⟩ =
    program.semanticSet model source.address
  simpa [edgeFacts.2] using binderValue

/-- Entering the body of a fixed point preserves the exact semantic set. -/
theorem fixedPoint_edge_semanticSet
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source target : Position State Action Observation program)
    (kind : FixedPointKind) (depth child : Nat)
    (sourceNode : program.nodeAt source = .fixedPoint kind depth child)
    (edge : program.gameEdge model source target = true) :
    program.semanticSet model target.address =
      program.semanticSet model source.address := by
  have edgeFacts :
      (target.state = source.state ∧ target.polarity = source.polarity) ∧
        target.address.val = child := by
    simpa [EvaluationGame.Program.gameEdge, sourceNode,
      EvaluationGame.Program.sameStateAndPolarity,
      EvaluationGame.Program.addressIs, Bool.and_eq_true] using edge
  have lookup := program.fixedPoint_semanticSet_lookup model source kind depth child
    sourceNode
  obtain ⟨childBound, childValue⟩ := List.getElem?_eq_some_iff.mp lookup
  change (program.semanticTable model).get
      ⟨target.address.val, by
        rw [program.semanticTable_length model]
        exact target.address.isLt⟩ =
    program.semanticSet model source.address
  simpa [edgeFacts.2] using childValue

/-- The root annotation is the denotation of the complete source formula. -/
theorem semanticSet_root (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    program.semanticSet model program.root =
      sat model.system.toLTS (program.semanticEnv model) program.formula := by
  have head := semanticTableAt_head model.system.toLTS
    (program.semanticEnv model) program.formula
  unfold semanticSet semanticTable
  rw [List.getElem?_eq_some_iff] at head
  exact head.2

/-- Truth invariant carried by a game position.  Negative polarity asks the
verifier to establish non-membership in the occurrence denotation. -/
def SemanticallyCorrect (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (position : Position State Action Observation program) : Prop :=
  if position.polarity then
    position.state ∈ program.semanticSet model position.address
  else
    position.state ∉ program.semanticSet model position.address

/-- At a true least-fixed-point binder, the retained source occurrence
supplies the finite entry rank and the preceding lower approximation in which
its body already holds. -/
theorem least_fixedPoint_exists_ranked_unfolding
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source : Position State Action Observation program)
    (depth child : Nat)
    (sourceNode : program.nodeAt source = .fixedPoint .least depth child)
    (polarity : source.polarity = true)
    (correct : program.SemanticallyCorrect model source) :
    let occurrence := program.sourceAt model source.address
    ∃ (body : Formula Action (occurrence.variableCount + 1))
      (positive : body.isPositive = true)
      (satisfied : satisfies model.system.toLTS occurrence.environment
        (.mu body) source.state)
      (previous : Nat),
      occurrence.formula = .mu body ∧
        muSemanticRank model.system.toLTS occurrence.environment body positive
          source.state satisfied = previous + 1 ∧
        satisfies model.system.toLTS
          (occurrence.environment.extend (lowerApproximation
            (bodyOrderHom model.system.toLTS occurrence.environment body positive)
            previous)) body source.state := by
  dsimp only
  let occurrence : SourceOccurrence State Action Observation :=
    program.sourceAt model source.address
  have nodeMatch := program.sourceAt_matchesNode model source
  rw [sourceNode] at nodeMatch
  have binderPositive := program.sourceAt_binderPositive model source.address
  have denotation := program.sourceAt_denotation model source.address
  unfold SemanticallyCorrect at correct
  simp [polarity] at correct
  rw [← denotation] at correct
  change source.state ∈
    occurrence.denotation model.system.toLTS at correct
  unfold SourceOccurrence.denotation at correct
  change occurrence.BinderPositive at binderPositive
  change occurrence.MatchesNode (.fixedPoint .least depth child) at nodeMatch
  generalize formulaEq : occurrence.formula = formula at nodeMatch binderPositive correct
  cases formula with
  | mu body =>
      have positive : body.isPositive = true := by
        simpa [SourceOccurrence.BinderPositive, formulaEq] using binderPositive
      have satisfied : satisfies model.system.toLTS occurrence.environment
          (.mu body) source.state := by
        change source.state ∈
          sat model.system.toLTS occurrence.environment (.mu body)
        exact correct
      obtain ⟨previous, rankEq, bodySatisfied⟩ :=
        muSemanticRank_unfold model.system.toLTS occurrence.environment body
          positive source.state satisfied
      exact ⟨body, positive, satisfied, previous, rfl,
        rankEq, bodySatisfied⟩
  | tt | ff | neg | conj | disj | diamond | box | nu | var =>
      simp [SourceOccurrence.MatchesNode, formulaEq] at nodeMatch

/-- At a refuted greatest-fixed-point binder, the retained source occurrence
supplies the finite exit rank and the preceding upper approximation from
which its body is already absent. -/
theorem greatest_fixedPoint_exists_ranked_refutation
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source : Position State Action Observation program)
    (depth child : Nat)
    (sourceNode : program.nodeAt source = .fixedPoint .greatest depth child)
    (polarity : source.polarity = false)
    (correct : program.SemanticallyCorrect model source) :
    let occurrence := program.sourceAt model source.address
    ∃ (body : Formula Action (occurrence.variableCount + 1))
      (positive : body.isPositive = true)
      (refuted : ¬ satisfies model.system.toLTS occurrence.environment
        (.nu body) source.state)
      (previous : Nat),
      occurrence.formula = .nu body ∧
        nuRefutationRank model.system.toLTS occurrence.environment body positive
          source.state refuted = previous + 1 ∧
        ¬ satisfies model.system.toLTS
          (occurrence.environment.extend (upperApproximation
            (bodyOrderHom model.system.toLTS occurrence.environment body positive)
            previous)) body source.state := by
  dsimp only
  let occurrence : SourceOccurrence State Action Observation :=
    program.sourceAt model source.address
  have nodeMatch := program.sourceAt_matchesNode model source
  rw [sourceNode] at nodeMatch
  have binderPositive := program.sourceAt_binderPositive model source.address
  have denotation := program.sourceAt_denotation model source.address
  unfold SemanticallyCorrect at correct
  simp [polarity] at correct
  rw [← denotation] at correct
  change source.state ∉
    occurrence.denotation model.system.toLTS at correct
  unfold SourceOccurrence.denotation at correct
  change occurrence.BinderPositive at binderPositive
  change occurrence.MatchesNode (.fixedPoint .greatest depth child) at nodeMatch
  generalize formulaEq : occurrence.formula = formula at nodeMatch binderPositive correct
  cases formula with
  | nu body =>
      have positive : body.isPositive = true := by
        simpa [SourceOccurrence.BinderPositive, formulaEq] using binderPositive
      have refuted : ¬ satisfies model.system.toLTS occurrence.environment
          (.nu body) source.state := by
        change source.state ∉
          sat model.system.toLTS occurrence.environment (.nu body)
        exact correct
      obtain ⟨previous, rankEq, bodyRefuted⟩ :=
        nuRefutationRank_unfold model.system.toLTS occurrence.environment body
          positive source.state refuted
      exact ⟨body, positive, refuted, previous, rfl,
        rankEq, bodyRefuted⟩
  | tt | ff | neg | conj | disj | diamond | box | mu | var =>
      simp [SourceOccurrence.MatchesNode, formulaEq] at nodeMatch

/-- At a truth terminal, semantic correctness is exactly the even terminal
priority assigned by the executable game. -/
theorem truth_semanticallyCorrect_iff_priority_zero
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (position : Position State Action Observation program) (value : Bool)
    (sourceNode : program.nodeAt position = .truth value) :
    program.SemanticallyCorrect model position ↔
      program.gamePriority model position = 0 := by
  have denotation := program.constructorDenotationAt model position
  rw [sourceNode] at denotation
  simp only [ConstructorDenotationAligned] at denotation
  unfold SemanticallyCorrect
  rw [denotation]
  cases polarity : position.polarity <;> cases value <;>
    simp [EvaluationGame.Program.gamePriority,
      sourceNode, EvaluationGame.Program.terminalWins, polarity]

/-- At an observation terminal, semantic correctness is exactly the even
priority determined by the model valuation. -/
theorem observation_semanticallyCorrect_iff_priority_zero
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (position : Position State Action Observation program)
    (label : Observation)
    (sourceNode : program.nodeAt position = .observation label) :
    program.SemanticallyCorrect model position ↔
      program.gamePriority model position = 0 := by
  have denotation := program.variableDenotationAt model position
  rw [sourceNode] at denotation
  simp only [VariableDenotationAligned] at denotation
  unfold SemanticallyCorrect
  rw [denotation]
  cases polarity : position.polarity <;>
    cases value : model.holds position.state label <;>
      simp [EvaluationGame.Program.gamePriority,
        sourceNode, EvaluationGame.Program.terminalWins,
        EvaluationGame.FiniteModel.observationSet, polarity, value]

/-- Semantic correctness is invariant when a variable occurrence returns to
its introducing binder. -/
theorem variable_edge_semanticallyCorrect
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source target : Position State Action Observation program)
    (binder : Nat)
    (sourceNode : program.nodeAt source = .variable binder)
    (edge : program.gameEdge model source target = true)
    (correct : program.SemanticallyCorrect model source) :
    program.SemanticallyCorrect model target := by
  obtain ⟨kind, depth, child, targetNode, stateEq, polarityEq⟩ :=
    program.variable_edge_enters_fixedPoint model source target binder sourceNode edge
  have setEq := program.variable_edge_semanticSet model source target binder
    sourceNode edge
  unfold SemanticallyCorrect at correct ⊢
  simpa [stateEq, polarityEq, setEq] using correct

/-- Semantic correctness is invariant when a fixed-point occurrence enters
its unfolded body. -/
theorem fixedPoint_edge_semanticallyCorrect
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source target : Position State Action Observation program)
    (kind : FixedPointKind) (depth child : Nat)
    (sourceNode : program.nodeAt source = .fixedPoint kind depth child)
    (edge : program.gameEdge model source target = true)
    (correct : program.SemanticallyCorrect model source) :
    program.SemanticallyCorrect model target := by
  have edgeFacts :
      (target.state = source.state ∧ target.polarity = source.polarity) ∧
        target.address.val = child := by
    simpa [EvaluationGame.Program.gameEdge, sourceNode,
      EvaluationGame.Program.sameStateAndPolarity,
      EvaluationGame.Program.addressIs, Bool.and_eq_true] using edge
  have setEq := program.fixedPoint_edge_semanticSet model source target
    kind depth child sourceNode edge
  unfold SemanticallyCorrect at correct ⊢
  simpa [edgeFacts.1.1, edgeFacts.1.2, setEq] using correct

/-- Negation flips polarity and moves to the complement's child, preserving
semantic correctness. -/
theorem negation_edge_semanticallyCorrect
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source target : Position State Action Observation program)
    (child : Nat)
    (sourceNode : program.nodeAt source = .negation child)
    (edge : program.gameEdge model source target = true)
    (correct : program.SemanticallyCorrect model source) :
    program.SemanticallyCorrect model target := by
  have relation := program.constructorDenotationAt model source
  rw [sourceNode] at relation
  rcases relation with ⟨childDenotation, childLookup, sourceSetEq⟩
  have edgeFacts : (target.state = source.state ∧
      target.polarity = !source.polarity) ∧ target.address.val = child := by
    simpa [EvaluationGame.Program.gameEdge, sourceNode,
      EvaluationGame.Program.toggledStateAndPolarity,
      EvaluationGame.Program.addressIs, Bool.and_eq_true] using edge
  obtain ⟨childBound, childValue⟩ := List.getElem?_eq_some_iff.mp childLookup
  have targetSetEq : program.semanticSet model target.address = childDenotation := by
    unfold semanticSet
    simpa [edgeFacts.2] using childValue
  unfold SemanticallyCorrect at correct ⊢
  cases polarity : source.polarity <;>
    simp [polarity, edgeFacts.1.1, edgeFacts.1.2, sourceSetEq,
      targetSetEq] at correct ⊢
  · exact correct
  · exact correct

/-- Every move controlled by the falsifier preserves semantic correctness.
At conjunction and box nodes this is universal elimination; at negative
disjunction and diamond nodes it is the corresponding De Morgan law. -/
theorem falsifier_edge_semanticallyCorrect
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source target : Position State Action Observation program)
    (owner : program.gameOwner source = .falsifier)
    (edge : program.gameEdge model source target = true)
    (correct : program.SemanticallyCorrect model source) :
    program.SemanticallyCorrect model target := by
  generalize sourceNode : program.nodeAt source = node
  cases node with
  | truth value =>
      simp [EvaluationGame.Program.gameOwner, sourceNode] at owner
  | observation label =>
      simp [EvaluationGame.Program.gameOwner, sourceNode] at owner
  | negation child =>
      simp [EvaluationGame.Program.gameOwner, sourceNode] at owner
  | fixedPoint kind depth child =>
      simp [EvaluationGame.Program.gameOwner, sourceNode] at owner
  | «variable» binder =>
      simp [EvaluationGame.Program.gameOwner, sourceNode] at owner
  | conjunction left right =>
      have polarity : source.polarity = true := by
        cases polarityEq : source.polarity with
        | false =>
            exfalso
            simp [EvaluationGame.Program.gameOwner, sourceNode,
              EvaluationGame.Program.ownerForChoice, polarityEq] at owner
        | true => rfl
      have relation := program.constructorDenotationAt model source
      rw [sourceNode] at relation
      rcases relation with
        ⟨leftDenotation, rightDenotation, leftLookup, rightLookup, sourceSetEq⟩
      have edgeFacts :
          (target.state = source.state ∧ target.polarity = source.polarity) ∧
            (target.address.val = left ∨ target.address.val = right) := by
        simpa [EvaluationGame.Program.gameEdge, sourceNode,
          EvaluationGame.Program.sameStateAndPolarity,
          EvaluationGame.Program.addressIs, Bool.and_eq_true,
          Bool.or_eq_true] using edge
      unfold SemanticallyCorrect at correct ⊢
      simp [polarity] at correct
      rw [sourceSetEq] at correct
      rcases edgeFacts.2 with leftAddress | rightAddress
      · have targetSetEq :
            program.semanticSet model target.address = leftDenotation := by
          obtain ⟨_tableBound, value⟩ :=
            List.getElem?_eq_some_iff.mp leftLookup
          unfold semanticSet
          simpa [leftAddress] using value
        simpa [edgeFacts.1.2, polarity, targetSetEq, edgeFacts.1.1] using correct.1
      · have targetSetEq :
            program.semanticSet model target.address = rightDenotation := by
          obtain ⟨_tableBound, value⟩ :=
            List.getElem?_eq_some_iff.mp rightLookup
          unfold semanticSet
          simpa [rightAddress] using value
        simpa [edgeFacts.1.2, polarity, targetSetEq, edgeFacts.1.1] using correct.2
  | disjunction left right =>
      have polarity : source.polarity = false := by
        cases polarityEq : source.polarity with
        | false => rfl
        | true =>
            exfalso
            simp [EvaluationGame.Program.gameOwner, sourceNode,
              EvaluationGame.Program.ownerForChoice, polarityEq] at owner
      have relation := program.constructorDenotationAt model source
      rw [sourceNode] at relation
      rcases relation with
        ⟨leftDenotation, rightDenotation, leftLookup, rightLookup, sourceSetEq⟩
      have edgeFacts :
          (target.state = source.state ∧ target.polarity = source.polarity) ∧
            (target.address.val = left ∨ target.address.val = right) := by
        simpa [EvaluationGame.Program.gameEdge, sourceNode,
          EvaluationGame.Program.sameStateAndPolarity,
          EvaluationGame.Program.addressIs, Bool.and_eq_true,
          Bool.or_eq_true] using edge
      unfold SemanticallyCorrect at correct ⊢
      simp [polarity] at correct
      rw [sourceSetEq] at correct
      rcases edgeFacts.2 with leftAddress | rightAddress
      · have targetSetEq :
            program.semanticSet model target.address = leftDenotation := by
          obtain ⟨_tableBound, value⟩ :=
            List.getElem?_eq_some_iff.mp leftLookup
          unfold semanticSet
          simpa [leftAddress] using value
        simpa [edgeFacts.1.2, polarity, targetSetEq, edgeFacts.1.1] using
          (fun member => correct (Or.inl member))
      · have targetSetEq :
            program.semanticSet model target.address = rightDenotation := by
          obtain ⟨_tableBound, value⟩ :=
            List.getElem?_eq_some_iff.mp rightLookup
          unfold semanticSet
          simpa [rightAddress] using value
        simpa [edgeFacts.1.2, polarity, targetSetEq, edgeFacts.1.1] using
          (fun member => correct (Or.inr member))
  | diamond action child =>
      have polarity : source.polarity = false := by
        cases polarityEq : source.polarity with
        | false => rfl
        | true =>
            exfalso
            simp [EvaluationGame.Program.gameOwner, sourceNode,
              EvaluationGame.Program.ownerForChoice, polarityEq] at owner
      by_cases successor :
          model.system.hasSuccessor source.state action = true
      · have relation := program.constructorDenotationAt model source
        rw [sourceNode] at relation
        rcases relation with ⟨childDenotation, childLookup, sourceSetEq⟩
        have edgeFacts :
            (model.system.edge source.state action target.state = true ∧
              target.address.val = child) ∧
                target.polarity = source.polarity := by
          simpa [EvaluationGame.Program.gameEdge, sourceNode,
            EvaluationGame.Program.modalEdge, successor,
            EvaluationGame.Program.addressIs, Bool.and_eq_true] using edge
        have targetSetEq :
            program.semanticSet model target.address = childDenotation := by
          obtain ⟨_tableBound, value⟩ :=
            List.getElem?_eq_some_iff.mp childLookup
          unfold semanticSet
          simpa [edgeFacts.1.2] using value
        unfold SemanticallyCorrect at correct ⊢
        simp [polarity] at correct
        rw [sourceSetEq] at correct
        simp [edgeFacts.2, polarity, targetSetEq]
        intro targetMember
        exact correct ⟨target.state, edgeFacts.1.1, targetMember⟩
      · have noSuccessor :
            model.system.hasSuccessor source.state action = false := by
          exact Bool.eq_false_of_not_eq_true successor
        have targetEq : target = source := by
          simpa [EvaluationGame.Program.gameEdge, sourceNode,
            EvaluationGame.Program.modalEdge, noSuccessor] using edge
        simpa [targetEq] using correct
  | box action child =>
      have polarity : source.polarity = true := by
        cases polarityEq : source.polarity with
        | false =>
            exfalso
            simp [EvaluationGame.Program.gameOwner, sourceNode,
              EvaluationGame.Program.ownerForChoice, polarityEq] at owner
        | true => rfl
      by_cases successor :
          model.system.hasSuccessor source.state action = true
      · have relation := program.constructorDenotationAt model source
        rw [sourceNode] at relation
        rcases relation with ⟨childDenotation, childLookup, sourceSetEq⟩
        have edgeFacts :
            (model.system.edge source.state action target.state = true ∧
              target.address.val = child) ∧
                target.polarity = source.polarity := by
          simpa [EvaluationGame.Program.gameEdge, sourceNode,
            EvaluationGame.Program.modalEdge, successor,
            EvaluationGame.Program.addressIs, Bool.and_eq_true] using edge
        have targetSetEq :
            program.semanticSet model target.address = childDenotation := by
          obtain ⟨_tableBound, value⟩ :=
            List.getElem?_eq_some_iff.mp childLookup
          unfold semanticSet
          simpa [edgeFacts.1.2] using value
        unfold SemanticallyCorrect at correct ⊢
        simp [polarity] at correct
        rw [sourceSetEq] at correct
        simpa [edgeFacts.2, polarity, targetSetEq] using
          correct target.state edgeFacts.1.1
      · have noSuccessor :
            model.system.hasSuccessor source.state action = false := by
          exact Bool.eq_false_of_not_eq_true successor
        have targetEq : target = source := by
          simpa [EvaluationGame.Program.gameEdge, sourceNode,
            EvaluationGame.Program.modalEdge, noSuccessor] using edge
        simpa [targetEq] using correct

/-- Every semantically correct verifier position has a semantically correct
legal successor.  The witness is obtained directly from the constructor's
denotational equation; no search or strategy semantics are added here. -/
theorem verifier_exists_semanticallyCorrect_successor
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source : Position State Action Observation program)
    (owner : program.gameOwner source = .verifier)
    (correct : program.SemanticallyCorrect model source) :
    ∃ target, program.gameEdge model source target = true ∧
      program.SemanticallyCorrect model target := by
  classical
  generalize sourceNode : program.nodeAt source = node
  cases node with
  | truth value =>
      refine ⟨source, ?_, correct⟩
      simp [EvaluationGame.Program.gameEdge, sourceNode]
  | observation label =>
      refine ⟨source, ?_, correct⟩
      simp [EvaluationGame.Program.gameEdge, sourceNode]
  | negation child =>
      have childBound : child < program.nodes.length :=
        program.target_lt_nodes_length source child (by
          simp [sourceNode, Node.targets])
      let target : Position State Action Observation program :=
        ⟨source.state, ⟨child, childBound⟩, !source.polarity⟩
      have edge : program.gameEdge model source target = true := by
        simp [EvaluationGame.Program.gameEdge, sourceNode,
          EvaluationGame.Program.toggledStateAndPolarity,
          EvaluationGame.Program.addressIs, target]
      exact ⟨target, edge,
        program.negation_edge_semanticallyCorrect model source target child
          sourceNode edge correct⟩
  | fixedPoint kind depth child =>
      have childBound : child < program.nodes.length :=
        program.target_lt_nodes_length source child (by
          simp [sourceNode, Node.targets])
      let target : Position State Action Observation program :=
        ⟨source.state, ⟨child, childBound⟩, source.polarity⟩
      have edge : program.gameEdge model source target = true := by
        simp [EvaluationGame.Program.gameEdge, sourceNode,
          EvaluationGame.Program.sameStateAndPolarity,
          EvaluationGame.Program.addressIs, target]
      exact ⟨target, edge,
        program.fixedPoint_edge_semanticallyCorrect model source target
          kind depth child sourceNode edge correct⟩
  | «variable» binder =>
      have binderBound : binder < program.nodes.length :=
        program.target_lt_nodes_length source binder (by
          simp [sourceNode, Node.targets])
      let target : Position State Action Observation program :=
        ⟨source.state, ⟨binder, binderBound⟩, source.polarity⟩
      have edge : program.gameEdge model source target = true := by
        simp [EvaluationGame.Program.gameEdge, sourceNode,
          EvaluationGame.Program.sameStateAndPolarity,
          EvaluationGame.Program.addressIs, target]
      exact ⟨target, edge,
        program.variable_edge_semanticallyCorrect model source target binder
          sourceNode edge correct⟩
  | conjunction left right =>
      have polarity : source.polarity = false := by
        cases polarityEq : source.polarity with
        | false => rfl
        | true =>
            exfalso
            simp [EvaluationGame.Program.gameOwner, sourceNode,
              EvaluationGame.Program.ownerForChoice, polarityEq] at owner
      have relation := program.constructorDenotationAt model source
      rw [sourceNode] at relation
      rcases relation with
        ⟨leftDenotation, rightDenotation, leftLookup, rightLookup, sourceSetEq⟩
      have leftBound : left < program.nodes.length :=
        program.target_lt_nodes_length source left (by
          simp [sourceNode, Node.targets])
      have rightBound : right < program.nodes.length :=
        program.target_lt_nodes_length source right (by
          simp [sourceNode, Node.targets])
      have leftSetEq :
          program.semanticSet model ⟨left, leftBound⟩ = leftDenotation :=
        program.semanticSet_eq_of_getElem?_eq_some model left leftDenotation
          leftLookup leftBound
      have rightSetEq :
          program.semanticSet model ⟨right, rightBound⟩ = rightDenotation :=
        program.semanticSet_eq_of_getElem?_eq_some model right rightDenotation
          rightLookup rightBound
      unfold SemanticallyCorrect at correct
      simp [polarity, sourceSetEq] at correct
      by_cases leftMember : source.state ∈ leftDenotation
      · have rightNotMember : source.state ∉ rightDenotation :=
          correct leftMember
        let target : Position State Action Observation program :=
          ⟨source.state, ⟨right, rightBound⟩, source.polarity⟩
        refine ⟨target, ?_, ?_⟩
        · simp [EvaluationGame.Program.gameEdge, sourceNode,
            EvaluationGame.Program.sameStateAndPolarity,
            EvaluationGame.Program.addressIs, target]
        · unfold SemanticallyCorrect
          simpa [target, polarity, rightSetEq] using rightNotMember
      · let target : Position State Action Observation program :=
          ⟨source.state, ⟨left, leftBound⟩, source.polarity⟩
        refine ⟨target, ?_, ?_⟩
        · simp [EvaluationGame.Program.gameEdge, sourceNode,
            EvaluationGame.Program.sameStateAndPolarity,
            EvaluationGame.Program.addressIs, target]
        · unfold SemanticallyCorrect
          simpa [target, polarity, leftSetEq] using leftMember
  | disjunction left right =>
      have polarity : source.polarity = true := by
        cases polarityEq : source.polarity with
        | false =>
            exfalso
            simp [EvaluationGame.Program.gameOwner, sourceNode,
              EvaluationGame.Program.ownerForChoice, polarityEq] at owner
        | true => rfl
      have relation := program.constructorDenotationAt model source
      rw [sourceNode] at relation
      rcases relation with
        ⟨leftDenotation, rightDenotation, leftLookup, rightLookup, sourceSetEq⟩
      have leftBound : left < program.nodes.length :=
        program.target_lt_nodes_length source left (by
          simp [sourceNode, Node.targets])
      have rightBound : right < program.nodes.length :=
        program.target_lt_nodes_length source right (by
          simp [sourceNode, Node.targets])
      have leftSetEq :
          program.semanticSet model ⟨left, leftBound⟩ = leftDenotation :=
        program.semanticSet_eq_of_getElem?_eq_some model left leftDenotation
          leftLookup leftBound
      have rightSetEq :
          program.semanticSet model ⟨right, rightBound⟩ = rightDenotation :=
        program.semanticSet_eq_of_getElem?_eq_some model right rightDenotation
          rightLookup rightBound
      unfold SemanticallyCorrect at correct
      simp [polarity, sourceSetEq] at correct
      rcases correct with leftMember | rightMember
      · let target : Position State Action Observation program :=
          ⟨source.state, ⟨left, leftBound⟩, source.polarity⟩
        refine ⟨target, ?_, ?_⟩
        · simp [EvaluationGame.Program.gameEdge, sourceNode,
            EvaluationGame.Program.sameStateAndPolarity,
            EvaluationGame.Program.addressIs, target]
        · unfold SemanticallyCorrect
          simpa [target, polarity, leftSetEq] using leftMember
      · let target : Position State Action Observation program :=
          ⟨source.state, ⟨right, rightBound⟩, source.polarity⟩
        refine ⟨target, ?_, ?_⟩
        · simp [EvaluationGame.Program.gameEdge, sourceNode,
            EvaluationGame.Program.sameStateAndPolarity,
            EvaluationGame.Program.addressIs, target]
        · unfold SemanticallyCorrect
          simpa [target, polarity, rightSetEq] using rightMember
  | diamond action child =>
      have polarity : source.polarity = true := by
        cases polarityEq : source.polarity with
        | false =>
            exfalso
            simp [EvaluationGame.Program.gameOwner, sourceNode,
              EvaluationGame.Program.ownerForChoice, polarityEq] at owner
        | true => rfl
      have relation := program.constructorDenotationAt model source
      rw [sourceNode] at relation
      rcases relation with ⟨childDenotation, childLookup, sourceSetEq⟩
      unfold SemanticallyCorrect at correct
      simp [polarity, sourceSetEq] at correct
      obtain ⟨targetState, transition, targetMember⟩ := correct
      have successor :
          model.system.hasSuccessor source.state action = true :=
        (FiniteLTS.hasSuccessor_eq_true_iff model.system source.state action).2
          ⟨targetState, transition⟩
      have childBound : child < program.nodes.length :=
        program.target_lt_nodes_length source child (by
          simp [sourceNode, Node.targets])
      have childSetEq :
          program.semanticSet model ⟨child, childBound⟩ = childDenotation :=
        program.semanticSet_eq_of_getElem?_eq_some model child childDenotation
          childLookup childBound
      let target : Position State Action Observation program :=
        ⟨targetState, ⟨child, childBound⟩, source.polarity⟩
      refine ⟨target, ?_, ?_⟩
      · simp [EvaluationGame.Program.gameEdge, sourceNode,
          EvaluationGame.Program.modalEdge, successor,
          EvaluationGame.Program.addressIs, target, transition]
      · unfold SemanticallyCorrect
        simpa [target, polarity, childSetEq] using targetMember
  | box action child =>
      have polarity : source.polarity = false := by
        cases polarityEq : source.polarity with
        | false => rfl
        | true =>
            exfalso
            simp [EvaluationGame.Program.gameOwner, sourceNode,
              EvaluationGame.Program.ownerForChoice, polarityEq] at owner
      have relation := program.constructorDenotationAt model source
      rw [sourceNode] at relation
      rcases relation with ⟨childDenotation, childLookup, sourceSetEq⟩
      unfold SemanticallyCorrect at correct
      simp [polarity, sourceSetEq] at correct
      have counterexample : ∃ targetState,
          model.system.edge source.state action targetState = true ∧
            targetState ∉ childDenotation := correct
      obtain ⟨targetState, transition, targetNotMember⟩ := counterexample
      have successor :
          model.system.hasSuccessor source.state action = true :=
        (FiniteLTS.hasSuccessor_eq_true_iff model.system source.state action).2
          ⟨targetState, transition⟩
      have childBound : child < program.nodes.length :=
        program.target_lt_nodes_length source child (by
          simp [sourceNode, Node.targets])
      have childSetEq :
          program.semanticSet model ⟨child, childBound⟩ = childDenotation :=
        program.semanticSet_eq_of_getElem?_eq_some model child childDenotation
          childLookup childBound
      let target : Position State Action Observation program :=
        ⟨targetState, ⟨child, childBound⟩, source.polarity⟩
      refine ⟨target, ?_, ?_⟩
      · simp [EvaluationGame.Program.gameEdge, sourceNode,
          EvaluationGame.Program.modalEdge, successor,
          EvaluationGame.Program.addressIs, target, transition]
      · unfold SemanticallyCorrect
        simpa [target, polarity, childSetEq] using targetNotMember

/-- Every semantically correct position has at least one semantically correct
legal successor, independently of which player owns the position. -/
theorem exists_semanticallyCorrect_successor
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source : Position State Action Observation program)
    (correct : program.SemanticallyCorrect model source) :
    ∃ target, program.gameEdge model source target = true ∧
      program.SemanticallyCorrect model target := by
  cases ownerEq : program.gameOwner source with
  | verifier =>
      exact program.verifier_exists_semanticallyCorrect_successor model source
        ownerEq correct
  | falsifier =>
      obtain ⟨target, edge⟩ := program.exists_gameEdge model source
      exact ⟨target, edge,
        program.falsifier_edge_semanticallyCorrect model source target
          ownerEq edge correct⟩

/-- Proof-side strategy obtained by selecting one denotationally correct
successor at every denotationally correct position.  It is noncomputable
because adequacy needs existence, not a second executable scheduler. -/
noncomputable def localSemanticStrategy
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation) :
    Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity.Strategy
      (Position State Action Observation program) := by
  classical
  exact {
    active := fun position =>
      decide (program.SemanticallyCorrect model position)
    next := fun position =>
      if correct : program.SemanticallyCorrect model position then
        Classical.choose
          (program.exists_semanticallyCorrect_successor model position correct)
      else
        position }

/-- At every semantically correct position, the proof-side strategy chooses a
legal semantically correct successor. -/
theorem localSemanticStrategy_next_spec
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (source : Position State Action Observation program)
    (correct : program.SemanticallyCorrect model source) :
    program.gameEdge model source
        ((program.localSemanticStrategy model).next source) = true ∧
      program.SemanticallyCorrect model
        ((program.localSemanticStrategy model).next source) := by
  classical
  simpa [localSemanticStrategy, correct] using
    Classical.choose_spec
      (program.exists_semanticallyCorrect_successor model source correct)

/-- The denotationally correct positions form a locally valid strategy cone:
the verifier's selected move and every falsifier move stay inside it. -/
theorem localSemanticStrategy_locallyValid
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation)
    (root : Position State Action Observation program)
    (correct : program.SemanticallyCorrect model root) :
    (program.localSemanticStrategy model).LocallyValid (program.game model) root := by
  classical
  refine ⟨by simp [localSemanticStrategy, correct], ?_⟩
  intro source active
  have sourceCorrect : program.SemanticallyCorrect model source := by
    simpa [localSemanticStrategy] using active
  have nextSpec := program.localSemanticStrategy_next_spec model source sourceCorrect
  constructor
  · refine ⟨(program.localSemanticStrategy model).next source, nextSpec.1, ?_⟩
    cases ownerEq : program.gameOwner source <;>
      simp [EvaluationGame.Program.game, ownerEq]
  · intro target controlled
    rcases controlled with ⟨edge, control⟩
    have targetCorrect : program.SemanticallyCorrect model target := by
      cases ownerEq : program.gameOwner source with
      | verifier =>
          have targetEq : target = (program.localSemanticStrategy model).next source := by
            simpa [EvaluationGame.Program.game, ownerEq] using control
          simpa [targetEq] using nextSpec.2
      | falsifier =>
          exact program.falsifier_edge_semanticallyCorrect model source target
            ownerEq edge sourceCorrect
    simp [localSemanticStrategy, targetCorrect]

/-- At the initial positive-polarity position, semantic correctness is exactly
the original denotational judgment. -/
theorem initial_semanticallyCorrect_iff
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation) (state : State) :
    program.SemanticallyCorrect model (program.initial state) ↔
      program.Denotes model state := by
  simp [SemanticallyCorrect, EvaluationGame.Program.initial,
    EvaluationGame.Program.Denotes, semanticSet_root, sat]

/-- The local-validity part of the evaluation-game strategy is equivalent at
the root to the original denotational judgment.  The remaining adequacy work
is therefore exactly the global parity condition. -/
theorem localSemanticStrategy_initial_locallyValid_iff
    [DecidableEq State]
    (program : Program Action Observation)
    (model : FiniteModel State Action Observation) (state : State) :
    (program.localSemanticStrategy model).LocallyValid (program.game model)
        (program.initial state) ↔
      program.Denotes model state := by
  classical
  constructor
  · intro locallyValid
    have correct :
        program.SemanticallyCorrect model (program.initial state) := by
      simpa [localSemanticStrategy] using locallyValid.1
    exact (program.initial_semanticallyCorrect_iff model state).1 correct
  · intro denotes
    exact program.localSemanticStrategy_locallyValid model (program.initial state)
      ((program.initial_semanticallyCorrect_iff model state).2 denotes)

end Mettapedia.Logic.ModalMuCalculus.EvaluationGame.Program

/-! ## Boundary controls -/

namespace Mettapedia.Logic.ModalMuCalculus.EvaluationGame.Adequacy.Canary

open Mettapedia.Logic.ModalMuCalculus.EvaluationGame
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity

open EvaluationGame.Canary

def rankSensitiveFormula : Formula Unit 0 :=
  .mu .tt

/-- At rank zero, even the immediately productive least fixed point has not
entered its finite approximation. -/
theorem rankSensitive_zero :
    boundedWinningSet singletonModel.system.toLTS (fun _ => 0) 0 true
      Fin.elim0 rankSensitiveFormula = (∅ : Set Unit) := by
  rfl

/-- One additional approximation step genuinely adds the singleton state.
Together with `rankSensitive_zero`, this prevents rank monotonicity from being
mistaken for a vacuous equality. -/
theorem rankSensitive_one :
    boundedWinningSet singletonModel.system.toLTS (fun _ => 1) 0 true
      Fin.elim0 rankSensitiveFormula = Set.univ := by
  ext state
  simp [rankSensitiveFormula, boundedWinningSet]

def leastLoopVariablePosition :
    Position Unit Unit Unit leastLoopProgram :=
  ⟨(), ⟨1, by decide⟩, true⟩

def leastLoopBinderPosition :
    Position Unit Unit Unit leastLoopProgram :=
  ⟨(), ⟨0, by decide⟩, true⟩

theorem leastLoop_variable_node :
    leastLoopProgram.nodeAt leastLoopVariablePosition = .variable 0 := by
  rfl

theorem leastLoop_variable_edge :
    leastLoopProgram.gameEdge singletonModel leastLoopVariablePosition
      leastLoopBinderPosition = true := by
  rfl

theorem leastLoop_fixedPoint_node :
    leastLoopProgram.nodeAt leastLoopBinderPosition =
      .fixedPoint .least 0 1 := by
  rfl

theorem leastLoop_fixedPoint_edge :
    leastLoopProgram.gameEdge singletonModel leastLoopBinderPosition
      leastLoopVariablePosition = true := by
  rfl

/-- Positive lexical-scope control: the binder itself has no enclosing binder,
while its body variable retains exactly the introducing address. -/
theorem leastLoop_binderStacks :
    (leastLoopProgram.sourceAt singletonModel
        leastLoopBinderPosition.address).binderStack = [] ∧
      (leastLoopProgram.sourceAt singletonModel
        leastLoopVariablePosition.address).binderStack = [0] := by
  decide

/-- Negative lexical-scope control: a binder reference cannot be hidden in the
ambient-observation suffix of an empty lexical stack. -/
theorem fabricatedAmbientBinder_rejected :
    ¬ BinderStackAligned
      (fun _ : Fin 1 =>
        (VariableReference.binder 7 : VariableReference Unit)) ([] : List Nat) := by
  intro aligned
  have impossible : 7 ∈ ([] : List Nat) :=
    aligned.binder_mem (index := (0 : Fin 1)) rfl
  simp at impossible

/-- Entering the body and returning through its variable back-edge both
preserve the fixed-point predicate on the minimal cycle. -/
theorem leastLoop_bodyEdge_preserves_semanticSet :
    leastLoopProgram.semanticSet singletonModel
        leastLoopVariablePosition.address =
      leastLoopProgram.semanticSet singletonModel
        leastLoopBinderPosition.address := by
  exact leastLoopProgram.fixedPoint_edge_semanticSet singletonModel
    leastLoopBinderPosition leastLoopVariablePosition .least 0 1
    leastLoop_fixedPoint_node leastLoop_fixedPoint_edge

/-- The minimal generated binder cycle preserves its semantic predicate when
the variable back-edge returns to the binder. -/
theorem leastLoop_backEdge_preserves_semanticSet :
    leastLoopProgram.semanticSet singletonModel leastLoopBinderPosition.address =
      leastLoopProgram.semanticSet singletonModel
        leastLoopVariablePosition.address := by
  exact leastLoopProgram.variable_edge_semanticSet singletonModel
    leastLoopVariablePosition leastLoopBinderPosition 0
    leastLoop_variable_node leastLoop_variable_edge

/-- A table assigning a different predicate to a binder occurrence fails the
alignment relation. -/
theorem mismatchedBinderDenotation_rejected :
    ¬ VariableDenotationAligned singletonModel [∅]
      (.variable 0) (Set.univ : Set Unit) := by
  simp only [VariableDenotationAligned, List.getElem?_cons_zero,
    Option.some.injEq]
  intro equal
  have membership := Set.ext_iff.mp equal ()
  simp at membership

theorem mismatchedFixedPointDenotation_rejected :
    ¬ FixedPointDenotationAligned ([Set.univ, ∅] : List (Set Unit))
      ((.fixedPoint .least 0 1) : Node Unit Unit) (Set.univ : Set Unit) := by
  simp only [FixedPointDenotationAligned, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.some.injEq]
  intro equal
  have membership := Set.ext_iff.mp equal ()
  simp at membership

theorem top_initial_semanticallyCorrect :
    topProgram.SemanticallyCorrect singletonModel (topProgram.initial ()) := by
  exact (topProgram.initial_semanticallyCorrect_iff singletonModel ()).2 trivial

theorem bottom_initial_not_semanticallyCorrect :
    ¬ bottomProgram.SemanticallyCorrect singletonModel
      (bottomProgram.initial ()) := by
  rw [bottomProgram.initial_semanticallyCorrect_iff singletonModel]
  simp [EvaluationGame.Program.Denotes, bottomProgram, compilePositive,
    satisfies]

/-- Positive control: denotational truth generates a locally valid strategy
cone in the one-state top game. -/
theorem top_localSemanticStrategy_locallyValid :
    (topProgram.localSemanticStrategy singletonModel).LocallyValid
      (topProgram.game singletonModel) (topProgram.initial ()) := by
  exact (topProgram.localSemanticStrategy_initial_locallyValid_iff
    singletonModel ()).2 trivial

/-- Negative control: the false root cannot be laundered into the active cone
of the semantic strategy. -/
theorem bottom_localSemanticStrategy_not_locallyValid :
    ¬ (bottomProgram.localSemanticStrategy singletonModel).LocallyValid
      (bottomProgram.game singletonModel) (bottomProgram.initial ()) := by
  rw [bottomProgram.localSemanticStrategy_initial_locallyValid_iff singletonModel]
  simp [EvaluationGame.Program.Denotes, bottomProgram, compilePositive,
    satisfies]

/-! ## Local truth preservation is not global parity progress -/

/-- The least fixed point `mu X. (top or X)` is true, but a verifier that
always chooses the recursive branch loops forever at the odd least-fixed-point
priority.  This is the minimal guard against confusing local semantic closure
with a parity-winning strategy. -/
def locallyValidLosingProgram : Program Unit Unit :=
  compilePositive (.mu (.disj .tt (.var 0))) Fin.elim0 rfl

theorem locallyValidLosingProgram_nodes :
    locallyValidLosingProgram.nodes =
      [.fixedPoint .least 0 1, .disjunction 2 3, .truth true, .variable 0] := by
  rfl

def locallyValidLosingBinder :
    Position Unit Unit Unit locallyValidLosingProgram :=
  ⟨(), ⟨0, by decide⟩, true⟩

def locallyValidLosingBody :
    Position Unit Unit Unit locallyValidLosingProgram :=
  ⟨(), ⟨1, by decide⟩, true⟩

def locallyValidLosingVariable :
    Position Unit Unit Unit locallyValidLosingProgram :=
  ⟨(), ⟨3, by decide⟩, true⟩

theorem locallyValidLosingBinder_priority :
    (locallyValidLosingProgram.game singletonModel).priority
      locallyValidLosingBinder = 0 := by
  decide

theorem locallyValidLosingBody_priority :
    (locallyValidLosingProgram.game singletonModel).priority
      locallyValidLosingBody = 0 := by
  decide

theorem locallyValidLosingVariable_priority :
    (locallyValidLosingProgram.game singletonModel).priority
      locallyValidLosingVariable = 1 := by
  decide

/-- The deliberately unfair local strategy enters the body, selects the
recursive disjunct, and returns to the binder. -/
def locallyValidLosingStrategy :
    Strategy (Position Unit Unit Unit locallyValidLosingProgram) where
  active position := decide (
    position = locallyValidLosingBinder ∨
    position = locallyValidLosingBody ∨
    position = locallyValidLosingVariable)
  next position :=
    if position = locallyValidLosingBinder then locallyValidLosingBody
    else if position = locallyValidLosingBody then locallyValidLosingVariable
    else locallyValidLosingBinder

theorem locallyValidLosingBinder_controlled :
    locallyValidLosingStrategy.ControlledEdge
      (locallyValidLosingProgram.game singletonModel)
      locallyValidLosingBinder locallyValidLosingBody := by
  decide

theorem locallyValidLosingBody_controlled :
    locallyValidLosingStrategy.ControlledEdge
      (locallyValidLosingProgram.game singletonModel)
      locallyValidLosingBody locallyValidLosingVariable := by
  decide

theorem locallyValidLosingVariable_controlled :
    locallyValidLosingStrategy.ControlledEdge
      (locallyValidLosingProgram.game singletonModel)
      locallyValidLosingVariable locallyValidLosingBinder := by
  decide

theorem locallyValidLosingStrategy_locallyValid :
    locallyValidLosingStrategy.LocallyValid
      (locallyValidLosingProgram.game singletonModel)
      locallyValidLosingBinder := by
  constructor
  · decide
  · intro source sourceActive
    simp only [locallyValidLosingStrategy, decide_eq_true_eq] at sourceActive
    rcases sourceActive with rfl | rfl | rfl
    · refine ⟨⟨locallyValidLosingBody, locallyValidLosingBinder_controlled⟩, ?_⟩
      intro target controlled
      have targetEq : target = locallyValidLosingBody := controlled.2
      subst target
      decide
    · refine ⟨⟨locallyValidLosingVariable, locallyValidLosingBody_controlled⟩, ?_⟩
      intro target controlled
      have targetEq : target = locallyValidLosingVariable := controlled.2
      subst target
      decide
    · refine ⟨⟨locallyValidLosingBinder, locallyValidLosingVariable_controlled⟩, ?_⟩
      intro target controlled
      have targetEq : target = locallyValidLosingBinder := controlled.2
      subst target
      decide

/-- The graph characterization pinpoints the defect in the merely local
semantic strategy: its recursive variable returns below the same odd
threshold without ever crossing a higher priority. -/
theorem locallyValidLosingStrategy_not_noOddThresholdReturn :
    ¬ ProgressMeasure.NoOddThresholdReturn
      (locallyValidLosingProgram.game singletonModel)
      locallyValidLosingStrategy := by
  intro noReturn
  let threshold :
      (locallyValidLosingProgram.game singletonModel).Threshold :=
    ⟨1, by decide⟩
  have binderStep : ProgressMeasure.thresholdEdge
      (locallyValidLosingProgram.game singletonModel)
      locallyValidLosingStrategy threshold
      locallyValidLosingBinder locallyValidLosingBody := by
    refine ⟨by decide, locallyValidLosingBinder_controlled, ?_, ?_⟩
    · rw [locallyValidLosingBinder_priority]
      simp [threshold]
    · rw [locallyValidLosingBody_priority]
      simp [threshold]
  have bodyStep : ProgressMeasure.thresholdEdge
      (locallyValidLosingProgram.game singletonModel)
      locallyValidLosingStrategy threshold
      locallyValidLosingBody locallyValidLosingVariable := by
    refine ⟨by decide, locallyValidLosingBody_controlled, ?_, ?_⟩
    · rw [locallyValidLosingBody_priority]
      simp [threshold]
    · simpa [threshold] using locallyValidLosingVariable_priority.le
  have returns : Relation.ReflTransGen
      (ProgressMeasure.thresholdEdge
        (locallyValidLosingProgram.game singletonModel)
        locallyValidLosingStrategy threshold)
      locallyValidLosingBinder locallyValidLosingVariable :=
    Relation.ReflTransGen.head binderStep
      (Relation.ReflTransGen.single bodyStep)
  exact noReturn threshold (by
      change Odd 1
      exact ⟨0, rfl⟩)
    locallyValidLosingVariable locallyValidLosingBinder (by decide)
    locallyValidLosingVariable_controlled
    (by simpa [threshold] using locallyValidLosingVariable_priority)
    (by
      rw [locallyValidLosingBinder_priority]
      simp [threshold])
    returns

/-- The strategy's unique controlled play, written as the three-state cycle. -/
def locallyValidLosingPlay :
    Strategy.Play (locallyValidLosingProgram.game singletonModel)
      locallyValidLosingStrategy locallyValidLosingBinder where
  state index :=
    match index % 3 with
    | 0 => locallyValidLosingBinder
    | 1 => locallyValidLosingBody
    | _ => locallyValidLosingVariable
  starts := by decide
  follows index := by
    have remainder_lt : index % 3 < 3 := Nat.mod_lt _ (by omega)
    have remainderCases :
        index % 3 = 0 ∨ index % 3 = 1 ∨ index % 3 = 2 := by
      omega
    rcases remainderCases with remainder | remainder | remainder
    · have nextRemainder : (index + 1) % 3 = 1 := by omega
      simpa [remainder, nextRemainder] using locallyValidLosingBinder_controlled
    · have nextRemainder : (index + 1) % 3 = 2 := by omega
      simpa [remainder, nextRemainder] using locallyValidLosingBody_controlled
    · have nextRemainder : (index + 1) % 3 = 0 := by omega
      simpa [remainder, nextRemainder] using locallyValidLosingVariable_controlled

theorem locallyValidLosingPlay_badOddDominant :
    Strategy.BadOddDominant
      (locallyValidLosingProgram.game singletonModel)
      locallyValidLosingPlay.state := by
  refine ⟨1, ⟨0, by omega⟩, ?_, 0, ?_⟩
  · have occurrencesInfinite :
        Set.Infinite (Set.range (fun n : Nat => 3 * n + 2)) :=
      Set.infinite_range_of_injective (by
        intro first second equal
        have products : 3 * first = 3 * second :=
          Nat.add_right_cancel equal
        exact Nat.mul_left_cancel (by omega) products)
    apply occurrencesInfinite.mono
    rintro index ⟨n, rfl⟩
    simpa [locallyValidLosingPlay] using locallyValidLosingVariable_priority
  · intro index _
    have remainder_lt : index % 3 < 3 := Nat.mod_lt _ (by omega)
    have remainderCases :
        index % 3 = 0 ∨ index % 3 = 1 ∨ index % 3 = 2 := by
      omega
    rcases remainderCases with remainder | remainder | remainder
    · simpa [locallyValidLosingPlay, remainder] using
        (show (locallyValidLosingProgram.game singletonModel).priority
          locallyValidLosingBinder ≤ 1 from
            locallyValidLosingBinder_priority.le.trans (by omega))
    · simpa [locallyValidLosingPlay, remainder] using
        (show (locallyValidLosingProgram.game singletonModel).priority
          locallyValidLosingBody ≤ 1 by
            rw [locallyValidLosingBody_priority]
            omega)
    · simpa [locallyValidLosingPlay, remainder] using
        (show (locallyValidLosingProgram.game singletonModel).priority
          locallyValidLosingVariable ≤ 1 by
            rw [locallyValidLosingVariable_priority])

/-- Local validity alone cannot witness denotational adequacy for recursive
formulas: the true root admits this locally valid but parity-losing strategy. -/
theorem locallyValidLosingStrategy_not_parityWinning :
    ¬ locallyValidLosingStrategy.ParityWinning
      (locallyValidLosingProgram.game singletonModel)
      locallyValidLosingBinder := by
  intro winning
  exact winning.2 locallyValidLosingPlay locallyValidLosingPlay_badOddDominant

theorem locallyValidLosingProgram_denotes :
    locallyValidLosingProgram.Denotes singletonModel () := by
  intro candidate preFixed
  exact preFixed () (Or.inl trivial)

/-! ## Priority is charged by recursion, not fixed-point syntax -/

/-- The inner least fixed point does not mention its own variable; it merely
returns the outer greatest-fixed-point variable.  Denotationally this is the
identity transformer under a greatest fixed point, hence true. -/
def outerGreatestInnerNonrecursiveProgram : Program Unit Unit :=
  compilePositive (.nu (.mu (.var 1))) Fin.elim0 rfl

theorem outerGreatestInnerNonrecursiveProgram_nodes :
    outerGreatestInnerNonrecursiveProgram.nodes =
      [.fixedPoint .greatest 0 1, .fixedPoint .least 1 2, .variable 0] := by
  rfl

def outerGreatestBinder :
    Position Unit Unit Unit outerGreatestInnerNonrecursiveProgram :=
  ⟨(), ⟨0, by decide⟩, true⟩

def innerNonrecursiveBinder :
    Position Unit Unit Unit outerGreatestInnerNonrecursiveProgram :=
  ⟨(), ⟨1, by decide⟩, true⟩

def outerGreatestVariable :
    Position Unit Unit Unit outerGreatestInnerNonrecursiveProgram :=
  ⟨(), ⟨2, by decide⟩, true⟩

theorem outerGreatestBinder_priority :
    (outerGreatestInnerNonrecursiveProgram.game singletonModel).priority
      outerGreatestBinder = 0 := by
  decide

theorem innerNonrecursiveBinder_priority :
    (outerGreatestInnerNonrecursiveProgram.game singletonModel).priority
      innerNonrecursiveBinder = 0 := by
  decide

theorem outerGreatestVariable_priority :
    (outerGreatestInnerNonrecursiveProgram.game singletonModel).priority
      outerGreatestVariable = 4 := by
  decide

/-- The unique generated cycle follows the outer variable back-edge. -/
def outerGreatestStrategy :
    Strategy (Position Unit Unit Unit outerGreatestInnerNonrecursiveProgram) where
  active position := decide (
    position = outerGreatestBinder ∨
    position = innerNonrecursiveBinder ∨
    position = outerGreatestVariable)
  next position :=
    if position = outerGreatestBinder then innerNonrecursiveBinder
    else if position = innerNonrecursiveBinder then outerGreatestVariable
    else outerGreatestBinder

def outerGreatestMeasure : ProgressMeasure
    (outerGreatestInnerNonrecursiveProgram.game singletonModel) where
  rank _ _ := 0

/-- The executable parity checker accepts the corrected cycle: its only
recursive priority is the outer greatest-fixed-point priority. -/
theorem outerGreatestCertificate_accepted :
    outerGreatestMeasure.check
      (outerGreatestInnerNonrecursiveProgram.game singletonModel)
      outerGreatestStrategy outerGreatestBinder = true := by
  decide

theorem outerGreatestStrategy_winning :
    outerGreatestStrategy.ParityWinning
      (outerGreatestInnerNonrecursiveProgram.game singletonModel)
      outerGreatestBinder := by
  apply ProgressMeasure.parity_sound
  exact (ProgressMeasure.check_eq_true_iff
    (outerGreatestInnerNonrecursiveProgram.game singletonModel)
    outerGreatestStrategy outerGreatestMeasure outerGreatestBinder).mp
      outerGreatestCertificate_accepted

theorem outerGreatestInnerNonrecursiveProgram_denotes :
    outerGreatestInnerNonrecursiveProgram.Denotes singletonModel () := by
  refine ⟨Set.univ, Set.mem_univ (), ?_⟩
  intro state _ candidate preFixed
  exact preFixed state (by simp [satisfies, Env.extend])

/-- A two-state recurrence formula in which the inner least fixed point may
recur once during every outer greatest-fixed-point round. -/
def recurringObservationFormula : Formula Unit 1 :=
  .nu (.mu (.disj
    (.conj (.var 2) (.diamond () (.var 1)))
    (.conj (.neg (.var 2)) (.diamond () (.var 0)))))

def alternatingModel : FiniteModel Bool Unit Unit where
  system.edge source _ target := decide (target = !source)
  holds state _ := state

def recurringObservationProgram : Program Unit Unit :=
  compilePositive recurringObservationFormula (fun _ => ()) rfl

theorem recurringObservationProgram_nodes :
    recurringObservationProgram.nodes =
      [.fixedPoint .greatest 0 1,
       .fixedPoint .least 1 2,
       .disjunction 3 7,
       .conjunction 4 5,
       .observation (),
       .diamond () 6,
       .variable 0,
       .conjunction 8 10,
       .negation 9,
       .observation (),
       .diamond () 11,
       .variable 1] := by
  rfl

def recurringOuterVariable :
    Position Bool Unit Unit recurringObservationProgram :=
  ⟨false, ⟨6, by decide⟩, true⟩

def recurringInnerVariable :
    Position Bool Unit Unit recurringObservationProgram :=
  ⟨true, ⟨11, by decide⟩, true⟩

/-- The outer greatest-fixed-point return dominates the inner least-fixed-point
return under the maximum-priority convention. -/
theorem recurring_outer_priority_dominates_inner :
    (recurringObservationProgram.game alternatingModel).priority
        recurringOuterVariable = 4 ∧
      (recurringObservationProgram.game alternatingModel).priority
        recurringInnerVariable = 1 := by
  decide

/-- Both states satisfy the recurrence formula.  At the false state, one inner
least-fixed-point step reaches the true state; the true state then returns to
the outer greatest fixed point. -/
theorem recurringObservationProgram_denotes (state : Bool) :
    recurringObservationProgram.Denotes alternatingModel state := by
  refine ⟨Set.univ, Set.mem_univ state, ?_⟩
  intro target _ candidate preFixed
  have trueMember : true ∈ candidate := by
    apply preFixed true
    left
    constructor
    · rfl
    · refine ⟨false, ?_, ?_⟩
      · simp [LTS.successors, FiniteLTS.toLTS, alternatingModel]
      · simp [satisfies, Env.extend]
  have falseMember : false ∈ candidate := by
    apply preFixed false
    right
    constructor
    · change ¬ (alternatingModel.holds false () = true)
      decide
    · refine ⟨true, ?_, ?_⟩
      · simp [LTS.successors, FiniteLTS.toLTS, alternatingModel]
      · simpa [satisfies, Env.extend] using trueMember
  cases target <;> assumption

end Mettapedia.Logic.ModalMuCalculus.EvaluationGame.Adequacy.Canary
