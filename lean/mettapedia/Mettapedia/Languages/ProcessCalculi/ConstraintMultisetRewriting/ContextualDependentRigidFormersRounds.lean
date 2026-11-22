import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlaceRounds

/-!
# The rigid-former round

A decomposition alone does not lower the rank, so, as for R90's decompositions, the decomposed store
is examined at once: a rigid clash among the pieces refutes it, the first of the pattern, prune and
exchange rules, or the in-place rule, may decide it. Otherwise nothing is committed.

The **rigid-former round** runs the in-place round, and when that is stuck, prepares the store and
decomposes the first equation between rigid formers that decides. Every refutation is certified,
every progress removes a declaration, and the round is eventually constant on every store
(`formersRound_const`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidFormers

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentInPlace ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- A decomposed equation, with the rest of the store, has the original solutions. -/
theorem parts_equivalent {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (parts : Parts equation)
    (rest : EquationStore (TotalTerm Θ)) :
    (frames S.levels).Equivalent (equation :: rest) (parts.val ++ rest) := fun _ σ => by
  rw [models_cons, Frames.models_append, parts.property σ]

/-- Move a rule outcome on an equivalent store back to the original store. -/
def moveFound {Θ : Context S.R} {problem parts : EquationStore (TotalTerm Θ)}
    (same : (frames S.levels).Equivalent problem parts) : Found parts → Found problem
  | .solved update smaller => .solved (((Update.pending S.levels parts).rephrase same).then update) smaller
  | .refuted absent => .refuted fun solvable =>
      absent (((Update.pending S.levels parts).rephrase same).solvable_iff.mp solvable)

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- **The rules run on a decomposed store**: a rigid clash among the pieces, the first of the
pattern, prune and exchange rules, and the in-place rule. -/
def afterParts (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (parts : EquationStore (TotalTerm Θ)) (same : (frames S.levels).Equivalent problem parts) : Option (Found problem) :=
  if clash : ContextualDependentRigid.storeClashes parts = true then
    some (.refuted fun solvable => ContextualDependentRigid.not_solvable_of_storeClashes rigid facts complete clash
      (((Update.pending S.levels parts).rephrase same).solvable_iff.mp solvable))
  else
    match firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel parts with
    | some found => some (moveFound same found)
    | none => (inPlaceRule facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique fuel parts).map (moveFound same)

/-- **The rigid-former decomposition of one store equation**, continued on the decomposed store. -/
def formerEquation (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ))
    (rest : EquationStore (TotalTerm Θ)) : Option (Found (equation :: rest)) :=
  (formerParts facts roots heads algebra complete declared choices reducer fuel equation).bind fun parts =>
    afterParts facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      headTypingUnique fuel (parts.val ++ rest) (parts_equivalent parts rest)

/-- Search the store for an equation whose decomposition decides. -/
def formerSearch (fuel : Nat) {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match formerEquation facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal headTypingUnique fuel equation rest with
      | some found => some found
      | none => (formerSearch fuel rest).map (Found.keepLeft equation)

/-- **One rigid-former round**: the in-place round, and when it is stuck, the rigid-former
decomposition on the prepared store. -/
def formersRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Round S.levels size problem :=
  match inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .progress update smaller => .progress update smaller
  | .refuted absent => .refuted absent
  | .stuck =>
      match formerSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
          headTypingUnique fuel (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining with
      | some (.solved update smaller) =>
          .progress ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then update)
            (Prod.Lex.left _ _ (by
              have same := prepare_arity facts roots heads root rootComplete fuel problem
              change update.target.arity < Θ.arity
              omega))
      | some (.refuted absent) =>
          .refuted fun solvable =>
            absent ((ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).solvable_iff.mp
              solvable)
      | none => .stuck

/-- **The rigid-former family.** -/
def formersFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := formersRound facts roots heads algebra declared choices reducer rigid complete root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

theorem idParts_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel => idParts facts roots heads algebra complete declared choices reducer fuel equation := by
  cases shaped : idShape equation with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      simp only [idParts, shaped]
  | some shape =>
      obtain ⟨t₁, s₁⟩ := (formType_const facts roots heads algebra declared choices reducer stable (Γ := Θ)
        shape.carrier).spec
      obtain ⟨t₂, s₂⟩ := (formType_const facts roots heads algebra declared choices reducer stable (Γ := Θ)
        shape.carrier').spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      simp only [idParts, shaped]
      erw [s₁ fuel (le_of_max_le_left enough), s₁ _ (le_max_left _ _), s₂ fuel (le_of_max_le_right enough),
        s₂ _ (le_max_right _ _)]

theorem binderParts_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel => binderParts facts roots heads algebra complete declared choices reducer fuel equation := by
  cases shaped : binderShape equation with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      simp only [binderParts, shaped]
  | some shape =>
      obtain ⟨t₁, s₁⟩ := (formType_const facts roots heads algebra declared choices reducer stable (Γ := Θ)
        (.pi shape.domain (.head shape.u))).spec
      obtain ⟨t₂, s₂⟩ := (formType_const facts roots heads algebra declared choices reducer stable (Γ := Θ)
        (.pi shape.domain' (.head shape.u))).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      simp only [binderParts, shaped]
      erw [s₁ fuel (le_of_max_le_left enough), s₁ _ (le_max_left _ _), s₂ fuel (le_of_max_le_right enough),
        s₂ _ (le_max_right _ _)]

theorem pairParts_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel => pairParts facts roots heads algebra declared choices reducer fuel equation := by
  cases shaped : pairShape equation with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      simp only [pairParts, shaped]
  | some shape =>
      obtain ⟨t₁, s₁⟩ := (formType_const facts roots heads algebra declared choices reducer stable (Γ := Θ)
        shape.domain).spec
      obtain ⟨t₂, s₂⟩ := (formType_const facts roots heads algebra declared choices reducer stable (Γ := Θ)
        (inst0 shape.first shape.family)).spec
      obtain ⟨t₃, s₃⟩ := (formType_const facts roots heads algebra declared choices reducer stable (Γ := Θ)
        (inst0 shape.first' shape.family)).spec
      refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
      have e₁ : t₁ ≤ fuel := by omega
      have e₂ : t₂ ≤ fuel := by omega
      have e₃ : t₃ ≤ fuel := by omega
      have f₁ : t₁ ≤ max t₁ (max t₂ t₃) := by omega
      have f₂ : t₂ ≤ max t₁ (max t₂ t₃) := by omega
      have f₃ : t₃ ≤ max t₁ (max t₂ t₃) := by omega
      simp only [pairParts, shaped]
      erw [s₁ fuel e₁, s₁ _ f₁, s₂ fuel e₂, s₂ _ f₂, s₃ fuel e₃, s₃ _ f₃]

/-- **The decomposition of one equation is eventually constant.** -/
theorem formerParts_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel => formerParts facts roots heads algebra complete declared choices reducer fuel equation :=
  EventuallyConst.comp
    (fun triple : Option (Parts equation) × Option (Parts equation) × Option (Parts equation) =>
      triple.1.or (triple.2.1.or triple.2.2))
    (EventuallyConst.pair (idParts_const facts roots heads algebra declared choices reducer complete stable equation)
      (EventuallyConst.pair (binderParts_const facts roots heads algebra declared choices reducer complete stable equation)
        (pairParts_const facts roots heads algebra declared choices reducer stable equation)))

theorem afterParts_const {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (parts : EquationStore (TotalTerm Θ)) (same : (frames S.levels).Equivalent problem parts) :
    EventuallyConst fun fuel => afterParts facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel parts same := by
  obtain ⟨t₁, first⟩ := (firstRule_const rigid facts complete roots heads algebra declared choices reducer root
    normalizes certifyNormal headTypingUnique stable parts).spec
  obtain ⟨t₂, inPlace⟩ := (inPlaceRule_const facts roots heads algebra declared choices reducer rigid complete root
    normalizes certifyNormal headTypingUnique stable parts).spec
  refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
  dsimp only
  unfold afterParts
  by_cases clash : ContextualDependentRigid.storeClashes parts = true
  · rw [dif_pos clash, dif_pos clash]
  · rw [dif_neg clash, dif_neg clash]
    erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), inPlace fuel (le_of_max_le_right enough),
      inPlace _ (le_max_right _ _)]

/-- **The rigid-former decomposition of one equation, continued, is eventually constant.** -/
theorem formerEquation_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => formerEquation facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique fuel equation rest :=
  EventuallyConst.dep (h := fun fuel => formerParts facts roots heads algebra complete declared choices reducer fuel
      equation)
    (k := fun fuel found => found.bind fun parts => afterParts facts roots heads algebra declared choices reducer rigid
      complete root normalizes certifyNormal headTypingUnique fuel (parts.val ++ rest) (parts_equivalent parts rest))
    (formerParts_const facts roots heads algebra declared choices reducer complete stable equation)
    (fun found => by
      cases found with
      | none => exact EventuallyConst.const _
      | some parts =>
          exact afterParts_const facts roots heads algebra declared choices reducer rigid complete root normalizes
            certifyNormal headTypingUnique stable (parts.val ++ rest) (parts_equivalent parts rest))

/-- The search through the store is eventually constant. -/
theorem formerSearch_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      formerSearch facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (formerEquation_const facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal headTypingUnique stable equation rest).spec
      obtain ⟨t₂, later⟩ := (formerSearch_const rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [formerSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

omit stable in
/-- The rigid-former round, read through its view. -/
theorem formersRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (formersRound facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        ((foundView (formerSearch facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal headTypingUnique fuel
          (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining)).map
          (Option.map fun update =>
            (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).then update)) := by
  unfold formersRound
  split
  · rename_i update smaller computed
    simp only [computed, roundView, Option.or]
  · rename_i absent computed
    simp only [computed, roundView, Option.or]
  · rename_i computed
    split
    · rename_i update smaller found
      simp only [computed, found, roundView, foundView, Option.or, Option.map_some]
    · rename_i absent found
      simp only [computed, found, roundView, foundView, Option.or, Option.map_some, Option.map_none]
    · rename_i found
      simp only [computed, found, roundView, foundView, Option.or, Option.map_none]

/-- **The rigid-former round is eventually constant on every store.** -/
theorem formersRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      formersRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => formersRound_view facts roots heads algebra declared choices reducer rigid
    complete root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.dep (h := fun fuel =>
      (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem,
        roundView (inPlaceRound facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)))
    (k := fun fuel pair => pair.2.or
      ((foundView (formerSearch facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique fuel pair.1.remaining)).map (Option.map fun update => pair.1.then update)))
    (EventuallyConst.pair (prepare_const root rootComplete facts roots heads problem)
      (EventuallyConst.comp roundView (inPlaceRound_const facts roots heads algebra declared choices reducer rigid
        complete root normalizes certifyNormal headTypingUnique rootComplete stable problem)))
    (fun pair => EventuallyConst.comp (fun found => pair.2.or ((foundView found).map
        (Option.map fun update => pair.1.then update)))
      (formerSearch_const facts roots heads algebra declared choices reducer rigid complete root normalizes
        certifyNormal headTypingUnique stable pair.1.remaining))

/-- **The rigid-former family settles** on every class of stores on which, at each nonempty store and
from some budget on, its round is not stuck and keeps every residual store in the class. -/
def formersSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        formersRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem} {smaller : Below (size update.remaining) (size problem)},
          formersRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller → holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (formersFamily facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => formersRound_const facts roots heads algebra declared choices reducer rigid complete
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentRigidFormers
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
