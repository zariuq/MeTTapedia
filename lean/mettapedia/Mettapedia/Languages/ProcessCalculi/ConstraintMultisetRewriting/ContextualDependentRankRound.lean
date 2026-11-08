import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRankParts

/-!
# The ranked round: decomposition commits unconditionally

The **ranked round** is a round for the weight rank. It runs the full occurs round:

* a refutation is kept;
* a progress that removes a declaration is kept, since it lowers the first component of the rank;
* otherwise, and when the full occurs round is stuck, it runs the conversion scan, and when the scan
  removes nothing it **decomposes the first equation between rigid formers and commits**, whatever the
  following rules do with the pieces.

Every progress lowers the weight rank (`Round` carries the proof), and the weight rank is well founded,
so the driver's progress argument applies unchanged. The commit-if-decides test of R94 is gone from this
variant: a decomposition is a step of its own, because it lowers the normal weight by two.

Neutral spines (R94's two-argument spine rule) are still decomposed only through the full occurs round.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRank

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentInPlace
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentOccursCheck
open ContextualDependentOccursFull ContextualDependentDecisiveFragment ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-! ## Lowering the weight rank -/

theorem below_of_arity {Θ Θ' : Context S.R} {first : EquationStore (TotalTerm Θ')}
    {second : EquationStore (TotalTerm Θ)} (lower : Θ'.arity < Θ.arity) :
    ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete first)
      (weightRank facts roots heads algebra rigid complete second) :=
  Prod.Lex.left _ _ lower

theorem below_of_weight {Θ : Context S.R} {first second : EquationStore (TotalTerm Θ)}
    (lower : storeWeight facts roots heads algebra rigid complete first <
      storeWeight facts roots heads algebra rigid complete second) :
    ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete first)
      (weightRank facts roots heads algebra rigid complete second) :=
  Prod.Lex.right _ lower

/-! ## Decomposing the first equation -/

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R)

/-- A decomposition with its weight. -/
abbrev WeighedParts {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :=
  {parts : Parts equation // storeWeight facts roots heads algebra rigid complete parts.val <
    equationWeight facts roots heads algebra rigid complete equation}

/-- The rigid-former decomposition of one equation, with its weight. -/
def weighedParts (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (WeighedParts facts roots heads algebra rigid complete equation) :=
  match found : formerParts facts roots heads algebra complete declared choices reducer fuel equation with
  | some parts => some ⟨parts, by
      have weighs := formerParts_weight facts roots heads algebra rigid complete declared choices reducer fuel found
      omega⟩
  | none => none

theorem weighedParts_val (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    (weighedParts facts roots heads algebra rigid complete declared choices reducer fuel equation).map Subtype.val =
      formerParts facts roots heads algebra complete declared choices reducer fuel equation := by
  unfold weighedParts
  split
  · rename_i parts found
    exact found.symm
  · rename_i found
    exact found.symm

/-- A decomposed store: equivalent to the original, and lighter. -/
abbrev Decomposed {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :=
  {store : EquationStore (TotalTerm Θ) // (frames S.levels).Equivalent problem store ∧
    storeWeight facts roots heads algebra rigid complete store <
      storeWeight facts roots heads algebra rigid complete problem}

/-- Decompose an equation in front of a store. -/
def decomposeHere {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (weighed : WeighedParts facts roots heads algebra rigid complete equation) :
    Decomposed facts roots heads algebra rigid complete (equation :: rest) :=
  ⟨weighed.val.val ++ rest, parts_equivalent weighed.val rest, by
    have weight := weighed.property
    rw [storeWeight_append]
    simp only [storeWeight]
    omega⟩

/-- Keep an equation in front of a decomposed store. -/
def decomposeLater {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) {rest : EquationStore (TotalTerm Θ)}
    (found : Decomposed facts roots heads algebra rigid complete rest) :
    Decomposed facts roots heads algebra rigid complete (equation :: rest) :=
  ⟨equation :: found.val, fun _ σ => by rw [models_cons, models_cons, found.property.1 _ σ], by
    have lighter := found.property.2
    simp only [storeWeight]
    omega⟩

/-- One step of the search: decompose the first equation, or keep it and search the rest. -/
def decomposeStep {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ))
    (pair : Option (WeighedParts facts roots heads algebra rigid complete equation) ×
      Option (Decomposed facts roots heads algebra rigid complete rest)) :
    Option (Decomposed facts roots heads algebra rigid complete (equation :: rest)) :=
  match pair.1 with
  | some weighed => some (decomposeHere facts roots heads algebra rigid complete rest weighed)
  | none => pair.2.map (decomposeLater facts roots heads algebra rigid complete equation)

/-- **Decompose the first equation between rigid formers.** -/
def decomposeFirst (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (Decomposed facts roots heads algebra rigid complete problem)
  | [] => none
  | equation :: rest => decomposeStep facts roots heads algebra rigid complete equation rest
      (weighedParts facts roots heads algebra rigid complete declared choices reducer fuel equation,
        decomposeFirst fuel rest)

/-! ## The ranked round -/

variable (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- The rest of a ranked round: the conversion scan, then one decomposition, committed. -/
def rankedRest (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  if shorter : (Conversion.scan facts roots heads algebra reducer fuel problem).length < problem.length then
    .progress (conversion facts roots heads algebra reducer fuel problem)
      (below_of_weight facts roots heads algebra rigid complete
        (scan_weight_lt facts roots heads algebra rigid complete reducer fuel problem shorter))
  else
    match decomposeFirst facts roots heads algebra rigid complete declared choices reducer fuel problem with
    | some found => .progress ((Update.pending S.levels found.val).rephrase found.property.1)
        (below_of_weight facts roots heads algebra rigid complete found.property.2)
    | none => .stuck

/-- **One ranked round**: the full occurs round, keeping its refutations and the progress that removes
a declaration; otherwise the conversion scan, then one committed decomposition. -/
def rankedRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match occursFullRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | .refuted absent => .refuted absent
  | .progress update _ =>
      if lower : update.target.arity < Θ.arity then
        .progress update (below_of_arity facts roots heads algebra rigid complete lower)
      else rankedRest facts roots heads algebra rigid complete declared choices reducer fuel problem
  | .stuck => rankedRest facts roots heads algebra rigid complete declared choices reducer fuel problem

/-- **The ranked family**, at the weight rank. -/
noncomputable def rankedFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := rankedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-- **Every refutation of the ranked round is a refutation of the full occurs round.** -/
theorem rankedRound_refuted {fuel : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {absent : ¬ (frames S.levels).Solvable problem}
    (refuted : rankedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem = .refuted absent) :
    ∃ absent', occursFullRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem = .refuted absent' := by
  unfold rankedRound at refuted
  split at refuted
  · rename_i absent' computed
    exact ⟨absent', computed⟩
  · split at refuted
    · cases refuted
    · unfold rankedRest at refuted
      split at refuted
      · cases refuted
      · split at refuted <;> cases refuted
  · unfold rankedRest at refuted
    split at refuted
    · cases refuted
    · split at refuted <;> cases refuted

/-! ## Eventual constancy -/

/-- The view of the rest of a ranked round. -/
def restView {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) (scanned : EquationStore (TotalTerm Θ))
    (converted : Update S.levels problem) (found : Option (Decomposed facts roots heads algebra rigid complete problem)) :
    Option (Option (Update S.levels problem)) :=
  if scanned.length < problem.length then some (some converted)
  else found.map fun found => some ((Update.pending S.levels found.val).rephrase found.property.1)

theorem rankedRest_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (rankedRest facts roots heads algebra rigid complete declared choices reducer fuel problem) =
      restView facts roots heads algebra rigid complete problem
        (Conversion.scan facts roots heads algebra reducer fuel problem)
        (conversion facts roots heads algebra reducer fuel problem)
        (decomposeFirst facts roots heads algebra rigid complete declared choices reducer fuel problem) := by
  unfold rankedRest restView
  by_cases shorter : (Conversion.scan facts roots heads algebra reducer fuel problem).length < problem.length
  · rw [dif_pos shorter, if_pos shorter]
    rfl
  · rw [dif_neg shorter, if_neg shorter]
    cases decomposeFirst facts roots heads algebra rigid complete declared choices reducer fuel problem <;> rfl

/-- The view of a ranked round, from the views of its parts. -/
def rankedView {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (base : Option (Option (Update S.levels problem))) (rest : Option (Option (Update S.levels problem))) :
    Option (Option (Update S.levels problem)) :=
  match base with
  | some none => some none
  | some (some update) => if update.target.arity < Θ.arity then some (some update) else rest
  | none => rest

theorem rankedRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (rankedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      rankedView (roundView (occursFullRound facts roots heads algebra rigid complete declared choices reducer root
          normalizes certifyNormal headTypingUnique rootComplete fuel problem))
        (roundView (rankedRest facts roots heads algebra rigid complete declared choices reducer fuel problem)) := by
  unfold rankedRound
  split
  · rename_i absent computed
    simp only [computed, roundView, rankedView]
  · rename_i update smaller computed
    by_cases lower : update.target.arity < Θ.arity
    · simp only [computed, roundView, rankedView, dif_pos lower, if_pos lower]
    · simp only [computed, roundView, rankedView, dif_neg lower, if_neg lower]
  · rename_i computed
    simp only [computed, roundView, rankedView]

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem weighedParts_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      weighedParts facts roots heads algebra rigid complete declared choices reducer fuel equation := by
  refine EventuallyConst.of_injective (g := Option.map Subtype.val) (Option.map_injective Subtype.val_injective) ?_
  exact EventuallyConst.of_eq (fun fuel => weighedParts_val facts roots heads algebra rigid complete declared choices
    reducer fuel equation) (formerParts_const facts roots heads algebra declared choices reducer complete stable equation)

include stable in
/-- **Decomposing the first equation is eventually constant.** -/
theorem decomposeFirst_const {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      EventuallyConst fun fuel =>
        decomposeFirst facts roots heads algebra rigid complete declared choices reducer fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.comp (decomposeStep facts roots heads algebra rigid complete equation rest)
        (EventuallyConst.pair
          (weighedParts_const facts roots heads algebra rigid complete declared choices reducer stable equation)
          (decomposeFirst_const rest))

include stable in
theorem rankedRest_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      rankedRest facts roots heads algebra rigid complete declared choices reducer fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => rankedRest_view facts roots heads algebra rigid complete declared choices
    reducer fuel problem) ?_
  exact EventuallyConst.comp (fun triple => restView facts roots heads algebra rigid complete problem triple.1 triple.2.1
      triple.2.2)
    (EventuallyConst.pair (scan_const facts roots heads algebra reducer stable problem)
      (EventuallyConst.pair (conversion_const facts roots heads algebra reducer stable problem)
        (decomposeFirst_const facts roots heads algebra rigid complete declared choices reducer stable problem)))

include stable in
/-- **The ranked round is eventually constant on every store.** -/
theorem rankedRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => rankedRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => rankedRound_view facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair => rankedView pair.1 pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (occursFullRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp roundView (rankedRest_const facts roots heads algebra rigid complete declared choices reducer
        stable problem)))

include stable in
/-- **The ranked family settles** on every class of stores on which, at each nonempty store and from
some budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def rankedSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        rankedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          rankedRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
              headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (rankedFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => rankedRound_const facts roots heads algebra rigid complete declared choices reducer
    root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentRank
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
