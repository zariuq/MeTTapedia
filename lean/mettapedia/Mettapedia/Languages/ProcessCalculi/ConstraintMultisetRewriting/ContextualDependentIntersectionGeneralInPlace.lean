import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralOlder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlaceRounds

/-!
# General intersection in place, below later declarations that mention the metavariable

Rotation reaches an older metavariable only when no later declaration mentions it. **In place**, with R86's
strengthening and carrying (`ContextualDependentInPlace`): the first equation is strengthened past the newest
declaration (`headSplit`), the general intersection rule runs on it there, and its answer is carried past the newest
declaration, whose type is instantiated by it (`Update.lift`). The other equations stay in place, in their order, and
are instantiated by the carried answer, never dropped. At depth `d` this is done `d` times.

**The rank.** The carried answer is the pruning answer read under the later declarations: a lifting of R76's answer,
which is exactly a `Site` of the η-long weight bound (`ContextualDependentWeightPrune.Site.lift`). So the instantiated
equations weigh no more (`storeWeight_sited`), moving the strengthened equation keeps the weight (`headSplit_weight`;
for R86's whole separation, `storeWeight_separate`), weakening keeps it, and the intersection's decrease carries through
(`carrySited`). The progress records its site (`SitedProgress`), which is how the next carry knows its answer is a
pruning answer.

The **in-place round** is the older round, and when that round is stuck, the in-place general intersection at every
depth below the newest declaration (`inPlaceRound`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentEtaLong
open ContextualDependentIntersection ContextualDependentCumulative ContextualDependentDynamicFragment
open ContextualDependentPermutation ContextualDependentPrune ContextualDependentInPlace

/-! ## Weights at a site, and under separation -/

section Weights

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **A pruning answer read under local binders**: the answer's substitution is a site of the η-long weight bound. -/
def PruneSited {Θ T : Context S.R} (answer : T ⟶ Θ) : Prop :=
  ∃ (Γ₀ : Context S.R) (type keptType : TypeOver Γ₀) (spine : Spine type) (kept : Spine keptType)
    (restriction : Restriction spine kept) (ρ : Ren (Γ₀.arity + 1) Θ.arity) (ρ' : Ren (Γ₀.arity + 1) T.arity),
    ContextualDependentWeightPrune.Site restriction Θ.raw T.raw answer.substitution ρ ρ'

include facts roots heads algebra rigid complete in
/-- **A side weighs no more under a pruning answer read under local binders.** -/
theorem sideWeight_sited {Θ T : Context S.R} (answer : T ⟶ Θ) (sited : PruneSited answer) (side : TotalTerm Θ) :
    sideWeight facts roots heads algebra rigid complete (side.reindex answer) ≤
      sideWeight facts roots heads algebra rigid complete side := by
  obtain ⟨Γ₀, type, keptType, spine, kept, restriction, ρ, ρ', site⟩ := sited
  obtain ⟨v, normal⟩ := long_exists facts roots heads algebra rigid complete Θ.formed side.2.typed
  obtain ⟨v', lv', ev, wv⟩ := (ContextualDependentWeightPrune.Long.prunes facts roots heads algebra rigid complete
    restriction normal.1) site
  have normal' : NormalForm S.R S.roles T.raw (side.reindex answer).2.code v' (side.reindex answer).1.code :=
    ⟨lv', (normal.2.substitute answer.typed).trans ev⟩
  rw [sideWeight_eq facts roots heads algebra rigid complete side normal,
    sideWeight_eq facts roots heads algebra rigid complete _ normal']
  exact wv

include facts roots heads algebra rigid complete in
/-- **A store weighs no more under a pruning answer read under local binders.** -/
theorem storeWeight_sited {Θ T : Context S.R} (answer : T ⟶ Θ) (sited : PruneSited answer) :
    ∀ problem : EquationStore (TotalTerm Θ),
      storeWeight facts roots heads algebra rigid complete ((frames S.levels).applyStore answer problem) ≤
        storeWeight facts roots heads algebra rigid complete problem
  | [] => le_refl _
  | equation :: rest => by
      have ih := storeWeight_sited answer sited rest
      have left := sideWeight_sited facts roots heads algebra rigid complete answer sited equation.1
      have right := sideWeight_sited facts roots heads algebra rigid complete answer sited equation.2
      change equationWeight facts roots heads algebra rigid complete (equation.1.reindex answer, equation.2.reindex answer) +
          storeWeight facts roots heads algebra rigid complete ((frames S.levels).applyStore answer rest) ≤
        equationWeight facts roots heads algebra rigid complete equation +
          storeWeight facts roots heads algebra rigid complete rest
      unfold equationWeight
      dsimp only
      omega

/-- **Lifting keeps the site**: the answer carried past a later declaration is the lifted site. -/
theorem PruneSited.lift {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (update : Update S.levels problem)
    (type : TypeOver Γ) (sited : PruneSited update.answer) : PruneSited (update.lift type).answer := by
  obtain ⟨Γ₀, type₀, keptType, spine, kept, restriction, ρ, ρ', site⟩ := sited
  exact ⟨Γ₀, type₀, keptType, spine, kept, restriction, _, _, site.lift type.code type.isType⟩

include facts roots heads algebra complete in
/-- Sides with the same codes weigh the same. -/
theorem sideWeight_of_codes {Θ : Context S.R} (side side' : TotalTerm Θ) (term : side.2.code = side'.2.code)
    (type : side.1.code = side'.1.code) :
    sideWeight facts roots heads algebra rigid complete side = sideWeight facts roots heads algebra rigid complete side' := by
  obtain ⟨v, normal⟩ := long_exists facts roots heads algebra rigid complete Θ.formed side.2.typed
  have normal' : NormalForm S.R S.roles Θ.raw side'.2.code v side'.1.code := by
    rw [← term, ← type]
    exact normal
  rw [sideWeight_eq facts roots heads algebra rigid complete side normal,
    sideWeight_eq facts roots heads algebra rigid complete side' normal']

include facts roots heads algebra complete in
/-- **Weakening keeps the weight.** -/
theorem storeWeight_projection {Γ : Context S.R} (type : TypeOver Γ) (problem : EquationStore (TotalTerm Γ)) :
    storeWeight facts roots heads algebra rigid complete ((frames S.levels).applyStore (projectionHom Γ type) problem) =
      storeWeight facts roots heads algebra rigid complete problem := by
  have same : projectionHom Γ type = renamingHom (Θ := Γ) (Θ' := extend Γ type) wk (CtxRen.wk Γ.raw type.code) :=
    Hom.ext rfl
  rw [same]
  exact storeWeight_renamingHom facts roots heads algebra rigid complete (Θ' := extend Γ type) wk _ problem

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R)

include facts roots heads algebra complete in
/-- **Separation keeps the weight**: the store weighs what its unstrengthened equations and its strengthened ones,
weakened back, weigh together. -/
theorem storeWeight_separate (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)),
      storeWeight facts roots heads algebra rigid complete
          ((separate facts roots heads algebra declared choices reducer fuel type problem).2 ++
            (frames S.levels).applyStore (projectionHom Γ type)
              (separate facts roots heads algebra declared choices reducer fuel type problem).1) =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      have ih := storeWeight_separate fuel type rest
      rw [storeWeight_append] at ih
      simp only [separate]
      split
      · rename_i left right _ _
        rw [storeWeight_append]
        change _ + (equationWeight facts roots heads algebra rigid complete
            (left.val.reindex (projectionHom Γ type), right.val.reindex (projectionHom Γ type)) +
            storeWeight facts roots heads algebra rigid complete ((frames S.levels).applyStore (projectionHom Γ type)
              (separate facts roots heads algebra declared choices reducer fuel type rest).1)) =
          equationWeight facts roots heads algebra rigid complete equation +
            storeWeight facts roots heads algebra rigid complete rest
        have first := sideWeight_of_codes facts roots heads algebra rigid complete
          (left.val.reindex (projectionHom Γ type)) equation.1 (weakened_codes type left).2 (weakened_codes type left).1
        have second := sideWeight_of_codes facts roots heads algebra rigid complete
          (right.val.reindex (projectionHom Γ type)) equation.2 (weakened_codes type right).2
          (weakened_codes type right).1
        unfold equationWeight
        dsimp only
        rw [first, second]
        omega
      · change storeWeight facts roots heads algebra rigid complete
            ((equation :: (separate facts roots heads algebra declared choices reducer fuel type rest).2) ++
              (frames S.levels).applyStore (projectionHom Γ type)
                (separate facts roots heads algebra declared choices reducer fuel type rest).1) =
          equationWeight facts roots heads algebra rigid complete equation +
            storeWeight facts roots heads algebra rigid complete rest
        rw [List.cons_append]
        change equationWeight facts roots heads algebra rigid complete equation + storeWeight facts roots heads algebra
            rigid complete (_ ++ _) = _
        rw [storeWeight_append]
        omega

end Weights

/-! ## Sited progress and its carrying -/

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- **A sited progress**: a progress of the weight rank whose answer is a pruning answer under local binders. -/
def SitedProgress {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Type :=
  {update : Update S.levels problem //
    ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
      (weightRank facts roots heads algebra rigid complete problem) ∧ PruneSited update.answer}

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- An update whose target and answer are a restriction's pruning answer is sited. -/
theorem pruneSited_of_heq {Γ₀ : Context S.R} {type keptType : TypeOver Γ₀} {spine : Spine type} {kept : Spine keptType}
    (restriction : Restriction spine kept) {T : Context S.R} (answer : T ⟶ extend Γ₀ type)
    (target : T = extend Γ₀ keptType) (same : HEq answer restriction.answer) : PruneSited answer := by
  subst target
  cases eq_of_heq same
  exact ⟨Γ₀, type, keptType, spine, kept, restriction, idRen, idRen, ContextualDependentWeightPrune.Site.base⟩

/-- **Every progress of general intersection on one recognized pattern is sited.** -/
theorem generalIntersect_sited (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    {scopeType : TypeOver (extend Γ₀ newer)} (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend Γ₀ newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ₀ newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ₀ newer))) (spine : Spine newer)
    (recognized : Recognized spine scope active)
    {found : Progress facts roots heads algebra rigid complete (equation :: rest)}
    (fired : generalIntersect facts roots heads algebra rigid complete declared choices reducer normalizes
      headTypingUnique fuel newer scope active equation view rest spine recognized = some found) :
    PruneSited found.val.answer := by
  have key : ∃ (keptType : TypeOver Γ₀) (kept : Spine keptType) (restriction : Restriction spine kept),
      found.val.target = extend Γ₀ keptType ∧ HEq found.val.answer restriction.answer := by
    unfold generalIntersect at fired
    dsimp only at fired
    repeat' (first | (split at fired) | (cases fired))
    exact ⟨_, _, _, rfl, heq_of_eq (Category.id_comp _)⟩
  obtain ⟨keptType, kept, restriction, target, same⟩ := key
  exact pruneSited_of_heq restriction found.val.answer target same

/-- **Every progress of general intersection on one store equation is sited.** -/
theorem generalIntersectEquation_sited (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    (equation : Equation (TotalTerm (extend Γ₀ newer))) (rest : EquationStore (TotalTerm (extend Γ₀ newer)))
    {found : Progress facts roots heads algebra rigid complete (equation :: rest)}
    (fired : generalIntersectEquation facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel newer equation rest = some found) :
    PruneSited found.val.answer := by
  unfold generalIntersectEquation at fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  exact generalIntersect_sited facts roots heads algebra rigid complete declared choices reducer normalizes
    headTypingUnique fuel newer _ _ equation _ rest _ _ fired

/-- **Every progress of the general intersection rule is sited.** -/
theorem generalIntersectRule_sited (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {found : Progress facts roots heads algebra rigid complete problem}
    (fired : generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem = some found) :
    PruneSited found.val.answer := by
  unfold generalIntersectRule at fired
  split at fired
  · cases fired
  rename_i view _
  rcases view with ⟨base, type, same⟩
  subst same
  cases problem with
  | nil => cases fired
  | cons equation rest =>
      exact generalIntersectEquation_sited facts roots heads algebra rigid complete declared choices reducer root
        normalizes headTypingUnique fuel type equation rest fired

/-- The general intersection rule, with the sites of its progresses. -/
def sitedRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (SitedProgress facts roots heads algebra rigid complete problem) :=
  match fired : generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem with
  | some found => some ⟨found.val, found.property, generalIntersectRule_sited facts roots heads algebra rigid complete
      declared choices reducer root normalizes headTypingUnique fuel problem fired⟩
  | none => none

/-- **Carry a sited progress on a strengthened store past the newest declaration.** -/
def carrySited {Γ : Context S.R} (type : TypeOver Γ) {strong : EquationStore (TotalTerm Γ)}
    {problem weak : EquationStore (TotalTerm (extend Γ type))}
    (same : (frames S.levels).Equivalent problem (weak ++ (frames S.levels).applyStore (projectionHom Γ type) strong))
    (weights : storeWeight facts roots heads algebra rigid complete
        (weak ++ (frames S.levels).applyStore (projectionHom Γ type) strong) =
      storeWeight facts roots heads algebra rigid complete problem)
    (found : SitedProgress facts roots heads algebra rigid complete strong) :
    SitedProgress facts roots heads algebra rigid complete problem :=
  ⟨((found.val.lift type).keepLeft weak).rephrase same, by
    have bound := storeWeight_sited facts roots heads algebra rigid complete _
      (PruneSited.lift found.val type found.property.2) weak
    have weakened : storeWeight facts roots heads algebra rigid complete (found.val.lift type).remaining =
        storeWeight facts roots heads algebra rigid complete found.val.remaining :=
      storeWeight_projection facts roots heads algebra rigid complete (type.reindex found.val.answer)
        found.val.remaining
    have strongWeight := storeWeight_projection facts roots heads algebra rigid complete type strong
    rw [storeWeight_append, strongWeight] at weights
    have lower := found.property.1
    unfold weightRank ContextualDependentWorklist.Below at lower ⊢
    change Prod.Lex (· < ·) (· < ·) (found.val.target.arity + 1, storeWeight facts roots heads algebra rigid complete
      ((frames S.levels).applyStore (found.val.lift type).answer weak ++ (found.val.lift type).remaining))
      (Γ.arity + 1, storeWeight facts roots heads algebra rigid complete problem)
    rw [storeWeight_append, weakened]
    rcases (Prod.lex_def).mp lower with arity | ⟨sameArity, weight⟩
    · exact Prod.Lex.left _ _ (by omega)
    · dsimp only at sameArity weight
      rw [sameArity]
      exact Prod.Lex.right _ (by omega),
    PruneSited.lift found.val type found.property.2⟩

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- Run a computation of sited progresses at the newest declaration. -/
def throughNewestSited {Θ : Context S.R} (view : Newest Θ) (problem : EquationStore (TotalTerm Θ))
    (solve : (stored : EquationStore (TotalTerm (extend view.base view.type))) →
      Option (SitedProgress facts roots heads algebra rigid complete stored)) :
    Option (SitedProgress facts roots heads algebra rigid complete problem) := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact solve problem

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- Moving a strengthened first equation, weakened back, behind the others keeps the solutions. -/
theorem headSplit_equivalent {Γ : Context S.R} (type : TypeOver Γ) (equation : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type)))
    (left : {strong : TotalTerm Γ // rename wk strong.1.code = equation.1.1.code ∧
      rename wk strong.2.code = equation.1.2.code})
    (right : {strong : TotalTerm Γ // rename wk strong.1.code = equation.2.1.code ∧
      rename wk strong.2.code = equation.2.2.code}) :
    (frames S.levels).Equivalent (equation :: rest)
      (rest ++ (frames S.levels).applyStore (projectionHom Γ type) [(left.val, right.val)]) := by
  intro Δ σ
  have same : (frames S.levels).Solves σ equation ↔
      (frames S.levels).Solves σ ((left.val.reindex (projectionHom Γ type)), (right.val.reindex (projectionHom Γ type))) :=
    solves_of_codes σ (weakened_codes type left).1.symm (weakened_codes type left).2.symm
      (weakened_codes type right).1.symm (weakened_codes type right).2.symm
  rw [models_cons, Frames.models_append, applyStore_cons, models_cons, same]
  have empty : (frames S.levels).Models σ ((frames S.levels).applyStore (projectionHom Γ type) []) :=
    fun _ member => absurd member List.not_mem_nil
  constructor
  · rintro ⟨first, later⟩
    exact ⟨later, first, empty⟩
  · rintro ⟨later, first, _⟩
    exact ⟨first, later⟩

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- Moving a strengthened first equation, weakened back, behind the others keeps the weight. -/
theorem headSplit_weight {Γ : Context S.R} (type : TypeOver Γ) (equation : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type)))
    (left : {strong : TotalTerm Γ // rename wk strong.1.code = equation.1.1.code ∧
      rename wk strong.2.code = equation.1.2.code})
    (right : {strong : TotalTerm Γ // rename wk strong.1.code = equation.2.1.code ∧
      rename wk strong.2.code = equation.2.2.code}) :
    storeWeight facts roots heads algebra rigid complete
        (rest ++ (frames S.levels).applyStore (projectionHom Γ type) [(left.val, right.val)]) =
      storeWeight facts roots heads algebra rigid complete (equation :: rest) := by
  rw [storeWeight_append]
  change _ + (equationWeight facts roots heads algebra rigid complete
      (left.val.reindex (projectionHom Γ type), right.val.reindex (projectionHom Γ type)) + 0) =
    equationWeight facts roots heads algebra rigid complete equation +
      storeWeight facts roots heads algebra rigid complete rest
  have first := sideWeight_of_codes facts roots heads algebra rigid complete
    (left.val.reindex (projectionHom Γ type)) equation.1 (weakened_codes type left).2 (weakened_codes type left).1
  have second := sideWeight_of_codes facts roots heads algebra rigid complete
    (right.val.reindex (projectionHom Γ type)) equation.2 (weakened_codes type right).2 (weakened_codes type right).1
  unfold equationWeight
  dsimp only
  rw [first, second]
  omega

omit [DecidableRel S.R.cumulative] in
/-- **Strengthen the first equation past the newest declaration**, leaving the others in place, with the solutions
and the weight of the store. -/
def headSplit (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    (problem : EquationStore (TotalTerm (extend Γ type))) →
    Option {pair : EquationStore (TotalTerm Γ) × EquationStore (TotalTerm (extend Γ type)) //
      (frames S.levels).Equivalent problem (pair.2 ++ (frames S.levels).applyStore (projectionHom Γ type) pair.1) ∧
      storeWeight facts roots heads algebra rigid complete
          (pair.2 ++ (frames S.levels).applyStore (projectionHom Γ type) pair.1) =
        storeWeight facts roots heads algebra rigid complete problem}
  | [] => none
  | equation :: rest =>
      match strengthen facts roots heads algebra declared choices reducer fuel type equation.1,
          strengthen facts roots heads algebra declared choices reducer fuel type equation.2 with
      | some left, some right => some ⟨([(left.val, right.val)], rest),
          headSplit_equivalent type equation rest left right,
          headSplit_weight facts roots heads algebra rigid complete type equation rest left right⟩
      | _, _ => none

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- Carry a sited progress of the strengthened first equation back, if the first equation strengthened. -/
def carryHead {Γ : Context S.R} (type : TypeOver Γ) (stored : EquationStore (TotalTerm (extend Γ type)))
    (recurse : (strong : EquationStore (TotalTerm Γ)) → Option (SitedProgress facts roots heads algebra rigid complete
      strong)) :
    Option {pair : EquationStore (TotalTerm Γ) × EquationStore (TotalTerm (extend Γ type)) //
      (frames S.levels).Equivalent stored (pair.2 ++ (frames S.levels).applyStore (projectionHom Γ type) pair.1) ∧
      storeWeight facts roots heads algebra rigid complete
          (pair.2 ++ (frames S.levels).applyStore (projectionHom Γ type) pair.1) =
        storeWeight facts roots heads algebra rigid complete stored} →
    Option (SitedProgress facts roots heads algebra rigid complete stored)
  | none => none
  | some split => (recurse split.val.1).map
      (carrySited facts roots heads algebra rigid complete type split.property.1 split.property.2)

/-- **General intersection at one depth below the newest declaration**, in place: the first equation is strengthened
past each later declaration, intersected there, and the answer carried back over the other equations, which keep their
order. -/
def inPlaceIntersectAt (fuel : Nat) : (depth : Nat) → {Θ : Context S.R} → (problem : EquationStore (TotalTerm Θ)) →
    Option (SitedProgress facts roots heads algebra rigid complete problem)
  | 0, _, problem => sitedRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem
  | depth + 1, Θ, problem =>
      match newestOf facts roots heads algebra declared choices reducer fuel Θ with
      | none => none
      | some view => throughNewestSited facts roots heads algebra rigid complete view problem fun stored =>
          carryHead facts roots heads algebra rigid complete view.type stored
            (fun strong => inPlaceIntersectAt fuel depth strong)
            (headSplit facts roots heads algebra rigid complete declared choices reducer fuel view.type stored)

/-- Try the depths in turn. -/
def inPlaceIntersectSearch (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    List Nat → Option (SitedProgress facts roots heads algebra rigid complete problem)
  | [] => none
  | depth :: rest =>
      match inPlaceIntersectAt facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel depth problem with
      | some found => some found
      | none => inPlaceIntersectSearch fuel problem rest

/-- **The in-place intersection rule**: every depth below the newest declaration. -/
def inPlaceIntersectRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (SitedProgress facts roots heads algebra rigid complete problem) :=
  inPlaceIntersectSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
    headTypingUnique fuel problem (List.range' 1 (Θ.arity - 1))

/-- **One in-place round**: the older round; when it is stuck, the in-place intersection rule. -/
def inPlaceRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match inPlaceIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel problem with
      | some found => .progress found.val found.property.1
      | none => .stuck
  | other => other

/-- **The in-place family**, at the weight rank. -/
noncomputable def inPlaceFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := inPlaceRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

end ContextualDependentIntersectionGeneral
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
