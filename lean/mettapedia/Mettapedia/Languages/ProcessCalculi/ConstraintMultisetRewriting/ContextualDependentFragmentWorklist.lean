import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaBudget

/-!
# The worklist round is eventually constant

The qualified worklist round refutes on a rigid clash, discharges the equations that the bounded
conversion scan certifies, and otherwise solves the newest declaration with the dispatcher. The
clash test reads no budget. The conversion scan, the conversion update, the dispatcher's alignment,
its recovery of the right side and its search through the store each give the **same result at every
large enough budget**, on every store, success and failure alike. Hence the worklist round, the
full round and the rigid round are eventually constant on every store, with no normality, typing or
fragment condition.

With every round eventually constant, settling reduces to two conditions on a class of stores:
from some budget on the round is not stuck, and when it progresses its residual store stays in the
class (`Settled.ofConst`).
-/

set_option autoImplicit false

universe u v

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentDecisiveFragment ContextualDependentConversionBudget

/-! ## Eventually constant sequences -/

/-- A function of an eventually constant sequence is eventually constant. -/
theorem EventuallyConst.comp {α : Sort u} {β : Sort v} {f : Nat → α} (g : α → β) (constant : EventuallyConst f) :
    EventuallyConst fun fuel => g (f fuel) := by
  obtain ⟨threshold, same⟩ := constant
  exact ⟨threshold, fun fuel enough => congrArg g (same fuel enough)⟩

/-- **Dependent composition**: a sequence that reads an eventually constant sequence, and that is
eventually constant at each fixed reading, is eventually constant. -/
theorem EventuallyConst.dep {α : Sort u} {β : Sort v} {h : Nat → α} {k : Nat → α → β}
    (inner : EventuallyConst h) (outer : ∀ a, EventuallyConst fun fuel => k fuel a) :
    EventuallyConst fun fuel => k fuel (h fuel) := by
  obtain ⟨t₁, same₁⟩ := inner
  obtain ⟨t₂, same₂⟩ := outer (h t₁)
  have same₂ : ∀ fuel, t₂ ≤ fuel → k fuel (h t₁) = k t₂ (h t₁) := same₂
  refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
  dsimp only
  rw [same₁ fuel (le_of_max_le_left enough), same₁ _ (le_max_left _ _), same₂ fuel (le_of_max_le_right enough),
    same₂ _ (le_max_right _ _)]

/-- An eventually constant sequence, restated pointwise. -/
theorem EventuallyConst.of_eq {α : Sort u} {f g : Nat → α} (same : ∀ fuel, f fuel = g fuel) (constant : EventuallyConst g) :
    EventuallyConst f := by
  obtain ⟨threshold, kept⟩ := constant
  exact ⟨threshold, fun fuel enough => by rw [same, same, kept fuel enough]⟩

/-- An injective image determines eventual constancy. -/
theorem EventuallyConst.of_injective {α : Sort u} {β : Sort v} {f : Nat → α} {g : α → β}
    (injective : Function.Injective g) (constant : EventuallyConst fun fuel => g (f fuel)) : EventuallyConst f := by
  obtain ⟨threshold, same⟩ := constant
  exact ⟨threshold, fun fuel enough => injective (same fuel enough)⟩

/-! ## Updates -/

section Updates

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- Two updates with the same target, answer and residual store are equal. -/
theorem Update.ext' {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)} {first second : Update levels problem}
    (target : first.target = second.target) (answer : HEq first.answer second.answer)
    (remaining : HEq first.remaining second.remaining) : first = second := by
  cases first
  cases second
  cases target
  cases answer
  cases remaining
  rfl

end Updates

/-! ## The conversion scan and the conversion update -/

section Conversion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
variable (reducer : ExecutableReduction.Reducer S.R)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- The typed comparison of two endpoints is eventually constant. -/
theorem compare_const {Γ : Context S.R} (first second : TotalTerm Γ) :
    EventuallyConst fun fuel => Conversion.compare facts roots heads algebra reducer fuel first second :=
  EventuallyConst.of_mono fun computed enough =>
    ContextualDependentEtaBudget.compare_mono facts roots heads algebra reducer stable computed enough

include stable in
/-- **The conversion scan is eventually constant on every store.** -/
theorem scan_const {Γ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Γ),
      EventuallyConst fun fuel => Conversion.scan facts roots heads algebra reducer fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (compare_const facts roots heads algebra reducer stable equation.1 equation.2).spec
      obtain ⟨t₂, later⟩ := (scan_const rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      simp only [Conversion.scan]
      rw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

/-- The conversion update is determined by its scan. -/
theorem conversion_eq_of_scan {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} {fuel larger : Nat}
    (same : Conversion.scan facts roots heads algebra reducer fuel problem =
      Conversion.scan facts roots heads algebra reducer larger problem) :
    conversion facts roots heads algebra reducer fuel problem = conversion facts roots heads algebra reducer larger problem :=
  Update.ext' rfl HEq.rfl (heq_of_eq same)

include stable in
/-- **The conversion update is eventually constant on every store.** -/
theorem conversion_const {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    EventuallyConst fun fuel => conversion facts roots heads algebra reducer fuel problem := by
  obtain ⟨threshold, same⟩ := (scan_const facts roots heads algebra reducer stable problem).spec
  exact ⟨threshold, fun fuel enough => conversion_eq_of_scan facts roots heads algebra reducer (same fuel enough)⟩

end Conversion

/-! ## The dispatcher -/

section Dispatch

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

omit [DecidableRel S.R.cumulative] in
/-- Alignment of an equation's annotations keeps its result. -/
theorem align_mono {Γ : Context S.R} (type : TypeOver Γ) (original : Equation (TotalTerm Γ)) {fuel larger : Nat}
    {result : ContextualDependentDispatch.Aligned S.levels type original}
    (computed : ContextualDependentDispatch.align facts roots heads algebra reducer fuel type original = some result)
    (enough : fuel ≤ larger) :
    ContextualDependentDispatch.align facts roots heads algebra reducer larger type original = some result := by
  unfold ContextualDependentDispatch.align at computed ⊢
  obtain ⟨first, firstRun, afterFirst⟩ := Option.bind_eq_some_iff.mp computed
  obtain ⟨second, secondRun, returned⟩ := Option.bind_eq_some_iff.mp afterFirst
  exact Option.bind_eq_some_iff.mpr ⟨first,
    ContextualDependentEtaBudget.compareTypes_mono facts roots heads algebra reducer stable firstRun enough,
    Option.bind_eq_some_iff.mpr ⟨second,
      ContextualDependentEtaBudget.compareTypes_mono facts roots heads algebra reducer stable secondRun enough,
      returned⟩⟩

omit [DecidableRel S.R.cumulative] in
theorem align_const {Γ : Context S.R} (type : TypeOver Γ) (original : Equation (TotalTerm Γ)) :
    EventuallyConst fun fuel => ContextualDependentDispatch.align facts roots heads algebra reducer fuel type original :=
  EventuallyConst.of_mono fun computed enough => align_mono facts roots heads algebra reducer stable type original
    computed enough

/-- Recovery through the projection maps is eventually constant. -/
theorem projectionRecover_const {source expanded target : Context S.R}
    (selection : ContextualDependentTypedInversion.Inclusion source expanded) (expand : expanded ⟶ target)
    (restore : target ⟶ expanded) (type : TypeOver source) (original : TotalTerm target) :
    EventuallyConst fun fuel =>
      ContextualDependentProjectionInversion.recover facts roots heads algebra declared choices reducer fuel selection
        expand restore type original :=
  EventuallyConst.of_mono fun computed enough =>
    ContextualDependentRecoveryBudget.projection_recover_mono facts roots heads algebra declared choices reducer stable
      computed enough

/-- **Recovery of a right side without the newest declaration is eventually constant.** -/
theorem recoverRight_const {Γ : Context S.R} {type : TypeOver Γ}
    (right : Term (extend Γ type) (type.reindex (projectionHom Γ type))) :
    EventuallyConst fun fuel =>
      ContextualDependentFlex.recoverRight facts roots heads algebra declared choices reducer fuel right := by
  obtain ⟨t₁, direct⟩ := (recover_const facts roots heads algebra declared choices reducer stable
    (ContextualDependentFlex.withoutNewest Γ type) type right.code).spec
  obtain ⟨t₂, projected⟩ := (projectionRecover_const facts roots heads algebra declared choices reducer stable
    (ContextualDependentFlex.withoutNewest Γ type) (𝟙 (extend Γ type)) (𝟙 (extend Γ type)) type
    (⟨_, right⟩ : TotalTerm _)).spec
  refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
  dsimp only
  unfold ContextualDependentFlex.recoverRight
  erw [direct fuel (le_of_max_le_left enough), direct _ (le_max_left _ _),
    projected fuel (le_of_max_le_right enough), projected _ (le_max_right _ _)]

/-- **Solving the newest declaration from one oriented equation is eventually constant.** -/
theorem solveNewest_const {Γ : Context S.R} {type : TypeOver Γ}
    (left right : Term (extend Γ type) (type.reindex (projectionHom Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    EventuallyConst fun fuel =>
      ContextualDependentFlex.solveNewest facts roots heads algebra declared choices reducer fuel left right rest := by
  obtain ⟨t₁, compared⟩ := (compare_const facts roots heads algebra reducer stable
    (⟨_, left⟩ : TotalTerm _) (Elimination.last Γ type)).spec
  obtain ⟨t₂, recovered⟩ := (recoverRight_const facts roots heads algebra declared choices reducer stable right).spec
  cases leftRun : Conversion.compare facts roots heads algebra reducer t₁ (⟨_, left⟩ : TotalTerm _)
      (Elimination.last Γ type) with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold ContextualDependentFlex.solveNewest
      simp only [Option.bind_eq_bind]
      erw [compared fuel enough, leftRun]
      rfl
  | some isVariable =>
      cases rightRun : ContextualDependentFlex.recoverRight facts roots heads algebra declared choices reducer t₂ right with
      | none =>
          refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
          dsimp only
          unfold ContextualDependentFlex.solveNewest
          simp only [Option.bind_eq_bind]
          erw [compared fuel (le_of_max_le_left enough), leftRun, compared _ (le_max_left _ _), leftRun]
          simp only [Option.bind_some]
          erw [recovered fuel (le_of_max_le_right enough), rightRun, recovered _ (le_max_right _ _), rightRun]
          rfl
      | some answer =>
          let eliminated := (ContextualDependentUpdate.definition S.levels answer.body rest).rephrase
            (ContextualDependentFlex.recovered_equivalent S.levels left right isVariable.down answer.body answer.solves
              rest)
          obtain ⟨t₃, converted⟩ := (conversion_const facts roots heads algebra reducer stable eliminated.remaining).spec
          refine ⟨max (max t₁ t₂) t₃, fun fuel enough => ?_⟩
          have e₁ : t₁ ≤ fuel := by omega
          have e₂ : t₂ ≤ fuel := by omega
          have e₃ : t₃ ≤ fuel := by omega
          have f₁ : t₁ ≤ max (max t₁ t₂) t₃ := by omega
          have f₂ : t₂ ≤ max (max t₁ t₂) t₃ := by omega
          have f₃ : t₃ ≤ max (max t₁ t₂) t₃ := by omega
          dsimp only
          unfold ContextualDependentFlex.solveNewest
          simp only [Option.bind_eq_bind]
          erw [compared fuel e₁, leftRun, compared _ f₁, leftRun]
          simp only [Option.bind_some]
          erw [recovered fuel e₂, rightRun, recovered _ f₂, rightRun]
          simp only [Option.bind_some]
          change some (eliminated.then (conversion facts roots heads algebra reducer fuel eliminated.remaining)) =
            some (eliminated.then (conversion facts roots heads algebra reducer _ eliminated.remaining))
          rw [converted fuel e₃, converted _ f₃]

/-- **The orientation of one equation by the dispatcher is eventually constant.** -/
theorem orient_const {Γ : Context S.R} (type : TypeOver Γ) (original : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    EventuallyConst fun fuel =>
      ContextualDependentDispatch.orient facts roots heads algebra declared choices reducer fuel type original rest := by
  obtain ⟨t₁, aligned⟩ := (align_const facts roots heads algebra reducer stable
    (type.reindex (projectionHom Γ type)) original).spec
  cases alignRun : ContextualDependentDispatch.align facts roots heads algebra reducer t₁
      (type.reindex (projectionHom Γ type)) original with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold ContextualDependentDispatch.orient
      simp only [Option.bind_eq_bind]
      erw [aligned fuel enough, alignRun]
      rfl
  | some alignment =>
      obtain ⟨t₂, forward⟩ := (solveNewest_const facts roots heads algebra declared choices reducer stable
        alignment.left alignment.right rest).spec
      obtain ⟨t₃, backward⟩ := (solveNewest_const facts roots heads algebra declared choices reducer stable
        alignment.right alignment.left rest).spec
      refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
      have e₁ : t₁ ≤ fuel := by omega
      have e₂ : t₂ ≤ fuel := by omega
      have e₃ : t₃ ≤ fuel := by omega
      have f₁ : t₁ ≤ max t₁ (max t₂ t₃) := by omega
      have f₂ : t₂ ≤ max t₁ (max t₂ t₃) := by omega
      have f₃ : t₃ ≤ max t₁ (max t₂ t₃) := by omega
      dsimp only
      unfold ContextualDependentDispatch.orient
      simp only [Option.bind_eq_bind]
      erw [aligned fuel e₁, alignRun, aligned _ f₁, alignRun]
      simp only [Option.bind_some]
      erw [forward fuel e₂, forward _ f₂, backward fuel e₃, backward _ f₃]

/-- **The dispatcher's search through the store is eventually constant.** -/
theorem search_const {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)), EventuallyConst fun fuel =>
      ContextualDependentDispatch.search facts roots heads algebra declared choices reducer fuel type problem
  | [] => EventuallyConst.const _
  | original :: rest => by
      obtain ⟨t₁, first⟩ := (orient_const facts roots heads algebra declared choices reducer stable type original
        rest).spec
      obtain ⟨t₂, later⟩ := (search_const type rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [ContextualDependentDispatch.search]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

omit stable in
/-- The dispatcher at the newest declaration, read without its rank proof. -/
theorem dispatchNewest_val (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type))) :
    (dispatchNewest facts roots heads algebra declared choices reducer fuel type problem).map Subtype.val =
      (ContextualDependentDispatch.search facts roots heads algebra declared choices reducer fuel type problem).map
        fun updated => updated.then (conversion facts roots heads algebra reducer fuel updated.remaining) := by
  unfold dispatchNewest
  split
  · rename_i found
    rw [found]
    rfl
  · rename_i updated found
    change some (updated.then (conversion facts roots heads algebra reducer fuel updated.remaining)) = _
    rw [found]
    rfl

/-- **The dispatcher at the newest declaration is eventually constant.** -/
theorem dispatchNewest_const {Γ : Context S.R} (type : TypeOver Γ) (problem : EquationStore (TotalTerm (extend Γ type))) :
    EventuallyConst fun fuel => dispatchNewest facts roots heads algebra declared choices reducer fuel type problem := by
  refine EventuallyConst.of_injective (g := Option.map Subtype.val) (Option.map_injective Subtype.val_injective) ?_
  refine EventuallyConst.of_eq (fun fuel => dispatchNewest_val facts roots heads algebra declared choices reducer fuel
    type problem) ?_
  exact EventuallyConst.dep (h := fun fuel =>
      ContextualDependentDispatch.search facts roots heads algebra declared choices reducer fuel type problem)
    (k := fun fuel found => found.map fun updated =>
      updated.then (conversion facts roots heads algebra reducer fuel updated.remaining))
    (search_const facts roots heads algebra declared choices reducer stable type problem)
    (fun found => by
      cases found with
      | none => exact EventuallyConst.const _
      | some updated =>
          exact EventuallyConst.comp (fun converted => some (updated.then converted))
            (conversion_const facts roots heads algebra reducer stable updated.remaining))

omit stable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative] in
theorem throughNewest_const {Γ : Context S.R} (view : Newest Γ) (problem : EquationStore (TotalTerm Γ))
    (solve : Nat → (stored : EquationStore (TotalTerm (extend view.base view.type))) →
      Option {update : Update S.levels stored // update.target.arity < view.base.arity + 1})
    (constant : ∀ stored, EventuallyConst fun fuel => solve fuel stored) :
    EventuallyConst fun fuel => throughNewest view problem (solve fuel) := by
  rcases view with ⟨base, type, same⟩
  subst same
  exact constant problem

end Dispatch

/-! ## The worklist round, the full round and the rigid round -/

section Rounds

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid) (facts : FormFacts S.R S.roles)
  (complete : AlgorithmicComplete S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

/-- **The worklist round is eventually constant on every store**: clash, conversion and dispatch. -/
theorem worklistRound_const {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) :
    EventuallyConst fun fuel =>
      ContextualDependentWorklist.round rigid facts complete roots heads algebra declared choices reducer fuel problem := by
  obtain ⟨t₁, scanned⟩ := (scan_const facts roots heads algebra reducer stable problem).spec
  obtain ⟨t₂, newest⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Γ).spec
  have converted : ∀ fuel, t₁ ≤ fuel →
      conversion facts roots heads algebra reducer fuel problem = conversion facts roots heads algebra reducer t₁ problem :=
    fun fuel enough => conversion_eq_of_scan facts roots heads algebra reducer (scanned fuel enough)
  cases viewRun : newestOf facts roots heads algebra declared choices reducer t₂ Γ with
  | none =>
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      have e₁ : t₁ ≤ fuel := by omega
      have e₂ : t₂ ≤ fuel := by omega
      have f₁ : t₁ ≤ max t₁ t₂ := by omega
      have f₂ : t₂ ≤ max t₁ t₂ := by omega
      dsimp only
      unfold ContextualDependentWorklist.round
      by_cases clash : ContextualDependentRigid.storeClashes problem = true
      · rw [dif_pos clash, dif_pos clash]
      · rw [dif_neg clash, dif_neg clash]
        by_cases shorter : (Conversion.scan facts roots heads algebra reducer t₁ problem).length < problem.length
        · have shorterAt : ∀ fuel', t₁ ≤ fuel' →
              (Conversion.scan facts roots heads algebra reducer fuel' problem).length < problem.length :=
            fun fuel' enough' => by rw [scanned fuel' enough']; exact shorter
          rw [dif_pos (shorterAt fuel e₁), dif_pos (shorterAt _ f₁)]
          congr 1
          rw [converted fuel e₁, converted _ f₁]
        · have notShorter : ∀ fuel', t₁ ≤ fuel' →
              ¬ (Conversion.scan facts roots heads algebra reducer fuel' problem).length < problem.length :=
            fun fuel' enough' => by rw [scanned fuel' enough']; exact shorter
          rw [dif_neg (notShorter fuel e₁), dif_neg (notShorter _ f₁)]
          erw [newest fuel e₂, viewRun, newest _ f₂, viewRun]
  | some view =>
      obtain ⟨t₃, dispatched⟩ := (throughNewest_const view problem
        (fun fuel => dispatchNewest facts roots heads algebra declared choices reducer fuel view.type)
        (fun stored => dispatchNewest_const facts roots heads algebra declared choices reducer stable view.type
          stored)).spec
      refine ⟨max (max t₁ t₂) t₃, fun fuel enough => ?_⟩
      have e₁ : t₁ ≤ fuel := by omega
      have e₂ : t₂ ≤ fuel := by omega
      have e₃ : t₃ ≤ fuel := by omega
      have f₁ : t₁ ≤ max (max t₁ t₂) t₃ := by omega
      have f₂ : t₂ ≤ max (max t₁ t₂) t₃ := by omega
      have f₃ : t₃ ≤ max (max t₁ t₂) t₃ := by omega
      dsimp only
      unfold ContextualDependentWorklist.round
      by_cases clash : ContextualDependentRigid.storeClashes problem = true
      · rw [dif_pos clash, dif_pos clash]
      · rw [dif_neg clash, dif_neg clash]
        by_cases shorter : (Conversion.scan facts roots heads algebra reducer t₁ problem).length < problem.length
        · have shorterAt : ∀ fuel', t₁ ≤ fuel' →
              (Conversion.scan facts roots heads algebra reducer fuel' problem).length < problem.length :=
            fun fuel' enough' => by rw [scanned fuel' enough']; exact shorter
          rw [dif_pos (shorterAt fuel e₁), dif_pos (shorterAt _ f₁)]
          congr 1
          rw [converted fuel e₁, converted _ f₁]
        · have notShorter : ∀ fuel', t₁ ≤ fuel' →
              ¬ (Conversion.scan facts roots heads algebra reducer fuel' problem).length < problem.length :=
            fun fuel' enough' => by rw [scanned fuel' enough']; exact shorter
          rw [dif_neg (notShorter fuel e₁), dif_neg (notShorter _ f₁)]
          erw [newest fuel e₂, viewRun, newest _ f₂, viewRun]
          dsimp only
          erw [dispatched fuel e₃, dispatched _ f₃]

/-- **The full round is eventually constant on every store.** -/
theorem fullRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      ContextualDependentPatternSolver.fullRound rigid facts complete roots heads algebra declared choices reducer root
        normalizes certifyNormal headTypingUnique fuel problem := by
  obtain ⟨t₁, firstSame⟩ := (firstRule_const rigid facts complete roots heads algebra declared choices reducer root
    normalizes certifyNormal headTypingUnique stable problem).spec
  obtain ⟨t₂, worklistSame⟩ := (worklistRound_const rigid facts complete roots heads algebra declared choices reducer
    stable problem).spec
  refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
  dsimp only
  rw [fullRound_eq, fullRound_eq, firstSame fuel (le_of_max_le_left enough), firstSame _ (le_max_left _ _)]
  cases firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique t₁ problem with
  | some found => cases found <;> rfl
  | none =>
      dsimp only
      rw [worklistSame fuel (le_of_max_le_right enough), worklistSame _ (le_max_right _ _)]

/-- **The rigid round is eventually constant on every store.** -/
theorem rigidRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices reducer
        root normalizes certifyNormal headTypingUnique fuel problem := by
  obtain ⟨t₁, localsSame⟩ := (localsRule_const facts roots heads algebra declared choices reducer root stable rigid
    complete problem).spec
  obtain ⟨t₂, fullSame⟩ := (fullRound_const rigid facts complete roots heads algebra declared choices reducer root
    normalizes certifyNormal headTypingUnique stable problem).spec
  refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
  dsimp only
  unfold ContextualDependentRigidDecomposition.rigidRound
  erw [localsSame fuel (le_of_max_le_left enough), localsSame _ (le_max_left _ _)]
  cases ContextualDependentRigidDecomposition.localsRule rigid complete facts roots heads algebra declared choices
      reducer root t₁ problem with
  | some absent => rfl
  | none =>
      dsimp only
      rw [fullSame fuel (le_of_max_le_right enough), fullSame _ (le_max_right _ _)]

end Rounds

/-! ## Settling from eventual constancy -/

section Settling

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **Settling, for a family whose rounds are eventually constant.** On a class of stores where,
at every nonempty store and from some budget on, the round is not stuck and every progressing
round leaves its residual store in the class, the family settles. -/
def Settled.ofConst (family : ContextualDependentDecisiveDriver.Family levels)
    (constant : ∀ {Γ : Context rules} (problem : EquationStore (TotalTerm Γ)),
      EventuallyConst fun fuel => family.round fuel problem)
    (holds : {Γ : Context rules} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context rules} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger → family.round larger problem ≠ .stuck ∧
        ∀ {update : Update levels problem}
          {smaller : Below (family.rank update.remaining) (family.rank problem)},
          family.round larger problem = .progress update smaller → holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled family where
  holds := holds
  settles := by
    intro Γ problem inside nonempty
    obtain ⟨t₁, same⟩ := (constant problem).spec
    obtain ⟨bound, firing⟩ := eventual inside nonempty
    let threshold := max t₁ bound
    have at_threshold := firing threshold (le_max_right _ _)
    refine ⟨threshold, at_threshold.1, fun fuel enough =>
      (same fuel (le_of_max_le_left enough)).trans (same _ (le_max_left _ _)).symm, ?_⟩
    intro update smaller progressed
    exact at_threshold.2 progressed

end Settling

end ContextualDependentFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
