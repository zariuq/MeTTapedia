import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFragmentWorklistRounds

/-!
# General intersection at an older metavariable

The general intersection rule reads the newest metavariable. An intersection equation `λ x̄. G ȳ ≐ λ x̄. G z̄` on an
older `G` is read by **rotation** (`ContextualDependentPermutation`): `G` moves to the newest position past the later
declarations, each strengthened past it, along a renaming isomorphism of contexts, and the general intersection rule
runs there (`rotateIntersect`).

**The rank.** A renaming isomorphism keeps the normal weight of every side (`storeWeight_renamingIso`): η-long forms are
kept by renaming (R88's `NormalForm.rename`) and renaming keeps the weight. The arity is kept too, so the rotation's
residual has the store's rank, and the intersection's decrease is a decrease of the store's rank.

The **older round** is the general round, and when that round is stuck, the rotations below the newest declaration with
the general intersection rule at each (`olderRound`). It is conservative over the general round, eventually constant,
and settles where it is not stuck. A later declaration that mentions `G` blocks the rotation; that row stays open.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentEtaLong
open ContextualDependentIntersection ContextualDependentCumulative ContextualDependentDynamicFragment
open ContextualDependentPermutation

/-! ## Weights along a renaming isomorphism -/

section Weights

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra complete in
/-- **A side keeps its normal weight along a compatible renaming.** -/
theorem sideWeight_renamingHom {Θ Θ' : Context S.R} (π : Ren Θ.arity Θ'.arity) (forth : CtxRen Θ.raw Θ'.raw π)
    (side : TotalTerm Θ) :
    sideWeight facts roots heads algebra rigid complete (side.reindex (renamingHom π forth)) =
      sideWeight facts roots heads algebra rigid complete side := by
  obtain ⟨v, normal⟩ := long_exists facts roots heads algebra rigid complete Θ.formed side.2.typed
  have renamed := normal.rename facts forth Θ.formed Θ'.formed
  have moved : NormalForm S.R S.roles Θ'.raw (side.reindex (renamingHom π forth)).2.code (Presentation.rename π v)
      (side.reindex (renamingHom π forth)).1.code := by
    change NormalForm S.R S.roles Θ'.raw (subst (renSub π) side.2.code) _ (subst (renSub π) side.1.code)
    rw [subst_renSub, subst_renSub]
    exact renamed
  rw [sideWeight_eq facts roots heads algebra rigid complete _ moved,
    sideWeight_eq facts roots heads algebra rigid complete side normal, weight_rename]

include facts roots heads algebra complete in
/-- **A store keeps its normal weight along a compatible renaming.** -/
theorem storeWeight_renamingHom {Θ Θ' : Context S.R} (π : Ren Θ.arity Θ'.arity) (forth : CtxRen Θ.raw Θ'.raw π) :
    ∀ problem : EquationStore (TotalTerm Θ),
      storeWeight facts roots heads algebra rigid complete ((frames S.levels).applyStore (renamingHom π forth) problem) =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      have ih := storeWeight_renamingHom π forth rest
      change equationWeight facts roots heads algebra rigid complete
          (equation.1.reindex (renamingHom π forth), equation.2.reindex (renamingHom π forth)) +
          storeWeight facts roots heads algebra rigid complete ((frames S.levels).applyStore (renamingHom π forth) rest) =
        equationWeight facts roots heads algebra rigid complete equation +
          storeWeight facts roots heads algebra rigid complete rest
      unfold equationWeight
      dsimp only
      rw [ih, sideWeight_renamingHom facts roots heads algebra rigid complete π forth equation.1,
        sideWeight_renamingHom facts roots heads algebra rigid complete π forth equation.2]

include facts roots heads algebra complete in
/-- **A renaming isomorphism keeps the weight rank.** -/
theorem weightRank_renamingIso {Θ Θ' : Context S.R} (problem : EquationStore (TotalTerm Θ)) (π : Ren Θ.arity Θ'.arity)
    (π' : Ren Θ'.arity Θ.arity) (forth : CtxRen Θ.raw Θ'.raw π) (back : CtxRen Θ'.raw Θ.raw π')
    (inverse : ∀ i, π' (π i) = i) (same : Θ'.arity = Θ.arity) :
    weightRank facts roots heads algebra rigid complete (ofRenamingIso S.levels problem π π' forth back inverse).remaining =
      weightRank facts roots heads algebra rigid complete problem := by
  change (Θ'.arity, storeWeight facts roots heads algebra rigid complete
    ((frames S.levels).applyStore (renamingHom π forth) problem)) = (Θ.arity, _)
  rw [same, storeWeight_renamingHom facts roots heads algebra rigid complete π forth problem]

end Weights

/-! ## The older rule -/

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

/-- **Rotate the declaration at one depth to the newest position, then intersect there.** -/
def rotateIntersect (fuel depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (Progress facts roots heads algebra rigid complete problem) :=
  match rotateRaw Θ.raw depth with
  | none => none
  | some raw =>
      match ExecutableChecking.formContext S.R choices reducer fuel raw with
      | none => none
      | some checked =>
          if forth : CtxRen Θ.raw raw (rotRen Θ.arity depth) then
            if back : CtxRen raw Θ.raw (rotInv Θ.arity depth) then
              if inverse : ∀ i, rotInv Θ.arity depth (rotRen Θ.arity depth i) = i then
                let rotated : Context S.R :=
                  ⟨Θ.arity, raw, ExecutableChecking.ContextAlgorithm.sound facts roots heads algebra declared checked.down⟩
                let moved := ofRenamingIso S.levels problem (Θ' := rotated) (rotRen Θ.arity depth)
                  (rotInv Θ.arity depth) forth back inverse
                match generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root
                    normalizes headTypingUnique fuel moved.remaining with
                | some found => some ⟨moved.then found.val, by
                    have kept := weightRank_renamingIso facts roots heads algebra rigid complete problem
                      (Θ' := rotated) (rotRen Θ.arity depth) (rotInv Θ.arity depth) forth back inverse rfl
                    have lower := found.property
                    change ContextualDependentWorklist.Below
                      (weightRank facts roots heads algebra rigid complete found.val.remaining)
                      (weightRank facts roots heads algebra rigid complete problem)
                    rw [← kept]
                    exact lower⟩
                | none => none
              else none
            else none
          else none

/-- Try the depths in turn. -/
def rotateIntersectSearch (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    List Nat → Option (Progress facts roots heads algebra rigid complete problem)
  | [] => none
  | depth :: rest =>
      match rotateIntersect facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel depth problem with
      | some found => some found
      | none => rotateIntersectSearch fuel problem rest

/-- **The older intersection rule**: every depth below the newest declaration. -/
def olderIntersectRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (Progress facts roots heads algebra rigid complete problem) :=
  rotateIntersectSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
    headTypingUnique fuel problem (List.range' 1 (Θ.arity - 1))

/-- **One older round**: the general round; when it is stuck, the older intersection rule. -/
def olderRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match olderIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel problem with
      | some found => .progress found.val found.property
      | none => .stuck
  | other => other

/-- **The older family**, at the weight rank. -/
noncomputable def olderFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Conservativity -/

/-- **The older round makes the move of the general round wherever that round moves.** -/
theorem olderRound_eq_of_general (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (moving : generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem ≠ .stuck) :
    olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem =
      generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete fuel problem := by
  unfold olderRound
  cases computed : generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem with
  | stuck => exact absurd computed moving
  | progress update smaller => rfl
  | refuted absent => rfl

/-- **Every run that the general family decides, the older family decides with the same outcome.** -/
theorem older_run_of_general (fuel rounds : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (decided : (run ((generalFamily facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds).Decided) :
    run ((olderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds =
      run ((generalFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete).solver fuel) problem rounds :=
  ContextualDependentAcceptance.drive_conservative (weightRank facts roots heads algebra rigid complete)
    (fun problem => generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun problem => olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem)
    (fun _ moving => olderRound_eq_of_general facts roots heads algebra rigid complete declared choices
      reducer root normalizes certifyNormal headTypingUnique rootComplete fuel moving)
    rounds _ decided

/-- **The older round is not stuck where the older intersection rule fires.** -/
theorem olderRound_not_stuck_of_rule (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (read : (olderIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem).isSome) :
    olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem ≠ .stuck := by
  unfold olderRound
  cases generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      obtain ⟨found, computed⟩ := Option.isSome_iff_exists.mp read
      rw [computed]
      exact fun impossible => by cases impossible
  | progress update smaller => exact fun impossible => by cases impossible
  | refuted absent => exact fun impossible => by cases impossible

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **One rotation, then intersection, is eventually constant.** -/
theorem rotateIntersect_const (depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      rotateIntersect facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel depth problem := by
  cases rotated : rotateRaw Θ.raw depth with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      dsimp only
      unfold rotateIntersect
      rw [rotated]
  | some raw =>
      obtain ⟨t₁, formed⟩ := (formContext_const choices reducer stable raw).spec
      cases formRun : ExecutableChecking.formContext S.R choices reducer t₁ raw with
      | none =>
          refine ⟨t₁, fun fuel enough => ?_⟩
          dsimp only
          unfold rotateIntersect
          rw [rotated]
          dsimp only
          erw [formed fuel enough, formRun]
      | some checked =>
          by_cases forth : CtxRen Θ.raw raw (rotRen Θ.arity depth)
          · by_cases back : CtxRen raw Θ.raw (rotInv Θ.arity depth)
            · by_cases inverse : ∀ i, rotInv Θ.arity depth (rotRen Θ.arity depth i) = i
              · let rotatedContext : Context S.R :=
                  ⟨Θ.arity, raw, ExecutableChecking.ContextAlgorithm.sound facts roots heads algebra declared checked.down⟩
                let moved := ofRenamingIso S.levels problem (Θ' := rotatedContext) (rotRen Θ.arity depth)
                  (rotInv Θ.arity depth) forth back inverse
                obtain ⟨t₂, ruleSame⟩ := (generalIntersectRule_const facts roots heads algebra rigid complete declared
                  choices reducer root normalizes headTypingUnique stable moved.remaining).spec
                refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
                dsimp only
                unfold rotateIntersect
                rw [rotated]
                dsimp only
                erw [formed fuel (le_of_max_le_left enough), formRun, formed _ (le_max_left _ _), formRun]
                dsimp only
                rw [dif_pos forth, dif_pos forth, dif_pos back, dif_pos back, dif_pos inverse, dif_pos inverse]
                erw [ruleSame fuel (le_of_max_le_right enough), ruleSame _ (le_max_right _ _)]
              · refine ⟨t₁, fun fuel enough => ?_⟩
                dsimp only
                unfold rotateIntersect
                rw [rotated]
                dsimp only
                erw [formed fuel enough, formRun]
                dsimp only
                rw [dif_pos forth, dif_pos forth, dif_pos back, dif_pos back, dif_neg inverse, dif_neg inverse]
            · refine ⟨t₁, fun fuel enough => ?_⟩
              dsimp only
              unfold rotateIntersect
              rw [rotated]
              dsimp only
              erw [formed fuel enough, formRun]
              dsimp only
              rw [dif_pos forth, dif_pos forth, dif_neg back, dif_neg back]
          · refine ⟨t₁, fun fuel enough => ?_⟩
            dsimp only
            unfold rotateIntersect
            rw [rotated]
            dsimp only
            erw [formed fuel enough, formRun]
            dsimp only
            rw [dif_neg forth, dif_neg forth]

include stable in
theorem rotateIntersectSearch_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    ∀ depths : List Nat, EventuallyConst fun fuel =>
      rotateIntersectSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
        headTypingUnique fuel problem depths
  | [] => EventuallyConst.const _
  | depth :: rest => by
      obtain ⟨t₁, first⟩ := (rotateIntersect_const facts roots heads algebra rigid complete declared choices reducer
        root normalizes headTypingUnique stable depth problem).spec
      obtain ⟨t₂, later⟩ := (rotateIntersectSearch_const problem rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [rotateIntersectSearch]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

theorem olderRound_view (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    roundView (olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem) =
      (roundView (generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete fuel problem)).or
        (progressView facts roots heads algebra rigid complete (olderIntersectRule facts roots heads algebra rigid
          complete declared choices reducer root normalizes headTypingUnique fuel problem)) := by
  unfold olderRound
  cases generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | stuck =>
      cases olderIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel problem with
      | some found => rfl
      | none => rfl
  | progress update smaller => rfl
  | refuted absent => rfl

include stable in
/-- **The older round is eventually constant on every store.** -/
theorem olderRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => olderRound facts roots heads algebra rigid complete declared choices reducer root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  refine round_const_of_view ?_
  refine EventuallyConst.of_eq (fun fuel => olderRound_view facts roots heads algebra rigid complete declared
    choices reducer root normalizes certifyNormal headTypingUnique rootComplete fuel problem) ?_
  exact EventuallyConst.comp (fun pair : Option (Option (Update S.levels problem)) ×
      Option (Option (Update S.levels problem)) => pair.1.or pair.2)
    (EventuallyConst.pair
      (EventuallyConst.comp roundView (generalRound_const facts roots heads algebra rigid complete declared choices
        reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem))
      (EventuallyConst.comp (progressView facts roots heads algebra rigid complete)
        (rotateIntersectSearch_const facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique stable problem _)))

include stable in
/-- **The older family settles** on every class of stores on which, at each nonempty store and from some budget on,
its round is not stuck and keeps every residual store in the class. -/
noncomputable def olderSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (olderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => olderRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

include stable in
/-- **Acceptance for the older family, reduced to settling on the Miller class.** -/
theorem older_decided_of_settling_miller
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)},
      ContextualDependentShortClosure.StratifiedMiller S.levels problem →
      problem ≠ [] → ∃ bound, ∀ larger, bound ≤ larger →
        olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          olderRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            ContextualDependentShortClosure.StratifiedMiller S.levels update.remaining)
    {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run ((olderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
        run ((olderFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique rootComplete).solver budget) problem budget ∧
      ((∃ state finished, run ((olderFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger =
              .solved state finished ∧ (frames S.levels).Principal problem state.answer) ∨
        (∃ absent, run ((olderFamily facts roots heads algebra rigid complete declared choices reducer root
            normalizes certifyNormal headTypingUnique rootComplete).solver larger) problem larger = .refuted absent)) :=
  (olderSettledOfConst facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete stable
    (fun problem => ContextualDependentShortClosure.StratifiedMiller S.levels problem) eventual).decided
    (ContextualDependentShortClosure.stratifiedMiller_of_fragment inside)

end ContextualDependentIntersectionGeneral
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
