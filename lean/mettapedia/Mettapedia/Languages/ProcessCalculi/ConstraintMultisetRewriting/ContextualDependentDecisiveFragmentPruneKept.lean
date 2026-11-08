import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDecisiveFragmentKept

/-!
# Rule results found at one budget, kept at every larger budget

Spine discovery, type formation and recovery keep their successful results; the readers between
them do not use the budget. So:

* the pattern rule on one reading is kept when its occurrence is not an application, or not a
  pattern, or its recovery finished, or its other side does not invert into the pattern's scope;
  the computable check `searchFirm` collects this, together with a finished reading, for a
  one-equation store, and `searchFirm_kept` keeps the pattern search there, whatever its outcome;
* the prune rule is kept through its outer layers (one reading, one equation, the store, the two
  newest declarations) once its step on the recognized pattern is kept;
* the first rule that fires is the prune rule's answer, kept, once the pattern rule is kept and
  fails and the prune rule is kept and fires.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDecisiveFragment

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentPiSpine ContextualDependentScope ContextualDependentConversionBudget
open ContextualDependentGeneralPattern ContextualDependentWorklist ContextualDependentPatternSolver
open ContextualDependentUpdate ContextualDependentPrune

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The two newest declarations -/

/-- The store read at the two newest declarations, as `throughTwo` reads it. -/
def twoNewestStore {Θ : Context S.R} (outer : Newest Θ) (inner : Newest outer.base)
    (problem : EquationStore (TotalTerm Θ)) :
    (Γ₀ : Context S.R) × (older : TypeOver Γ₀) × (newer : TypeOver (extend Γ₀ older)) ×
      EquationStore (TotalTerm (extend (extend Γ₀ older) newer)) := by
  cases outer with
  | mk base newer same =>
      cases inner with
      | mk base₀ older same₀ =>
          change base = extend base₀ older at same₀
          subst same₀
          subst same
          exact ⟨base₀, older, newer, problem⟩

/-- Two computations agree through the two newest declarations when they agree on the store read
there. -/
theorem throughTwo_congr {Θ : Context S.R} (outer : Newest Θ) (inner : Newest outer.base)
    (problem : EquationStore (TotalTerm Θ))
    (first second : {Γ₀ : Context S.R} → (older : TypeOver Γ₀) → (newer : TypeOver (extend Γ₀ older)) →
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (Found stored))
    (same : first (twoNewestStore outer inner problem).2.1 (twoNewestStore outer inner problem).2.2.1
        (twoNewestStore outer inner problem).2.2.2 =
      second (twoNewestStore outer inner problem).2.1 (twoNewestStore outer inner problem).2.2.1
        (twoNewestStore outer inner problem).2.2.2) :
    throughTwo outer inner problem first = throughTwo outer inner problem second := by
  cases outer with
  | mk base newer sameOuter =>
      cases inner with
      | mk base₀ older sameInner =>
          change base = extend base₀ older at sameInner
          subst sameInner
          subst sameOuter
          exact same

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

/-! ## The prune rule, kept -/

section Prune

include stable

/-- **The prune rule on one scoped reading is kept** once its spine is discovered, its pattern
recognized, and the prune rule on that pattern kept. -/
theorem pruneActive_kept {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) {budget : Nat}
    {headIndex : Fin scope.target.arity} {arguments : List (Fin scope.target.arity)}
    (read : readApplication active.left.code = some (headIndex, arguments)) {spine : Spine newer}
    (discovered : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer budget
      arguments.length newer = some spine)
    {found : Recognized spine scope active} (recognized : recognize spine scope active = some found)
    (pruneKept : ∀ larger, budget ≤ larger →
      tryPrune rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique larger older newer scope active equation view rest spine found =
        tryPrune rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique budget older newer scope active equation view rest spine found) :
    ∀ larger, budget ≤ larger →
      pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique larger older newer scope active equation view rest =
        pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique budget older newer scope active equation view rest := by
  intro larger enough
  unfold pruneActive
  rw [read]
  dsimp only
  erw [discover_mono facts roots heads algebra declared choices reducer stable _ newer discovered enough, discovered]
  dsimp only
  rw [recognized]
  dsimp only
  exact pruneKept larger enough

omit stable in
/-- **The prune rule on one equation is kept** once its reading is kept and its first orientation
fires and is kept. -/
theorem pruneEquation_kept {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) {budget : Nat}
    {reading : (scope : Spine equation.1.1) × (active : Active scope.target) ×'
      ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
        (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution}
    (viewed : viewEquation facts roots heads algebra declared choices reducer root budget equation = some reading)
    (viewKept : ∀ larger, budget ≤ larger →
      viewEquation facts roots heads algebra declared choices reducer root larger equation =
        viewEquation facts roots heads algebra declared choices reducer root budget equation)
    {found : Found (equation :: rest)}
    (fires : pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique budget older newer reading.1 reading.2.1 equation reading.2.2 rest = some found)
    (activeKept : ∀ larger, budget ≤ larger →
      pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique larger older newer reading.1 reading.2.1 equation reading.2.2 rest =
        pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique budget older newer reading.1 reading.2.1 equation reading.2.2 rest) :
    ∀ larger, budget ≤ larger →
      pruneEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique larger older newer equation rest = some found := by
  intro larger enough
  unfold pruneEquation
  rw [viewKept larger enough, viewed]
  dsimp only
  rw [activeKept larger enough, fires]

omit stable in
/-- The prune search through a one-equation store is kept once its equation is. -/
theorem pruneSearch_singleton_kept {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer))) {budget : Nat} {found : Found [equation]}
    (fires : ∀ larger, budget ≤ larger →
      pruneEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique larger older newer equation [] = some found) :
    ∀ larger, budget ≤ larger →
      pruneSearch rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique larger older newer [equation] = some found := by
  intro larger enough
  simp only [pruneSearch]
  rw [fires larger enough]

/-- **The prune rule is kept** once its two newest declarations are read and its search, on the
store read there, is kept. -/
theorem pruneRule_kept {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) {budget : Nat}
    {outer : Newest Θ} {inner : Newest outer.base}
    (outerRead : ContextualDependentWorklist.newestOf facts roots heads algebra declared choices reducer budget Θ =
      some outer)
    (innerRead : ContextualDependentWorklist.newestOf facts roots heads algebra declared choices reducer budget
      outer.base = some inner)
    (searched : ∀ larger, budget ≤ larger →
      pruneSearch rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique larger (twoNewestStore outer inner problem).2.1 (twoNewestStore outer inner problem).2.2.1
          (twoNewestStore outer inner problem).2.2.2 =
        pruneSearch rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique budget (twoNewestStore outer inner problem).2.1 (twoNewestStore outer inner problem).2.2.1
          (twoNewestStore outer inner problem).2.2.2) :
    ∀ larger, budget ≤ larger →
      pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique larger problem =
        pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique budget problem := by
  intro larger enough
  unfold pruneRule
  rw [newestOf_kept facts roots heads algebra declared choices reducer stable outerRead larger enough, outerRead]
  dsimp only
  rw [newestOf_kept facts roots heads algebra declared choices reducer stable innerRead larger enough, innerRead]
  dsimp only
  exact throughTwo_congr outer inner problem _ _ (searched larger enough)

end Prune

/-! ## The pattern rule, kept where it fails without the budget -/

section Pattern

/-- Recovery fails at every budget when the other side does not invert into the pattern's scope. -/
theorem recover_of_inversion_fails (fuel : Nat) {Γ Δ : Context S.R}
    (inclusion : ContextualDependentTypedInversion.Inclusion Γ Δ) (type : TypeOver Γ) (target : Tm Head Δ.arity)
    (inverted : ContextualDependentInversion.invert (ContextualDependentInversion.lookup inclusion.forward) target =
      none) :
    ContextualDependentTypedInversion.recover facts roots heads algebra declared choices reducer fuel inclusion type
      target = none := by
  unfold ContextualDependentTypedInversion.recover
  split
  · rfl
  · rename_i body computed
    rw [inverted] at computed
    cases computed

/-- **The pattern rule on one reading needs no more budget**: its occurrence is not an
application, or its spine is discovered and the occurrence is not a pattern, or the pattern's
recovery finished, or its other side does not invert into the pattern's scope. -/
def activeFirm (budget : Nat) {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) : Bool :=
  match readApplication active.left.code with
  | none => true
  | some (_, arguments) =>
      match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer budget
          arguments.length type with
      | none => false
      | some spine =>
          match recognize spine scope active with
          | none => true
          | some found =>
              (ContextualDependentTypedInversion.recover facts roots heads algebra declared choices reducer budget
                found.pattern.bodyInclusion spine.result found.right.code).isSome ||
              (ContextualDependentInversion.invert
                (ContextualDependentInversion.lookup found.pattern.bodyInclusion.forward) found.right.code).isNone

/-- **The scoped reading of an equation needs no more budget**: its comparison, spine discovery and
both normalizations finished. -/
def readingFirm (budget : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Bool :=
  match ContextualDependentEta.Conversion.compareTypes facts roots heads algebra reducer budget equation.2.1
      equation.1.1 with
  | none => false
  | some same =>
      match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer budget
          (lamDepth equation.1.2.code) equation.1.1 with
      | none => false
      | some scope =>
          (ContextualDependentNormalization.reduceTerm root facts roots heads budget
            ⟨scope.result, scope.openFunction equation.1.2⟩).isSome &&
          (ContextualDependentNormalization.reduceTerm root facts roots heads budget
            ⟨scope.result, scope.openFunction (equation.2.2.convertType equation.1.1 same.down)⟩).isSome

/-- **The pattern search on a one-equation store needs no more budget**: its reading and both
orientations need no more budget. -/
def searchFirm (budget : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    EquationStore (TotalTerm (extend Γ type)) → Bool
  | [equation] =>
      readingFirm facts roots heads algebra declared choices reducer root budget equation &&
      match viewEquation facts roots heads algebra declared choices reducer root budget equation with
      | none => false
      | some reading =>
          activeFirm facts roots heads algebra declared choices reducer budget type reading.1 reading.2.1 &&
          activeFirm facts roots heads algebra declared choices reducer budget type reading.1
            ⟨reading.2.1.type, reading.2.1.right, reading.2.1.left⟩
  | _ => false

/-- **The prune rule's final pattern search needs no more budget**: the prune rule's steps, followed
by `searchFirm` on the store it hands to its final pattern search. -/
def pruneFirm (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    (spine : Spine newer) (recognized : Recognized spine scope active) : Bool := by
  haveI := localDecidableEq scope
  haveI := localDecidableEq spine
  exact
  match readApplication recognized.right.code with
  | none => false
  | some (_, arguments) =>
    match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel
        arguments.length ((older.reindex (projectionHom Γ₀ older)).reindex (projectionHom (extend Γ₀ older) newer)) with
    | none => false
    | some olderSpine =>
      match arguments.mapM (localOf scope) with
      | none => false
      | some values =>
        match assigned : assign olderSpine values with
        | none => false
        | some olderArgs =>
          if distinct : values.Nodup then
          if olderCompatible : CtxRen olderSpine.target.raw scope.target.raw (argRen olderSpine scope idRen olderArgs) then
            let app : Application scope :=
              ⟨_, (newest Γ₀ older).reindex (projectionHom (extend Γ₀ older) newer), olderSpine, olderArgs,
                assign_injective olderSpine values olderArgs assigned distinct, olderCompatible⟩
            if sameType : (app.spine.result.reindex app.map.hom).code =
                ((lifted spine).result.reindex recognized.pattern.map.hom).code ∧
                (app.spine.result.reindex app.map.hom).level =
                ((lifted spine).result.reindex recognized.pattern.map.hom).level then
              if rightSame : recognized.right.code = app.term.code then
                let image := (locals olderSpine).map olderArgs
                let mask := (locals spine).map fun position => decide (recognized.pattern.args position ∈ image)
                let keepList := (locals spine).filter fun position => decide (recognized.pattern.args position ∈ image)
                match dropPis mask (withoutNewest Γ₀.arity) newer.code with
                | none => false
                | some keptCode =>
                  match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
                      Γ₀ keptCode with
                  | none => false
                  | some next =>
                    match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices
                        reducer fuel keepList.length (ContextualDependentParameterExchange.second older next.val) with
                    | none => false
                    | some kept =>
                      match keptAssigned : assign kept keepList with
                      | none => false
                      | some keep =>
                        if keptDistinct : keepList.Nodup then
                        if keptCompatible : CtxRen kept.target.raw spine.target.raw (argRen kept spine idRen keep) then
                        if keptResult : spine.result.code = Presentation.rename (argRen kept spine idRen keep) kept.result.code ∧
                            spine.result.level = kept.result.level then
                          let restriction : Restriction spine kept :=
                            ⟨keep, assign_injective kept keepList keep keptAssigned keptDistinct, keptCompatible,
                              keptResult.1, keptResult.2⟩
                          if covering : ∀ position ∈ locals spine,
                              (∃ other ∈ locals olderSpine, olderArgs other = recognized.pattern.args position) →
                                ∃ chosen ∈ locals kept, keep chosen = position then
                            let pruned := pruneFlexFlex rigid complete normalizes facts algebra headTypingUnique roots heads
                              declared recognized.pattern app (TypeOver.ext sameType.1 sameType.2) restriction
                              (fun position found => by
                                obtain ⟨other, same⟩ := found
                                obtain ⟨chosen, _, hit⟩ := covering position (mem_locals spine position)
                                  ⟨other, mem_locals olderSpine other, same⟩
                                exact ⟨chosen, hit⟩)
                              (equation :: rest)
                              (fun solution solved => by
                                have held := (recognized.holds_iff solution).mp ((view solution).mp
                                  (fun other member => by
                                    obtain rfl := List.mem_singleton.mp member
                                    exact solved _ List.mem_cons_self))
                                have same : recognized.right = app.term.cast (TypeOver.ext sameType.1 sameType.2) :=
                                  Term.ext (by rw [Term.cast_code]; exact rightSame)
                                rw [same] at held
                                exact held)
                            let exchanged := ContextualDependentPrune.exchange S.levels older next.val pruned.remaining
                            searchFirm facts roots heads algebra declared choices reducer root fuel
                              (ContextualDependentParameterExchange.second next.val older) exchanged.remaining
                          else false
                        else false
                        else false
                        else false
              else false
            else false
          else false
          else false

include stable

/-- **The pattern rule on one reading is kept** when its occurrence is recognized as a pattern but the
other side does not invert into the pattern's scope. -/
theorem tryActive_kept_of_inversion_fails {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) {budget : Nat} {headIndex : Fin scope.target.arity}
    {arguments : List (Fin scope.target.arity)} (read : readApplication active.left.code = some (headIndex, arguments))
    {spine : Spine type}
    (discovered : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer budget
      arguments.length type = some spine)
    {found : Recognized spine scope active} (recognized : recognize spine scope active = some found)
    (inverted : ContextualDependentInversion.invert
      (ContextualDependentInversion.lookup found.pattern.bodyInclusion.forward) found.right.code = none) :
    ∀ larger, budget ≤ larger →
      tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal larger type
          scope active equation view rest =
        tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal budget type
          scope active equation view rest := by
  intro larger enough
  unfold tryActive
  rw [read]
  dsimp only
  erw [discover_mono facts roots heads algebra declared choices reducer stable _ type discovered enough, discovered]
  dsimp only
  rw [recognized]
  dsimp only
  unfold Pattern.step
  rw [recover_of_inversion_fails facts roots heads algebra declared choices reducer larger _ _ _ inverted,
    recover_of_inversion_fails facts roots heads algebra declared choices reducer budget _ _ _ inverted]

/-- **The pattern rule on one reading is kept** when its spine is discovered and its occurrence is
not recognized as a pattern. -/
theorem tryActive_kept_of_unrecognized {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) {budget : Nat} {headIndex : Fin scope.target.arity}
    {arguments : List (Fin scope.target.arity)} (read : readApplication active.left.code = some (headIndex, arguments))
    {spine : Spine type}
    (discovered : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer budget
      arguments.length type = some spine)
    (unrecognized : recognize spine scope active = none) :
    ∀ larger, budget ≤ larger →
      tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal larger type
          scope active equation view rest =
        tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal budget type
          scope active equation view rest := by
  intro larger enough
  unfold tryActive
  rw [read]
  dsimp only
  erw [discover_mono facts roots heads algebra declared choices reducer stable _ type discovered enough, discovered]
  dsimp only
  rw [unrecognized]

omit stable in
/-- **The pattern rule on one equation is kept** once its reading and both orientations are kept. -/
theorem tryEquation_kept_of {Γ : Context S.R} (type : TypeOver Γ) (equation : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) {budget : Nat}
    {reading : (scope : Spine equation.1.1) × (active : Active scope.target) ×'
      ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
        (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution}
    (viewed : viewEquation facts roots heads algebra declared choices reducer root budget equation = some reading)
    (viewKept : ∀ larger, budget ≤ larger →
      viewEquation facts roots heads algebra declared choices reducer root larger equation =
        viewEquation facts roots heads algebra declared choices reducer root budget equation)
    (firstKept : ∀ larger, budget ≤ larger →
      tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal larger type
          reading.1 reading.2.1 equation reading.2.2 rest =
        tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal budget type
          reading.1 reading.2.1 equation reading.2.2 rest)
    (secondKept : ∀ larger, budget ≤ larger →
      tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal larger type
          reading.1 ⟨reading.2.1.type, reading.2.1.right, reading.2.1.left⟩ equation
          (fun solution => (reading.2.2 solution).trans (toScoped_swap reading.1 reading.2.1 solution).symm) rest =
        tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal budget type
          reading.1 ⟨reading.2.1.type, reading.2.1.right, reading.2.1.left⟩ equation
          (fun solution => (reading.2.2 solution).trans (toScoped_swap reading.1 reading.2.1 solution).symm) rest) :
    ∀ larger, budget ≤ larger →
      tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
          type equation rest =
        tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal budget
          type equation rest := by
  intro larger enough
  unfold tryEquation
  rw [viewKept larger enough, viewed]
  dsimp only
  erw [firstKept larger enough, secondKept larger enough]

omit stable in
/-- The search through a one-equation store is kept once its equation is. -/
theorem searchStore_singleton_kept_of {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type))) {budget : Nat}
    (kept : ∀ larger, budget ≤ larger →
      tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
          type equation [] =
        tryEquation rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal budget
          type equation []) :
    ∀ larger, budget ≤ larger →
      searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
          type [equation] =
        searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal budget
          type [equation] := by
  intro larger enough
  simp only [searchStore]
  rw [kept larger enough]

/-- **The pattern rule is kept** once its newest declaration is read and its search is kept. -/
theorem patternRule_kept_of {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) {budget : Nat}
    {view : Newest Θ}
    (read : ContextualDependentWorklist.newestOf facts roots heads algebra declared choices reducer budget Θ = some view)
    (searched : ∀ larger, budget ≤ larger →
      searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
          view.type (view.same ▸ problem) =
        searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal budget
          view.type (view.same ▸ problem)) :
    ∀ larger, budget ≤ larger →
      patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
          problem =
        patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal budget
          problem := by
  intro larger enough
  unfold patternRule
  rw [newestOf_kept facts roots heads algebra declared choices reducer stable read larger enough, read]
  dsimp only
  apply throughNewest_eq
  rw [searched larger enough]

/-- **A reading that needs no more budget is kept.** -/
theorem readingFirm_kept {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) {budget : Nat}
    (firm : readingFirm facts roots heads algebra declared choices reducer root budget equation = true) :
    ∀ larger, budget ≤ larger →
      viewEquation facts roots heads algebra declared choices reducer root larger equation =
        viewEquation facts roots heads algebra declared choices reducer root budget equation := by
  unfold readingFirm at firm
  split at firm
  · cases firm
  · rename_i same compared
    split at firm
    · cases firm
    · rename_i scope discovered
      simp only [Bool.and_eq_true] at firm
      exact viewEquation_kept facts roots heads algebra declared choices reducer root stable equation same compared
        discovered firm.1 firm.2

/-- **The pattern rule on a reading that needs no more budget is kept.** -/
theorem activeFirm_kept {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) {budget : Nat}
    (firm : activeFirm facts roots heads algebra declared choices reducer budget type scope active = true) :
    ∀ larger, budget ≤ larger →
      tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal larger type
          scope active equation view rest =
        tryActive rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal budget type
          scope active equation view rest := by
  unfold activeFirm at firm
  split at firm
  · rename_i unread
    intro larger _
    unfold tryActive
    rw [unread]
  · rename_i headIndex arguments read
    split at firm
    · cases firm
    · rename_i spine discovered
      split at firm
      · rename_i unrecognized
        exact tryActive_kept_of_unrecognized rigid facts complete roots heads algebra declared choices reducer
          normalizes certifyNormal stable type scope active equation view rest read discovered unrecognized
      · rename_i found recognized
        simp only [Bool.or_eq_true] at firm
        rcases firm with recovered | inverted
        · obtain ⟨recovery, computed⟩ := Option.isSome_iff_exists.mp recovered
          exact tryActive_kept rigid facts complete roots heads algebra declared choices reducer normalizes
            certifyNormal stable type scope active equation view rest read discovered recognized computed
        · exact tryActive_kept_of_inversion_fails rigid facts complete roots heads algebra declared choices reducer
            normalizes certifyNormal stable type scope active equation view rest read discovered recognized
            (Option.isNone_iff_eq_none.mp inverted)

/-- **The pattern search on a store that needs no more budget is kept.** -/
theorem searchFirm_kept {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ (problem : EquationStore (TotalTerm (extend Γ type))) {budget : Nat},
      searchFirm facts roots heads algebra declared choices reducer root budget type problem = true →
      ∀ larger, budget ≤ larger →
        searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            larger type problem =
          searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            budget type problem
  | [], _, firm => by simp [searchFirm] at firm
  | [equation], budget, firm => by
      simp only [searchFirm, Bool.and_eq_true] at firm
      obtain ⟨readingSettles, orientations⟩ := firm
      have viewKept := readingFirm_kept facts roots heads algebra declared choices reducer root stable equation
        readingSettles
      cases viewed : viewEquation facts roots heads algebra declared choices reducer root budget equation with
      | none => rw [viewed] at orientations; cases orientations
      | some reading =>
          rw [viewed] at orientations
          simp only [Bool.and_eq_true] at orientations
          apply searchStore_singleton_kept_of rigid facts complete roots heads algebra declared choices reducer root
            normalizes certifyNormal type equation
          exact tryEquation_kept_of rigid facts complete roots heads algebra declared choices reducer root normalizes
            certifyNormal type equation [] viewed viewKept
            (activeFirm_kept rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal
              stable type reading.1 reading.2.1 equation reading.2.2 [] orientations.1)
            (activeFirm_kept rigid facts complete roots heads algebra declared choices reducer normalizes certifyNormal
              stable type reading.1 ⟨reading.2.1.type, reading.2.1.right, reading.2.1.left⟩ equation
              (fun solution => (reading.2.2 solution).trans (toScoped_swap reading.1 reading.2.1 solution).symm) []
              orientations.2)
  | _ :: _ :: _, _, firm => by simp [searchFirm] at firm

/-- **The pattern search on a pruned and exchanged store that needs no more budget is kept**, stated
on the store exactly as the prune rule builds it. -/
theorem searchFirm_pruned_kept {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} {scope : Spine scopeType} {spine : Spine newer}
    (pattern : Pattern spine scope) (app : Application scope)
    (sameType : app.spine.result.reindex app.map.hom = (lifted spine).result.reindex pattern.map.hom)
    (next : TypeOver Γ₀) {kept : Spine (ContextualDependentParameterExchange.second older next)}
    (restriction : Restriction spine kept)
    (covers : ∀ position : spine.Local, (∃ other, app.args other = pattern.args position) →
      ∃ chosen, restriction.keep chosen = position)
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    (contains : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution problem → (pattern.constraint ((app.term).cast sameType)).Holds solution)
    {budget : Nat}
    (firm : searchFirm facts roots heads algebra declared choices reducer root budget
      (ContextualDependentParameterExchange.second next older)
      (exchange S.levels older next (pruneFlexFlex rigid complete normalizes facts algebra headTypingUnique roots heads
        declared pattern app sameType restriction covers problem contains).remaining).remaining = true) :
    ∀ larger, budget ≤ larger →
      searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          larger (ContextualDependentParameterExchange.second next older)
          (exchange S.levels older next (pruneFlexFlex rigid complete normalizes facts algebra headTypingUnique roots
            heads declared pattern app sameType restriction covers problem contains).remaining).remaining =
        searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          budget (ContextualDependentParameterExchange.second next older)
          (exchange S.levels older next (pruneFlexFlex rigid complete normalizes facts algebra headTypingUnique roots
            heads declared pattern app sameType restriction covers problem contains).remaining).remaining :=
  searchFirm_kept rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal stable
    _ _ firm

end Pattern

omit stable in
/-- **The first rule that fires is the prune rule's answer, kept**, once the pattern rule is kept
and fails and the prune rule is kept and fires. -/
theorem firstRule_kept_of_prune {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) {budget : Nat}
    (patternKept : ∀ larger, budget ≤ larger →
      patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal larger
          problem =
        patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal budget
          problem)
    (patternFails : patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal budget problem = none)
    (pruneKept : ∀ larger, budget ≤ larger →
      pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique larger problem =
        pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique budget problem)
    {found : Found problem}
    (pruneFires : pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique budget problem = some found) :
    ∀ larger, budget ≤ larger →
      firstRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique larger problem = some found := by
  intro larger enough
  unfold firstRule
  rw [patternKept larger enough, patternFails]
  dsimp only
  rw [pruneKept larger enough, pruneFires]

end ContextualDependentDecisiveFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
