import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidFormersDeep

/-!
# Recognizing a pattern up to conversion of its annotation

`recognize` accepts `F x̄ ≐ t` only when the equation's annotation is **syntactically** the type of
the pattern application, code and universe level. An annotation that is merely equal to it, for
instance a universe written `sort (max 0 0)` where the metavariable is declared at `sort 0`, is not
recognized.

**Recognition up to conversion** reads the same pattern, and compares the annotation with the
pattern's type by the bounded type comparison (`recognizeConv`). On success the right side is retyped
along the certified type equality, and the recognized constraint has exactly the equation's
solutions (`conv_holds_iff`): typed equality at two equal types is the same relation. Only the type
comparison reads the budget, and it keeps its results, so the recognition is eventually constant
(`recognizeConv_const`).

The **conversion pattern rule** is the pattern rule with this recognition, and the **recognition
round** extends the deep round by it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRecognitionConversion

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentScope
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentPatternSolver
open ContextualDependentDecisiveFragment ContextualDependentFragment ContextualDependentInPlace
open ContextualDependentEtaExpansion ContextualDependentRigidFormers ContextualDependentConversionBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A pattern read from the left side**, before its annotation is compared. -/
structure PatternShape {Γ : Context S.R} {type : TypeOver Γ} (spine : Spine type) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) where
  pattern : Pattern spine scope
  sameLeft : active.left.code = pattern.application.code

/-- **Equal annotations give the same solutions**: the equation at its own annotation, and the pattern
constraint with the right side retyped at the pattern's type. -/
theorem conv_holds_iff {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type} {scopeType : TypeOver (extend Γ type)}
    {scope : Spine scopeType} {active : Active scope.target} (shape : PatternShape spine scope active)
    (same : TypeEq S.R scope.target.raw active.type.code ((lifted spine).result.reindex shape.pattern.map.hom).code)
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type) :
    (scope.toScoped active).Holds solution ↔
      (shape.pattern.constraint (active.right.convertType _ same)).Holds solution := by
  rw [Pattern.constraint, Spine.toScoped_holds_iff, Spine.toScoped_holds_iff]
  obtain ⟨u, hu, e⟩ := same
  have substituted : TypeEq S.R (scope.reindex solution).target.raw
      (Presentation.subst (scope.map solution).substitution active.type.code)
      (Presentation.subst (scope.map solution).substitution
        ((lifted spine).result.reindex shape.pattern.map.hom).code) :=
    ⟨u, hu, e.substitute (scope.map solution).typed⟩
  change Equal S.R (scope.reindex solution).target.raw (Presentation.subst (scope.map solution).substitution active.left.code)
      (Presentation.subst (scope.map solution).substitution active.right.code)
      (Presentation.subst (scope.map solution).substitution active.type.code) ↔
    Equal S.R (scope.reindex solution).target.raw
      (Presentation.subst (scope.map solution).substitution shape.pattern.application.code)
      (Presentation.subst (scope.map solution).substitution active.right.code)
      (Presentation.subst (scope.map solution).substitution ((lifted spine).result.reindex shape.pattern.map.hom).code)
  rw [shape.sameLeft]
  exact ⟨fun held => Equal.convType held substituted, fun held => Equal.convType held substituted.symm⟩

variable [DecidableEq Head]

/-- Read the pattern of the left side; no budget. -/
def patternShape {Γ : Context S.R} {type : TypeOver Γ} (spine : Spine type) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) : Option (PatternShape spine scope active) :=
  letI := localDecidableEq scope
  match readApplication active.left.code with
  | none => none
  | some (_, arguments) =>
      match arguments.mapM (localOf scope) with
      | none => none
      | some values =>
          match assigned : assign spine values with
          | none => none
          | some args =>
              if distinct : values.Nodup then
                if compatible : CtxRen (lifted spine).target.raw scope.target.raw
                    (argRen (lifted spine) scope idRen (fun position => args (spine.localReindexEquiv _ position))) then
                  let pattern : Pattern spine scope :=
                    ⟨args, assign_injective spine values args assigned distinct, compatible⟩
                  if sameLeft : active.left.code = pattern.application.code then some ⟨pattern, sameLeft⟩ else none
                else none
              else none

variable [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
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

/-- **Recognition up to conversion**: the pattern of the left side, with the annotation compared to the
pattern's type by the bounded type comparison. -/
def recognizeConv (fuel : Nat) {Γ : Context S.R} {type : TypeOver Γ} (spine : Spine type)
    {scopeType : TypeOver (extend Γ type)} (scope : Spine scopeType) (active : Active scope.target) :
    Option (Recognized spine scope active) :=
  (patternShape spine scope active).bind fun shape =>
    (Conversion.compareTypes facts roots heads algebra reducer fuel active.type
        ((lifted spine).result.reindex shape.pattern.map.hom)).map fun same =>
      ⟨shape.pattern, active.right.convertType _ same.down, fun solution => conv_holds_iff shape same.down solution⟩

/-- The pattern rule on one scoped reading, with recognition up to conversion. -/
def tryActiveConv (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) : Option (Found (equation :: rest)) :=
  match readApplication active.left.code with
  | none => none
  | some (_, arguments) =>
      match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel
          arguments.length type with
      | none => none
      | some spine =>
          match recognizeConv facts roots heads algebra reducer fuel spine scope active with
          | none => none
          | some recognized =>
              let reading : View equation := ⟨scope.toScoped active, view⟩
              match Pattern.step facts roots heads algebra declared
                  (ContextualDependentScopeConsequence.root_reflection rigid) complete rigid normalizes certifyNormal
                  choices reducer fuel recognized.pattern recognized.right with
              | .solved result _ =>
                  let moved : ContextualDependentScopedDispatch.Result S.levels [reading.constraint] :=
                    result.rephrase fun solution => by
                      simp only [ContextualDependentScopedDispatch.Holds, List.mem_singleton, forall_eq]
                      exact recognized.holds_iff solution
                  if smaller : (reading.combine rest moved).target.arity < (extend Γ type).arity then
                    some (.solved (reading.combine rest moved) smaller)
                  else none
              | .refuted absent =>
                  some (.refuted (reading.refutes (fun solution held =>
                    absent solution ((recognized.holds_iff solution).mp held)) rest))
              | .pending =>
                  match occursCheck rigid complete normalizes recognized.pattern recognized.right with
                  | some absent =>
                      some (.refuted (reading.refutes (fun solution held =>
                        absent.down solution ((recognized.holds_iff solution).mp held)) rest))
                  | none => none

/-- The conversion pattern rule on one store equation, in both orientations. -/
def tryEquationConv (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ)
    (equation : Equation (TotalTerm (extend Γ type))) (rest : EquationStore (TotalTerm (extend Γ type))) :
    Option (Found (equation :: rest)) :=
  match viewEquation facts roots heads algebra declared choices reducer root fuel equation with
  | none => none
  | some ⟨scope, active, view⟩ =>
      match tryActiveConv facts roots heads algebra declared choices reducer rigid complete normalizes certifyNormal
          fuel type scope active equation view rest with
      | some found => some found
      | none =>
          tryActiveConv facts roots heads algebra declared choices reducer rigid complete normalizes certifyNormal
            fuel type scope ⟨active.type, active.right, active.left⟩ equation
            (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest

/-- Search the store for an equation on which the conversion pattern rule decides. -/
def searchStoreConv (fuel : Nat) {Γ : Context S.R} (type : TypeOver Γ) :
    (problem : EquationStore (TotalTerm (extend Γ type))) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match tryEquationConv facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal fuel type equation rest with
      | some found => some found
      | none => (searchStoreConv fuel type rest).map (Found.keepLeft equation)

/-- **The conversion pattern rule** at the newest declaration. -/
def patternRuleConv (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  match newestOf facts roots heads algebra declared choices reducer fuel Θ with
  | none => none
  | some view => ContextualDependentPatternSolver.throughNewest view problem
      (searchStoreConv facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel view.type)

/-- **One recognition round**: the deep round, and when it is stuck, the conversion pattern rule on the
prepared store. -/
def recognitionRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels size problem :=
  extendRound root rootComplete facts roots heads
    (fun fuel => deepRound facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique rootComplete fuel)
    (fun fuel => patternRuleConv facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal fuel) fuel problem

/-- **The recognition family.** -/
def recognitionFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := size
  round fuel := recognitionRound facts roots heads algebra declared choices reducer rigid complete root normalizes
    certifyNormal headTypingUnique rootComplete fuel

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))
include stable

omit [DecidableRel S.R.cumulative] in
theorem recognizeConv_const {Γ : Context S.R} {type : TypeOver Γ} (spine : Spine type)
    {scopeType : TypeOver (extend Γ type)} (scope : Spine scopeType) (active : Active scope.target) :
    EventuallyConst fun fuel => recognizeConv facts roots heads algebra reducer fuel spine scope active := by
  cases shaped : patternShape spine scope active with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      simp only [recognizeConv, shaped, Option.bind_none]
  | some shape =>
      obtain ⟨threshold, same⟩ := (compareTypes_const facts roots heads algebra reducer stable active.type
        ((lifted spine).result.reindex shape.pattern.map.hom)).spec
      refine ⟨threshold, fun fuel enough => ?_⟩
      simp only [recognizeConv, shaped, Option.bind_some]
      erw [same fuel enough]

theorem tryActiveConv_const {Γ : Context S.R} (type : TypeOver Γ) {scopeType : TypeOver (extend Γ type)}
    (scope : Spine scopeType) (active : Active scope.target) (equation : Equation (TotalTerm (extend Γ type)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    EventuallyConst fun fuel =>
      tryActiveConv facts roots heads algebra declared choices reducer rigid complete normalizes certifyNormal fuel type
        scope active equation view rest := by
  cases read : readApplication active.left.code with
  | none =>
      refine ⟨0, fun fuel _ => ?_⟩
      dsimp only
      unfold tryActiveConv
      rw [read]
  | some found =>
      obtain ⟨headIndex, arguments⟩ := found
      obtain ⟨t₁, discovered⟩ := (discover_const facts roots heads algebra declared choices reducer stable
        arguments.length type).spec
      cases spineFound : ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer
          t₁ arguments.length type with
      | none =>
          refine ⟨t₁, fun fuel enough => ?_⟩
          dsimp only
          unfold tryActiveConv
          rw [read]
          dsimp only
          erw [discovered fuel enough, spineFound]
      | some spine =>
          obtain ⟨t₂, recognizedSame⟩ := (recognizeConv_const facts roots heads algebra reducer stable spine scope
            active).spec
          cases recognized : recognizeConv facts roots heads algebra reducer t₂ spine scope active with
          | none =>
              refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
              dsimp only
              unfold tryActiveConv
              rw [read]
              dsimp only
              erw [discovered fuel (le_of_max_le_left enough), spineFound, discovered _ (le_max_left _ _), spineFound]
              dsimp only
              erw [recognizedSame fuel (le_of_max_le_right enough), recognized, recognizedSame _ (le_max_right _ _),
                recognized]
          | some found =>
              obtain ⟨t₃, stepped⟩ := (step_const rigid facts complete roots heads algebra declared choices reducer
                normalizes certifyNormal stable found.pattern found.right).spec
              refine ⟨max (max t₁ t₂) t₃, fun fuel enough => ?_⟩
              have e₁ : t₁ ≤ fuel := by omega
              have e₂ : t₂ ≤ fuel := by omega
              have e₃ : t₃ ≤ fuel := by omega
              have f₁ : t₁ ≤ max (max t₁ t₂) t₃ := by omega
              have f₂ : t₂ ≤ max (max t₁ t₂) t₃ := by omega
              have f₃ : t₃ ≤ max (max t₁ t₂) t₃ := by omega
              dsimp only
              unfold tryActiveConv
              rw [read]
              dsimp only
              erw [discovered fuel e₁, spineFound, discovered _ f₁, spineFound]
              dsimp only
              erw [recognizedSame fuel e₂, recognized, recognizedSame _ f₂, recognized]
              dsimp only
              erw [stepped fuel e₃, stepped _ f₃]

theorem tryEquationConv_const {Γ : Context S.R} (type : TypeOver Γ) (equation : Equation (TotalTerm (extend Γ type)))
    (rest : EquationStore (TotalTerm (extend Γ type))) :
    EventuallyConst fun fuel =>
      tryEquationConv facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel type equation rest := by
  obtain ⟨t₁, viewed⟩ := (viewEquation_const facts roots heads algebra declared choices reducer root stable
    equation).spec
  cases reading : viewEquation facts roots heads algebra declared choices reducer root t₁ equation with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold tryEquationConv
      erw [viewed fuel enough, reading]
  | some found =>
      obtain ⟨scope, active, view⟩ := found
      obtain ⟨t₂, first⟩ := (tryActiveConv_const facts roots heads algebra declared choices reducer rigid complete
        normalizes certifyNormal stable type scope active equation view rest).spec
      obtain ⟨t₃, second⟩ := (tryActiveConv_const facts roots heads algebra declared choices reducer rigid complete
        normalizes certifyNormal stable type scope ⟨active.type, active.right, active.left⟩ equation
        (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest).spec
      refine ⟨max t₁ (max t₂ t₃), fun fuel enough => ?_⟩
      have e₁ : t₁ ≤ fuel := by omega
      have e₂ : t₂ ≤ fuel := by omega
      have e₃ : t₃ ≤ fuel := by omega
      have f₁ : t₁ ≤ max t₁ (max t₂ t₃) := by omega
      have f₂ : t₂ ≤ max t₁ (max t₂ t₃) := by omega
      have f₃ : t₃ ≤ max t₁ (max t₂ t₃) := by omega
      dsimp only
      unfold tryEquationConv
      erw [viewed fuel e₁, reading, viewed _ f₁, reading]
      dsimp only
      erw [first fuel e₂, first _ f₂, second fuel e₃, second _ f₃]

theorem searchStoreConv_const {Γ : Context S.R} (type : TypeOver Γ) :
    ∀ problem : EquationStore (TotalTerm (extend Γ type)), EventuallyConst fun fuel =>
      searchStoreConv facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel type problem
  | [] => EventuallyConst.const _
  | equation :: rest => by
      obtain ⟨t₁, first⟩ := (tryEquationConv_const facts roots heads algebra declared choices reducer rigid complete root
        normalizes certifyNormal stable type equation rest).spec
      obtain ⟨t₂, later⟩ := (searchStoreConv_const type rest).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      simp only [searchStoreConv]
      erw [first fuel (le_of_max_le_left enough), first _ (le_max_left _ _), later fuel (le_of_max_le_right enough),
        later _ (le_max_right _ _)]

/-- **The conversion pattern rule is eventually constant on every store.** -/
theorem patternRuleConv_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      patternRuleConv facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        fuel problem := by
  obtain ⟨t₁, newest⟩ := (newestOf_const facts roots heads algebra declared choices reducer stable Θ).spec
  cases found : newestOf facts roots heads algebra declared choices reducer t₁ Θ with
  | none =>
      refine ⟨t₁, fun fuel enough => ?_⟩
      dsimp only
      unfold patternRuleConv
      erw [newest fuel enough, found]
  | some view =>
      obtain ⟨t₂, searched⟩ := (ContextualDependentDecisiveFragment.throughNewest_const view problem
        (fun fuel => searchStoreConv facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal fuel view.type)
        (searchStoreConv_const facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal stable view.type)).spec
      refine ⟨max t₁ t₂, fun fuel enough => ?_⟩
      dsimp only
      unfold patternRuleConv
      erw [newest fuel (le_of_max_le_left enough), found, newest _ (le_max_left _ _), found]
      dsimp only
      exact (searched fuel (le_of_max_le_right enough)).trans (searched _ (le_max_right _ _)).symm

/-- **The recognition round is eventually constant on every store.** -/
theorem recognitionRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => recognitionRound facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal headTypingUnique rootComplete fuel problem :=
  extendRound_const root rootComplete facts roots heads _ _
    (fun problem => deepRound_const facts roots heads algebra declared choices reducer rigid complete root normalizes
      certifyNormal headTypingUnique rootComplete stable problem)
    (fun problem => patternRuleConv_const facts roots heads algebra declared choices reducer rigid complete root
      normalizes certifyNormal stable problem) problem

/-- **The recognition family settles** on every class of stores on which, at each nonempty store and
from some budget on, its round is not stuck and keeps every residual store in the class. -/
def recognitionSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        recognitionRound facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
            headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem} {smaller : Below (size update.remaining) (size problem)},
          recognitionRound facts roots heads algebra declared choices reducer rigid complete root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (recognitionFamily facts roots heads algebra declared choices reducer rigid complete root normalizes certifyNormal
        headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => recognitionRound_const facts roots heads algebra declared choices reducer rigid
    complete root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentRecognitionConversion
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
