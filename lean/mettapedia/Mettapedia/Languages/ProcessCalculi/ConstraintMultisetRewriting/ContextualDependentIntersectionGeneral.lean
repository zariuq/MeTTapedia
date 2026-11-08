import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentWeightPrune
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeRound

/-!
# General intersection: `λ x̄. G ȳ ≐ λ x̄. G z̄` with other equations mentioning `G`

R110's intersection rule (`ContextualDependentIntersection.tryIntersect`) prunes the newest metavariable `G` to the
binders at which `ȳ` and `z̄` agree and drops the instantiated equation. It fired only when no other equation mentions
`G`, because its rank decrease read the other equations as weakenings.

The η-long weight bound under pruning (`ContextualDependentWeightPrune.storeWeight_prune_drop`) removes that condition:
the pruning answer, applied to the whole store, does not raise the normal weight of any equation, and the dropped
equation weighs at least one. So the same update, on any store, is a progress of the weight rank
(`generalIntersect`). It is exact (R110's `pruneIntersection` through `forced_intersection`, then a certified drop),
lowers the rank, and is eventually constant (`ContextualDependentIntersectionGeneralRound`).

The **general round** is the cumulative round, and when that round is stuck, the general intersection rule at the
newest declaration on the first equation (`generalRound`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentIntersectionGeneral

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope
open ContextualDependentPrune ContextualDependentPiSpine.Transport
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentEtaLong ContextualDependentConversionBudget
open ContextualDependentFlexReorder ContextualDependentIntersection ContextualDependentCumulative

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

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- **Pruning to the intersection, then dropping the instantiated equation, lowers the weight rank**, whatever the
other equations are. -/
theorem prune_drop_below {Γ₀ : Context S.R} {newer keptType : TypeOver Γ₀} {spine : Spine newer}
    {kept : Spine keptType} (restriction : Restriction spine kept) (equation : Equation (TotalTerm (extend Γ₀ newer)))
    (rest : EquationStore (TotalTerm (extend Γ₀ newer))) :
    ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete
        ((frames S.levels).applyStore restriction.answer rest))
      (weightRank facts roots heads algebra rigid complete (equation :: rest)) := by
  unfold weightRank ContextualDependentWorklist.Below
  exact Prod.Lex.right _ (ContextualDependentWeightPrune.storeWeight_prune_drop facts roots heads algebra rigid
    complete restriction equation rest)

/-- **General intersection on one recognized pattern** `G ȳ` against `G z̄` on the right: prune `G` to the agreeing
binders in the whole store, and drop the instantiated equation. -/
def generalIntersect (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    {scopeType : TypeOver (extend Γ₀ newer)} (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend Γ₀ newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ₀ newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ₀ newer)))
    (spine : Spine newer) (recognized : Recognized spine scope active) :
    Option (Progress facts roots heads algebra rigid complete (equation :: rest)) := by
  haveI := localDecidableEq scope
  haveI := localDecidableEq spine
  exact
  match readApplication recognized.right.code with
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
          let second : Pattern spine scope := ⟨args, assign_injective spine values args assigned distinct, compatible⟩
          if sameType : ((lifted spine).result.reindex second.map.hom).code =
              ((lifted spine).result.reindex recognized.pattern.map.hom).code ∧
              ((lifted spine).result.reindex second.map.hom).level =
              ((lifted spine).result.reindex recognized.pattern.map.hom).level then
          if rightSame : recognized.right.code = second.application.code then
            let mask := (locals spine).map fun position => decide (second.args position = recognized.pattern.args position)
            let keepList := (locals spine).filter fun position =>
              decide (second.args position = recognized.pattern.args position)
            match dropPis mask (fun index => some index) newer.code with
            | none => none
            | some keptCode =>
              match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ₀
                  keptCode with
              | none => none
              | some next =>
                match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer
                    fuel keepList.length next.val with
                | none => none
                | some kept =>
                  match keptAssigned : assign kept keepList with
                  | none => none
                  | some keep =>
                    if keptDistinct : keepList.Nodup then
                    if keptCompatible : CtxRen kept.target.raw spine.target.raw (argRen kept spine idRen keep) then
                    if keptResult : spine.result.code = Presentation.rename (argRen kept spine idRen keep) kept.result.code ∧
                        spine.result.level = kept.result.level then
                      let restriction : Restriction spine kept :=
                        ⟨keep, assign_injective kept keepList keep keptAssigned keptDistinct, keptCompatible,
                          keptResult.1, keptResult.2⟩
                      if covering : ∀ position ∈ locals spine,
                          second.args position = recognized.pattern.args position →
                            ∃ chosen ∈ locals kept, keep chosen = position then
                        let pruned := pruneIntersection rigid complete normalizes facts algebra headTypingUnique roots
                          heads declared recognized.pattern second (TypeOver.ext sameType.1 sameType.2) restriction
                          (fun position same => by
                            obtain ⟨chosen, _, hit⟩ := covering (spine.localReindexEquiv _ position)
                              (mem_locals spine _) same
                            exact ⟨chosen, hit⟩)
                          (equation :: rest)
                          (fun solution solved => by
                            have held := (recognized.holds_iff solution).mp ((view solution).mp
                              (fun other member => by
                                obtain rfl := List.mem_singleton.mp member
                                exact solved _ List.mem_cons_self))
                            have same : recognized.right = second.application.cast (TypeOver.ext sameType.1 sameType.2) :=
                              Term.ext (by rw [Term.cast_code]; exact rightSame)
                            rw [same] at held
                            exact held)
                        match Conversion.compare facts roots heads algebra reducer fuel
                            (equation.1.reindex restriction.answer) (equation.2.reindex restriction.answer) with
                        | none => none
                        | some certificate =>
                            some ⟨pruned.then (dropValid (equation.1.reindex restriction.answer,
                                equation.2.reindex restriction.answer)
                                ((frames S.levels).applyStore restriction.answer rest) certificate.down),
                              prune_drop_below facts roots heads algebra rigid complete restriction equation rest⟩
                      else none
                    else none
                    else none
                    else none
          else none
          else none
        else none
        else none

/-- **General intersection on one store equation**: the scoped reading, `G`'s spine and the recognized pattern on the
left; no condition on the other equations. -/
def generalIntersectEquation (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    (equation : Equation (TotalTerm (extend Γ₀ newer))) (rest : EquationStore (TotalTerm (extend Γ₀ newer))) :
    Option (Progress facts roots heads algebra rigid complete (equation :: rest)) :=
  match viewEquation facts roots heads algebra declared choices reducer root fuel equation with
  | none => none
  | some ⟨scope, active, view⟩ =>
      match readApplication active.left.code with
      | none => none
      | some (_, arguments) =>
          match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel
              arguments.length newer with
          | none => none
          | some spine =>
              match recognize spine scope active with
              | none => none
              | some recognized =>
                  generalIntersect facts roots heads algebra rigid complete declared choices reducer normalizes
                    headTypingUnique fuel newer scope active equation view rest spine recognized

/-- **The general intersection rule**: the first equation, at the newest declaration. -/
def generalIntersectRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (Progress facts roots heads algebra rigid complete problem) :=
  match newestOf facts roots heads algebra declared choices reducer fuel Θ with
  | none => none
  | some view => throughNewestProgress facts roots heads algebra rigid complete view problem fun newer stored =>
      match stored with
      | [] => none
      | equation :: rest => generalIntersectEquation facts roots heads algebra rigid complete declared choices reducer
          root normalizes headTypingUnique fuel newer equation rest

/-- **One general round**: the cumulative round; when it is stuck, the general intersection rule. -/
def generalRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match cumulativeRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          headTypingUnique fuel problem with
      | some found => .progress found.val found.property
      | none => .stuck
  | other => other

/-- **The general family**, at the weight rank. -/
noncomputable def generalFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := generalRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

end ContextualDependentIntersectionGeneral
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
