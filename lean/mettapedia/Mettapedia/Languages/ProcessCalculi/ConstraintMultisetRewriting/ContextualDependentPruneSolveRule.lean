import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneSolve
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionRound

/-!
# The prune-and-solve rule under rigid binder contexts

For a store equation read as `F x̄ ≐ t` (or a swap), with `t` a rigid binder context around `G ȳ` (along domains and
codomains of dependent function and pair types), `G` the newest and `F` the next older metavariable, the pattern rule
for `F` is pending when some `y` is not among `x̄`. The **prune-and-solve rule** (`tryCodomain`, `tryContext`):

1. finds an application in `t` along the binder types, strengthened past the binders it passes (`binderPath`), and
   recognizes it as a pattern of `G`;
2. reads `F x̄` on the other side through `F`'s own discovered spine;
3. keeps exactly the binders of `G` whose argument occurs among `x̄`, deletes the others and every reference to `F`
   from `G`'s type, and checks the result with the type former; the restriction's conditions are decided;
4. prunes `G := λ ȳ. H (ȳ restricted)` (`pruneBinderContext`), which loses no solution;
5. exchanges `F` and `H` and runs R76's pattern search for `F`, now the newest.

As in R76's prune rule, it progresses only when the last step solves `F`, so it removes a declaration: the progress
lowers the first component of the weight rank. When `F` is the newest declaration and `G` the next older, the two are
exchanged first (`exchangeSolve`), an isomorphism of contexts.

The **prune-and-solve round** is the intersection round, and when that round is stuck, the rule (`pruneSolveRound`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPruneSolve

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentEta
open ContextualDependentUpdate ContextualDependentScope ContextualDependentPrune ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentFlexReorder
open ContextualDependentIntersection
open ContextualDependentParameterExchange (second)

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

/-! ## Finding the pattern in a rigid binder context -/

omit [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq] [DecidableRel S.R.cumulative] in
/-- One binder step of the search: a candidate in the domain, or one in the codomain read back past the binder. -/
def binderStep {m : Nat} (isPi : Bool) (A : Tm Head m) (B : Tm Head (m + 1))
    (inDomain : Option {P : Tm Head m // BinderContext P A})
    (inCodomain : Option {P : Tm Head (m + 1) // BinderContext P B}) :
    Option {P : Tm Head m // BinderContext P (ContextualDependentRigidFormers.binder isPi A B)} :=
  match inDomain with
  | some found => some ⟨found.val, .domain isPi B found.property⟩
  | none =>
      match inCodomain with
      | none => none
      | some found =>
          match ContextualDependentInversion.invert (withoutNewest m) found.val with
          | none => none
          | some P =>
              if same : found.val = Presentation.rename wk P then
                some ⟨P, .codomain isPi A (same ▸ found.property)⟩
              else none

omit [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq] [DecidableRel S.R.cumulative] in
/-- **A pattern candidate in a rigid binder context**: an application, or a candidate found in the domain or the
codomain of a dependent function or pair type. -/
def binderPath : {m : Nat} → (t : Tm Head m) → Option {P : Tm Head m // BinderContext P t}
  | _, .app f a => some ⟨.app f a, .here _⟩
  | _, .pi A B => binderStep true A B (binderPath A) (binderPath B)
  | _, .sigma A B => binderStep false A B (binderPath A) (binderPath B)
  | _, .var _ | _, .const _ | _, .head _ | _, .id _ _ _ | _, .lam _ | _, .pair _ _ | _, .fst _ | _, .snd _
  | _, .refl _ => none

/-! ## The rule on one scoped reading -/

/-- **Prune `G` under a rigid binder context and solve `F`**, for the annotation a universe. -/
def tryContext (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) {u : Head}
    (hu : S.R.isUniverse u) (annotation : active.type.code = .head u) :
    Option (Found (equation :: rest)) := by
  haveI := localDecidableEq scope
  exact
      match binderPath active.right.code with
      | none => none
      | some ⟨inner, context⟩ =>
        match readApplication inner with
        | none => none
        | some (_, gArgs) =>
          match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel
              gArgs.length newer with
          | none => none
          | some spine =>
            letI := localDecidableEq spine
            match gArgs.mapM (localOf scope) with
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
                  if innerSame : inner = pattern.application.code then
                  match gUniverse : ((lifted spine).result.reindex pattern.map.hom).code with
                  | .head v =>
                    if hv : S.R.isUniverse v then
                    match readApplication active.left.code with
                    | none => none
                    | some (_, fArgs) =>
                      match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices
                          reducer fuel fArgs.length
                          ((older.reindex (projectionHom Γ₀ older)).reindex (projectionHom (extend Γ₀ older) newer)) with
                      | none => none
                      | some olderSpine =>
                        match fArgs.mapM (localOf scope) with
                        | none => none
                        | some fValues =>
                          match fAssigned : assign olderSpine fValues with
                          | none => none
                          | some olderArgs =>
                            if fDistinct : fValues.Nodup then
                            if olderCompatible : CtxRen olderSpine.target.raw scope.target.raw
                                (argRen olderSpine scope idRen olderArgs) then
                              let app : Application scope :=
                                ⟨_, (newest Γ₀ older).reindex (projectionHom (extend Γ₀ older) newer), olderSpine,
                                  olderArgs, assign_injective olderSpine fValues olderArgs fAssigned fDistinct,
                                  olderCompatible⟩
                              if leftType : (app.spine.result.reindex app.map.hom).code = active.type.code then
                              if leftSame : active.left.code = app.term.code then
                                let image := (locals olderSpine).map olderArgs
                                let mask := (locals spine).map fun position => decide (pattern.args position ∈ image)
                                let keepList := (locals spine).filter fun position =>
                                  decide (pattern.args position ∈ image)
                                match dropPis mask (withoutNewest Γ₀.arity) newer.code with
                                | none => none
                                | some keptCode =>
                                  match ContextualDependentPruning.formType facts roots heads algebra declared choices
                                      reducer fuel Γ₀ keptCode with
                                  | none => none
                                  | some next =>
                                    match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared
                                        choices reducer fuel keepList.length (second older next.val) with
                                    | none => none
                                    | some kept =>
                                      match keptAssigned : assign kept keepList with
                                      | none => none
                                      | some keep =>
                                        if keptDistinct : keepList.Nodup then
                                        if keptCompatible : CtxRen kept.target.raw spine.target.raw
                                            (argRen kept spine idRen keep) then
                                        if keptResult : spine.result.code =
                                            Presentation.rename (argRen kept spine idRen keep) kept.result.code ∧
                                            spine.result.level = kept.result.level then
                                          let restriction : Restriction spine kept :=
                                            ⟨keep, assign_injective kept keepList keep keptAssigned keptDistinct,
                                              keptCompatible, keptResult.1, keptResult.2⟩
                                          if covering : ∀ position ∈ locals spine,
                                              (∃ other ∈ locals olderSpine, olderArgs other = pattern.args position) →
                                                ∃ chosen ∈ locals kept, keep chosen = position then
                                            let pruned := pruneBinderContext rigid complete normalizes facts algebra
                                              headTypingUnique roots heads declared pattern app active hu hv leftSame
                                              (innerSame ▸ context) annotation leftType gUniverse
                                              restriction
                                              (fun position found => by
                                                obtain ⟨other, same⟩ := found
                                                obtain ⟨chosen, _, hit⟩ := covering position (mem_locals spine position)
                                                  ⟨other, mem_locals olderSpine other, same⟩
                                                exact ⟨chosen, hit⟩)
                                              (equation :: rest)
                                              (fun solution solved => (view solution).mp
                                                (fun other member => by
                                                  obtain rfl := List.mem_singleton.mp member
                                                  exact solved _ List.mem_cons_self))
                                            let exchanged := ContextualDependentPrune.exchange S.levels older next.val
                                              pruned.remaining
                                            match searchStore rigid facts complete roots heads algebra declared choices
                                                reducer root normalizes certifyNormal fuel (second next.val older)
                                                exchanged.remaining with
                                            | none => none
                                            | some (.solved solved smaller) =>
                                                some (.solved ((pruned.then exchanged).then solved) smaller)
                                            | some (.refuted absent) =>
                                                some (.refuted fun solvable =>
                                                  absent ((pruned.then exchanged).solvable_iff.mp solvable))
                                          else none
                                        else none
                                        else none
                                        else none
                              else none
                              else none
                            else none
                            else none
                    else none
                  | _ => none
                  else none
                else none
                else none

/-- **Prune `G` under a rigid binder context and solve `F`**: the annotation a universe. -/
def tryCodomain (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) : Option (Found (equation :: rest)) :=
  match annotation : active.type.code with
  | .head u =>
      if hu : S.R.isUniverse u then
        tryContext facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
          headTypingUnique fuel older newer scope active equation view rest hu annotation
      else none
  | _ => none

/-- The rule on one store equation, in both orientations. -/
def codomainEquation (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) : Option (Found (equation :: rest)) :=
  match viewEquation facts roots heads algebra declared choices reducer root fuel equation with
  | none => none
  | some ⟨scope, active, view⟩ =>
      match tryCodomain facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique fuel older newer scope active equation view rest with
      | some found => some found
      | none =>
          tryCodomain facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
            headTypingUnique fuel older newer scope ⟨active.type, active.right, active.left⟩ equation
            (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest

/-- The rule through the store. -/
def codomainSearch (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)) :
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match codomainEquation facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique fuel older newer equation rest with
      | some found => some found
      | none => (codomainSearch fuel older newer rest).map (Found.keepLeft equation)

/-- **The rule at the two newest declarations**: `G` the newest, `F` the next older. -/
def codomainRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  match newestOf facts roots heads algebra declared choices reducer fuel Θ with
  | none => none
  | some outer =>
      match newestOf facts roots heads algebra declared choices reducer fuel outer.base with
      | none => none
      | some inner => throughTwo outer inner problem fun older newer stored =>
          codomainSearch facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique fuel older newer stored

/-! ## Exchanging first -/

/-- **Exchange the two newest declarations, then solve.** When the newest does not depend on the one below it, the
two are exchanged and `solve` runs on the exchanged store; its outcome is composed with the exchange. -/
def exchangeSolve (fuel : Nat)
    (solve : {Γ : Context S.R} → (stored : EquationStore (TotalTerm Γ)) → Option (Found stored))
    {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) : Option (Found problem) := by
  exact
  match ContextualDependentInversion.invert (withoutNewest Γ₀.arity) newer.code with
  | none => none
  | some code =>
      match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ₀ code with
      | none => none
      | some next =>
          if same : newer.code = (second older next.val).code ∧ newer.level = (second older next.val).level then by
            have independent : newer = second older next.val := TypeOver.ext same.1 same.2
            subst independent
            exact afterExchange (ContextualDependentPrune.exchange S.levels older next.val problem) rfl
              (solve (ContextualDependentPrune.exchange S.levels older next.val problem).remaining)
          else none

/-- The rule after exchanging the two newest declarations. -/
def exchangedRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  match newestOf facts roots heads algebra declared choices reducer fuel Θ with
  | none => none
  | some outer =>
      match newestOf facts roots heads algebra declared choices reducer fuel outer.base with
      | none => none
      | some inner => throughTwo outer inner problem fun older newer stored =>
          exchangeSolve facts roots heads algebra declared choices reducer fuel
            (fun exchanged => codomainRule facts roots heads algebra rigid complete declared choices reducer root
              normalizes certifyNormal headTypingUnique fuel exchanged) older newer stored

/-- **The prune-and-solve rule**: at the two newest declarations as they are, and after exchanging them. -/
def pruneSolveRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  match codomainRule facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel problem with
  | some found => some found
  | none => exchangedRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem

/-! ## The round -/

/-- **One prune-and-solve round**: the intersection round; when it is stuck, the prune-and-solve rule. -/
def pruneSolveRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match intersectRound facts roots heads algebra rigid complete declared choices reducer root normalizes certifyNormal
      headTypingUnique rootComplete fuel problem with
  | .stuck =>
      match pruneSolveRule facts roots heads algebra rigid complete declared choices reducer root normalizes
          certifyNormal headTypingUnique fuel problem with
      | some (.solved update smaller) => .progress update (below_of_arity facts roots heads algebra rigid complete smaller)
      | some (.refuted absent) => .refuted absent
      | none => .stuck
  | other => other

/-- **The prune-and-solve family**, at the weight rank. -/
noncomputable def pruneSolveFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := pruneSolveRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

end ContextualDependentPruneSolve
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
