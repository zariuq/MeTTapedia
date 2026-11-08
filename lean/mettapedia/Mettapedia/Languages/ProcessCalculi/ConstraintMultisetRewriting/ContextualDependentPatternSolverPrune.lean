import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolver

/-!
# Pruning inside the pattern solver

For a store equation read as `G ȳ ≐ F x̄`, with `G` the newest and `F` the next older
metavariable, the pattern step alone is pending when some `x` is not among `ȳ`. The prune rule:

1. recognizes `F x̄` as an application of `F` through its own discovered spine;
2. keeps exactly the binders of `G` whose argument occurs among `x̄` (the intersection);
3. computes the type of the fresh `H` by deleting the other binders and every reference to `F`
   from `G`'s type, then **checks** it with the existing type former and discovers its spine;
   the restriction's compatibility, result and covering conditions are decided, not assumed;
4. prunes `G := λ ȳ. H (ȳ restricted)` with the flex-flex forcing theorem, which loses no
   solution of the store;
5. exchanges `F` and `H`, which is possible because `H`'s type does not mention `F`;
6. runs the pattern rule again, now for `F` as the newest metavariable.

The round progresses only when the last step removes a declaration, so the rank of the
composed solver still drops. Each part is an update of the original store, hence the round is
sound and loses no solution; a refutation from the last step refutes the original store.
Unrecognized shapes, failed checks and exhausted budgets return nothing, never a refutation.

The exchange rule covers the remaining case where the equation is a pattern for the next older
metavariable and the newest one does not depend on it: the two are exchanged and the pattern rule
runs for the older one. The full round tries the pattern rule, the prune rule, the exchange rule and
then the qualified worklist round.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternSolver

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentScope
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentWorklist
open ContextualDependentPrune

/-! ## Raw deletion of binders -/

section Raw

variable {Head : Type}

/-- Delete the binders marked `false` from a Pi chain, inverting every remaining code through
the partial inverse. Any reference to a deleted variable makes the operation fail. -/
def dropPis : List Bool → {n m : Nat} → ContextualDependentInversion.Partial n m → Tm Head m → Option (Tm Head n)
  | [], _, _, inverse, code => ContextualDependentInversion.invert inverse code
  | true :: rest, _, _, inverse, .pi domain body => do
      let domain' ← ContextualDependentInversion.invert inverse domain
      let body' ← dropPis rest (ContextualDependentInversion.lift inverse) body
      return .pi domain' body'
  | false :: rest, _, _, inverse, .pi _ body => dropPis rest (Fin.cases none inverse) body
  | _ :: _, _, _, _, _ => none

/-- The partial inverse of weakening: the newest variable has no preimage. -/
def withoutNewest (n : Nat) : ContextualDependentInversion.Partial n (n + 1) := Fin.cases none some

end Raw

/-- All binders of a spine, outermost first. -/
def locals {Head : Type} {rules : Rules Head} : {Γ : Context rules} → {type : TypeOver Γ} → (spine : Spine type) →
    List spine.Local
  | _, _, .stop _ => []
  | _, _, .bind _ rest => .inl () :: (locals rest).map Sum.inr

theorem mem_locals {Head : Type} {rules : Rules Head} {Γ : Context rules} {type : TypeOver Γ} (spine : Spine type) :
    ∀ position, position ∈ locals spine := by
  induction spine with
  | stop type => intro position; exact position.elim
  | bind shape rest ih =>
      intro position
      rcases position with ⟨⟩ | position
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (ih position))

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- Run a computation at the two newest declarations of a context. -/
def throughTwo {Θ : Context S.R} (outer : Newest Θ) (inner : Newest outer.base)
    (problem : EquationStore (TotalTerm Θ))
    (solve : {Γ₀ : Context S.R} → (older : TypeOver Γ₀) → (newer : TypeOver (extend Γ₀ older)) →
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (Found stored)) :
    Option (Found problem) := by
  cases outer with
  | mk base newer same =>
      cases inner with
      | mk base₀ older same₀ =>
          change base = extend base₀ older at same₀
          subst same₀
          subst same
          exact solve older newer problem

theorem throughTwo_nil {Θ : Context S.R} (outer : Newest Θ) (inner : Newest outer.base)
    (solve : {Γ₀ : Context S.R} → (older : TypeOver Γ₀) → (newer : TypeOver (extend Γ₀ older)) →
      (stored : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (Found stored))
    (nothing : ∀ {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)),
      solve older newer [] = none) :
    throughTwo outer inner [] solve = none := by
  cases outer with
  | mk base newer same =>
      cases inner with
      | mk base₀ older same₀ =>
          change base = extend base₀ older at same₀
          subst same₀
          subst same
          exact nothing older newer

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

/-! ## The prune rule on one recognized pattern -/

/-- Prune `G` to the intersection with the arguments of `F`, exchange, and solve `F`. -/
def tryPrune (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    (spine : Spine newer) (recognized : Recognized spine scope active) : Option (Found (equation :: rest)) := by
  haveI := localDecidableEq scope
  haveI := localDecidableEq spine
  exact
  match readApplication recognized.right.code with
  | none => none
  | some (_, arguments) =>
    match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices reducer fuel
        arguments.length ((older.reindex (projectionHom Γ₀ older)).reindex (projectionHom (extend Γ₀ older) newer)) with
    | none => none
    | some olderSpine =>
      match arguments.mapM (localOf scope) with
      | none => none
      | some values =>
        match assigned : assign olderSpine values with
        | none => none
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
                | none => none
                | some keptCode =>
                  match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
                      Γ₀ keptCode with
                  | none => none
                  | some next =>
                    match ContextualDependentPiSpineDiscovery.discover facts roots heads algebra declared choices
                        reducer fuel keepList.length (ContextualDependentParameterExchange.second older next.val) with
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
                            match searchStore rigid facts complete roots heads algebra declared choices reducer root
                                normalizes certifyNormal fuel (ContextualDependentParameterExchange.second next.val older)
                                exchanged.remaining with
                            | none => none
                            | some (.solved solved smaller) => some (.solved ((pruned.then exchanged).then solved) smaller)
                            | some (.refuted absent) =>
                                some (.refuted fun solvable => absent ((pruned.then exchanged).solvable_iff.mp solvable))
                          else none
                        else none
                        else none
                        else none
              else none
            else none
          else none
          else none

/-- The prune rule on one scoped reading. -/
def pruneActive (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    {scopeType : TypeOver (extend (extend Γ₀ older) newer)} (scope : Spine scopeType)
    (active : Active scope.target) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) : Option (Found (equation :: rest)) :=
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
              tryPrune rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
                headTypingUnique fuel older newer scope active equation view rest spine recognized

/-- The prune rule on one store equation, in both orientations. -/
def pruneEquation (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) : Option (Found (equation :: rest)) :=
  match viewEquation facts roots heads algebra declared choices reducer root fuel equation with
  | none => none
  | some ⟨scope, active, view⟩ =>
      match pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique fuel older newer scope active equation view rest with
      | some found => some found
      | none =>
          pruneActive rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            headTypingUnique fuel older newer scope ⟨active.type, active.right, active.left⟩ equation
            (fun solution => (view solution).trans (toScoped_swap scope active solution).symm) rest

def pruneSearch (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older)) :
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match pruneEquation rigid facts complete roots heads algebra declared choices reducer root normalizes
          certifyNormal headTypingUnique fuel older newer equation rest with
      | some found => some found
      | none => (pruneSearch fuel older newer rest).map (Found.keepLeft equation)

/-- **The prune rule** at the two newest declarations. -/
def pruneRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  match newestOf facts roots heads algebra declared choices reducer fuel Θ with
  | none => none
  | some outer =>
      match newestOf facts roots heads algebra declared choices reducer fuel outer.base with
      | none => none
      | some inner => throughTwo outer inner problem fun older newer stored =>
          pruneSearch rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            headTypingUnique fuel older newer stored

theorem pruneRule_nil (fuel : Nat) {Θ : Context S.R} :
    pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel ([] : EquationStore (TotalTerm Θ)) = none := by
  unfold pruneRule
  split
  · rfl
  · split
    · rfl
    · apply throughTwo_nil
      intro _ _ _
      rfl

/-! ## Exchange so that the right metavariable is solved -/

/-- When the newest metavariable does not depend on the next older one, exchange them and run the
pattern rule for the older one, now the newest. Independence is computed by strengthening the newer
type past the older declaration and checking it with the existing type former. -/
def exchangeAt (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀) (newer : TypeOver (extend Γ₀ older))
    (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) : Option (Found problem) := by
  exact
  match problem, ContextualDependentInversion.invert (withoutNewest Γ₀.arity) newer.code with
  | [], _ => none
  | _ :: _, none => none
  | equation :: rest, some code =>
      match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ₀ code with
      | none => none
      | some next =>
          if same : newer.code = (ContextualDependentParameterExchange.second older next.val).code ∧
              newer.level = (ContextualDependentParameterExchange.second older next.val).level then by
            have independent : newer = ContextualDependentParameterExchange.second older next.val :=
              TypeOver.ext same.1 same.2
            subst independent
            exact
              let exchanged := ContextualDependentPrune.exchange S.levels older next.val (equation :: rest)
              match searchStore rigid facts complete roots heads algebra declared choices reducer root normalizes
                  certifyNormal fuel (ContextualDependentParameterExchange.second next.val older) exchanged.remaining with
              | none => none
              | some (.solved solved smaller) => some (.solved (exchanged.then solved) smaller)
              | some (.refuted absent) =>
                  some (.refuted fun solvable => absent (exchanged.solvable_iff.mp solvable))
          else none

/-- **The exchange rule** at the two newest declarations. -/
def exchangeRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  match newestOf facts roots heads algebra declared choices reducer fuel Θ with
  | none => none
  | some outer =>
      match newestOf facts roots heads algebra declared choices reducer fuel outer.base with
      | none => none
      | some inner => throughTwo outer inner problem fun older newer stored =>
          exchangeAt rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
            fuel older newer stored

theorem exchangeRule_nil (fuel : Nat) {Θ : Context S.R} :
    exchangeRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      fuel ([] : EquationStore (TotalTerm Θ)) = none := by
  unfold exchangeRule
  split
  · rfl
  · split
    · rfl
    · apply throughTwo_nil
      intro _ _ _
      rfl

/-! ## The composed solver with pruning -/

/-- **One round of the full solver**: the pattern rule, then the prune rule, then the qualified
worklist round. -/
def fullRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels size problem :=
  match patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      fuel problem with
  | some (.solved update smaller) => .progress update (Prod.Lex.left _ _ smaller)
  | some (.refuted absent) => .refuted absent
  | none =>
      match pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
          headTypingUnique fuel problem with
      | some (.solved update smaller) => .progress update (Prod.Lex.left _ _ smaller)
      | some (.refuted absent) => .refuted absent
      | none =>
          match exchangeRule rigid facts complete roots heads algebra declared choices reducer root normalizes
              certifyNormal fuel problem with
          | some (.solved update smaller) => .progress update (Prod.Lex.left _ _ smaller)
          | some (.refuted absent) => .refuted absent
          | none => ContextualDependentWorklist.round rigid facts complete roots heads algebra declared choices reducer
              fuel problem

/-- **The full solver** for the worklist driver. -/
def fullSolver (fuel : Nat) : Solver S.levels where
  rank := size
  round := fullRound rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
    headTypingUnique fuel

theorem fullRound_nil (fuel : Nat) {Θ : Context S.R} :
    fullRound rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel ([] : EquationStore (TotalTerm Θ)) = .stuck := by
  unfold fullRound
  rw [patternRule_nil, pruneRule_nil, exchangeRule_nil]
  exact ContextualDependentWorklist.round_nil rigid facts complete roots heads algebra declared choices reducer fuel

/-- **Refutations are certified**: a rigid clash, or a refutation by the pattern rule, or one by
the pattern rule after a no-loss prune and exchange, or after a no-loss exchange alone. -/
theorem fullRound_refuted_grounds (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {absent : ¬ (frames S.levels).Solvable problem}
    (refuted : fullRound rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem = .refuted absent) :
    ContextualDependentRigid.storeClashes problem = true ∨
      (∃ absent', patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal fuel problem = some (.refuted absent')) ∨
      (∃ absent', pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal headTypingUnique fuel problem = some (.refuted absent')) ∨
      (∃ absent', exchangeRule rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal fuel problem = some (.refuted absent')) := by
  unfold fullRound at refuted
  cases found : patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal fuel problem with
  | some result =>
      cases result with
      | solved update smaller => simp only [found] at refuted; cases refuted
      | refuted absent' => exact .inr (.inl ⟨absent', rfl⟩)
  | none =>
      simp only [found] at refuted
      cases pruned : pruneRule rigid facts complete roots heads algebra declared choices reducer root normalizes
          certifyNormal headTypingUnique fuel problem with
      | some result =>
          cases result with
          | solved update smaller => simp only [pruned] at refuted; cases refuted
          | refuted absent' => exact .inr (.inr (.inl ⟨absent', rfl⟩))
      | none =>
          simp only [pruned] at refuted
          cases exchanged : exchangeRule rigid facts complete roots heads algebra declared choices reducer root
              normalizes certifyNormal fuel problem with
          | some result =>
              cases result with
              | solved update smaller => simp only [exchanged] at refuted; cases refuted
              | refuted absent' => exact .inr (.inr (.inr ⟨absent', rfl⟩))
          | none =>
          simp only [exchanged] at refuted
          exact .inl (ContextualDependentWorklist.round_refuted_clashes rigid facts complete roots heads algebra declared
            choices reducer fuel refuted)

/-- **The stores the full solver decides form a fragment.** -/
def fullFragment (fuel : Nat) :
    Fragment (fullSolver rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
      headTypingUnique fuel) :=
  Reaches.fragment _ (fullRound_nil rigid facts complete roots heads algebra declared choices reducer root normalizes
    certifyNormal headTypingUnique fuel)

/-! ## The driver guarantees for the full solver -/

section Guarantees

variable (fuel : Nat) {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}

/-- **No solution is lost** by any run of the full solver. -/
theorem full_no_loss (budget : Nat) {Δ : Context S.R} (solution : Δ ⟶ Θ)
    (solved : (frames S.levels).Models solution original) :
    ∃ state, (run (fullSolver rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal headTypingUnique fuel) original budget).state? = some state ∧
      ∃ residual : Δ ⟶ state.target, (frames S.levels).Models residual state.remaining ∧
        ∀ term : TotalTerm Θ, (frames S.levels).E (term.reindex solution) (term.reindex (residual ≫ state.answer)) :=
  drive_no_loss _ budget _ solution solved

/-- **Every run finishes** at some budget. -/
theorem full_finishes :
    ∃ budget, (run (fullSolver rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel) original budget).Finished :=
  drive_finishes _ _

/-- **Budget monotonicity**: a finished run has the same outcome at every larger budget. -/
theorem full_mono (budget : Nat)
    (finished : (run (fullSolver rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel) original budget).Finished) (larger : Nat) (enough : budget ≤ larger) :
    run (fullSolver rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal headTypingUnique fuel) original larger =
      run (fullSolver rigid facts complete roots heads algebra declared choices reducer root normalizes
        certifyNormal headTypingUnique fuel) original budget :=
  drive_mono _ budget _ finished larger enough

/-- **A refutation is certified**: the store has no solution in any future context. -/
theorem full_refuted (budget : Nat)
    (refuted : (run (fullSolver rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel) original budget).readout = .refuted) :
    ¬ (frames S.levels).Solvable original :=
  drive_refuted _ budget _ refuted

/-- **A solved run is principal.** -/
theorem full_solved_principal {budget : Nat} {state : Update S.levels original} {finished : state.remaining = []}
    (solved : run (fullSolver rigid facts complete roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel) original budget = .solved state finished) :
    (frames S.levels).Principal original state.answer :=
  drive_solved_principal _ solved

end Guarantees

end ContextualDependentPatternSolver
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
