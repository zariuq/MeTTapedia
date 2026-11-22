import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternSolverPrune

/-!
# The unconditional fibre join, where the full solver decides

R77's full solver (`ContextualDependentPatternSolver.fullSolver`) adds two rules to the pattern
solver: the prune rule (prune the newest metavariable to the binders shared with the next older one,
exchange, and solve) and the exchange rule (exchange the two newest metavariables and solve the older
one). Both end at the frame `Γ₀.H`, where `Γ₀` is the telescope below the two newest declarations and
`H`'s type is computed from the newest type: by deleting binders (`dropPis`) for pruning, by
strengthening past the older declaration (`invert`) for exchange.

**Translated types are chains of constants** (`liftClosed_bindingType`). The closed type `Π Γ. s` of
a metavariable is a Π-chain of sort constants ending in a sort constant, with no variable anywhere.
Strengthening returns the chain unchanged (`invert_chain`); deleting binders returns the chain of the
kept sorts (`dropPis_chain`), which is the closed type of the pruned arity.

**Both rules keep translated telescopes** (`exchangeRule_translated`, `pruneRule_translated`), read off
their definitions. With the pattern rule and the worklist round (`DependentFullJoin`), the full solver
keeps translated telescopes (`full_keeps_translated`), so the fibre join is unconditional on every
translated store the full solver decides (`decidedInFibre_of_full`, `fibre_admission_transfer_of_full`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentFibre Translation
open ContextualDependentUpdate

/-! ## Chains of constants -/

section Chains

variable {Head : Type}

/-- **A Π-chain of constants** ending in a constant: no variable occurs. -/
def constChain : {n : Nat} → List DeclName → DeclName → Tm Head n
  | _, [], result => .const result
  | _, c :: cs, result => .pi (.const c) (constChain cs result)

theorem rename_chain : ∀ {n m : Nat} (ρ : Ren n m) (cs : List DeclName) (result : DeclName),
    rename ρ (constChain (Head := Head) cs result) = constChain cs result
  | _, _, _, [], _ => rfl
  | _, _, ρ, c :: cs, result => by
      show Tm.pi (.const c) (rename (liftRen ρ) (constChain cs result)) = _
      rw [rename_chain (liftRen ρ) cs result]
      rfl

theorem liftClosed_chain {n : Nat} (cs : List DeclName) (result : DeclName) :
    (liftClosed (constChain (Head := Head) (n := 0) cs result) : Tm Head n) = constChain cs result :=
  rename_chain _ cs result

/-- Keep the entries marked `true`, in order; the rest of the list is kept whole. -/
def keepMarked {α : Type*} : List Bool → List α → List α
  | [], rest => rest
  | true :: mask, x :: rest => x :: keepMarked mask rest
  | false :: mask, _ :: rest => keepMarked mask rest
  | _ :: _, [] => []

theorem keepMarked_map {α β : Type*} (f : α → β) :
    ∀ (mask : List Bool) (l : List α), keepMarked mask (l.map f) = (keepMarked mask l).map f
  | [], _ => rfl
  | true :: _, [] => rfl
  | false :: _, [] => rfl
  | true :: mask, _ :: l => congrArg (List.cons _) (keepMarked_map f mask l)
  | false :: mask, _ :: l => keepMarked_map f mask l

/-- **Strengthening keeps a chain.** -/
theorem invert_chain : ∀ {n m : Nat} (inverse : ContextualDependentInversion.Partial n m)
    (cs : List DeclName) (result : DeclName),
    ContextualDependentInversion.invert inverse (constChain (Head := Head) cs result) =
      some (constChain cs result)
  | _, _, _, [], _ => rfl
  | _, _, inverse, c :: cs, result => by
      show ContextualDependentInversion.invert inverse (.pi (.const c) (constChain cs result)) = _
      simp only [ContextualDependentInversion.invert, invert_chain (ContextualDependentInversion.lift inverse) cs result]
      rfl

/-- **Deleting binders of a chain leaves the chain of the kept constants.** -/
theorem dropPis_chain : ∀ (mask : List Bool) {n m : Nat} (inverse : ContextualDependentInversion.Partial n m)
    (cs : List DeclName) (result : DeclName) {code : Tm Head n},
    ContextualDependentPatternSolver.dropPis mask inverse (constChain cs result) = some code →
      code = constChain (keepMarked mask cs) result
  | [], _, _, inverse, cs, result, code, dropped => by
      have computed : ContextualDependentInversion.invert inverse (constChain (Head := Head) cs result) =
          some code := dropped
      rw [invert_chain] at computed
      exact (Option.some.inj computed).symm
  | true :: mask, _, _, _, [], _, _, dropped => by cases dropped
  | false :: mask, _, _, _, [], _, _, dropped => by cases dropped
  | true :: mask, _, _, inverse, c :: cs, result, code, dropped => by
      have computed : (do
          let domain' ← ContextualDependentInversion.invert inverse (Tm.const (Head := Head) c)
          let body' ← ContextualDependentPatternSolver.dropPis mask (ContextualDependentInversion.lift inverse)
            (constChain cs result)
          return Tm.pi domain' body') = some code := dropped
      obtain ⟨domain', domainSame, computed⟩ := Option.bind_eq_some_iff.mp computed
      obtain ⟨body', bodySame, computed⟩ := Option.bind_eq_some_iff.mp computed
      cases computed
      cases domainSame
      rw [dropPis_chain mask _ cs result bodySame]
      rfl
  | false :: mask, _, _, inverse, c :: cs, result, code, dropped => by
      exact dropPis_chain mask _ cs result dropped

end Chains

/-! ## Translated types -/

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (church : ConversionCoherence.ChurchRosser S.R)
variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)

theorem telescope_chain : ∀ (Γ : List sig.Srt) (cs : List DeclName) (result : DeclName),
    BindingSignatureEmbedding.telescopeType (Head := Head) names Γ (constChain cs result) =
      constChain ((Γ.reverse.map names.sort) ++ cs) result
  | [], _, _ => rfl
  | x :: Γ, cs, result => by
      show BindingSignatureEmbedding.telescopeType names Γ
          (BindingSignatureEmbedding.closedArrow (BindingSignatureEmbedding.sortType names x)
            (constChain cs result)) = _
      have arrow : BindingSignatureEmbedding.closedArrow (Head := Head)
          (BindingSignatureEmbedding.sortType names x) (constChain cs result) =
          constChain (names.sort x :: cs) result := by
        show Tm.pi (.const (names.sort x)) (liftClosed (constChain cs result)) = _
        rw [liftClosed_chain]
        rfl
      rw [arrow, telescope_chain Γ (names.sort x :: cs) result]
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append]

/-- **The closed type `Π Γ. s` is the chain of its sort constants.** -/
theorem liftClosed_bindingType {n : Nat} (Γ : List sig.Srt) (s : sig.Srt) :
    (liftClosed (BindingSignatureEmbedding.bindingType (Head := Head) names Γ s) : Tm Head n) =
      constChain (Γ.reverse.map names.sort) (names.sort s) := by
  have chain := telescope_chain (Head := Head) names Γ [] (names.sort s)
  rw [List.append_nil] at chain
  show liftClosed (BindingSignatureEmbedding.telescopeType names Γ (constChain [] (names.sort s))) = _
  rw [chain, liftClosed_chain]

/-- **A translated telescope with a newest declaration.** -/
theorem extend_eq_obj {Γ₀ : Context S.R} {T : TypeOver Γ₀} {M : List (Binding.MetaArity sig)}
    (same : extend Γ₀ T = (fibre facts roots heads church names realization).obj M) :
    ∃ (a : Binding.MetaArity sig) (N : List (Binding.MetaArity sig)), M = a :: N ∧
      Γ₀ = (fibre facts roots heads church names realization).obj N ∧
        HEq T.code (liftClosed (BindingSignatureEmbedding.bindingType (Head := Head) names a.1 a.2) :
          Tm Head N.length) := by
  obtain ⟨k, raw, formed⟩ := Γ₀
  cases M with
  | nil => exact absurd (congrArg Context.arity same) (Nat.succ_ne_zero k)
  | cons a N =>
      have arity : k + 1 = N.length + 1 := congrArg Context.arity same
      obtain rfl : k = N.length := Nat.succ.inj arity
      have raws : Ctx.snoc raw T.code =
          Ctx.snoc (metaCtx (Head := Head) names N)
            (liftClosed (BindingSignatureEmbedding.bindingType names a.1 a.2)) :=
        eq_of_heq (congr_arg_heq Context.raw same)
      obtain ⟨rfl, codes⟩ := Ctx.snoc.inj raws
      exact ⟨a, N, rfl, rfl, heq_of_eq codes⟩

/-- **Extending a translated telescope by a closed type `Π Γ. s` gives a translated telescope.** -/
theorem translated_extend {N : List (Binding.MetaArity sig)} {Γ₀ : Context S.R}
    (base : Γ₀ = (fibre facts roots heads church names realization).obj N) (next : TypeOver Γ₀)
    (Γ : List sig.Srt) (s : sig.Srt)
    (code : HEq next.code (liftClosed (BindingSignatureEmbedding.bindingType (Head := Head) names Γ s) :
      Tm Head N.length)) :
    Translated facts roots heads church names realization (extend Γ₀ next) := by
  subst base
  refine ⟨(Γ, s) :: N, ?_⟩
  exact ContextualDependentWorklist.context_eq (congrArg (Ctx.snoc _) (eq_of_heq code)) _ _

/-- **The two newest declarations of a translated telescope**: the rest is translated, and the
newest type is a closed type `Π Γ. s`. -/
theorem translated_two {Γ₀ : Context S.R} {older : TypeOver Γ₀} {newer : TypeOver (extend Γ₀ older)}
    (translated : Translated facts roots heads church names realization (extend (extend Γ₀ older) newer)) :
    ∃ (a : Binding.MetaArity sig) (N : List (Binding.MetaArity sig)),
      Γ₀ = (fibre facts roots heads church names realization).obj N ∧
        HEq newer.code (liftClosed (BindingSignatureEmbedding.bindingType (Head := Head) names a.1 a.2) :
          Tm Head (N.length + 1)) := by
  obtain ⟨M, same⟩ := translated
  obtain ⟨a, M', rfl, middle, newerCode⟩ := extend_eq_obj facts roots heads church names realization same
  obtain ⟨b, N, rfl, base, -⟩ := extend_eq_obj facts roots heads church names realization middle
  exact ⟨a, N, base, newerCode⟩

/-- **Strengthening the newest type of a translated telescope past the older declaration gives a
closed type.** -/
theorem translated_strengthened {Γ₀ : Context S.R} {older : TypeOver Γ₀} {newer : TypeOver (extend Γ₀ older)}
    (translated : Translated facts roots heads church names realization (extend (extend Γ₀ older) newer))
    {code : Tm Head Γ₀.arity}
    (strengthened : (∃ mask, ContextualDependentPatternSolver.dropPis mask
        (ContextualDependentPatternSolver.withoutNewest Γ₀.arity) newer.code = some code) ∨
      ContextualDependentInversion.invert (ContextualDependentPatternSolver.withoutNewest Γ₀.arity) newer.code =
        some code)
    (next : TypeOver Γ₀) (same : next.code = code) :
    Translated facts roots heads church names realization (extend Γ₀ next) := by
  obtain ⟨a, N, base, newerCode⟩ := translated_two facts roots heads church names realization translated
  subst base
  have newerChain : newer.code = constChain (a.1.reverse.map names.sort) (names.sort a.2) :=
    (eq_of_heq newerCode).trans (liftClosed_bindingType names a.1 a.2)
  rcases strengthened with ⟨mask, dropped⟩ | inverted
  · rw [newerChain] at dropped
    have kept := dropPis_chain mask _ _ _ dropped
    rw [keepMarked_map] at kept
    refine translated_extend facts roots heads church names realization rfl next
      (keepMarked mask a.1.reverse).reverse a.2 (heq_of_eq ?_)
    rw [same, kept, liftClosed_bindingType, List.reverse_reverse]
    rfl
  · rw [newerChain, invert_chain] at inverted
    refine translated_extend facts roots heads church names realization rfl next a.1 a.2 (heq_of_eq ?_)
    rw [same, ← Option.some.inj inverted, liftClosed_bindingType]
    rfl


/-! ## The prune and exchange rules keep translated telescopes -/

section Rules

variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (algebra : CumulativeAlgebra S.R)
  (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- **A solved exchange ends at `Γ₀.G'`**, where `G'` is the newest type strengthened past the older
declaration. -/
theorem exchangeAt_target (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀)
    (newer : TypeOver (extend Γ₀ older)) (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    {update : Update S.levels problem} {smaller : update.target.arity < (extend (extend Γ₀ older) newer).arity}
    (solved : ContextualDependentPatternSolver.exchangeAt rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel older newer problem = some (.solved update smaller)) :
    ∃ (code : Tm Head Γ₀.arity) (next : TypeOver Γ₀),
      ContextualDependentInversion.invert (ContextualDependentPatternSolver.withoutNewest Γ₀.arity) newer.code =
        some code ∧ next.code = code ∧ update.target = extend Γ₀ next := by
  cases problem with
  | nil =>
      unfold ContextualDependentPatternSolver.exchangeAt at solved
      cases solved
  | cons equation rest =>
      cases inverted : ContextualDependentInversion.invert
          (ContextualDependentPatternSolver.withoutNewest Γ₀.arity) newer.code with
      | none =>
          unfold ContextualDependentPatternSolver.exchangeAt at solved
          simp only [inverted] at solved
          cases solved
      | some code =>
          cases formed : ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
              Γ₀ code with
          | none =>
              unfold ContextualDependentPatternSolver.exchangeAt at solved
              simp only [inverted] at solved
              erw [formed] at solved
              cases solved
          | some next =>
              by_cases same : newer.code = (ContextualDependentParameterExchange.second older next.val).code ∧
                  newer.level = (ContextualDependentParameterExchange.second older next.val).level
              · have independent : newer = ContextualDependentParameterExchange.second older next.val :=
                  TypeOver.ext same.1 same.2
                subst independent
                unfold ContextualDependentPatternSolver.exchangeAt at solved
                simp only [inverted] at solved
                erw [formed] at solved
                dsimp only at solved
                rw [dif_pos same] at solved
                split at solved
                · cases solved
                · rename_i found foundSmaller computed
                  cases solved
                  exact ⟨code, next.val, rfl, next.property,
                    searchStore_target facts roots heads rigid complete algebra declared choices reducer root normalizes
                      certifyNormal fuel _ _ computed⟩
                · cases solved
              · unfold ContextualDependentPatternSolver.exchangeAt at solved
                simp only [inverted] at solved
                erw [formed] at solved
                dsimp only at solved
                rw [dif_neg same] at solved
                cases solved

/-- **The exchange rule keeps translated telescopes.** -/
theorem exchangeRule_translated (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {update : Update S.levels problem} {smaller : update.target.arity < Θ.arity}
    (solved : ContextualDependentPatternSolver.exchangeRule rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal fuel problem = some (.solved update smaller))
    (translated : Translated facts roots heads church names realization Θ) :
    Translated facts roots heads church names realization update.target := by
  unfold ContextualDependentPatternSolver.exchangeRule at solved
  split at solved
  · cases solved
  · rename_i outer _
    split at solved
    · cases solved
    · rename_i inner _
      obtain ⟨base, newer, same⟩ := outer
      obtain ⟨base₀, older, same₀⟩ := inner
      change base = extend base₀ older at same₀
      subst same₀
      subst same
      obtain ⟨code, next, inverted, codeSame, target⟩ := exchangeAt_target facts roots heads rigid complete algebra
        declared choices reducer root normalizes certifyNormal fuel older newer problem solved
      rw [target]
      exact translated_strengthened facts roots heads church names realization translated (.inr inverted) next
        codeSame

/-- **A solved prune ends at `Γ₀.H`**, where `H`'s type deletes binders of the newest type. -/
theorem tryPrune_target (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀)
    (newer : TypeOver (extend Γ₀ older)) {scopeType : TypeOver (extend (extend Γ₀ older) newer)}
    (scope : ContextualDependentPiSpine.Spine scopeType) (active : ContextualDependentScope.Active scope.target)
    (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    (spine : ContextualDependentPiSpine.Spine newer)
    (recognized : ContextualDependentGeneralPattern.Recognized spine scope active)
    {update : Update S.levels (equation :: rest)}
    {smaller : update.target.arity < (extend (extend Γ₀ older) newer).arity}
    (solved : ContextualDependentPatternSolver.tryPrune rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel older newer scope active equation view rest spine
      recognized = some (.solved update smaller)) :
    ∃ (code : Tm Head Γ₀.arity) (next : TypeOver Γ₀) (mask : List Bool),
      ContextualDependentPatternSolver.dropPis mask (ContextualDependentPatternSolver.withoutNewest Γ₀.arity)
        newer.code = some code ∧ next.code = code ∧ update.target = extend Γ₀ next := by
  unfold ContextualDependentPatternSolver.tryPrune at solved
  repeat' (first | split at solved | (dsimp (config := { zeta := true, iota := false, proj := false, decide := false, beta := false, eta := false }) only at solved; split at solved))
  all_goals first
    | (cases solved; done)
    | (cases solved
       have dropped := ‹ContextualDependentPatternSolver.dropPis _
         (ContextualDependentPatternSolver.withoutNewest Γ₀.arity) newer.code = some _›
       have searched := ‹ContextualDependentPatternSolver.searchStore rigid facts complete roots heads algebra declared
         choices reducer root normalizes certifyNormal fuel _ _ = some (.solved _ _)›
       have target := searchStore_target facts roots heads rigid complete algebra declared choices reducer root
         normalizes certifyNormal fuel _ _ searched
       refine ⟨_, _, _, dropped, ?_, target⟩
       exact (‹{ t : TypeOver Γ₀ // t.code = _ }›).2)

theorem pruneActive_target (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀)
    (newer : TypeOver (extend Γ₀ older)) {scopeType : TypeOver (extend (extend Γ₀ older) newer)}
    {scope : ContextualDependentPiSpine.Spine scopeType} {active : ContextualDependentScope.Active scope.target}
    {equation : Equation (TotalTerm (extend (extend Γ₀ older) newer))}
    {view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend (extend Γ₀ older) newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution}
    {rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))}
    {update : Update S.levels (equation :: rest)}
    {smaller : update.target.arity < (extend (extend Γ₀ older) newer).arity}
    (solved : ContextualDependentPatternSolver.pruneActive rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel older newer scope active equation view rest =
        some (.solved update smaller)) :
    ∃ (code : Tm Head Γ₀.arity) (next : TypeOver Γ₀) (mask : List Bool),
      ContextualDependentPatternSolver.dropPis mask (ContextualDependentPatternSolver.withoutNewest Γ₀.arity)
        newer.code = some code ∧ next.code = code ∧ update.target = extend Γ₀ next := by
  unfold ContextualDependentPatternSolver.pruneActive at solved
  split at solved
  · cases solved
  · split at solved
    · cases solved
    · split at solved
      · cases solved
      · exact tryPrune_target facts roots heads rigid complete algebra declared choices reducer root normalizes
          certifyNormal headTypingUnique fuel older newer _ _ _ _ _ _ _ solved

theorem pruneEquation_target (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀)
    (newer : TypeOver (extend Γ₀ older)) (equation : Equation (TotalTerm (extend (extend Γ₀ older) newer)))
    (rest : EquationStore (TotalTerm (extend (extend Γ₀ older) newer)))
    {update : Update S.levels (equation :: rest)}
    {smaller : update.target.arity < (extend (extend Γ₀ older) newer).arity}
    (solved : ContextualDependentPatternSolver.pruneEquation rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel older newer equation rest =
        some (.solved update smaller)) :
    ∃ (code : Tm Head Γ₀.arity) (next : TypeOver Γ₀) (mask : List Bool),
      ContextualDependentPatternSolver.dropPis mask (ContextualDependentPatternSolver.withoutNewest Γ₀.arity)
        newer.code = some code ∧ next.code = code ∧ update.target = extend Γ₀ next := by
  unfold ContextualDependentPatternSolver.pruneEquation at solved
  split at solved
  · cases solved
  · rename_i scope active view _
    split at solved
    · rename_i found computed
      cases solved
      exact pruneActive_target facts roots heads rigid complete algebra declared choices reducer root normalizes
        certifyNormal headTypingUnique fuel older newer computed
    · exact pruneActive_target facts roots heads rigid complete algebra declared choices reducer root normalizes
        certifyNormal headTypingUnique fuel older newer (view := fun solution =>
          (view solution).trans (ContextualDependentPatternSolver.toScoped_swap scope active solution).symm) solved

theorem pruneSearch_target (fuel : Nat) {Γ₀ : Context S.R} (older : TypeOver Γ₀)
    (newer : TypeOver (extend Γ₀ older)) :
    ∀ (problem : EquationStore (TotalTerm (extend (extend Γ₀ older) newer))) {update : Update S.levels problem}
      {smaller : update.target.arity < (extend (extend Γ₀ older) newer).arity},
      ContextualDependentPatternSolver.pruneSearch rigid facts complete roots heads algebra declared choices reducer
        root normalizes certifyNormal headTypingUnique fuel older newer problem = some (.solved update smaller) →
      ∃ (code : Tm Head Γ₀.arity) (next : TypeOver Γ₀) (mask : List Bool),
        ContextualDependentPatternSolver.dropPis mask (ContextualDependentPatternSolver.withoutNewest Γ₀.arity)
          newer.code = some code ∧ next.code = code ∧ update.target = extend Γ₀ next
  | [], _, _, solved => by simp [ContextualDependentPatternSolver.pruneSearch] at solved
  | equation :: rest, update, smaller, solved => by
      simp only [ContextualDependentPatternSolver.pruneSearch] at solved
      split at solved
      · rename_i found computed
        cases solved
        exact pruneEquation_target facts roots heads rigid complete algebra declared choices reducer root normalizes
          certifyNormal headTypingUnique fuel older newer equation rest computed
      · obtain ⟨found, computed, kept⟩ := Option.map_eq_some_iff.mp solved
        cases found with
        | solved inner innerSmaller =>
            cases kept
            exact pruneSearch_target fuel older newer rest computed
        | refuted _ => cases kept

/-- **The prune rule keeps translated telescopes.** -/
theorem pruneRule_translated (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {update : Update S.levels problem} {smaller : update.target.arity < Θ.arity}
    (solved : ContextualDependentPatternSolver.pruneRule rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel problem = some (.solved update smaller))
    (translated : Translated facts roots heads church names realization Θ) :
    Translated facts roots heads church names realization update.target := by
  unfold ContextualDependentPatternSolver.pruneRule at solved
  split at solved
  · cases solved
  · rename_i outer _
    split at solved
    · cases solved
    · rename_i inner _
      obtain ⟨base, newer, same⟩ := outer
      obtain ⟨base₀, older, same₀⟩ := inner
      change base = extend base₀ older at same₀
      subst same₀
      subst same
      obtain ⟨code, next, mask, dropped, codeSame, target⟩ := pruneSearch_target facts roots heads rigid complete
        algebra declared choices reducer root normalizes certifyNormal headTypingUnique fuel older newer problem solved
      rw [target]
      exact translated_strengthened facts roots heads church names realization translated (.inl ⟨mask, dropped⟩)
        next codeSame

/-- **The full solver keeps translated telescopes**: each progressing round keeps the frame, removes
the newest declaration, or ends at a frame `Γ₀.H` with a closed type `Π Γ. s` for `H`. -/
theorem full_keeps_translated (fuel : Nat) :
    KeepsFrames (ContextualDependentPatternSolver.fullSolver rigid facts complete roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel)
      (Translated facts roots heads church names realization) := by
  intro Γ problem update smaller progressed translated
  change ContextualDependentPatternSolver.fullRound rigid facts complete roots heads algebra declared choices reducer
    root normalizes certifyNormal headTypingUnique fuel problem = .progress update smaller at progressed
  unfold ContextualDependentPatternSolver.fullRound at progressed
  split at progressed
  · rename_i u s computed
    cases progressed
    obtain ⟨view, same⟩ := patternRule_target facts roots heads rigid complete algebra declared choices reducer root
      normalizes certifyNormal fuel problem computed
    rw [same]
    exact translated_base facts roots heads church names realization view translated
  · cases progressed
  · split at progressed
    · rename_i u s computed
      cases progressed
      exact pruneRule_translated facts roots heads church names realization rigid complete algebra declared choices
        reducer root normalizes certifyNormal headTypingUnique fuel problem computed translated
    · cases progressed
    · split at progressed
      · rename_i u s computed
        cases progressed
        exact exchangeRule_translated facts roots heads church names realization rigid complete algebra declared
          choices reducer root normalizes certifyNormal fuel problem computed translated
      · cases progressed
      · rcases worklist_round_target facts roots heads rigid complete algebra declared choices reducer fuel progressed
          with same | ⟨view, same⟩
        · rw [same]
          exact translated
        · rw [same]
          exact translated_base facts roots heads church names realization view translated

/-- **The full solver's decision is a decision in the fibre.** -/
theorem decidedInFibre_of_full {M : List (Binding.MetaArity sig)}
    (K : EquationStore (Binding.ContextualFamily.Observation sig M.get)) (rounds fuel : Nat)
    (decided : (ContextualDependentWorklist.run (ContextualDependentPatternSolver.fullSolver rigid facts complete roots
      heads algebra declared choices reducer root normalizes certifyNormal headTypingUnique rounds)
      ((fibre facts roots heads church names realization).store K) fuel).Decided) :
    DecidedInFibre facts roots heads church names realization K := by
  generalize computed : ContextualDependentWorklist.run (ContextualDependentPatternSolver.fullSolver rigid facts
      complete roots heads algebra declared choices reducer root normalizes certifyNormal headTypingUnique rounds)
      ((fibre facts roots heads church names realization).store K) fuel = outcome at decided
  cases outcome with
  | solved state finished =>
      have principal := ContextualDependentWorklist.drive_solved_principal _ computed
      obtain ⟨N, same⟩ := drive_solved_target _
        (full_keeps_translated facts roots heads church names realization rigid complete algebra declared choices
          reducer root normalizes certifyNormal headTypingUnique rounds)
        fuel _ (translated_obj facts roots heads church names realization M) computed
      have landing : ∀ (T : Context S.R) (answer : T ⟶ (fibre facts roots heads church names realization).obj M),
          T = (fibre facts roots heads church names realization).obj N →
          (frames S.levels).Principal ((fibre facts roots heads church names realization).store K) answer →
          DecidedInFibre facts roots heads church names realization K := by
        intro T answer same principal
        subst same
        exact .inl ⟨N, answer, principal⟩
      exact landing _ state.answer same principal
  | refuted absent => exact .inr absent
  | stuck _ => exact False.elim decided
  | cutoff _ => exact False.elim decided

/-- **The fibre join is unconditional where the full solver decides.** -/
theorem fibre_admission_transfer_of_full
    (sortInjective : Function.Injective names.sort)
    (closed : ClosedRealization (S := S) names)
    (operatorInjective : ∀ {s : sig.Srt}, Function.Injective (names.operator (sort := s)))
    {O : Type} [DecidableEq O] {State : Type} {Firing : State → Type}
    (P : Step (listFrames sig) O State Firing) [P.Guarded]
    (guards : ∀ {s : State} (f : Firing s),
      EquationStore (Binding.ContextualFamily.Observation sig (P.target f).get))
    (holds : ∀ {s : State} (f : Firing s) (N : List (Binding.MetaArity sig))
      (g : Binding.ContextualFamily.Assignment (S := sig) (P.target f).get N.get),
      P.Holds f N g ↔ (listFrames sig).Models g (guards f))
    {s : State} (f : Firing s) (rounds fuel : Nat)
    (decided : (ContextualDependentWorklist.run (ContextualDependentPatternSolver.fullSolver rigid facts complete roots
      heads algebra declared choices reducer root normalizes certifyNormal headTypingUnique rounds)
      ((fibre facts roots heads church names realization).store (P.information f)) fuel).Decided) :
    P.Admits f ↔ P.Shapes f ∧
      Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : O => ())
        (P.present s) ((P.selection f).commit (T := Unit)) ∧
      (frames S.levels).Solvable ((fibre facts roots heads church names realization).store
        (P.information f)) ∧
      (frames S.levels).Entails ((fibre facts roots heads church names realization).store
          (P.information f))
        (fun _ g => (frames S.levels).Models g
          ((fibre facts roots heads church names realization).store (guards f))) :=
  fibre_admission_transfer facts roots heads algebra complete rigid church names realization sortInjective closed
    @operatorInjective P guards holds f
    (decidedInFibre_of_full facts roots heads church names realization rigid complete algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique (P.information f) rounds fuel decided)

end Rules

end DependentFull

#print axioms DependentFull.rename_chain
#print axioms DependentFull.invert_chain
#print axioms DependentFull.dropPis_chain
#print axioms DependentFull.liftClosed_bindingType
#print axioms DependentFull.extend_eq_obj
#print axioms DependentFull.translated_extend
#print axioms DependentFull.translated_two
#print axioms DependentFull.translated_strengthened
#print axioms DependentFull.exchangeAt_target
#print axioms DependentFull.exchangeRule_translated
#print axioms DependentFull.tryPrune_target
#print axioms DependentFull.pruneRule_translated
#print axioms DependentFull.full_keeps_translated
#print axioms DependentFull.decidedInFibre_of_full
#print axioms DependentFull.fibre_admission_transfer_of_full

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
