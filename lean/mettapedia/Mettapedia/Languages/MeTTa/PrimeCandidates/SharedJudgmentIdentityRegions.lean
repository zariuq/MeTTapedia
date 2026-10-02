import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeIdentityLevelInstantiation

/-!
# Conditional identity regions in the native dependent calculus

Local uniqueness is used as an ordinary object-language identity witness,
not as a new conversion rule. The construction below builds congruence by
the actual native J declaration, retains its motive, and abstracts a local
identity assumption when exporting the result. Supplying a separately typed
witness discharges that assumption by the existing substitution calculus.

This does not derive uniqueness for every type or identify proof syntax.
In particular, an object-language Hedberg derivation is not obtained from
the external route-family elimination capability by an implicit bridge.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentIdentityRegions

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open NativeIndexedFamilies NativeIndexedFamilies.Intrinsic


variable {n m : Nat} {theta : Nat → LevelExpr Nat} {signature : Signature Tower.Head}
variable {context : Tower.Ctx n}

/-- The nondependent arrow remains the existing Pi constructor. -/
def arrow (domain codomain : Tower.Tm n) : Tower.Tm n :=
  .pi domain (rename wk codomain)

theorem apply_typed {domain codomain function argument : Tower.Tm n}
    (functionTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context function (arrow domain codomain))
    (argumentTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context argument domain) :
    Typing (NativeIdentityLevelInstantiation.rules theta signature) context (.app function argument) codomain := by
  simpa only [arrow, inst0_rename_wk] using Typing.appElim functionTyped argumentTyped

/-- Native J at an arbitrary endpoint, with a submitted motive body and
an independently typed method. No target result is an admission premise. -/
theorem ofBody_point
    {domain left method right witness : Tower.Tm n}
    (formed : ContextFormation (NativeIdentityLevelInstantiation.rules theta signature) context)
    (domainFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context domain (sortTm (theta 0)))
    (leftTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context left domain)
    (body : Tower.Tm (n + 2))
    (bodyFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature)
      (FormationSensitiveBasedIdentity.basedContext context domain left) body (sortTm (theta 1)))
    (methodTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context method
      (subst (FormationSensitiveBasedIdentity.reflexivitySub left) body))
    (rightTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context right domain)
    (witnessTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context witness (.id domain left right)) :
    Judgment (NativeIdentityLevelInstantiation.rules theta signature) context
      (identityEliminateApp domain left (.lam (.lam body)) method right witness)
      (subst (FormationSensitiveBasedIdentity.pointSub right witness) body) := by
  have parameters := NativeIdentityLevelInstantiation.ofBody formed domainFormed leftTyped body bodyFormed methodTyped
  have identity := FormationSensitiveContextual.identityTyped
    (rules := NativeIdentityLevelInstantiation.rules theta signature) context
  have point : Typing (NativeIdentityLevelInstantiation.rules theta signature) context right (subst ids domain) := by
    simpa only [subst_ids] using rightTyped
  have actual : FormationSensitive.CtxMor (NativeIdentityLevelInstantiation.rules theta signature)
      (FormationSensitiveBasedIdentity.basedContext context domain left) context (FormationSensitiveBasedIdentity.pointSub right witness) := by
    refine (identity.extend point).extend ?_
    simpa only [subst, subst_consSub_rename_wk, subst_ids, consSub_zero] using witnessTyped
  have generic := (NativeIdentityLevelInstantiation.generic_judgment parameters).substitute formed actual
  have resultFormed := bodyFormed.substitute actual
  refine ⟨formed, ?_⟩
  exact .conv (by simpa only [FormationSensitiveBasedIdentity.pointSub_genericTerm, FormationSensitiveBasedIdentity.pointSub_motiveBody] using generic.typing)
    resultFormed (.sort (theta 1)) (NativeIdentityLevelInstantiation.abstract_motive_beta _ body right witness)

/-- Congruence's dependent motive records the fixed left application and
the variable right application; its equality-proof binder is not inspected. -/
def congruenceMotive (left codomain function : Tower.Tm n) : Tower.Tm (n + 2) :=
  .id (FormationSensitiveBasedIdentity.doubleWeaken codomain)
    (.app (FormationSensitiveBasedIdentity.doubleWeaken function) (FormationSensitiveBasedIdentity.doubleWeaken left))
    (.app (FormationSensitiveBasedIdentity.doubleWeaken function) (.var 1))

theorem congruenceMotive_formed {domain left codomain function : Tower.Tm n}
    (codomainFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context codomain (sortTm (theta 1)))
    (leftTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context left domain)
    (functionTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context function (arrow domain codomain)) :
    Typing (NativeIdentityLevelInstantiation.rules theta signature) (FormationSensitiveBasedIdentity.basedContext context domain left)
      (congruenceMotive left codomain function) (sortTm (theta 1)) := by
  have codomainTwice := codomainFormed.weaken (extension := domain)
    |>.weaken (extension := .id (rename wk domain) (rename wk left) (.var 0))
  have leftTwice := leftTyped.weaken (extension := domain)
    |>.weaken (extension := .id (rename wk domain) (rename wk left) (.var 0))
  have functionTwice := functionTyped.weaken (extension := domain)
    |>.weaken (extension := .id (rename wk domain) (rename wk left) (.var 0))
  have functionExact : Typing (NativeIdentityLevelInstantiation.rules theta signature)
      (FormationSensitiveBasedIdentity.basedContext context domain left) (FormationSensitiveBasedIdentity.doubleWeaken function)
      (arrow (FormationSensitiveBasedIdentity.doubleWeaken domain) (FormationSensitiveBasedIdentity.doubleWeaken codomain)) := by
    simpa only [arrow, FormationSensitiveBasedIdentity.doubleWeaken,
      FormationSensitiveBasedIdentity.basedContext, rename, rename_comp, liftRen, wk,
      Fin.cases_succ] using functionTwice
  exact .idForm codomainTwice (.sort (theta 1))
    (apply_typed functionExact leftTwice) (apply_typed functionExact (.var 1))

@[simp] theorem congruenceMotive_point (left codomain function right witness : Tower.Tm n) :
    subst (FormationSensitiveBasedIdentity.pointSub right witness) (congruenceMotive left codomain function) =
      .id codomain (.app function left) (.app function right) := by
  simp only [congruenceMotive, subst, FormationSensitiveBasedIdentity.pointSub_doubleWeaken]
  rfl

def congruenceTerm (domain left codomain function right witness : Tower.Tm n) : Tower.Tm n :=
  identityEliminateApp domain left (.lam (.lam (congruenceMotive left codomain function)))
    (.refl (.app function left)) right witness

/-- A proof of equality gives an actual native proof of equality after any
typed function. Applying this with domain `Id A a b` is the local-region
interchangeability rule: uniqueness is supplied, never globally assumed. -/
theorem congruence_typed {domain left codomain function right witness : Tower.Tm n}
    (formed : ContextFormation (NativeIdentityLevelInstantiation.rules theta signature) context)
    (domainFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context domain (sortTm (theta 0)))
    (codomainFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context codomain (sortTm (theta 1)))
    (leftTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context left domain)
    (rightTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context right domain)
    (functionTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context function (arrow domain codomain))
    (witnessTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context witness (.id domain left right)) :
    Judgment (NativeIdentityLevelInstantiation.rules theta signature) context
      (congruenceTerm domain left codomain function right witness)
      (.id codomain (.app function left) (.app function right)) := by
  have methodTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context (.refl (.app function left))
      (subst (FormationSensitiveBasedIdentity.reflexivitySub left) (congruenceMotive left codomain function)) := by
    change Typing _ _ _ (subst (FormationSensitiveBasedIdentity.pointSub left (.refl left)) _)
    rw [congruenceMotive_point]
    exact .reflIntro (apply_typed functionTyped leftTyped)
  simpa only [congruenceTerm, congruenceMotive_point] using
    ofBody_point formed domainFormed leftTyped (congruenceMotive left codomain function)
      (congruenceMotive_formed codomainFormed leftTyped functionTyped)
      methodTyped rightTyped witnessTyped

theorem congruence_reflexivity (domain left codomain function : Tower.Tm n) :
    (NativeIdentityLevelInstantiation.rules theta signature).computation.step
      (congruenceTerm domain left codomain function left (.refl left))
      (.refl (.app function left)) := NativeIdentityLevelInstantiation.beta theta signature ..

/-- Leaving a local context exports its hypothesis as a Pi binder. -/
def conditionalCongruence (domain left codomain function right : Tower.Tm n) : Tower.Tm n :=
  .lam (congruenceTerm (rename wk domain) (rename wk left) (rename wk codomain)
    (rename wk function) (rename wk right) (.var 0))

theorem conditionalCongruence_typed {domain left codomain function right : Tower.Tm n}
    (formed : ContextFormation (NativeIdentityLevelInstantiation.rules theta signature) context)
    (domainFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context domain
      (sortTm (theta 0)))
    (codomainFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context codomain
      (sortTm (theta 1)))
    (leftTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context left domain)
    (rightTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context right domain)
    (functionTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context function
      (arrow domain codomain)) :
    Judgment (NativeIdentityLevelInstantiation.rules theta signature) context
      (conditionalCongruence domain left codomain function right)
      (arrow (.id domain left right) (.id codomain (.app function left) (.app function right))) := by
  have hypothesisFormed := Typing.idForm domainFormed (.sort (theta 0)) leftTyped rightTyped
  have resultFormed := Typing.idForm codomainFormed (.sort (theta 1))
    (apply_typed functionTyped leftTyped) (apply_typed functionTyped rightTyped)
  have functionWeakened : Typing (NativeIdentityLevelInstantiation.rules theta signature)
      (.snoc context (.id domain left right)) (rename wk function)
      (arrow (rename wk domain) (rename wk codomain)) := by
    simpa only [arrow, rename, rename_comp, liftRen, wk, Fin.cases_succ]
      using functionTyped.weaken (extension := .id domain left right)
  have inside := congruence_typed (.snoc formed hypothesisFormed (.sort (theta 0)))
    domainFormed.weaken codomainFormed.weaken leftTyped.weaken rightTyped.weaken
    functionWeakened (Typing.var 0)
  exact ⟨formed, .lamIntro
    (.piForm hypothesisFormed (.sort (theta 0)) resultFormed.weaken (.sort (theta 1))
      (.sorts (theta 0) (theta 1))) (.sort (.max (theta 0) (theta 1))) inside.typing⟩

/-- A separately derived equality witness discharges the same exported
conditional theorem. No new constant, axiom or kernel rule is registered. -/
theorem discharge_conditional {domain left codomain function right witness : Tower.Tm n}
    (formed : ContextFormation (NativeIdentityLevelInstantiation.rules theta signature) context)
    (domainFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context domain
      (sortTm (theta 0)))
    (codomainFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context codomain
      (sortTm (theta 1)))
    (leftTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context left domain)
    (rightTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context right domain)
    (functionTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context function
      (arrow domain codomain))
    (witnessTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context witness
      (.id domain left right)) :
    Judgment (NativeIdentityLevelInstantiation.rules theta signature) context
      (.app (conditionalCongruence domain left codomain function right) witness)
      (.id codomain (.app function left) (.app function right)) :=
  ⟨formed, apply_typed
    (conditionalCongruence_typed formed domainFormed codomainFormed leftTyped rightTyped functionTyped).typing
    witnessTyped⟩

theorem congruenceMotive_substitute (substitution : Sub Tower.Head n m)
    (left codomain function : Tower.Tm n) :
    subst (liftSub (liftSub substitution)) (congruenceMotive left codomain function) =
      congruenceMotive (subst substitution left) (subst substitution codomain)
        (subst substitution function) := by
  simp only [congruenceMotive, subst, FormationSensitiveBasedIdentity.doubleWeaken,
    subst_liftSub_wk, liftSub]
  rfl

/-- Reindexing preserves the actual retained motive and proof term, not just
its proposition. -/
theorem congruenceTerm_substitute (substitution : Sub Tower.Head n m)
    (domain left codomain function right witness : Tower.Tm n) :
    subst substitution (congruenceTerm domain left codomain function right witness) =
      congruenceTerm (subst substitution domain) (subst substitution left)
        (subst substitution codomain) (subst substitution function)
        (subst substitution right) (subst substitution witness) := by
  simp only [congruenceTerm, identityEliminateApp, subst, congruenceMotive_substitute]

/-- Discharging the exported hypothesis has the exact native body as its
beta reduct. This is an equation of proof syntax, independent of typing. -/
theorem discharge_beta (domain left codomain function right witness : Tower.Tm n) :
    Conv (NativeIdentityLevelInstantiation.rules theta signature).headEq
      (.app (conditionalCongruence domain left codomain function right) witness)
      (congruenceTerm domain left codomain function right witness)
      (NativeIdentityLevelInstantiation.rules theta signature).computation := by
  have beta : Conv (NativeIdentityLevelInstantiation.rules theta signature).headEq
      (.app (conditionalCongruence domain left codomain function right) witness)
      (inst0 witness (congruenceTerm (rename wk domain) (rename wk left) (rename wk codomain)
        (rename wk function) (rename wk right) (.var 0)))
      (NativeIdentityLevelInstantiation.rules theta signature).computation := .rel _ _ (.betaPi _ _)
  have cancel (term : Tower.Tm n) : subst (subst0 witness) (rename wk term) = term :=
    inst0_rename_wk witness term
  simpa only [inst0, congruenceTerm_substitute, cancel, subst, subst0, Fin.cases_zero] using beta

/-- A region can be supplied pointwise by a theorem or kept as an ordinary
context variable. In both cases the actual region witness is a typed term. -/
theorem region_application {carrier first second left right codomain function uniqueness : Tower.Tm n}
    (formed : ContextFormation (NativeIdentityLevelInstantiation.rules theta signature) context)
    (carrierFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context carrier
      (sortTm (theta 0)))
    (firstTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context first carrier)
    (secondTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context second carrier)
    (codomainFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context codomain
      (sortTm (theta 1)))
    (leftTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context left
      (.id carrier first second))
    (rightTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context right
      (.id carrier first second))
    (functionTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context function
      (arrow (.id carrier first second) codomain))
    (uniquenessTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context uniqueness
      (.id (.id carrier first second) left right)) :
    Judgment (NativeIdentityLevelInstantiation.rules theta signature) context
      (congruenceTerm (.id carrier first second) left codomain function right uniqueness)
      (.id codomain (.app function left) (.app function right)) :=
  congruence_typed formed (.idForm carrierFormed (.sort (theta 0)) firstTyped secondTyped)
    codomainFormed leftTyped rightTyped functionTyped uniquenessTyped

/-- An assumed non-reflexive witness remains neutral at the J root. This
does not claim non-derivability or normalization of the complete calculus. -/
theorem neutral_witness_no_iota
    (opacity : OpaqueRelatorExtension.Opacity signature)
    (domain left codomain function right : Tower.Tm (n + 1))
    (output : Tower.Tm (n + 1)) :
    ¬ (NativeIdentityLevelInstantiation.rules theta signature).computation.step
      (congruenceTerm domain left codomain function right (.var 0)) output := by
  intro root
  obtain ⟨_, impossible, _⟩ := FormationSensitiveNativeIdentity.identity_root_iff.mp
    ((NativeIdentityLevelInstantiation.root_iff theta opacity).mp root)
  cases impossible

/-- The same native construction has conditional export, typed discharge,
an exact beta equation, and reflexivity computation. The context and level
instance are fixed across all clauses. -/
theorem scoped_identity_contract {domain left codomain function right witness : Tower.Tm n}
    (formed : ContextFormation (NativeIdentityLevelInstantiation.rules theta signature) context)
    (domainFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context domain
      (sortTm (theta 0)))
    (codomainFormed : Typing (NativeIdentityLevelInstantiation.rules theta signature) context codomain
      (sortTm (theta 1)))
    (leftTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context left domain)
    (rightTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context right domain)
    (functionTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context function
      (arrow domain codomain))
    (witnessTyped : Typing (NativeIdentityLevelInstantiation.rules theta signature) context witness
      (.id domain left right)) :
    Judgment (NativeIdentityLevelInstantiation.rules theta signature) context
        (conditionalCongruence domain left codomain function right)
        (arrow (.id domain left right) (.id codomain (.app function left) (.app function right))) ∧
      Judgment (NativeIdentityLevelInstantiation.rules theta signature) context
        (.app (conditionalCongruence domain left codomain function right) witness)
        (.id codomain (.app function left) (.app function right)) ∧
      Conv (NativeIdentityLevelInstantiation.rules theta signature).headEq
        (.app (conditionalCongruence domain left codomain function right) witness)
        (congruenceTerm domain left codomain function right witness)
        (NativeIdentityLevelInstantiation.rules theta signature).computation ∧
      (NativeIdentityLevelInstantiation.rules theta signature).computation.step
        (congruenceTerm domain left codomain function left (.refl left))
        (.refl (.app function left)) :=
  ⟨conditionalCongruence_typed formed domainFormed codomainFormed leftTyped rightTyped functionTyped,
    discharge_conditional formed domainFormed codomainFormed leftTyped rightTyped functionTyped witnessTyped,
    discharge_beta .., congruence_reflexivity ..⟩

namespace Controls

/-- An ordinary five-entry native context: B, C, f, p, q. Its endpoints are
different variables, not a singleton or reflexivity-only input selection. -/
def telescope (theta : Nat → LevelExpr Nat) : Tower.Ctx 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil (sortTm (theta 0))) (sortTm (theta 1)))
    (arrow (.var 1) (.var 0))) (.var 2)) (.var 3)

theorem context_formed (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head) :
    ContextFormation (NativeIdentityLevelInstantiation.rules theta signature) (telescope theta) := by
  exact .snoc (.snoc (.snoc
    (.snoc (.snoc .nil (.headType (.sort (theta 0))) (.sort (.succ (theta 0))))
      (.headType (.sort (theta 1))) (.sort (.succ (theta 1))))
    (.piForm (.var 1) (.sort (theta 0)) (.var 1) (.sort (theta 1))
      (.sorts (theta 0) (theta 1))) (.sort (.max (theta 0) (theta 1))))
    (.var 2) (.sort (theta 0))) (.var 3) (.sort (theta 0))

theorem conditional_example (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head) :
    Judgment (NativeIdentityLevelInstantiation.rules theta signature) (telescope theta)
      (conditionalCongruence (.var 4) (.var 1) (.var 3) (.var 2) (.var 0))
      (arrow (.id (.var 4) (.var 1) (.var 0))
        (.id (.var 3) (.app (.var 2) (.var 1)) (.app (.var 2) (.var 0)))) :=
  conditionalCongruence_typed (context_formed theta signature)
    (.var 4) (.var 3) (.var 1) (.var 0) (.var 2)

def assumedContext (theta : Nat → LevelExpr Nat) : Tower.Ctx 6 :=
  .snoc (telescope theta) (.id (.var 4) (.var 1) (.var 0))

theorem assumed_context_formed (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head) :
    ContextFormation (NativeIdentityLevelInstantiation.rules theta signature) (assumedContext theta) :=
  .snoc (context_formed theta signature)
    (.idForm (.var 4) (.sort (theta 0)) (.var 1) (.var 0)) (.sort (theta 0))

theorem assumed_example (theta : Nat → LevelExpr Nat) (signature : Signature Tower.Head) :
    Judgment (NativeIdentityLevelInstantiation.rules theta signature) (assumedContext theta)
      (congruenceTerm (.var 5) (.var 2) (.var 4) (.var 3) (.var 1) (.var 0))
      (.id (.var 4) (.app (.var 3) (.var 2)) (.app (.var 3) (.var 1))) :=
  congruence_typed
    (assumed_context_formed theta signature)
    (.var 5) (.var 4) (.var 2) (.var 1) (.var 3) (.var 0)

/-- The export really retains a hypothesis. Its advertised type is not the
unconditional conclusion. This is syntactic scope accountability, not a
claim of non-derivability of the conclusion by all possible proofs. -/
theorem export_is_not_unconditional :
    (arrow (.id (.var 4) (.var 1) (.var 0))
      (.id (.var 3) (.app (.var 2) (.var 1)) (.app (.var 2) (.var 0))) : Tower.Tm 5) ≠
      .id (.var 3) (.app (.var 2) (.var 1)) (.app (.var 2) (.var 0)) := by decide

theorem assumed_endpoints_remain_distinct :
    (.var (2 : Fin 6) : Tower.Tm 6) ≠ .var 1 := by decide

theorem assumed_example_neutral (theta : Nat → LevelExpr Nat)
    {signature : Signature Tower.Head} (opacity : OpaqueRelatorExtension.Opacity signature)
    (output : Tower.Tm 6) :
    ¬ (NativeIdentityLevelInstantiation.rules theta signature).computation.step
      (congruenceTerm (.var 5) (.var 2) (.var 4) (.var 3) (.var 1) (.var 0)) output :=
  neutral_witness_no_iota opacity (.var 5) (.var 2) (.var 4) (.var 3) (.var 1) output

/-- Executable syntax discriminators supplement the typing theorems above;
they do not replace theorem checking or claim a general native evaluator. -/
def syntaxChecks : List Bool :=
  [decide ((.var (2 : Fin 6) : Tower.Tm 6) ≠ .var 1),
   decide ((arrow (.id (.var 4) (.var 1) (.var 0))
     (.id (.var 3) (.app (.var 2) (.var 1)) (.app (.var 2) (.var 0))) : Tower.Tm 5) ≠
       .id (.var 3) (.app (.var 2) (.var 1)) (.app (.var 2) (.var 0))),
   match (conditionalCongruence (.var 5) (.var 2) (.var 4) (.var 3) (.var 1) : Tower.Tm 6) with
   | .lam body => decide (inst0 (.var 0) body =
       congruenceTerm (.var 5) (.var 2) (.var 4) (.var 3) (.var 1) (.var 0))
   | _ => false,
   decide ((congruenceTerm (.var 5) (.var 2) (.var 4) (.var 3) (.var 1) (.var 0) : Tower.Tm 6) ≠
     congruenceTerm (.var 5) (.var 2) (.var 4) (.var 3) (.var 2) (.refl (.var 2)))]

theorem syntaxChecks_pass : syntaxChecks = [true, true, true, true] := by decide

#eval syntaxChecks

end Controls

#print axioms ofBody_point
#print axioms congruenceMotive_formed
#print axioms congruence_typed
#print axioms congruence_reflexivity
#print axioms conditionalCongruence_typed
#print axioms discharge_conditional
#print axioms congruenceTerm_substitute
#print axioms discharge_beta
#print axioms region_application
#print axioms neutral_witness_no_iota
#print axioms scoped_identity_contract
#print axioms Controls.conditional_example
#print axioms Controls.assumed_context_formed
#print axioms Controls.assumed_example
#print axioms Controls.export_is_not_unconditional
#print axioms Controls.assumed_endpoints_remain_distinct
#print axioms Controls.assumed_example_neutral
#print axioms Controls.syntaxChecks_pass

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentIdentityRegions
