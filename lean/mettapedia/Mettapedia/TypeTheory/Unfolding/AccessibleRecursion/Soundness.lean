import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Judgments
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Semantics

/-!
# Soundness in the standard model over `Prop`

The standard meaning of the signature (`sigValue`) sends implication to `→`,
every quantifier to `∀`, and the recursor to a chosen interpretation.  An
environment for `Γ ++ signature A P` is *standard* when it reads every
symbol this way.

Under a standard environment the codes mean what they say:

* `accCode R a` holds exactly when `a` is accessible for `R` (`denote_accCode`);
* `respCode R F` holds exactly when `F` respects `R` (`denote_respCode`);
* `resultEq u v` holds exactly when `u = v` (`denote_resultEq`);
* `falsum` holds exactly when every proposition holds (`denote_falsum`).

A judgment is *valid* for an interpretation of the recursor when it holds in
every standard environment satisfying its hypotheses; a definitional or
propositional equality is valid when both sides denote the same value there.

* Every rule except the two unfolding rules is sound for **any**
  interpretation of the recursor (`noWitness_sound`).
* The unfolding rules are sound for every interpretation that satisfies the
  unfolding equation at accessible points of respecting steps
  (`UnfoldSound`), so the strong and carved variants are sound for such
  interpretations (`strong_sound`, `carved_sound`).
* The semantic recursor `recSem` is such an interpretation
  (`standardRecursor_unfoldSound`), so neither variant derives `falsum` in the
  empty context (`strong_consistent`, `carved_consistent`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Unfolding.AccessibleRecursion

open Mettapedia.Logic
open Mettapedia.TypeTheory.Unfolding
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT

variable {A P : Ty}

/-- The empty environment. -/
def emptyEnvironment : Environment Prop [] where
  lookup := fun symbol => nomatch symbol

/-- The standard environment of the signature, for an interpretation of the
recursor: implication is `→` and every quantifier is `∀`. -/
def sigEnvironmentAt (recursor : Val (recTy A P)) : Environment Prop (signature A P) :=
  Environment.extend recursor <| Environment.extend (fun premise conclusion => premise → conclusion) <|
    Environment.extend (fun body => ∀ x, body x) <| Environment.extend (fun body => ∀ x, body x) <|
    Environment.extend (fun body => ∀ x, body x) <| Environment.extend (fun body => ∀ x, body x) <|
    Environment.extend (fun body => ∀ x, body x) emptyEnvironment

/-- The standard meaning of a symbol. -/
def sigValue (recursor : Val (recTy A P)) {T : Ty} (symbol : Var (signature A P) T) : Val T :=
  (sigEnvironmentAt recursor).lookup symbol

@[simp] theorem sigValue_rec (recursor : Val (recTy A P)) :
    sigValue recursor (recSymbol A P) = recursor := rfl

@[simp] theorem sigValue_imp (recursor : Val (recTy A P)) :
    sigValue recursor (impSymbol A P) = fun premise conclusion => premise → conclusion := rfl

/-- Every quantifier symbol means universal quantification. -/
@[simp] theorem sigValue_quantifier (recursor : Val (recTy A P)) {σ : Ty}
    (quantifier : Var (signature A P) (quantTy σ)) :
    sigValue recursor quantifier = fun body => ∀ x, body x := by
  cases quantifier with
  | succ quantifier =>
      cases quantifier with
      | succ quantifier =>
          cases quantifier with
          | zero => rfl
          | succ quantifier =>
              cases quantifier with
              | zero => rfl
              | succ quantifier =>
                  cases quantifier with
                  | zero => rfl
                  | succ quantifier =>
                      cases quantifier with
                      | zero => rfl
                      | succ quantifier =>
                          cases quantifier with
                          | zero => rfl
                          | succ quantifier => cases quantifier

/-- An environment reads every symbol by its standard meaning. -/
def Standard (recursor : Val (recTy A P)) {Γ : List Ty}
    (environment : Environment Prop (Γ ++ signature A P)) : Prop :=
  ∀ {T : Ty} (symbol : Var (signature A P) T),
    environment.lookup (liftSymbol Γ symbol) = sigValue recursor symbol

theorem Standard.extend {recursor : Val (recTy A P)} {Γ : List Ty} {B : Ty}
    {environment : Environment Prop (Γ ++ signature A P)} (standard : Standard recursor environment)
    (value : Val B) : Standard (Γ := B :: Γ) recursor (Environment.extend value environment) :=
  fun symbol => standard symbol

theorem Standard.lookup {recursor : Val (recTy A P)} {Γ : List Ty}
    {environment : Environment Prop (Γ ++ signature A P)} (standard : Standard recursor environment)
    {T : Ty} (symbol : Var (signature A P) T) :
    environment.lookup (liftSymbol Γ symbol) = sigValue recursor symbol :=
  standard symbol

/-- The standard environment of the empty data context. -/
def sigEnvironment (recursor : Val (recTy A P)) : Environment Prop ([] ++ signature A P) :=
  sigEnvironmentAt recursor

theorem sigEnvironment_standard (recursor : Val (recTy A P)) :
    Standard (Γ := []) recursor (sigEnvironment recursor) :=
  fun _ => rfl

@[simp] theorem liftSymbol_cons {S : List Ty} {T B : Ty} {Γ : List Ty} (symbol : Var S T) :
    liftSymbol (B :: Γ) symbol = .succ (liftSymbol Γ symbol) := rfl

@[simp] theorem lookup_extend_zero {Γ : List Ty} {B : Ty} (value : Val B)
    (environment : Environment Prop Γ) :
    (Environment.extend value environment).lookup .zero = value := rfl

@[simp] theorem lookup_extend_succ {Γ : List Ty} {B T : Ty} (value : Val B)
    (environment : Environment Prop Γ) (v : Var Γ T) :
    (Environment.extend value environment).lookup (.succ v) = environment.lookup v := rfl

/-! ## Denotations of the codes -/

section Denotations

variable {recursor : Val (recTy A P)} {Γ : List Ty}
  {environment : Environment Prop (Γ ++ signature A P)}

theorem denote_sym (standard : Standard recursor environment) {T : Ty}
    (symbol : Var (signature A P) T) : (sym Γ symbol).denote environment = sigValue recursor symbol :=
  standard symbol

theorem denote_imp (standard : Standard recursor environment) (premise conclusion : Tm A P Γ prop) :
    (imp premise conclusion).denote environment =
      (premise.denote environment → conclusion.denote environment) := by
  change (sym Γ (impSymbol A P)).denote environment (premise.denote environment)
    (conclusion.denote environment) = _
  rw [denote_sym standard]
  rfl

theorem denote_all (standard : Standard recursor environment) {σ : Ty}
    (quantifier : Var (signature A P) (quantTy σ)) (body : Tm A P Γ (.arr σ prop)) :
    (all quantifier body).denote environment = ∀ x, body.denote environment x := by
  change (sym Γ quantifier).denote environment (body.denote environment) = _
  rw [denote_sym standard, sigValue_quantifier]

theorem renamingEnvironment_weakening {Δ : List Ty} {B : Ty} (value : Val B)
    (base : Environment Prop Δ) :
    renamingEnvironment weakening (Environment.extend value base) = base := by
  apply Environment.ext
  intro T v
  rfl

@[simp] theorem denote_wk {Δ : List Ty} {B T : Ty} (term : Tm A P Δ T) (value : Val B)
    (base : Environment Prop (Δ ++ signature A P)) :
    (wk (B := B) term).denote (Environment.extend value base) = term.denote base := by
  change (term.rename weakening).denote _ = _
  rw [Term.denote_rename, renamingEnvironment_weakening]

theorem denote_inst {B T : Ty} (body : Tm A P (B :: Γ) T) (argument : Tm A P Γ B) :
    (inst body argument).denote environment =
      body.denote (Environment.extend (argument.denote environment) environment) := by
  change (Term.substitute (newestSubstitution argument) body).denote environment = _
  rw [Term.denote_substitute, substitutionEnvironment_newest]

theorem denote_falsum (standard : Standard recursor environment) :
    (falsum : Tm A P Γ prop).denote environment = ∀ p : Prop, p := by
  unfold falsum
  rw [denote_all standard]
  rfl

theorem denote_resultEq (standard : Standard recursor environment) (left right : Tm A P Γ P) :
    (resultEq left right).denote environment ↔ left.denote environment = right.denote environment := by
  simp only [resultEq, all, imp, sym, Term.denote, liftSymbol_cons, lookup_extend_succ,
    lookup_extend_zero, standard.lookup, sigValue_quantifier, sigValue_imp, denote_wk]
  constructor
  · intro leibniz
    exact leibniz (fun value => left.denote environment = value) rfl
  · intro same Q holds
    rw [← same]
    exact holds

theorem denote_recTerm (standard : Standard recursor environment) (R : Tm A P Γ (relTy A))
    (F : Tm A P Γ (stepTy A P)) (point : Tm A P Γ A) :
    (recTerm R F point).denote environment =
      recursor (R.denote environment) (F.denote environment) (point.denote environment) := by
  simp only [recTerm, sym, Term.denote, standard.lookup, sigValue_rec]

theorem denote_unfoldTerm (standard : Standard recursor environment) (R : Tm A P Γ (relTy A))
    (F : Tm A P Γ (stepTy A P)) (point : Tm A P Γ A) :
    (unfoldTerm R F point).denote environment =
      F.denote environment (point.denote environment)
        (recursor (R.denote environment) (F.denote environment)) := by
  simp only [unfoldTerm, recTerm, sym, Term.denote, liftSymbol_cons, lookup_extend_succ,
    lookup_extend_zero, standard.lookup, sigValue_rec, denote_wk]

/-- The impredicative accessibility code means accessibility. -/
theorem denote_accCode (standard : Standard recursor environment) (R : Tm A P Γ (relTy A))
    (point : Tm A P Γ A) :
    (accCode R point).denote environment ↔ Acc (R.denote environment) (point.denote environment) := by
  simp only [accCode, all, imp, sym, Term.denote, liftSymbol_cons, lookup_extend_succ,
    lookup_extend_zero, standard.lookup, sigValue_quantifier, sigValue_imp, denote_wk]
  constructor
  · intro closed
    exact closed (Acc (R.denote environment)) fun x below => Acc.intro x below
  · intro accessible X closed
    exact Acc.rec (motive := fun x _ => X x) (fun x _ ih => closed x fun y related => ih y related)
      accessible

/-- The respect code means respect. -/
theorem denote_respCode (standard : Standard recursor environment) (R : Tm A P Γ (relTy A))
    (F : Tm A P Γ (stepTy A P)) :
    (respCode R F).denote environment ↔ RespectsSem (R.denote environment) (F.denote environment) := by
  simp only [respCode, resultEq, all, imp, sym, Term.denote, liftSymbol_cons, lookup_extend_succ,
    lookup_extend_zero, standard.lookup, sigValue_quantifier, sigValue_imp, denote_wk]
  constructor
  · intro respects x g g' agree
    exact respects x g g' (fun y related Q holds => Eq.subst (motive := Q) (agree y related) holds)
      (fun value => F.denote environment x g = value) rfl
  · intro respects x g g' agree Q holds
    have same : F.denote environment x g = F.denote environment x g' :=
      respects x g g' fun y related => agree y related (fun value => g y = value) rfl
    rw [← same]
    exact holds

end Denotations

/-! ## Validity and soundness -/

/-- Every hypothesis holds. -/
def HypsHold {Γ : List Ty} (environment : Environment Prop (Γ ++ signature A P))
    (hyps : List (Tm A P Γ prop)) : Prop :=
  ∀ hypothesis ∈ hyps, hypothesis.denote environment

/-- Validity of a judgment for an interpretation of the recursor. -/
def Valid (recursor : Val (recTy A P)) : Judgment A P → Prop
  | .holds Γ hyps goal => ∀ environment : Environment Prop (Γ ++ signature A P),
      Standard recursor environment → HypsHold environment hyps → goal.denote environment
  | .conv Γ hyps _ left right => ∀ environment : Environment Prop (Γ ++ signature A P),
      Standard recursor environment → HypsHold environment hyps →
        left.denote environment = right.denote environment
  | .equal Γ hyps _ left right => ∀ environment : Environment Prop (Γ ++ signature A P),
      Standard recursor environment → HypsHold environment hyps →
        left.denote environment = right.denote environment

/-- The unfolding equation holds at accessible points of respecting steps. -/
def UnfoldSound (recursor : Val (recTy A P)) : Prop :=
  ∀ (R : Val A → Val A → Prop) (F : Val A → (Val A → Val P) → Val P) (point : Val A),
    Acc R point → RespectsSem R F → recursor R F point = F point (recursor R F)

theorem hypsHold_wk {Γ : List Ty} {B : Ty} {environment : Environment Prop (Γ ++ signature A P)}
    {hyps : List (Tm A P Γ prop)} (value : Val B) (holds : HypsHold environment hyps) :
    HypsHold (Γ := B :: Γ) (Environment.extend value environment) (wkHyps hyps) := by
  intro hypothesis member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  rw [denote_wk]
  exact holds original originalMember

theorem hypsHold_cons {Γ : List Ty} {environment : Environment Prop (Γ ++ signature A P)}
    {hyps : List (Tm A P Γ prop)} {first : Tm A P Γ prop} (firstHolds : first.denote environment)
    (holds : HypsHold environment hyps) : HypsHold environment (first :: hyps) := by
  intro hypothesis member
  cases member with
  | head => exact firstHolds
  | tail _ rest => exact holds hypothesis rest

/-- The shared rules are sound; the propositional unfolding needs the
unfolding equation. -/
theorem sharedRule_sound (recursor : Val (recTy A P)) (witness : Bool)
    (unfoldSound : witness = true → UnfoldSound recursor) :
    ∀ premises conclusion, SharedRule witness premises conclusion →
      (∀ premise ∈ premises, Valid recursor premise) → Valid recursor conclusion := by
  intro premises conclusion rule valid
  cases rule with
  | hyp member =>
      intro environment _ holds
      exact holds _ member
  | impIntro premise conclusion' =>
      intro environment standard holds
      rw [denote_imp standard]
      intro premiseHolds
      exact valid _ mem₀ environment standard (hypsHold_cons premiseHolds holds)
  | impElim premise conclusion' =>
      intro environment standard holds
      have implication := valid _ mem₀ environment standard holds
      rw [denote_imp standard] at implication
      exact implication (valid _ mem₁ environment standard holds)
  | allIntro quantifier body =>
      intro environment standard holds
      rw [denote_all standard]
      intro value
      have bodyHolds := valid _ mem₀ (Environment.extend value environment) (standard.extend value)
        (hypsHold_wk value holds)
      change (wk body).denote (Environment.extend value environment) value at bodyHolds
      rwa [denote_wk] at bodyHolds
  | allElim quantifier body witnessTerm =>
      intro environment standard holds
      have allHolds := valid _ mem₀ environment standard holds
      rw [denote_all standard] at allHolds
      exact allHolds _
  | convert source target =>
      intro environment standard holds
      have sourceHolds := valid _ mem₀ environment standard holds
      have same := valid _ mem₁ environment standard holds
      change source.denote environment = target.denote environment at same
      rw [← same]
      exact sourceHolds
  | equalOfConv left right => exact valid (.conv _ _ _ left right) mem₀
  | equalSymm left right =>
      intro environment standard holds
      exact (valid _ mem₀ environment standard holds).symm
  | equalTrans left middle right =>
      intro environment standard holds
      exact (valid _ mem₀ environment standard holds).trans (valid _ mem₁ environment standard holds)
  | equalApp function function' argument argument' =>
      intro environment standard holds
      have functions := valid _ mem₀ environment standard holds
      have arguments := valid _ mem₁ environment standard holds
      change function.denote environment (argument.denote environment) =
        function'.denote environment (argument'.denote environment)
      rw [show function.denote environment = function'.denote environment from functions,
        show argument.denote environment = argument'.denote environment from arguments]
  | equalLam body body' =>
      intro environment standard holds
      funext value
      exact valid _ mem₀ (Environment.extend value environment) (standard.extend value)
        (hypsHold_wk value holds)
  | transport motive left right =>
      intro environment standard holds
      have same := valid _ mem₀ environment standard holds
      have motiveHolds := valid _ mem₁ environment standard holds
      change left.denote environment = right.denote environment at same
      change (inst motive left).denote environment at motiveHolds
      change (inst motive right).denote environment
      rw [denote_inst] at motiveHolds ⊢
      rwa [← same]
  | unfoldEqual R F point witnessTrue =>
      intro environment standard holds
      have accessible := (denote_accCode standard R point).mp (valid _ mem₀ environment standard holds)
      have respects := (denote_respCode standard R F).mp (valid _ mem₁ environment standard holds)
      change (recTerm R F point).denote environment = (unfoldTerm R F point).denote environment
      rw [denote_recTerm standard, denote_unfoldTerm standard]
      exact unfoldSound witnessTrue _ _ _ accessible respects

/-- The carved conversion rules are sound for every interpretation. -/
theorem convRule_sound (recursor : Val (recTy A P)) :
    ∀ premises conclusion, ConvRule premises conclusion →
      (∀ premise ∈ premises, Valid recursor premise) → Valid recursor conclusion := by
  intro premises conclusion rule valid
  cases rule with
  | beta left right convertible =>
      intro environment _ _
      exact BetaConv.denote convertible environment
  | symm left right =>
      intro environment standard holds
      exact (valid _ mem₀ environment standard holds).symm
  | trans left middle right =>
      intro environment standard holds
      exact (valid _ mem₀ environment standard holds).trans (valid _ mem₁ environment standard holds)
  | app function function' argument argument' =>
      intro environment standard holds
      have functions := valid _ mem₀ environment standard holds
      have arguments := valid _ mem₁ environment standard holds
      change function.denote environment (argument.denote environment) =
        function'.denote environment (argument'.denote environment)
      rw [show function.denote environment = function'.denote environment from functions,
        show argument.denote environment = argument'.denote environment from arguments]
  | lam body body' =>
      intro environment standard holds
      funext value
      exact valid _ mem₀ (Environment.extend value environment) (standard.extend value)
        (hypsHold_wk value holds)

/-- The definitional unfolding is sound for interpretations satisfying the
unfolding equation. -/
theorem unfoldRule_sound (recursor : Val (recTy A P)) (unfoldSound : UnfoldSound recursor) :
    ∀ premises conclusion, UnfoldRule premises conclusion →
      (∀ premise ∈ premises, Valid recursor premise) → Valid recursor conclusion := by
  intro premises conclusion rule valid
  cases rule with
  | unfold R F point =>
      intro environment standard holds
      have accessible := (denote_accCode standard R point).mp (valid _ mem₀ environment standard holds)
      have respects := (denote_respCode standard R F).mp (valid _ mem₁ environment standard holds)
      change (recTerm R F point).denote environment = (unfoldTerm R F point).denote environment
      rw [denote_recTerm standard, denote_unfoldTerm standard]
      exact unfoldSound _ _ _ accessible respects

/-- Without either unfolding rule, derivations are sound for **every**
interpretation of the recursor. -/
theorem noWitness_sound (recursor : Val (recTy A P)) {judgment : Judgment A P}
    (derivation : Derives (RuleUnion (SharedRule false) ConvRule) judgment) :
    Valid recursor judgment := by
  refine Derives.least (Valid recursor) ?_ derivation
  intro premises conclusion rule valid
  rcases rule with rule | rule
  · exact sharedRule_sound recursor false (fun impossible => nomatch impossible) _ _ rule valid
  · exact convRule_sound recursor _ _ rule valid

/-- **The strong variant is sound** for interpretations satisfying the
unfolding equation. -/
theorem strong_sound {recursor : Val (recTy A P)} (unfoldSound : UnfoldSound recursor)
    {judgment : Judgment A P} (derivation : Strong A P judgment) : Valid recursor judgment := by
  refine Derives.least (Valid recursor) ?_ derivation
  intro premises conclusion rule valid
  rcases rule with (rule | rule) | rule
  · exact sharedRule_sound recursor true (fun _ => unfoldSound) _ _ rule valid
  · exact convRule_sound recursor _ _ rule valid
  · exact unfoldRule_sound recursor unfoldSound _ _ rule valid

/-- The carved variant is sound for the same interpretations. -/
theorem carved_sound {recursor : Val (recTy A P)} (unfoldSound : UnfoldSound recursor)
    {judgment : Judgment A P} (derivation : Carved A P judgment) : Valid recursor judgment :=
  strong_sound unfoldSound (carved_restricts derivation)

/-! ## The standard recursor and consistency -/

/-- The standard interpretation of the recursor. -/
def standardRecursor : Val (recTy A P) := fun R F point => recSem R F point

theorem standardRecursor_unfoldSound : UnfoldSound (standardRecursor (A := A) (P := P)) :=
  fun _ _ _ accessible respects => recSem_unfold respects accessible

/-- **Consistency.**  The strong variant does not derive `falsum` in the empty
context. -/
theorem strong_consistent : ¬ Strong A P (.holds [] [] falsum) := by
  intro derivation
  have valid := strong_sound standardRecursor_unfoldSound derivation
  have falsumHolds := valid (sigEnvironment standardRecursor) (sigEnvironment_standard _)
    (fun _ member => nomatch member)
  rw [denote_falsum (sigEnvironment_standard _)] at falsumHolds
  exact falsumHolds False

/-- The carved variant does not derive `falsum` in the empty context. -/
theorem carved_consistent : ¬ Carved A P (.holds [] [] falsum) :=
  fun derivation => strong_consistent (carved_restricts derivation)

/-- A goal that fails in some standard environment satisfying the hypotheses
is not derivable in the strong variant. -/
theorem strong_not_derivable_of_countermodel {Γ : List Ty} {hyps : List (Tm A P Γ prop)}
    {goal : Tm A P Γ prop} (environment : Environment Prop (Γ ++ signature A P))
    (standard : Standard standardRecursor environment) (holds : HypsHold environment hyps)
    (fails : ¬ goal.denote environment) : ¬ Strong A P (.holds Γ hyps goal) :=
  fun derivation => fails (strong_sound standardRecursor_unfoldSound derivation environment standard holds)

end Mettapedia.TypeTheory.Unfolding.AccessibleRecursion
