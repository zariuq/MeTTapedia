import Mettapedia.GSLT.Dedukti.TypingSubstitution
import Mettapedia.GSLT.Dedukti.Phenomena
import Mettapedia.Languages.OpenTheory.EtaNotDerivable

/-!
# Two routes for higher-order logic: the native kernel and the Dedukti encoding

OpenTheory is hosted natively: its nine primitive rules are the existing
`Mettapedia.Languages.OpenTheory` kernel.  It is also translated to Dedukti by
Holide (A. Assaf and G. Burel, *Translating HOL to Dedukti*, PxTP 2015).
`holTheory` is the part of the theory file of that translation that the
statements below use, transcribed from
`libraries/theories/opentheory.dk` of the Dedukti distribution: the types,
the terms with the rule `term (arr a b) ⟶ term a → term b`, equality, proofs,
and the constants `REFL` and `ABS_THM`.

Holide's translation of a HOL term uses the abstraction and application of
the framework for those of HOL, and the rule above makes the HOL terms of a
function type the functions of the framework.  That one choice decides what
the route keeps.

* **Beta.**  Natively `betaConv` is a primitive rule: from the redex
  `(λ x. f x) y` it gives the theorem `⊢ (λ x. f x) y = f y`
  (existing `Eta.betaTheorem_derives`), and the redex and its contractum are
  two different terms (`native_redex_ne_contractum`).  In the encoding the
  statement of that theorem is convertible to a statement of reflexivity
  (`beta_statement_conv`), and `REFL` proves it (`beta_by_refl`); the theory
  file defines `BETA_CONV` as `REFL`.  The route preserves the theorem.  It
  does not preserve the rule application, and it does not keep a redex apart
  from its contractum.
* **Eta.**  Natively the eta sequent `⊢ (λ x. f x) = f` is not derivable from
  the nine rules without axioms (existing `Eta.eta_not_derivable`); a theorem
  that uses eta carries the eta axiom in its provenance.  In the encoding the
  eta sequent has a proof with no axiom (`eta_by_abs`): the native rule `abs`
  becomes the constant `ABS_THM`, whose two function arguments range over the
  functions of the framework, so that it is extensionality of functions, and
  eta is an instance.  The route does not reflect derivability from the
  axiom-free kernel, and it does not keep the provenance of eta.
* **Eta by reflexivity.**  With beta conversion only, the eta statement and
  the statement of reflexivity are distinct normal terms
  (`eta_statement_not_joinable`), so `REFL` alone does not prove eta.  With
  conversion modulo eta, which the checker offers as an option, they are
  convertible (`eta_statement_betaEta`).

`two_routes_at_beta` and `two_routes_at_eta` state the two sides together.

What is modelled and what is not.  The theory is transcribed from the local
theory file, and the Dedukti checker confirms the behaviours on that file:
it accepts beta by `REFL` and eta by `ABS_THM`, rejects eta by `REFL`, and
accepts eta by `REFL` with the eta option.  The translation function from
the native terms and theorems to the terms of the encoding is not
formalized: the statements on the two sides are about the same sequents by
the definition of the translation in the paper, not by a Lean theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.TwoRoutes

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig Decl lookupBody lift subst subst0 Ctx)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-! ## The theory of the encoding -/

/-- The type of HOL types. -/
def holType : Term := .con "type"

def bool : Term := .con "bool"

def arr (domain codomain : Term) : Term := .app (.app (.con "arr") domain) codomain

/-- The type of the HOL terms of a HOL type. -/
def termOf (type : Term) : Term := .app (.con "term") type

/-- HOL equality at a type. -/
def equal (type left right : Term) : Term := .app (.app (.app (.con "eq") type) left) right

/-- The type of the proofs of a HOL proposition. -/
def proof (proposition : Term) : Term := .app (.con "proof") proposition

def refl (type term : Term) : Term := .app (.app (.con "REFL") type) term

def absThm (domain codomain left right pointwise : Term) : Term :=
  .app (.app (.app (.app (.app (.con "ABS_THM") domain) codomain) left) right) pointwise

/-- The declared type of `ABS_THM`:
`Π a b : type. Π f g : term a → term b. (Π x : term a. proof (eq b (f x) (g x))) → proof (eq (arr a b) f g)`. -/
def absType : Term :=
  .pi holType (.pi holType
    (.pi (.pi (termOf (.var 1)) (termOf (.var 1)))
      (.pi (.pi (termOf (.var 2)) (termOf (.var 2)))
        (.pi (.pi (termOf (.var 3))
            (proof (equal (.var 3) (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))
          (proof (equal (arr (.var 4) (.var 3)) (.var 2) (.var 1)))))))

/-- The declarations used here, in the order of the theory file. -/
def holSig : Sig :=
  [.const "type" (.srt .type), .const "bool" holType,
    .const "arr" (.pi holType (.pi holType holType)),
    .const "term" (.pi holType (.srt .type)),
    .const "eq" (.pi holType (termOf (arr (.var 0) (arr (.var 0) bool)))),
    .const "proof" (.pi (termOf bool) (.srt .type)),
    .const "REFL" (.pi holType (.pi (termOf (.var 0)) (proof (equal (.var 1) (.var 0) (.var 0))))),
    .const "ABS_THM" absType]

/-- `term (arr a b) ⟶ term a → term b`. -/
def termArrow : RewriteRule :=
  ⟨termOf (arr (.var 1) (.var 0)), .pi (termOf (.var 1)) (termOf (.var 1))⟩

/-- **The theory of the Holide encoding**, as far as it is used here. -/
def holTheory : Theory := Theory.ofSig holSig [termArrow]

def holCover : holTheory.Cover :=
  Theory.coverOfRules holSig [termArrow] fun name => by simp [holSig, lookupBody]

theorem hol_closedBodies : holTheory.ClosedBodies := fun name term defined => by
  have undefined : lookupBody holSig name = none := by simp [holSig, lookupBody]
  exact absurd (undefined.symm.trans defined) (by simp)

theorem hol_closedTypes : holTheory.ClosedTypes := by
  intro name type declared
  rcases Phenomena.lookupType_mem declared with member | ⟨_, member⟩
  · simp only [holSig, List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
      ⟨_, rfl⟩
    all_goals exact wellScoped_of_test _ 0 (by decide)
  · simp [holSig] at member

/-- Typing in the encoding. -/
abbrev Hol (context : Ctx) (term type : Term) : Prop := LambdaPiModulo holTheory context term type

variable {context : Ctx}

theorem type_termOf {type : Term} (typed : Hol context type holType) :
    Hol context (termOf type) (.srt .type) := by
  have constant : Hol context (.con "term") (.pi holType (.srt .type)) := .con rfl
  exact .app constant typed

theorem type_bool : Hol context bool holType := .con rfl

theorem type_arr {domain codomain : Term} (domainTyped : Hol context domain holType)
    (codomainTyped : Hol context codomain holType) : Hol context (arr domain codomain) holType := by
  have constant : Hol context (.con "arr") (.pi holType (.pi holType holType)) := .con rfl
  exact .app (.app constant domainTyped) codomainTyped

/-- The declared rule, as a conversion. -/
theorem conv_arrow (domain codomain : Term) :
    Conv holTheory (termOf (arr domain codomain)) (.pi (termOf domain) (termOf (lift 1 0 codomain))) := by
  have instance_ := Conv.rule (theory := holTheory) (rule := termArrow) (List.mem_singleton.mpr rfl)
    fun index => if index = 0 then codomain else domain
  simpa [termArrow, termOf, arr, inst, instantiate, lift_zero] using instance_

theorem weaken {term type : Term} (inserted : Term) (typed : Hol context term type) :
    Hol (inserted :: context) (lift 1 0 term) (lift 1 0 type) :=
  HasType.weaken hol_closedBodies hol_closedTypes inserted typed

theorem function_formed {domain codomain : Term} (domainTyped : Hol context domain holType)
    (codomainTyped : Hol context codomain holType) :
    Hol context (.pi (termOf domain) (termOf (lift 1 0 codomain))) (.srt .type) :=
  .pi (type_termOf domainTyped) (type_termOf (weaken (termOf domain) codomainTyped)) arrow_rule

/-- A HOL term of a function type is a function of the framework. -/
theorem as_function {domain codomain function : Term} (domainTyped : Hol context domain holType)
    (codomainTyped : Hol context codomain holType)
    (typed : Hol context function (termOf (arr domain codomain))) :
    Hol context function (.pi (termOf domain) (termOf (lift 1 0 codomain))) :=
  .conv typed (conv_arrow domain codomain) (function_formed domainTyped codomainTyped)

theorem apply_typed {domain codomain function argument : Term}
    (domainTyped : Hol context domain holType) (codomainTyped : Hol context codomain holType)
    (functionTyped : Hol context function (termOf (arr domain codomain)))
    (argumentTyped : Hol context argument (termOf domain)) :
    Hol context (.app function argument) (termOf codomain) := by
  have applied := HasType.app (as_function domainTyped codomainTyped functionTyped) argumentTyped
  have shape : subst0 argument (termOf (lift 1 0 codomain)) = termOf codomain := by
    simp [subst0, subst, termOf, subst_lift_cancel]
  rwa [shape] at applied

theorem equal_typed {type left right : Term} (typeTyped : Hol context type holType)
    (leftTyped : Hol context left (termOf type)) (rightTyped : Hol context right (termOf type)) :
    Hol context (equal type left right) (termOf bool) := by
  have constant : Hol context (.con "eq") (.pi holType (termOf (arr (.var 0) (arr (.var 0) bool)))) :=
    .con rfl
  have first := HasType.app constant typeTyped
  have shape : subst0 type (termOf (arr (.var 0) (arr (.var 0) bool))) =
      termOf (arr type (arr type bool)) := by
    simp [subst0, subst, termOf, arr, bool]
  rw [shape] at first
  exact apply_typed typeTyped type_bool
    (apply_typed typeTyped (type_arr typeTyped type_bool) first leftTyped) rightTyped

theorem proof_typed {proposition : Term} (typed : Hol context proposition (termOf bool)) :
    Hol context (proof proposition) (.srt .type) := by
  have constant : Hol context (.con "proof") (.pi (termOf bool) (.srt .type)) := .con rfl
  exact .app constant typed

/-- `REFL a t : proof (eq a t t)`. -/
theorem refl_typed {type term : Term} (typeTyped : Hol context type holType)
    (termTyped : Hol context term (termOf type)) :
    Hol context (refl type term) (proof (equal type term term)) := by
  have constant : Hol context (.con "REFL")
      (.pi holType (.pi (termOf (.var 0)) (proof (equal (.var 1) (.var 0) (.var 0))))) := .con rfl
  have first := HasType.app constant typeTyped
  have firstShape : subst0 type (.pi (termOf (.var 0)) (proof (equal (.var 1) (.var 0) (.var 0)))) =
      .pi (termOf type) (proof (equal (lift 1 0 type) (.var 0) (.var 0))) := by
    simp [subst0, subst, termOf, proof, equal]
  rw [firstShape] at first
  have second := HasType.app first termTyped
  have secondShape : subst0 term (proof (equal (lift 1 0 type) (.var 0) (.var 0))) =
      proof (equal type term term) := by
    simp [subst0, subst, proof, equal, subst_lift_cancel]
  rw [secondShape] at second
  exact second

/-! ## Beta -/

/-- **The statement of a beta theorem is a statement of reflexivity**, up to
the conversion of the framework. -/
theorem beta_statement_conv (type annotation body argument : Term) :
    Conv holTheory (proof (equal type (.app (.lam annotation body) argument) (subst0 argument body)))
      (proof (equal type (subst0 argument body) (subst0 argument body))) :=
  Conv.app (.refl _) (Conv.app (Conv.app (.refl _) (Conv.beta annotation body argument)) (.refl _))

/-- **`REFL` proves the beta theorem.**  No step of the proof corresponds to
the native rule. -/
theorem beta_by_refl {type annotation body argument : Term} {sort : Srt}
    (typeTyped : Hol context type holType)
    (contractumTyped : Hol context (subst0 argument body) (termOf type))
    (statementFormed : Hol context
      (proof (equal type (.app (.lam annotation body) argument) (subst0 argument body))) (.srt sort)) :
    Hol context (refl type (subst0 argument body))
      (proof (equal type (.app (.lam annotation body) argument) (subst0 argument body))) :=
  .conv (refl_typed typeTyped contractumTyped)
    (.symm _ _ (beta_statement_conv type annotation body argument)) statementFormed

/-- Natively the redex and its contractum are different terms. -/
theorem native_redex_ne_contractum (name : Languages.OpenTheory.Name)
    (domain codomain : Languages.OpenTheory.Ty) (argumentName : Languages.OpenTheory.Name) :
    Languages.OpenTheory.Eta.redex name domain codomain argumentName ≠
      Languages.OpenTheory.Eta.contractum name domain codomain argumentName := by
  intro same
  have terms := congrArg Languages.OpenTheory.CanonicalTerm.term same
  simp [Languages.OpenTheory.Eta.redex, Languages.OpenTheory.Eta.contractum,
    Languages.OpenTheory.Eta.expansionDB] at terms

/-- **The two routes at beta.**  Natively: a derivation by the primitive rule
of an equation between two different terms.  In the encoding: the statement
is a statement of reflexivity. -/
theorem two_routes_at_beta (name : Languages.OpenTheory.Name)
    (domain codomain : Languages.OpenTheory.Ty) (argumentName : Languages.OpenTheory.Name) :
    (Mettapedia.Logic.Derives
        (Languages.OpenTheory.PolicyPrimitiveRule Languages.OpenTheory.emptyAxiomPolicy)
        (Languages.OpenTheory.Eta.betaTheorem name domain codomain argumentName) ∧
      Languages.OpenTheory.Eta.redex name domain codomain argumentName ≠
        Languages.OpenTheory.Eta.contractum name domain codomain argumentName) ∧
    ∀ type annotation body argument : Term,
      Conv holTheory
        (proof (equal type (.app (.lam annotation body) argument) (subst0 argument body)))
        (proof (equal type (subst0 argument body) (subst0 argument body))) :=
  ⟨⟨Languages.OpenTheory.Eta.betaTheorem_derives name domain codomain argumentName,
      native_redex_ne_contractum name domain codomain argumentName⟩,
    beta_statement_conv⟩

/-! ## Eta -/

/-- The eta expansion `λ x. f x` of a function. -/
def expansion (annotation function : Term) : Term :=
  .lam annotation (.app (lift 1 0 function) (.var 0))

/-- The statement `(λ x. f x) = f` of the encoding. -/
def etaStatement (type annotation function : Term) : Term :=
  proof (equal type (expansion annotation function) function)

/-- The statement `f = f`. -/
def reflStatement (type function : Term) : Term := proof (equal type function function)

/-- A substitution under a lift at the outermost cutoff. -/
theorem subst_lift_zero {target amount : Nat} (below : target < amount) (replacement term : Term) :
    subst target replacement (lift amount 0 term) = lift (amount - 1) 0 term := by
  simpa using subst_lift_above term target amount 0 replacement below

/-- **`ABS_THM` applied**: from a pointwise equation between two functions of
the framework, their equation. -/
theorem abs_typed {domain codomain left right pointwise : Term}
    (domainTyped : Hol context domain holType) (codomainTyped : Hol context codomain holType)
    (leftTyped : Hol context left (.pi (termOf domain) (termOf (lift 1 0 codomain))))
    (rightTyped : Hol context right (.pi (termOf domain) (termOf (lift 1 0 codomain))))
    (pointwiseTyped : Hol context pointwise
      (.pi (termOf domain)
        (proof (equal (lift 1 0 codomain) (.app (lift 1 0 left) (.var 0))
          (.app (lift 1 0 right) (.var 0)))))) :
    Hol context (absThm domain codomain left right pointwise)
      (proof (equal (arr domain codomain) left right)) := by
  have constant : Hol context (.con "ABS_THM") absType := .con rfl
  have first := HasType.app constant domainTyped
  simp [subst0, subst, termOf, proof, equal, arr, holType, lift_lift_same] at first
  have second := HasType.app first codomainTyped
  simp [subst0, subst, lift_lift_same, subst_lift_zero, lift_zero] at second
  have third := HasType.app second leftTyped
  simp [subst0, subst, lift_lift_same, subst_lift_zero, lift_zero] at third
  have fourth := HasType.app third rightTyped
  simp [subst0, subst, subst_lift_zero, lift_zero] at fourth
  have fifth := HasType.app fourth pointwiseTyped
  simp [subst0, subst, subst_lift_zero, lift_zero] at fifth
  exact fifth

/-- The eta expansion of a HOL term of a function type is a function of the
framework. -/
theorem expansion_typed {domain codomain function : Term}
    (domainTyped : Hol context domain holType) (codomainTyped : Hol context codomain holType)
    (functionTyped : Hol context function (termOf (arr domain codomain))) :
    Hol context (expansion (termOf domain) function)
      (.pi (termOf domain) (termOf (lift 1 0 codomain))) := by
  have variable_ : Hol (termOf domain :: context) (.var 0) (termOf (lift 1 0 domain)) := .var rfl
  have body := apply_typed (weaken (termOf domain) domainTyped) (weaken (termOf domain) codomainTyped)
    (weaken (termOf domain) functionTyped) variable_
  exact .lam (type_termOf domainTyped) (type_termOf (weaken (termOf domain) codomainTyped))
    arrow_rule body

/-- **The eta sequent has a proof in the encoding, with beta conversion only
and no axiom.** -/
theorem eta_by_abs {domain codomain function : Term}
    (domainTyped : Hol context domain holType) (codomainTyped : Hol context codomain holType)
    (functionTyped : Hol context function (termOf (arr domain codomain))) :
    Hol context
      (absThm domain codomain (expansion (termOf domain) function) function
        (.lam (termOf domain) (refl (lift 1 0 codomain) (.app (lift 1 0 function) (.var 0)))))
      (etaStatement (arr domain codomain) (termOf domain) function) := by
  have expanded := expansion_typed domainTyped codomainTyped functionTyped
  have variable_ : Hol (termOf domain :: context) (.var 0) (termOf (lift 1 0 domain)) := .var rfl
  have liftedDomain := weaken (termOf domain) domainTyped
  have liftedCodomain := weaken (termOf domain) codomainTyped
  have applied := apply_typed liftedDomain liftedCodomain (weaken (termOf domain) functionTyped)
    variable_
  have natural : Hol context
      (.lam (termOf domain) (refl (lift 1 0 codomain) (.app (lift 1 0 function) (.var 0))))
      (.pi (termOf domain)
        (proof (equal (lift 1 0 codomain) (.app (lift 1 0 function) (.var 0))
          (.app (lift 1 0 function) (.var 0))))) :=
    .lam (type_termOf domainTyped) (proof_typed (equal_typed liftedCodomain applied applied))
      arrow_rule (refl_typed liftedCodomain applied)
  have liftedExpansion := weaken (termOf domain) expanded
  have expansionApplied : Hol (termOf domain :: context)
      (.app (lift 1 0 (expansion (termOf domain) function)) (.var 0)) (termOf (lift 1 0 codomain)) := by
    have step : Hol (termOf domain :: context)
        (.app (lift 1 0 (expansion (termOf domain) function)) (.var 0))
        (subst0 (.var 0) (termOf (lift 1 1 (lift 1 0 codomain)))) :=
      HasType.app liftedExpansion variable_
    have shape : subst0 (.var 0) (termOf (lift 1 1 (lift 1 0 codomain))) =
        termOf (lift 1 0 codomain) := congrArg termOf (subst0_var_lift (lift 1 0 codomain))
    rwa [shape] at step
  have betaStep : Conv holTheory (.app (lift 1 0 (expansion (termOf domain) function)) (.var 0))
      (.app (lift 1 0 function) (.var 0)) := by
    have beta := Conv.beta (theory := holTheory) (lift 1 0 (termOf domain))
      (lift 1 1 (.app (lift 1 0 function) (.var 0))) (.var 0)
    rw [subst0_var_lift] at beta
    simpa [expansion, lift] using beta
  have required : Hol context
      (.pi (termOf domain)
        (proof (equal (lift 1 0 codomain) (.app (lift 1 0 (expansion (termOf domain) function)) (.var 0))
          (.app (lift 1 0 function) (.var 0))))) (.srt .type) :=
    .pi (type_termOf domainTyped)
      (proof_typed (equal_typed liftedCodomain expansionApplied applied)) arrow_rule
  have pointwise := HasType.conv natural
    (Conv.pi (.refl _)
      (Conv.app (.refl _) (Conv.app (Conv.app (.refl _) (.symm _ _ betaStep)) (.refl _))))
    required
  exact abs_typed domainTyped codomainTyped expanded
    (as_function domainTyped codomainTyped functionTyped) pointwise

/-- Removing a variable that was just skipped gives the term back. -/
theorem unbind_lift (term : Term) :
    ∀ cutoff : Nat, LFBetaEta.unbind cutoff (lift 1 cutoff term) = some term := by
  induction term with
  | var index =>
      intro cutoff
      by_cases below : index < cutoff
      · simp [lift, LFBetaEta.unbind, below]
      · have notBelow : ¬ index + 1 < cutoff := by omega
        have notSame : index + 1 ≠ cutoff := by omega
        simp [lift, LFBetaEta.unbind, below, notBelow, notSame]
  | srt sort => intro cutoff; rfl
  | con name => intro cutoff; rfl
  | pi domain body ihDomain ihBody => intro cutoff; simp [lift, LFBetaEta.unbind, ihDomain, ihBody]
  | lam domain body ihDomain ihBody => intro cutoff; simp [lift, LFBetaEta.unbind, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      intro cutoff; simp [lift, LFBetaEta.unbind, ihFunction, ihArgument]

/-- **With conversion modulo eta the eta statement is a statement of
reflexivity.**  The conversion is the existing beta-eta conversion. -/
theorem eta_statement_betaEta (type annotation function : Term) :
    LFBetaEta.Conv [] (etaStatement type annotation function) (reflStatement type function) :=
  .common
    (.app .refl (.app (.app .refl (.eta (unbind_lift function 0))) .refl))
    .refl

/-- The eta statement at a variable of type `bool → bool`. -/
def etaAtVariable : Term := etaStatement (arr bool bool) (termOf bool) (.var 0)

def reflAtVariable : Term := reflStatement (arr bool bool) (.var 0)

/-- **With beta conversion only, the eta statement and the statement of
reflexivity have no common reduct**: `REFL` alone does not prove eta. -/
theorem eta_statement_not_joinable : ¬ Joinable holTheory etaAtVariable reflAtVariable :=
  not_joinable_of_normal (normal_of_normalTest holCover etaAtVariable (by decide))
    (normal_of_normalTest holCover reflAtVariable (by decide)) (by decide)

/-- Under confluence of the encoding they are not convertible. -/
theorem eta_statement_not_conv (confluent : Confluent (Step holTheory)) :
    ¬ Conv holTheory etaAtVariable reflAtVariable :=
  fun convertible => eta_statement_not_joinable ((conv_iff_joinable confluent).mp convertible)

/-- **The two routes at eta.**  Natively the eta sequent is not derivable
without axioms.  In the encoding it has a proof, for every function of every
function type, in every context. -/
theorem two_routes_at_eta (name : Languages.OpenTheory.Name)
    (domain codomain : Languages.OpenTheory.Ty) :
    (∀ {out : Languages.OpenTheory.Theorem},
        Mettapedia.Logic.Derives
          (Languages.OpenTheory.PolicyPrimitiveRule Languages.OpenTheory.emptyAxiomPolicy) out →
        out.sequent ≠ ⟨∅, Languages.OpenTheory.Eta.equation name domain codomain⟩) ∧
      ∀ (context : Ctx) (source target function : Term),
        Hol context source holType → Hol context target holType →
        Hol context function (termOf (arr source target)) →
          ∃ evidence, Hol context evidence
            (etaStatement (arr source target) (termOf source) function) :=
  ⟨fun derivation => Languages.OpenTheory.Eta.eta_not_derivable name domain codomain derivation,
    fun _ _ _ _ sourceTyped targetTyped functionTyped =>
      ⟨_, eta_by_abs sourceTyped targetTyped functionTyped⟩⟩

#print axioms refl_typed
#print axioms beta_by_refl
#print axioms two_routes_at_beta
#print axioms abs_typed
#print axioms eta_by_abs
#print axioms eta_statement_betaEta
#print axioms eta_statement_not_joinable
#print axioms two_routes_at_eta

end Mettapedia.GSLT.Dedukti.TwoRoutes
