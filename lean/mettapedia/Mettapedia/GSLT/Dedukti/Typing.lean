import Mettapedia.GSLT.Dedukti.Rewriting
import Mettapedia.GSLT.LanguageDef.LF.ConversionProfileChecker

/-!
# Typing modulo declared rewrite rules

`HasType profile theory` is the typing judgment of a pure type system over the
two sorts of the existing λΠ syntax, with typed constants, in which the
conversion rule uses the conversion declared by the theory.

* The sorts, axioms and product rules are an existing `LFProfile.Profile`.
  At `LFProfile.basic` the judgment is the λΠ-calculus modulo the rules of the
  theory.  At any profile and the empty theory it is the pure type system of
  that profile, with beta conversion.
* Dependent function types, typed constants, and the conversion rule
  `t : A`, `A ≡ B`, `B : s` give `t : B`, where `≡` is `Conv theory`.

Why a new judgment.  `LFTyping.HasType` fixes conversion to a common
beta-delta reduct and its abstraction rule does not ask that the product be
formed.  `LFConversionProfileChecker.Deriv` is parametric in the profile but
fixes conversion to a common beta-delta-eta reduct.  Neither takes declared
rules.  The judgment here maps into the second one when there is no declared
rule and reduction is confluent (`HasType.toDeriv`); confluence is used
exactly to turn a declared conversion into a common reduct.

The generation lemmas (`HasType.sort_inv`, `pi_inv`, `lam_inv`, `app_inv`,
`var_inv`, `con_inv`) invert the judgment up to conversion.

## Where the three obligations are used

* **Confluence**: `HasType.toDeriv`, and the negative example
  `example_untypable_without_rule`.
* **Type preservation** (`SubjectReduction`): `HasType.reduces`, and with
  confluence `typed_common_reduct`: two convertible terms of one type have a
  common reduct of that type, so that the test "reduce both sides" stays
  inside the typed terms.
* **Termination**, at one term (`Acc`): `typed_normal_form`, a typed term has
  a normal form of the same type.  With confluence that normal form is unique
  (`normal_form_unique`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig sigT lookupBody lift subst subst0 Ctx ctxLookup)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-- **Typing modulo the declared conversion of a theory.** -/
inductive HasType (profile : Profile) (theory : Theory) : Ctx → Term → Term → Prop where
  | sort {context : Ctx} {source target : Srt} :
      profile.sortAxiom source = some target →
      HasType profile theory context (.srt source) (.srt target)
  | var {context : Ctx} {index : Nat} {type : Term} :
      ctxLookup context index = some type →
      HasType profile theory context (.var index) type
  | con {context : Ctx} {name : String} {type : Term} :
      theory.constType name = some type →
      HasType profile theory context (.con name) type
  | pi {context : Ctx} {domain body : Term} {domainSort codomainSort resultSort : Srt} :
      HasType profile theory context domain (.srt domainSort) →
      HasType profile theory (domain :: context) body (.srt codomainSort) →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈ profile.products →
      HasType profile theory context (.pi domain body) (.srt resultSort)
  | lam {context : Ctx} {domain body bodyType : Term} {domainSort codomainSort resultSort : Srt} :
      HasType profile theory context domain (.srt domainSort) →
      HasType profile theory (domain :: context) bodyType (.srt codomainSort) →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈ profile.products →
      HasType profile theory (domain :: context) body bodyType →
      HasType profile theory context (.lam domain body) (.pi domain bodyType)
  | app {context : Ctx} {function argument domain bodyType : Term} :
      HasType profile theory context function (.pi domain bodyType) →
      HasType profile theory context argument domain →
      HasType profile theory context (.app function argument) (subst0 argument bodyType)
  | conv {context : Ctx} {term source target : Term} {sort : Srt} :
      HasType profile theory context term source →
      Conv theory source target →
      HasType profile theory context target (.srt sort) →
      HasType profile theory context term target

/-- **The λΠ-calculus modulo the rules of a theory.** -/
abbrev LambdaPiModulo (theory : Theory) : Ctx → Term → Term → Prop :=
  HasType LFProfile.basic theory

variable {profile : Profile} {theory : Theory}

/-- A larger profile and a larger theory type at least as much. -/
theorem HasType.mono {small large : Profile} {less more : Theory}
    (profiles : LFProfile.Subsumed small large) (theories : less.Extends more)
    {context : Ctx} {term type : Term} (typed : HasType small less context term type) :
    HasType large more context term type := by
  induction typed with
  | sort axiomHolds => exact .sort (profiles.1 _ _ axiomHolds)
  | var found => exact .var found
  | con declared => exact .con (theories.constType _ _ declared)
  | pi _ _ rule ihDomain ihBody => exact .pi ihDomain ihBody (profiles.2 _ rule)
  | lam _ _ rule _ ihDomain ihBodyType ihBody =>
      exact .lam ihDomain ihBodyType (profiles.2 _ rule) ihBody
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument
  | conv _ convertible _ ihTerm ihTarget => exact .conv ihTerm (convertible.mono theories) ihTarget

/-! ## Generation -/

theorem HasType.sort_inv {context : Ctx} {source : Srt} {type : Term}
    (typed : HasType profile theory context (.srt source) type) :
    ∃ target, profile.sortAxiom source = some target ∧ Conv theory (.srt target) type := by
  generalize same : Term.srt source = term at typed
  induction typed with
  | sort axiomHolds => cases same; exact ⟨_, axiomHolds, .refl _⟩
  | var _ => cases same
  | con _ => cases same
  | pi _ _ _ _ _ => cases same
  | lam _ _ _ _ _ _ _ => cases same
  | app _ _ _ _ => cases same
  | conv _ convertible _ ihTerm _ =>
      obtain ⟨target, axiomHolds, earlier⟩ := ihTerm same
      exact ⟨target, axiomHolds, .trans _ _ _ earlier convertible⟩

theorem HasType.var_inv {context : Ctx} {index : Nat} {type : Term}
    (typed : HasType profile theory context (.var index) type) :
    ∃ declared, ctxLookup context index = some declared ∧ Conv theory declared type := by
  generalize same : Term.var index = term at typed
  induction typed with
  | sort _ => cases same
  | var found => cases same; exact ⟨_, found, .refl _⟩
  | con _ => cases same
  | pi _ _ _ _ _ => cases same
  | lam _ _ _ _ _ _ _ => cases same
  | app _ _ _ _ => cases same
  | conv _ convertible _ ihTerm _ =>
      obtain ⟨declared, found, earlier⟩ := ihTerm same
      exact ⟨declared, found, .trans _ _ _ earlier convertible⟩

theorem HasType.con_inv {context : Ctx} {name : String} {type : Term}
    (typed : HasType profile theory context (.con name) type) :
    ∃ declared, theory.constType name = some declared ∧ Conv theory declared type := by
  generalize same : Term.con name = term at typed
  induction typed with
  | sort _ => cases same
  | var _ => cases same
  | con found => cases same; exact ⟨_, found, .refl _⟩
  | pi _ _ _ _ _ => cases same
  | lam _ _ _ _ _ _ _ => cases same
  | app _ _ _ _ => cases same
  | conv _ convertible _ ihTerm _ =>
      obtain ⟨declared, found, earlier⟩ := ihTerm same
      exact ⟨declared, found, .trans _ _ _ earlier convertible⟩

theorem HasType.pi_inv {context : Ctx} {domain body type : Term}
    (typed : HasType profile theory context (.pi domain body) type) :
    ∃ domainSort codomainSort resultSort,
      HasType profile theory context domain (.srt domainSort) ∧
      HasType profile theory (domain :: context) body (.srt codomainSort) ∧
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈ profile.products ∧
      Conv theory (.srt resultSort) type := by
  generalize same : Term.pi domain body = term at typed
  induction typed with
  | sort _ => cases same
  | var _ => cases same
  | con _ => cases same
  | pi domainTyped bodyTyped rule _ _ =>
      cases same
      exact ⟨_, _, _, domainTyped, bodyTyped, rule, .refl _⟩
  | lam _ _ _ _ _ _ _ => cases same
  | app _ _ _ _ => cases same
  | conv _ convertible _ ihTerm _ =>
      obtain ⟨domainSort, codomainSort, resultSort, domainTyped, bodyTyped, rule, earlier⟩ :=
        ihTerm same
      exact ⟨domainSort, codomainSort, resultSort, domainTyped, bodyTyped, rule,
        .trans _ _ _ earlier convertible⟩

theorem HasType.lam_inv {context : Ctx} {domain body type : Term}
    (typed : HasType profile theory context (.lam domain body) type) :
    ∃ bodyType domainSort codomainSort resultSort,
      HasType profile theory context domain (.srt domainSort) ∧
      HasType profile theory (domain :: context) bodyType (.srt codomainSort) ∧
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈ profile.products ∧
      HasType profile theory (domain :: context) body bodyType ∧
      Conv theory (.pi domain bodyType) type := by
  generalize same : Term.lam domain body = term at typed
  induction typed with
  | sort _ => cases same
  | var _ => cases same
  | con _ => cases same
  | pi _ _ _ _ _ => cases same
  | lam domainTyped bodyTypeTyped rule bodyTyped _ _ _ =>
      cases same
      exact ⟨_, _, _, _, domainTyped, bodyTypeTyped, rule, bodyTyped, .refl _⟩
  | app _ _ _ _ => cases same
  | conv _ convertible _ ihTerm _ =>
      obtain ⟨bodyType, domainSort, codomainSort, resultSort, domainTyped, bodyTypeTyped, rule,
        bodyTyped, earlier⟩ := ihTerm same
      exact ⟨bodyType, domainSort, codomainSort, resultSort, domainTyped, bodyTypeTyped, rule,
        bodyTyped, .trans _ _ _ earlier convertible⟩

theorem HasType.app_inv {context : Ctx} {function argument type : Term}
    (typed : HasType profile theory context (.app function argument) type) :
    ∃ domain bodyType,
      HasType profile theory context function (.pi domain bodyType) ∧
      HasType profile theory context argument domain ∧
      Conv theory (subst0 argument bodyType) type := by
  generalize same : Term.app function argument = term at typed
  induction typed with
  | sort _ => cases same
  | var _ => cases same
  | con _ => cases same
  | pi _ _ _ _ _ => cases same
  | lam _ _ _ _ _ _ _ => cases same
  | app functionTyped argumentTyped _ _ =>
      cases same
      exact ⟨_, _, functionTyped, argumentTyped, .refl _⟩
  | conv _ convertible _ ihTerm _ =>
      obtain ⟨domain, bodyType, functionTyped, argumentTyped, earlier⟩ := ihTerm same
      exact ⟨domain, bodyType, functionTyped, argumentTyped, .trans _ _ _ earlier convertible⟩

/-! ## The existing profile-parametric judgment -/

/-- **Where confluence is used**: with no declared rule and confluent
reduction, a derivation here is a derivation of the existing
profile-parametric judgment, whose conversion is by a common reduct. -/
theorem HasType.toDeriv {signature : Sig}
    (confluent : Confluent (Step (Theory.ofSig signature [])))
    {context : Ctx} {term type : Term}
    (typed : HasType profile (Theory.ofSig signature []) context term type) :
    LFConversionProfileChecker.Deriv profile signature context term type := by
  induction typed with
  | sort axiomHolds => exact .sort axiomHolds
  | var found => exact .var found
  | con declared => exact .con declared
  | pi _ _ rule ihDomain ihBody => exact .pi ihDomain ihBody rule
  | lam _ _ rule _ ihDomain ihBodyType ihBody => exact .lam ihDomain ihBody ihBodyType rule
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument
  | conv _ convertible _ ihTerm _ =>
      obtain ⟨common, leftReduces, rightReduces⟩ := (conv_iff_joinable confluent).mp convertible
      exact .conv ihTerm (.common
        (LFBetaEta.Reduces.ofBetaDelta ((reduces_ofSig_iff signature).mp leftReduces))
        (LFBetaEta.Reduces.ofBetaDelta ((reduces_ofSig_iff signature).mp rightReduces)))

/-! ## Type preservation and termination, where they are used -/

/-- **Type preservation**: a step of a typed term keeps its type. -/
def SubjectReduction (profile : Profile) (theory : Theory) : Prop :=
  ∀ (context : Ctx) (term next type : Term),
    HasType profile theory context term type → Step theory term next →
      HasType profile theory context next type

/-- Under type preservation, reduction keeps the type. -/
theorem HasType.reduces (preserved : SubjectReduction profile theory) {context : Ctx}
    {term next type : Term} (typed : HasType profile theory context term type)
    (reduces : Reduces theory term next) : HasType profile theory context next type := by
  induction reduces with
  | refl => exact typed
  | tail _ step ih => exact preserved _ _ _ _ ih step

/-- **Where confluence and type preservation are used together**: two
convertible terms of one type have a common reduct of that type. -/
theorem typed_common_reduct (confluent : Confluent (Step theory))
    (preserved : SubjectReduction profile theory) {context : Ctx} {left right type : Term}
    (leftTyped : HasType profile theory context left type)
    (convertible : Conv theory left right) :
    ∃ common, Reduces theory left common ∧ Reduces theory right common ∧
      HasType profile theory context common type := by
  obtain ⟨common, leftReduces, rightReduces⟩ := (conv_iff_joinable confluent).mp convertible
  exact ⟨common, leftReduces, rightReduces, leftTyped.reduces preserved leftReduces⟩

/-- A term from which every reduction sequence is finite reduces to a normal
term. -/
theorem exists_normal_of_acc {α : Type} {relation : α → α → Prop} {source : α}
    (accessible : Acc (fun next term => relation term next) source) :
    ∃ normal, Relation.ReflTransGen relation source normal ∧ IsNormal relation normal := by
  induction accessible with
  | intro term _ ih =>
      by_cases reducible : ∃ next, relation term next
      · obtain ⟨next, step⟩ := reducible
        obtain ⟨normal, reduces, isNormal⟩ := ih next step
        exact ⟨normal, .head step reduces, isNormal⟩
      · exact ⟨term, .refl, fun next step => reducible ⟨next, step⟩⟩

/-- **Where termination and type preservation are used**: a typed term from
which every reduction sequence is finite has a normal form of its type. -/
theorem typed_normal_form (preserved : SubjectReduction profile theory) {context : Ctx}
    {term type : Term} (typed : HasType profile theory context term type)
    (terminates : Acc (fun next term => Step theory term next) term) :
    ∃ normal, Reduces theory term normal ∧ IsNormal (Step theory) normal ∧
      HasType profile theory context normal type := by
  obtain ⟨normal, reduces, isNormal⟩ := exists_normal_of_acc terminates
  exact ⟨normal, reduces, isNormal, typed.reduces preserved reduces⟩

/-- **Where confluence is used**: the normal form is unique. -/
theorem normal_form_unique (confluent : Confluent (Step theory)) {term first second : Term}
    (firstReduces : Reduces theory term first) (firstNormal : IsNormal (Step theory) first)
    (secondReduces : Reduces theory term second) (secondNormal : IsNormal (Step theory) second) :
    first = second := by
  obtain ⟨common, firstJoin, secondJoin⟩ := confluent term first second firstReduces secondReduces
  exact (firstNormal.reflTransGen_eq firstJoin).symm.trans (secondNormal.reflTransGen_eq secondJoin)

/-! ## A worked theory: one rule that makes a term typable

The example of Cousineau and Dowek (Example 1 of their paper): two type
constants `P` and `Q` and the rule `P ⟶ Q → Q`.  The term `λ f : P. λ x : Q. f x`
is typable modulo the rule and, under confluence, not without it. -/

namespace Example

/-- Two type constants. -/
def signature : Sig := [.const "P" (.srt .type), .const "Q" (.srt .type)]

/-- The rule `P ⟶ Q → Q`. -/
def unfoldP : RewriteRule := ⟨.con "P", .pi (.con "Q") (.con "Q")⟩

/-- The theory with the rule. -/
def withRule : Theory := Theory.ofSig signature [unfoldP]

/-- The theory without it. -/
def withoutRule : Theory := Theory.ofSig signature []

/-- `λ f : P. λ x : Q. f x`. -/
def term : Term := .lam (.con "P") (.lam (.con "Q") (.app (.var 1) (.var 0)))

/-- `P → Q → Q`. -/
def type : Term := .pi (.con "P") (.pi (.con "Q") (.con "Q"))

theorem conv_P : Conv withRule (.con "P") (.pi (.con "Q") (.con "Q")) :=
  Conv.rule (theory := withRule) (rule := unfoldP) (List.mem_singleton.mpr rfl) fun _ => .srt .type

theorem type_Q (context : Ctx) : LambdaPiModulo withRule context (.con "Q") (.srt .type) :=
  .con rfl

theorem type_arrow (context : Ctx) :
    LambdaPiModulo withRule context (.pi (.con "Q") (.con "Q")) (.srt .type) :=
  .pi (type_Q _) (type_Q _)
    (by decide : (⟨.type, .type, .type⟩ : ProductRule) ∈ LFProfile.basic.products)

/-- **Positive**: the term is typable modulo the rule. -/
theorem typable_with_rule : LambdaPiModulo withRule [] term type := by
  have rule : (⟨.type, .type, .type⟩ : ProductRule) ∈ LFProfile.basic.products := by decide
  refine .lam (.con rfl) (type_arrow _) rule ?_
  refine .lam (type_Q _) (type_Q _) rule ?_
  have function : LambdaPiModulo withRule [.con "Q", .con "P"] (.var 1)
      (.pi (.con "Q") (.con "Q")) :=
    .conv (.var rfl) conv_P (type_arrow _)
  exact .app function (.var rfl)

theorem withoutRule_headed : withoutRule.Headed := fun _ member => absurd member List.not_mem_nil

theorem P_normal : IsNormal (Step withoutRule) (.con "P") := by
  intro target step
  rcases step.con_inv.con_inv with defined | ⟨_, _, member, _, _⟩
  · have undefined : withoutRule.body "P" = none := rfl
    rw [undefined] at defined
    cases defined
  · exact absurd member List.not_mem_nil

/-- **Negative, where confluence is used**: without the rule the term has no
type, in any profile. -/
theorem untypable_without_rule (confluent : Confluent (Step withoutRule)) (candidate : Term) :
    ¬ HasType profile withoutRule [] term candidate := by
  intro typed
  obtain ⟨_, _, _, _, _, _, _, outerBody, _⟩ := typed.lam_inv
  obtain ⟨_, _, _, _, _, _, _, innerBody, _⟩ := outerBody.lam_inv
  obtain ⟨domain, bodyType, function, _, _⟩ := innerBody.app_inv
  obtain ⟨declared, found, convertible⟩ := function.var_inv
  have same : declared = .con "P" := by
    have computed : ctxLookup [Term.con "Q", Term.con "P"] 1 = some (.con "P") := rfl
    exact (Option.some.inj (found.symm.trans computed))
  subst same
  obtain ⟨common, leftReduces, rightReduces⟩ := (conv_iff_joinable confluent).mp convertible
  have left := P_normal.reflTransGen_eq leftReduces
  obtain ⟨_, _, shape, _, _⟩ := rightReduces.pi_inv withoutRule_headed
  rw [left] at shape
  cases shape

end Example

#print axioms HasType.mono
#print axioms HasType.lam_inv
#print axioms HasType.app_inv
#print axioms HasType.toDeriv
#print axioms typed_common_reduct
#print axioms typed_normal_form
#print axioms normal_form_unique
#print axioms Example.typable_with_rule
#print axioms Example.untypable_without_rule

end Mettapedia.GSLT.Dedukti
