import Mettapedia.GSLT.Dedukti.OrthogonalCheck
import Mettapedia.GSLT.Dedukti.TwoRoutes
import Mettapedia.GSLT.Dedukti.CousineauDowekConservativity

/-!
# The confluence hypotheses of the λΠ-calculus modulo, discharged

Every theorem of `Mettapedia/GSLT/Dedukti/` that takes a hypothesis
`Confluent (Step theory)` is restated here without it.

## Theories that are orthogonal

* the theory with no rule, and every theory with no rule and closed
  definitions (`Theory.empty_orthogonal`, `ofSig_orthogonal`);
* unary numbers with addition by recursion on the first argument, and on the
  second (`unary_orthogonal`, `rightLibrary_orthogonal`);
* the fragment of the Holide encoding of OpenTheory (`holTheory_orthogonal`);
* **the theory of the Cousineau–Dowek embedding of every pure type system
  over the two sorts** (`cdTheory_orthogonal`).  Its confluence
  (`cdTheory_confluent`) is Proposition 10 of their paper.

## The restatements

For a theorem stated for an arbitrary theory, the version here takes
`theory.Orthogonal` in place of confluence (`…_of_orthogonal`).  For a theorem
stated for one theory, the version here, in the namespace `Unconditional`,
has no hypothesis left.  The first group below is the one that needs
confluence of beta alone.

Confluence of beta alone:

* `Unconditional.conv_iff_joinable`, `not_conv_of_normal`, `pi_injective`,
  `srt_injective`, `srt_ne_pi`, `normal_form_unique`: conversion in the pure
  calculus;
* `Unconditional.hasType_unique`: uniqueness of types in a functional pure
  type system;
* `Unconditional.beta_root`: a beta contraction at the root keeps the type;
* `Unconditional.typed_common_reduct`: under type preservation;
* `Unconditional.toDeriv`, `Unconditional.lfConv_iff_conv`: the existing
  judgment and the existing conversion by a common reduct, for a signature
  whose definitions are closed;
* `Unconditional.untypable_without_rule`;
* `Unconditional.explicit_A_ne_B`, `target_untyped_without_cast`,
  `no_structural_translation`;
* `Unconditional.rewritingTheory_confluentUpTo`,
  `Unconditional.withChoice_not_hosted_by_beta`,
  `Unconditional.choice_strictly_above`.

Confluence of beta with orthogonal rules:

* `Unconditional.wrongDouble_not_respects`, `Unconditional.align_not_respects`;
* `Unconditional.eta_statement_not_conv`;
* `Unconditional.constructions_not_exhaustsTyped`,
  `Unconditional.nonFunctional_not_respectsErasure`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Sig lookupBody lift subst subst0 Ctx)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile ProductRule)
open Mettapedia.Logic.Relation (Confluent IsNormal)

variable {theory : Theory}

/-! ## Orthogonal in place of confluent -/

theorem conv_iff_joinable_of_orthogonal (orthogonal : theory.Orthogonal) {left right : Term} :
    Conv theory left right ↔ Joinable theory left right :=
  conv_iff_joinable (confluent_of_orthogonal orthogonal)

theorem not_conv_of_normal_of_orthogonal (orthogonal : theory.Orthogonal) {left right : Term}
    (leftNormal : IsNormal (Step theory) left) (rightNormal : IsNormal (Step theory) right)
    (distinct : left ≠ right) : ¬ Conv theory left right :=
  not_conv_of_normal (confluent_of_orthogonal orthogonal) leftNormal rightNormal distinct

/-- **Convertible products have convertible parts**, in every orthogonal
theory. -/
theorem pi_injective_of_orthogonal (orthogonal : theory.Orthogonal)
    {domain domain' body body' : Term}
    (convertible : Conv theory (.pi domain body) (.pi domain' body')) :
    Conv theory domain domain' ∧ Conv theory body body' :=
  Conv.pi_injective (confluent_of_orthogonal orthogonal) orthogonal.leftAlgebraic.headed convertible

theorem srt_injective_of_orthogonal (orthogonal : theory.Orthogonal) {first second : Srt}
    (convertible : Conv theory (.srt first) (.srt second)) : first = second :=
  Conv.srt_injective (confluent_of_orthogonal orthogonal) orthogonal.leftAlgebraic.headed
    convertible

theorem srt_ne_pi_of_orthogonal (orthogonal : theory.Orthogonal) {sort : Srt}
    {domain body : Term} : ¬ Conv theory (.srt sort) (.pi domain body) :=
  Conv.srt_ne_pi (confluent_of_orthogonal orthogonal) orthogonal.leftAlgebraic.headed

theorem normal_form_unique_of_orthogonal (orthogonal : theory.Orthogonal)
    {term first second : Term}
    (firstReduces : Reduces theory term first) (firstNormal : IsNormal (Step theory) first)
    (secondReduces : Reduces theory term second) (secondNormal : IsNormal (Step theory) second) :
    first = second :=
  normal_form_unique (confluent_of_orthogonal orthogonal) firstReduces firstNormal secondReduces
    secondNormal

theorem typed_common_reduct_of_orthogonal {profile : Profile} (orthogonal : theory.Orthogonal)
    (preserved : SubjectReduction profile theory) {context : Ctx} {left right type : Term}
    (leftTyped : HasType profile theory context left type)
    (convertible : Conv theory left right) :
    ∃ common, Reduces theory left common ∧ Reduces theory right common ∧
      HasType profile theory context common type :=
  typed_common_reduct (confluent_of_orthogonal orthogonal) preserved leftTyped convertible

/-- **Uniqueness of types**: in a functional system over an orthogonal
theory, two types of one term in one context are convertible. -/
theorem hasType_unique_of_orthogonal {profile : Profile} (functional : Functional profile)
    (orthogonal : theory.Orthogonal) (term : Term) {context : Ctx} {first second : Term}
    (firstTyped : HasType profile theory context term first)
    (secondTyped : HasType profile theory context term second) : Conv theory first second :=
  HasType.unique functional (confluent_of_orthogonal orthogonal) orthogonal.leftAlgebraic.headed
    orthogonal.closedBodies term firstTyped secondTyped

/-- **A beta contraction at the root keeps a formed type**, in every
orthogonal theory with closed declared types. -/
theorem beta_root_of_orthogonal {profile : Profile} (orthogonal : theory.Orthogonal)
    (closedTypes : theory.ClosedTypes) {context : Ctx}
    {annotation body argument type : Term} {sort : Srt}
    (typed : HasType profile theory context (.app (.lam annotation body) argument) type)
    (formed : HasType profile theory context type (.srt sort)) :
    HasType profile theory context (LFTyping.subst0 argument body) type :=
  HasType.beta_root (confluent_of_orthogonal orthogonal) orthogonal.leftAlgebraic.headed
    orthogonal.closedBodies closedTypes typed formed

/-- The running presentation of an orthogonal theory is confluent. -/
theorem rewritingTheory_confluentUpTo_of_orthogonal (orthogonal : theory.Orthogonal) :
    (rewritingTheory theory).ConfluentUpTo :=
  rewritingTheory_confluentUpTo (confluent_of_orthogonal orthogonal)

/-- **No orthogonal theory hosts a theory with choice.** -/
theorem withChoice_not_hosted_by_orthogonal (headed : theory.Headed) {host : Theory}
    (orthogonal : host.Orthogonal)
    (map : ContextMap (rewritingTheory (withChoice theory)) (rewritingTheory host)) :
    ¬ map.Hosting :=
  withChoice_not_hosted_by_rewriting headed (confluent_of_orthogonal orthogonal) map

theorem rewritingTheoryAvoiding_confluentUpTo_of_orthogonal {name : String}
    (closed : theory.PreservesAvoiding name) (orthogonal : theory.Orthogonal) :
    (rewritingTheoryAvoiding name theory).ConfluentUpTo :=
  rewritingTheoryAvoiding_confluentUpTo closed (confluent_of_orthogonal orthogonal)

/-- **Different degrees of the hosting preorder**, for every orthogonal
theory whose steps do not introduce the choice symbol. -/
theorem choice_strictly_above_of_orthogonal (orthogonal : theory.Orthogonal)
    (closed : theory.PreservesAvoiding chooseName) :
    (∃ map : ContextMap (rewritingTheoryAvoiding chooseName theory)
        (rewritingTheory (withChoice theory)), map.Hosting) ∧
      ¬ ∃ map : ContextMap (rewritingTheory (withChoice theory))
        (rewritingTheoryAvoiding chooseName theory), map.Hosting :=
  choice_strictly_above orthogonal.leftAlgebraic.headed closed (confluent_of_orthogonal orthogonal)

/-! ## Theories that are orthogonal -/

/-- A signature with closed definitions and no declared rule. -/
theorem ofSig_orthogonal {signature : Sig} (closed : (Theory.ofSig signature []).ClosedBodies) :
    (Theory.ofSig signature []).Orthogonal :=
  Theory.orthogonal_of_no_rule closed fun _ member => absurd member List.not_mem_nil

theorem withoutRule_orthogonal : Example.withoutRule.Orthogonal :=
  ofSig_orthogonal fun name term defined => by
    have undefined : lookupBody Example.signature name = none := by
      simp [Example.signature, lookupBody]
    exact absurd (undefined.symm.trans defined) (by simp)

theorem explicit_orthogonal : Phenomena.explicit.Orthogonal :=
  ofSig_orthogonal fun name term defined => by
    have undefined : lookupBody Phenomena.explicitSig name = none := by
      simp [Phenomena.explicitSig, Phenomena.silentSig, lookupBody]
    exact absurd (undefined.symm.trans defined) (by simp)

/-- **Addition by recursion on the first argument is orthogonal.** -/
theorem unary_orthogonal : Phenomena.unary.Orthogonal :=
  orthogonal_of_check [Phenomena.plusZero, Phenomena.plusSucc] (fun _ member => member)
    (fun name => by
      show lookupBody Phenomena.unarySig name = none
      simp [Phenomena.unarySig, lookupBody])
    (by decide)

/-- Addition by recursion on the second argument is orthogonal. -/
theorem rightLibrary_orthogonal : Phenomena.rightLibrary.Orthogonal :=
  orthogonal_of_check [Phenomena.addZero, Phenomena.addSucc] (fun _ member => member)
    (fun name => by
      show lookupBody Phenomena.rightSig name = none
      simp [Phenomena.rightSig, lookupBody])
    (by decide)

/-- The rule `term (arr a b) ⟶ term a → term b` is orthogonal: its right side
binds, its left side does not. -/
theorem holTheory_orthogonal : TwoRoutes.holTheory.Orthogonal :=
  orthogonal_of_check [TwoRoutes.termArrow] (fun _ member => member)
    (fun name => by
      show lookupBody TwoRoutes.holSig name = none
      simp [TwoRoutes.holSig, lookupBody])
    (by decide)

/-- Every rule that the embedding of some pure type system over the two sorts
can declare. -/
def universeRuleList : List RewriteRule :=
  [codeRule .type .type, codeRule .type .kind, codeRule .kind .type, codeRule .kind .kind,
    prodRule ⟨.type, .type, .type⟩, prodRule ⟨.type, .type, .kind⟩,
    prodRule ⟨.type, .kind, .type⟩, prodRule ⟨.type, .kind, .kind⟩,
    prodRule ⟨.kind, .type, .type⟩, prodRule ⟨.kind, .type, .kind⟩,
    prodRule ⟨.kind, .kind, .type⟩, prodRule ⟨.kind, .kind, .kind⟩]

theorem universeRule_mem {profile : Profile} {rule : RewriteRule}
    (member : UniverseRule profile rule) : rule ∈ universeRuleList := by
  cases member with
  | @code source target _ => cases source <;> cases target <;> decide
  | @prod product _ =>
      obtain ⟨domain, codomain, result⟩ := product
      cases domain <;> cases codomain <;> cases result <;> decide

theorem universeRuleList_checked : orthogonalCheck universeRuleList = true := by
  decide

/-- **The theory of the embedding of every pure type system is orthogonal.** -/
theorem cdTheory_orthogonal (profile : Profile) : (cdTheory profile).Orthogonal :=
  orthogonal_of_check universeRuleList (fun _ member => universeRule_mem member)
    (fun _ => rfl) universeRuleList_checked

/-- **The theory of the embedding of every pure type system is confluent**
(Cousineau and Dowek, Proposition 10). -/
theorem cdTheory_confluent (profile : Profile) : Confluent (Step (cdTheory profile)) :=
  confluent_of_orthogonal (cdTheory_orthogonal profile)

/-! ## No hypothesis left -/

namespace Unconditional

/-! ### Beta alone -/

/-- **In the pure calculus, conversion is decided by reducing both sides.** -/
theorem conv_iff_joinable {left right : Term} :
    Conv Theory.empty left right ↔ Joinable Theory.empty left right :=
  Dedukti.conv_iff_joinable confluent_empty

theorem not_conv_of_normal {left right : Term}
    (leftNormal : IsNormal (Step Theory.empty) left)
    (rightNormal : IsNormal (Step Theory.empty) right) (distinct : left ≠ right) :
    ¬ Conv Theory.empty left right :=
  Dedukti.not_conv_of_normal confluent_empty leftNormal rightNormal distinct

/-- **Convertible products have convertible parts.** -/
theorem pi_injective {domain domain' body body' : Term}
    (convertible : Conv Theory.empty (.pi domain body) (.pi domain' body')) :
    Conv Theory.empty domain domain' ∧ Conv Theory.empty body body' :=
  pi_injective_of_orthogonal Theory.empty_orthogonal convertible

/-- Convertible sorts are equal. -/
theorem srt_injective {first second : Srt}
    (convertible : Conv Theory.empty (.srt first) (.srt second)) : first = second :=
  srt_injective_of_orthogonal Theory.empty_orthogonal convertible

/-- A sort is convertible to no product. -/
theorem srt_ne_pi {sort : Srt} {domain body : Term} :
    ¬ Conv Theory.empty (.srt sort) (.pi domain body) :=
  srt_ne_pi_of_orthogonal Theory.empty_orthogonal

/-- A term has at most one normal form. -/
theorem normal_form_unique {term first second : Term}
    (firstReduces : Reduces Theory.empty term first)
    (firstNormal : IsNormal (Step Theory.empty) first)
    (secondReduces : Reduces Theory.empty term second)
    (secondNormal : IsNormal (Step Theory.empty) second) : first = second :=
  normal_form_unique_of_orthogonal Theory.empty_orthogonal firstReduces firstNormal secondReduces
    secondNormal

theorem typed_common_reduct {profile : Profile}
    (preserved : SubjectReduction profile Theory.empty) {context : Ctx} {left right type : Term}
    (leftTyped : HasType profile Theory.empty context left type)
    (convertible : Conv Theory.empty left right) :
    ∃ common, Reduces Theory.empty left common ∧ Reduces Theory.empty right common ∧
      HasType profile Theory.empty context common type :=
  typed_common_reduct_of_orthogonal Theory.empty_orthogonal preserved leftTyped convertible

/-- **Uniqueness of types in a functional pure type system.** -/
theorem hasType_unique {profile : Profile} (functional : Functional profile) (term : Term)
    {context : Ctx} {first second : Term}
    (firstTyped : HasType profile Theory.empty context term first)
    (secondTyped : HasType profile Theory.empty context term second) :
    Conv Theory.empty first second :=
  hasType_unique_of_orthogonal functional Theory.empty_orthogonal term firstTyped secondTyped

/-- **In a pure type system a beta contraction at the root keeps a formed
type.** -/
theorem beta_root {profile : Profile} {context : Ctx} {annotation body argument type : Term}
    {sort : Srt}
    (typed : HasType profile Theory.empty context (.app (.lam annotation body) argument) type)
    (formed : HasType profile Theory.empty context type (.srt sort)) :
    HasType profile Theory.empty context (LFTyping.subst0 argument body) type :=
  beta_root_of_orthogonal Theory.empty_orthogonal
    (fun _ _ declared => by cases declared) typed formed

/-- **A derivation over a signature with closed definitions and no rule is a
derivation of the existing profile-parametric judgment.** -/
theorem toDeriv {profile : Profile} {signature : Sig}
    (closed : (Theory.ofSig signature []).ClosedBodies) {context : Ctx} {term type : Term}
    (typed : HasType profile (Theory.ofSig signature []) context term type) :
    LFConversionProfileChecker.Deriv profile signature context term type :=
  HasType.toDeriv (confluent_of_orthogonal (ofSig_orthogonal closed)) typed

/-- **The existing conversion by a common reduct is the declared conversion**,
for a signature with closed definitions. -/
theorem lfConv_iff_conv {signature : Sig} (closed : (Theory.ofSig signature []).ClosedBodies)
    {left right : Term} :
    LFTyping.Conv signature left right ↔ Conv (Theory.ofSig signature []) left right :=
  Dedukti.lfConv_iff_conv (confluent_of_orthogonal (ofSig_orthogonal closed))

/-- **Without the rule `P ⟶ Q → Q` the term `λ f : P. λ x : Q. f x` has no
type**, in any profile. -/
theorem untypable_without_rule {profile : Profile} (candidate : Term) :
    ¬ HasType profile Example.withoutRule [] Example.term candidate :=
  Example.untypable_without_rule (confluent_of_orthogonal withoutRule_orthogonal) candidate

theorem explicit_A_ne_B : ¬ Conv Phenomena.explicit Phenomena.typeA Phenomena.typeB :=
  Phenomena.explicit_A_ne_B (confluent_of_orthogonal explicit_orthogonal)

/-- **Without the transport the element does not have the second type.** -/
theorem target_untyped_without_cast {profile : Profile} :
    ¬ HasType profile Phenomena.explicit [] (.con "a") Phenomena.typeB :=
  Phenomena.target_untyped_without_cast (confluent_of_orthogonal explicit_orthogonal)

/-- **No structural morphism keeps the two types fixed.** -/
theorem no_structural_translation (interpretation : Interpretation)
    (keepsA : interpretation.meaning "A" = Phenomena.typeA)
    (keepsB : interpretation.meaning "B" = Phenomena.typeB) :
    ¬ interpretation.Respects Phenomena.silent Phenomena.explicit :=
  Phenomena.no_structural_translation (confluent_of_orthogonal explicit_orthogonal)
    interpretation keepsA keepsB

/-- The pure calculus as it runs is confluent. -/
theorem rewritingTheory_confluentUpTo : (rewritingTheory Theory.empty).ConfluentUpTo :=
  rewritingTheory_confluentUpTo_of_orthogonal Theory.empty_orthogonal

/-- **The pure calculus hosts no theory with choice.** -/
theorem withChoice_not_hosted_by_beta (headed : theory.Headed)
    (map : ContextMap (rewritingTheory (withChoice theory)) (rewritingTheory Theory.empty)) :
    ¬ map.Hosting :=
  withChoice_not_hosted_by_orthogonal headed Theory.empty_orthogonal map

/-- **Beta and beta with choice are different degrees of the hosting
preorder.** -/
theorem choice_strictly_above :
    (∃ map : ContextMap (rewritingTheoryAvoiding chooseName Theory.empty)
        (rewritingTheory (withChoice Theory.empty)), map.Hosting) ∧
      ¬ ∃ map : ContextMap (rewritingTheory (withChoice Theory.empty))
        (rewritingTheoryAvoiding chooseName Theory.empty), map.Hosting :=
  choice_strictly_above_of_orthogonal Theory.empty_orthogonal (empty_preservesAvoiding chooseName)

/-! ### Beta with orthogonal rules -/

/-- **The wrong definition of doubling fails the obligation on rules.** -/
theorem wrongDouble_not_respects :
    ¬ Phenomena.wrongDouble.Respects Phenomena.withDouble Phenomena.unary :=
  Phenomena.wrongDouble_not_respects (confluent_of_orthogonal unary_orthogonal)

/-- **The alignment of the two additions is not a structural morphism.** -/
theorem align_not_respects : ¬ Phenomena.align.Respects Phenomena.unary Phenomena.rightLibrary :=
  Phenomena.align_not_respects (confluent_of_orthogonal rightLibrary_orthogonal)

/-- **With beta conversion only, the eta statement and the statement of
reflexivity are not convertible.** -/
theorem eta_statement_not_conv :
    ¬ Conv TwoRoutes.holTheory TwoRoutes.etaAtVariable TwoRoutes.reflAtVariable :=
  TwoRoutes.eta_statement_not_conv (confluent_of_orthogonal holTheory_orthogonal)

/-- **The embedding of the calculus of constructions is not exhausting on
typed terms.** -/
theorem constructions_not_exhaustsTyped : ¬ ExhaustsTyped constructions :=
  Dedukti.constructions_not_exhaustsTyped (cdTheory_confluent constructions)

/-- **For a system that is not functional the translation is not a function
of raw terms.** -/
theorem nonFunctional_not_respectsErasure : ¬ RespectsErasure nonFunctional :=
  Dedukti.nonFunctional_not_respectsErasure (cdTheory_confluent nonFunctional)

end Unconditional

#print axioms unary_orthogonal
#print axioms holTheory_orthogonal
#print axioms cdTheory_orthogonal
#print axioms cdTheory_confluent
#print axioms hasType_unique_of_orthogonal
#print axioms Unconditional.conv_iff_joinable
#print axioms Unconditional.pi_injective
#print axioms Unconditional.hasType_unique
#print axioms Unconditional.beta_root
#print axioms Unconditional.toDeriv
#print axioms Unconditional.lfConv_iff_conv
#print axioms Unconditional.untypable_without_rule
#print axioms Unconditional.target_untyped_without_cast
#print axioms Unconditional.no_structural_translation
#print axioms Unconditional.choice_strictly_above
#print axioms Unconditional.wrongDouble_not_respects
#print axioms Unconditional.align_not_respects
#print axioms Unconditional.eta_statement_not_conv
#print axioms Unconditional.constructions_not_exhaustsTyped
#print axioms Unconditional.nonFunctional_not_respectsErasure

end Mettapedia.GSLT.Dedukti
