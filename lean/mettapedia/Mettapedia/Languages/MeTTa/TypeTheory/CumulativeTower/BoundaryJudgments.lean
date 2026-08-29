import Mettapedia.Languages.MeTTa.Pure.Intrinsic.RegularBidirectionalCompleteness
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SchemaElaboration
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SyntacticContextualCategory
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TowerConversionSkeleton
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TypingGeneration

/-!
# Object judgments at the regular/tower authority boundary

The eight regression rows are judgments, not expected status tags.  The first
four are exact regular-fragment checks.  The latter four are explicit Russell
tower checks or synthesis queries.  Every row below carries either a checked
derivation or a checked obstruction; fragment coverage is layered over these
objects by `OutcomeContract`.

The syntax is de Bruijn syntax, so the definitions are also a stable,
name-independent encoding of the corresponding surface queries.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

namespace BoundaryJudgments

open Mettapedia.Languages.MeTTa.Pure.Intrinsic
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary
open SchemaElaboration

abbrev FormedTowerContext :=
  SyntacticContextual.FormedContext Tower.rules

/-- The formed empty context used by the closed authority rows. -/
abbrev emptyTowerContext : FormedTowerContext :=
  SyntacticContextual.emptyContext Tower.rules

/-- The closed authority context carries its formation evidence positively. -/
theorem emptyTowerContext_wellFormed :
    Declaration.ContextWellFormed Tower.rules emptyTowerContext.context :=
  emptyTowerContext.wellFormed

/-- A raw telescope whose sole entry names no declaration.  It remains useful
as a negative boundary witness, but cannot be supplied to an authoritative
tower judgment. -/
def missingDeclarationContext : Tower.Ctx 1 :=
  .snoc .nil (.const .anonymous)

theorem missingDeclarationContext_not_wellFormed :
    ¬ Declaration.ContextWellFormed Tower.rules missingDeclarationContext := by
  intro formed
  cases formed with
  | snoc _ typing _ =>
      exact typing.constantImpossibleWhenMissing rfl

/-! ## Judgment kinds and their exact meanings -/

inductive JudgmentForm where
  | check
  | synthesize
  | formation
deriving DecidableEq, Repr

/-- A tower query retains its operational direction.  Checking and synthesis
both require the returned type to be formed; formation asks directly for the
displayed typing derivation. -/
def TowerMeaning (form : JudgmentForm) (context : FormedTowerContext)
    (term type : Tower.Tm context.arity) : Prop :=
  match form with
  | .check =>
      Tower.HasType context.context term type ∧
        ∃ level, Tower.HasType context.context type (sortTm level)
  | .synthesize =>
      Tower.HasType context.context term type ∧
        ∃ level, Tower.HasType context.context type (sortTm level)
  | .formation => Tower.HasType context.context term type

/-- The semantic judgment universe used by the authority contract.  The
regular constructor packages the established regular context proof rather
than silently treating a raw telescope as formed. -/
inductive ExactJudgment where
  | sealedCheck {n : Nat} (context : Legacy.Ctx n)
      (term type : Legacy.Tm n)
  | regularCheck {n : Nat} (context : Context.Ctx n)
      (regular : RegularCtx context) (term type : Syntax.PureTm n)
  | tower (form : JudgmentForm) (context : FormedTowerContext)
      (term type : Tower.Tm context.arity)

def ExactJudgment.Meaning : ExactJudgment → Prop
  | .sealedCheck context term type => Legacy.HasType context term type
  | .regularCheck context _ term type =>
      RegularHasType context term type ∧
        (type = .u1 ∨ RegularHasType context type .u1)
  | .tower form context term type => TowerMeaning form context term type

inductive BoundaryRow where
  | positiveInhabitant
  | selfApplication
  | lambdaAtNonFunction
  | distinctIdentityEndpoints
  | polymorphicModusPonens
  | typeLevelEquality
  | largeSigma
  | upperSortSynthesis
deriving DecidableEq, Repr

/-! ## Four exact regular-fragment judgments -/

namespace RegularRows

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax

/-- Nondependent function space inside the regular dependent syntax. -/
def arrow (domain codomain : PureTm n) : PureTm n :=
  .pi domain
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.wk codomain)

def positiveTerm : PureTm 0 :=
  .lam (.lam (.app (.var 0) (.var 1)))

def positiveType : PureTm 0 :=
  .pi .u0 (.pi (arrow .u0 .u0) .u0)

def selfApplicationTerm : PureTm 0 :=
  .lam (.lam (.app (.var 0) (.var 0)))

def lambdaAtNonFunctionTerm : PureTm 0 := .lam (.var 0)

def distinctIdentityTerm : PureTm 0 :=
  .lam (.lam (.refl (.var 1)))

def distinctIdentityType : PureTm 0 :=
  .pi .u0 (.pi .u0 (.id .u0 (.var 1) (.var 0)))

@[simp] theorem rename_arrow
    (rnm : Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.Ren n m)
    (domain codomain : PureTm n) :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename rnm
        (arrow domain codomain) =
      arrow
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename rnm domain)
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename rnm codomain) := by
  simp [arrow, Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename,
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename_comp]
  apply Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename_ext
  intro index
  rfl

private theorem u0_normal (n : Nat) :
    RedNormal (.u0 : PureTm n) := by
  intro reduct step
  cases step

/-- A regular dependent-function type cannot convert to the lower universe. -/
theorem not_conv_pi_u0 (domain : PureTm n) (codomain : PureTm (n + 1)) :
    ¬ Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv
      (.pi domain codomain) .u0 := by
  intro conversion
  rcases Mettapedia.Languages.MeTTa.Pure.Intrinsic.Confluence.church_rosser_conv
      conversion with ⟨common, piSteps, u0Steps⟩
  rcases Mettapedia.Languages.MeTTa.Pure.Intrinsic.Confluence.redStar_pi_head
      piSteps with ⟨domain', codomain', commonShape⟩
  have commonU0 : common = (.u0 : PureTm n) :=
    (u0_normal n).redStar_eq u0Steps
  rw [commonU0] at commonShape
  cases commonShape

/-- Variable typing differs from context lookup only by regular conversion. -/
theorem variable_generation {Gamma : Context.Ctx n} {index : Fin n}
    {type : PureTm n} (typing : RegularHasType Gamma (.var index) type) :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv
      (Context.lookup Gamma index) type := by
  generalize termEquality : (.var index : PureTm n) = term at typing
  induction typing with
  | u0_type context => cases termEquality
  | var actualIndex =>
      cases termEquality
      exact Relation.EqvGen.refl _
  | pi_form domainTyping codomainTyping ihDomain ihCodomain =>
      cases termEquality
  | sigma_form domainTyping codomainTyping ihDomain ihCodomain =>
      cases termEquality
  | lam_intro domainTyping codomainTyping bodyTyping
      ihDomain ihCodomain ihBody => cases termEquality
  | app_elim domainTyping functionTyping argumentTyping codomainTyping
      ihDomain ihFunction ihArgument ihCodomain => cases termEquality
  | pair_intro domainTyping firstTyping secondTyping codomainTyping
      ihDomain ihFirst ihSecond ihCodomain => cases termEquality
  | fst_elim domainTyping pairTyping codomainTyping
      ihDomain ihPair ihCodomain => cases termEquality
  | snd_elim domainTyping pairTyping codomainTyping
      ihDomain ihPair ihCodomain => cases termEquality
  | id_form carrierTyping leftTyping rightTyping ihCarrier ihLeft ihRight =>
      cases termEquality
  | refl_intro carrierTyping termTyping ihCarrier ihTerm => cases termEquality
  | conv_type sourceTyping targetTyping conversion ihSource ihTarget =>
      exact Relation.EqvGen.trans _ _ _ (ihSource termEquality)
        conversion.toConv
  | conv_sort sourceTyping conversion ihSource =>
      exact Relation.EqvGen.trans _ _ _ (ihSource termEquality)
        conversion.toConv

/-- Application typing exposes the function and argument premises even when
the result type is subsequently converted. -/
theorem application_generation {Gamma : Context.Ctx n}
    {function argument type : PureTm n}
    (typing : RegularHasType Gamma (.app function argument) type) :
    ∃ domain codomain,
      RegularHasType Gamma function (.pi domain codomain) ∧
        RegularHasType Gamma argument domain := by
  generalize termEquality : (.app function argument : PureTm n) = term at typing
  induction typing with
  | u0_type context => cases termEquality
  | var index => cases termEquality
  | pi_form domainTyping codomainTyping ihDomain ihCodomain =>
      cases termEquality
  | sigma_form domainTyping codomainTyping ihDomain ihCodomain =>
      cases termEquality
  | lam_intro domainTyping codomainTyping bodyTyping
      ihDomain ihCodomain ihBody => cases termEquality
  | app_elim domainTyping functionTyping argumentTyping codomainTyping
      ihDomain ihFunction ihArgument ihCodomain =>
      cases termEquality
      exact ⟨_, _, functionTyping, argumentTyping⟩
  | pair_intro domainTyping firstTyping secondTyping codomainTyping
      ihDomain ihFirst ihSecond ihCodomain => cases termEquality
  | fst_elim domainTyping pairTyping codomainTyping
      ihDomain ihPair ihCodomain => cases termEquality
  | snd_elim domainTyping pairTyping codomainTyping
      ihDomain ihPair ihCodomain => cases termEquality
  | id_form carrierTyping leftTyping rightTyping ihCarrier ihLeft ihRight =>
      cases termEquality
  | refl_intro carrierTyping termTyping ihCarrier ihTerm => cases termEquality
  | conv_type sourceTyping targetTyping conversion ihSource ihTarget =>
      exact ihSource termEquality
  | conv_sort sourceTyping conversion ihSource => exact ihSource termEquality

/-- Reflexivity typing exposes its reflexive identity type up to conversion. -/
theorem reflexivity_generation {Gamma : Context.Ctx n}
    {term type : PureTm n} (typing : RegularHasType Gamma (.refl term) type) :
    ∃ carrier, RegularHasType Gamma term carrier ∧
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv
        (.id carrier term term) type := by
  generalize termEquality : (.refl term : PureTm n) = subject at typing
  induction typing with
  | u0_type context => cases termEquality
  | var index => cases termEquality
  | pi_form domainTyping codomainTyping ihDomain ihCodomain =>
      cases termEquality
  | sigma_form domainTyping codomainTyping ihDomain ihCodomain =>
      cases termEquality
  | lam_intro domainTyping codomainTyping bodyTyping
      ihDomain ihCodomain ihBody => cases termEquality
  | app_elim domainTyping functionTyping argumentTyping codomainTyping
      ihDomain ihFunction ihArgument ihCodomain => cases termEquality
  | pair_intro domainTyping firstTyping secondTyping codomainTyping
      ihDomain ihFirst ihSecond ihCodomain => cases termEquality
  | fst_elim domainTyping pairTyping codomainTyping
      ihDomain ihPair ihCodomain => cases termEquality
  | snd_elim domainTyping pairTyping codomainTyping
      ihDomain ihPair ihCodomain => cases termEquality
  | id_form carrierTyping leftTyping rightTyping ihCarrier ihLeft ihRight =>
      cases termEquality
  | refl_intro carrierTyping termTyping ihCarrier ihTerm =>
      cases termEquality
      exact ⟨_, termTyping, Relation.EqvGen.refl _⟩
  | conv_type sourceTyping targetTyping conversion ihSource ihTarget =>
      rcases ihSource termEquality with ⟨carrier, payloadTyping, sourceConv⟩
      exact ⟨carrier, payloadTyping,
        Relation.EqvGen.trans _ _ _ sourceConv conversion.toConv⟩
  | conv_sort sourceTyping conversion ihSource =>
      rcases ihSource termEquality with ⟨carrier, payloadTyping, sourceConv⟩
      exact ⟨carrier, payloadTyping,
        Relation.EqvGen.trans _ _ _ sourceConv conversion.toConv⟩

theorem positiveType_formed :
    RegularHasType (.nil : Context.Ctx 0) positiveType .u1 := by
  unfold positiveType
  apply RegularHasType.pi_form (.u0_type .nil)
  apply RegularHasType.pi_form
  · unfold arrow
    exact .pi_form (.u0_type _) (.u0_type _)
  · exact .u0_type _

theorem positiveTerm_hasType :
    RegularHasType (.nil : Context.Ctx 0) positiveTerm positiveType := by
  unfold positiveTerm positiveType
  apply RegularHasType.lam_intro
  · exact .u0_type .nil
  · apply RegularHasType.pi_form
    · unfold arrow
      exact .pi_form (.u0_type _) (.u0_type _)
    · exact .u0_type _
  · apply RegularHasType.lam_intro
    · unfold arrow
      exact .pi_form (.u0_type _) (.u0_type _)
    · exact .u0_type _
    · have application :
          RegularHasType
            (.snoc (.snoc (.nil : Context.Ctx 0) .u0) (arrow .u0 .u0))
            (.app (.var 0) (.var 1))
            (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.inst0
              (.var 1) (.u0 : PureTm 3)) := by
        apply RegularHasType.app_elim (A := .u0) (B := (.u0 : PureTm 3))
        · exact .u0_type _
        · simpa [arrow, Context.lookup,
            Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename] using
            (RegularHasType.var (Γ :=
              (.snoc (.snoc (.nil : Context.Ctx 0) .u0) (arrow .u0 .u0)))
              (0 : Fin 2))
        · have variableTyping :=
            RegularHasType.var (Γ :=
              (.snoc (.snoc (.nil : Context.Ctx 0) .u0) (arrow .u0 .u0)))
              (Fin.succ (0 : Fin 1))
          rw [Context.lookup_snoc_succ, Context.lookup_snoc_zero] at variableTyping
          simpa [Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename] using
            variableTyping
        · exact .u0_type _
      simpa [Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.inst0,
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution.subst] using
        application

theorem positive_evidence :
    RegularHasType (.nil : Context.Ctx 0) positiveTerm positiveType ∧
      (positiveType = .u1 ∨
        RegularHasType (.nil : Context.Ctx 0) positiveType .u1) :=
  ⟨positiveTerm_hasType, Or.inr positiveType_formed⟩

theorem lambdaAtNonFunction_not_hasType :
    ¬ RegularHasType (.nil : Context.Ctx 0) lambdaAtNonFunctionTerm .u0 := by
  intro typing
  rcases regular_lam_generation typing with
    ⟨domain, codomain, domainFormed, codomainFormed, bodyTyping, conversion⟩
  exact not_conv_pi_u0 domain codomain conversion

theorem selfApplication_not_hasType :
    ¬ RegularHasType (.nil : Context.Ctx 0) selfApplicationTerm positiveType := by
  intro typing
  rcases regular_lam_generation typing with
    ⟨outerDomain, outerCodomain, outerDomainFormed, outerCodomainFormed,
      innerTyping, outerConversion⟩
  have outerParts :=
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Confluence.pi_injectivity
      outerConversion
  rcases regular_lam_generation innerTyping with
    ⟨innerDomain, innerCodomain, innerDomainFormed, innerCodomainFormed,
      applicationTyping, innerConversion⟩
  have innerToExpected :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv
        (.pi innerDomain innerCodomain) (.pi (arrow .u0 .u0) .u0) :=
    Relation.EqvGen.trans _ _ _ innerConversion outerParts.2
  have innerParts :=
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Confluence.pi_injectivity
      innerToExpected
  rcases application_generation applicationTyping with
    ⟨argumentDomain, resultCodomain, functionTyping, argumentTyping⟩
  have functionLookup := variable_generation functionTyping
  have argumentLookup := variable_generation argumentTyping
  have innerDomainWeakened :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv
        (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename
          Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.wk innerDomain)
        (arrow .u0 .u0) := by
    simpa [Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.rename] using
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.conv_rename
        Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming.wk innerParts.1
  have functionTypeToExpected :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv
        (.pi argumentDomain resultCodomain) (arrow .u0 .u0) := by
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ functionLookup)
      innerDomainWeakened
  have argumentDomainToU0 :=
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Confluence.pi_injectivity
      functionTypeToExpected).1
  have expectedToArgumentDomain :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv
        (arrow .u0 .u0) argumentDomain :=
    Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ innerDomainWeakened) argumentLookup
  have impossible :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv
        (arrow .u0 .u0) .u0 :=
    Relation.EqvGen.trans _ _ _ expectedToArgumentDomain argumentDomainToU0
  exact not_conv_pi_u0 .u0 .u0 impossible

theorem distinctIdentity_not_hasType :
    ¬ RegularHasType (.nil : Context.Ctx 0)
      distinctIdentityTerm distinctIdentityType := by
  intro typing
  rcases regular_lam_generation typing with
    ⟨outerDomain, outerCodomain, outerDomainFormed, outerCodomainFormed,
      innerTyping, outerConversion⟩
  have outerParts :=
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Confluence.pi_injectivity
      outerConversion
  rcases regular_lam_generation innerTyping with
    ⟨innerDomain, innerCodomain, innerDomainFormed, innerCodomainFormed,
      reflexivityTyping, innerConversion⟩
  have innerToExpected :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv
        (.pi innerDomain innerCodomain)
        (.pi .u0 (.id .u0 (.var 1) (.var 0))) :=
    Relation.EqvGen.trans _ _ _ innerConversion outerParts.2
  have codomainConversion :=
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Confluence.pi_injectivity
      innerToExpected).2
  rcases reflexivity_generation reflexivityTyping with
    ⟨carrier, payloadTyping, reflexiveConversion⟩
  have identityConversion :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv
        (.id carrier (.var 1) (.var 1))
        (.id .u0 (.var 1) (.var 0)) :=
    Relation.EqvGen.trans _ _ _ reflexiveConversion codomainConversion
  have endpointConversion :=
    (TowerConversionSkeleton.pure_id_components_of_conv identityConversion).2.2
  have endpointEquality : (.var 1 : PureTm 2) = .var 0 := by
    apply normalForms_eq_of_conv
      (Reduction.RedStar.refl _) (Reduction.RedStar.refl _)
    · intro reduct step
      cases step
    · intro reduct step
      cases step
    · exact endpointConversion
  cases endpointEquality

theorem selfApplication_obstruction :
    ¬ (RegularHasType (.nil : Context.Ctx 0) selfApplicationTerm positiveType ∧
      (positiveType = .u1 ∨
        RegularHasType (.nil : Context.Ctx 0) positiveType .u1)) := by
  intro meaning
  exact selfApplication_not_hasType meaning.1

theorem lambdaAtNonFunction_obstruction :
    ¬ (RegularHasType (.nil : Context.Ctx 0) lambdaAtNonFunctionTerm .u0 ∧
      ((.u0 : PureTm 0) = .u1 ∨
        RegularHasType (.nil : Context.Ctx 0) .u0 .u1)) := by
  intro meaning
  exact lambdaAtNonFunction_not_hasType meaning.1

theorem distinctIdentity_obstruction :
    ¬ (RegularHasType (.nil : Context.Ctx 0)
        distinctIdentityTerm distinctIdentityType ∧
      (distinctIdentityType = .u1 ∨
        RegularHasType (.nil : Context.Ctx 0) distinctIdentityType .u1)) := by
  intro meaning
  exact distinctIdentity_not_hasType meaning.1

end RegularRows

/-! ## Reusable tower inversions -/

namespace TowerInversion

open TowerConversionSkeleton

/-- A typed lambda ultimately comes from function introduction.  Conversion
may change its displayed function type, but cumulativity cannot manufacture a
non-function type because `Pi` and universe-head conversion are disjoint. -/
theorem lambda {context : Tower.Ctx n} {body : Tower.Tm (n + 1)}
    {type : Tower.Tm n} (typing : Tower.HasType context (.lam body) type) :
    ∃ domain codomain,
      Tower.HasType (.snoc context domain) body codomain ∧
        Conv Tower.HeadEq (.pi domain codomain) type := by
  generalize termEquality : (.lam body : Tower.Tm n) = term at typing
  induction typing with
  | headType headTyping => cases termEquality
  | var index => cases termEquality
  | const impossible => simp [Tower.rules] at impossible
  | piForm typeDomain isDomain typeCodomain isCodomain join ihDomain ihCodomain =>
      cases termEquality
  | sigmaForm typeDomain isDomain typeCodomain isCodomain join ihDomain ihCodomain =>
      cases termEquality
  | lamIntro bodyTyping ihBody =>
      cases termEquality
      exact ⟨_, _, bodyTyping, Relation.EqvGen.refl _⟩
  | appElim functionTyping argumentTyping ihFunction ihArgument =>
      cases termEquality
  | pairIntro firstTyping secondTyping ihFirst ihSecond => cases termEquality
  | fstElim pairTyping ihPair => cases termEquality
  | sndElim pairTyping ihPair => cases termEquality
  | idForm carrierTyping isUniverse leftTyping rightTyping
      ihCarrier ihLeft ihRight => cases termEquality
  | reflIntro termTyping ihTerm => cases termEquality
  | @cumul _ _ _ sourceLevel targetLevel sourceTyping cumulative ih =>
      rcases ih termEquality with ⟨domain, codomain, bodyTyping, conversion⟩
      exact False.elim (not_conv_pi_head domain codomain sourceLevel conversion)
  | conv sourceTyping conversion ih =>
      rcases ih termEquality with
        ⟨domain, codomain, bodyTyping, sourceConversion⟩
      exact ⟨domain, codomain, bodyTyping,
        Relation.EqvGen.trans _ _ _ sourceConversion conversion⟩

/-- A typed reflexivity term ultimately has a reflexive identity type. -/
theorem refl {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typing : Tower.HasType context (.refl term) type) :
    ∃ carrier, Tower.HasType context term carrier ∧
      Conv Tower.HeadEq (.id carrier term term) type := by
  generalize termEquality : (.refl term : Tower.Tm n) = subject at typing
  induction typing with
  | headType headTyping => cases termEquality
  | var index => cases termEquality
  | const impossible => simp [Tower.rules] at impossible
  | piForm typeDomain isDomain typeCodomain isCodomain join ihDomain ihCodomain =>
      cases termEquality
  | sigmaForm typeDomain isDomain typeCodomain isCodomain join ihDomain ihCodomain =>
      cases termEquality
  | lamIntro bodyTyping ihBody => cases termEquality
  | appElim functionTyping argumentTyping ihFunction ihArgument =>
      cases termEquality
  | pairIntro firstTyping secondTyping ihFirst ihSecond => cases termEquality
  | fstElim pairTyping ihPair => cases termEquality
  | sndElim pairTyping ihPair => cases termEquality
  | idForm carrierTyping isUniverse leftTyping rightTyping
      ihCarrier ihLeft ihRight => cases termEquality
  | reflIntro termTyping ihTerm =>
      cases termEquality
      exact ⟨_, termTyping, Relation.EqvGen.refl _⟩
  | @cumul _ _ _ sourceLevel targetLevel sourceTyping cumulative ih =>
      rcases ih termEquality with ⟨carrier, payloadTyping, conversion⟩
      exact False.elim
        (not_conv_id_head carrier term term sourceLevel conversion)
  | conv sourceTyping conversion ih =>
      rcases ih termEquality with
        ⟨carrier, payloadTyping, sourceConversion⟩
      exact ⟨carrier, payloadTyping,
        Relation.EqvGen.trans _ _ _ sourceConversion conversion⟩

end TowerInversion

/-! ## Four explicit tower judgments -/

namespace TowerRows

open TowerConversionSkeleton

def universe0 : Tower.Tm n := sortTm Tower.zero
def universe1 : Tower.Tm n := sortTm (.succ Tower.zero)
def universe2 : Tower.Tm n := sortTm (.succ (.succ Tower.zero))

/-! ### Polymorphic Modus Ponens -/

def modusPonensType : Tower.Tm 0 :=
  .pi universe0
    (.pi universe0
      (.pi (arrow (.var 1) (.var 0))
        (.pi (.var 2) (.var 2))))

def modusPonensTerm : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.app (.var 1) (.var 0)))))

def mpCtxP : Tower.Ctx 1 := .snoc .nil universe0
def mpCtxPQ : Tower.Ctx 2 := .snoc mpCtxP universe0
def mpCtxPQH : Tower.Ctx 3 :=
  .snoc mpCtxPQ (arrow (.var 1) (.var 0))
def mpCtxPQHX : Tower.Ctx 4 := .snoc mpCtxPQH (.var 2)

@[simp] theorem mp_lookup_x :
    Ctx.lookup mpCtxPQHX 0 = (.var 3 : Tower.Tm 4) := by decide

@[simp] theorem mp_lookup_h :
    Ctx.lookup mpCtxPQHX 1 = arrow (.var 3) (.var 2) := by decide

theorem modusPonensTerm_hasType :
    Tower.HasType .nil modusPonensTerm modusPonensType := by
  unfold modusPonensTerm modusPonensType
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  apply Presentation.HasType.lamIntro
  change Tower.HasType mpCtxPQHX (.app (.var 1) (.var 0)) (.var 2)
  have functionTyping : Tower.HasType mpCtxPQHX (.var 1)
      (arrow (.var 3) (.var 2)) := by
    simpa only [mp_lookup_h] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := mpCtxPQHX) (1 : Fin 4))
  have argumentTyping : Tower.HasType mpCtxPQHX (.var 0) (.var 3) := by
    simpa only [mp_lookup_x] using
      (Presentation.HasType.var (R := Tower.rules)
        (Γ := mpCtxPQHX) (0 : Fin 4))
  simpa only [arrow, inst0_rename_wk] using
    (Presentation.HasType.appElim functionTyping argumentTyping)

theorem modusPonensType_hasType :
    ∃ level, Tower.HasType .nil modusPonensType (sortTm level) := by
  refine ⟨.max (.succ Tower.zero)
    (.max (.succ Tower.zero)
      (.max (.max Tower.zero Tower.zero) (.max Tower.zero Tower.zero))), ?_⟩
  unfold modusPonensType
  apply Presentation.HasType.piForm
  · exact .headType (.sort Tower.zero)
  · exact .sort (.succ Tower.zero)
  · apply Presentation.HasType.piForm
    · exact .headType (.sort Tower.zero)
    · exact .sort (.succ Tower.zero)
    · apply Presentation.HasType.piForm
      · apply Presentation.HasType.piForm
        · exact Presentation.HasType.var 1
        · exact .sort Tower.zero
        · exact Presentation.HasType.var 1
        · exact .sort Tower.zero
        · exact .sorts Tower.zero Tower.zero
      · exact .sort (.max Tower.zero Tower.zero)
      · apply Presentation.HasType.piForm
        · exact Presentation.HasType.var 2
        · exact .sort Tower.zero
        · exact Presentation.HasType.var 2
        · exact .sort Tower.zero
        · exact .sorts Tower.zero Tower.zero
      · exact .sort (.max Tower.zero Tower.zero)
      · exact .sorts (.max Tower.zero Tower.zero)
          (.max Tower.zero Tower.zero)
    · exact .sort (.max (.max Tower.zero Tower.zero)
        (.max Tower.zero Tower.zero))
    · exact .sorts (.succ Tower.zero)
        (.max (.max Tower.zero Tower.zero) (.max Tower.zero Tower.zero))
  · exact .sort (.max (.succ Tower.zero)
      (.max (.max Tower.zero Tower.zero) (.max Tower.zero Tower.zero)))
  · exact .sorts (.succ Tower.zero)
      (.max (.succ Tower.zero)
        (.max (.max Tower.zero Tower.zero) (.max Tower.zero Tower.zero)))

theorem modusPonens_evidence :
    TowerMeaning .check emptyTowerContext modusPonensTerm modusPonensType :=
  ⟨modusPonensTerm_hasType, modusPonensType_hasType⟩

/-! ### Type-level equality mismatch -/

def typeLevelEqualityTerm : Tower.Tm 0 :=
  .lam (.refl universe0)

def typeLevelEqualityType : Tower.Tm 0 :=
  .pi universe0 (.id universe0 (.var 0) (.var 0))

theorem typeLevelEqualityType_hasType :
    ∃ level, Tower.HasType .nil typeLevelEqualityType (sortTm level) := by
  refine ⟨.max (.succ Tower.zero) (.succ Tower.zero), ?_⟩
  unfold typeLevelEqualityType
  apply Presentation.HasType.piForm
  · exact .headType (.sort Tower.zero)
  · exact .sort (.succ Tower.zero)
  · apply Presentation.HasType.idForm
    · exact .headType (.sort Tower.zero)
    · exact .sort (.succ Tower.zero)
    · exact Presentation.HasType.var 0
    · exact Presentation.HasType.var 0
  · exact .sort (.succ Tower.zero)
  · exact .sorts (.succ Tower.zero) (.succ Tower.zero)

theorem typeLevelEquality_not_hasType :
    ¬ Tower.HasType .nil typeLevelEqualityTerm typeLevelEqualityType := by
  intro typing
  rcases TowerInversion.lambda typing with
    ⟨domain, codomain, bodyTyping, functionConversion⟩
  have functionParts := pi_components_of_conv functionConversion
  rcases TowerInversion.refl bodyTyping with
    ⟨carrier, universeTyping, identityConversion⟩
  have identityToCodomain := conv_erases identityConversion
  have identityToExpected :
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv
        (.id (erase carrier) .u0 .u0)
        (.id .u0 (.var 0) (.var 0)) := by
    exact Relation.EqvGen.trans _ _ _ identityToCodomain functionParts.2
  have endpointConversion :=
    (pure_id_components_of_conv identityToExpected).2.1
  have endpointEquality : (.u0 : Syntax.PureTm 1) = .var 0 := by
    apply normalForms_eq_of_conv
      (Reduction.RedStar.refl _) (Reduction.RedStar.refl _)
    · intro reduct step
      cases step
    · intro reduct step
      cases step
    · exact endpointConversion
  cases endpointEquality

theorem typeLevelEquality_obstruction :
    ¬ TowerMeaning .check emptyTowerContext typeLevelEqualityTerm
      typeLevelEqualityType := by
  intro meaning
  exact typeLevelEquality_not_hasType meaning.1

/-! ### Large Sigma checked against a lambda -/

def largeSigmaType : Tower.Tm 0 :=
  .sigma universe1 universe0

def largeSigmaTerm : Tower.Tm 0 := .lam (.var 0)

theorem largeSigmaType_hasType :
    ∃ level, Tower.HasType .nil largeSigmaType (sortTm level) := by
  refine ⟨.max (.succ (.succ Tower.zero)) (.succ Tower.zero), ?_⟩
  unfold largeSigmaType
  apply Presentation.HasType.sigmaForm
  · exact .headType (.sort (.succ Tower.zero))
  · exact .sort (.succ (.succ Tower.zero))
  · exact .headType (.sort Tower.zero)
  · exact .sort (.succ Tower.zero)
  · exact .sorts (.succ (.succ Tower.zero)) (.succ Tower.zero)

theorem largeSigma_not_hasType :
    ¬ Tower.HasType .nil largeSigmaTerm largeSigmaType := by
  intro typing
  rcases TowerInversion.lambda typing with
    ⟨domain, codomain, bodyTyping, conversion⟩
  exact not_conv_pi_sigma domain codomain universe1 universe0 conversion

theorem largeSigma_obstruction :
    ¬ TowerMeaning .check emptyTowerContext largeSigmaTerm largeSigmaType := by
  intro meaning
  exact largeSigma_not_hasType meaning.1

/-! ### Synthesis of the upper sort -/

theorem upperSort_hasType :
    Tower.HasType .nil universe1 universe2 := by
  exact .headType (.sort (.succ Tower.zero))

theorem upperSortResult_hasType :
    ∃ level, Tower.HasType .nil universe2 (sortTm level) := by
  exact ⟨.succ (.succ (.succ Tower.zero)),
    .headType (.sort (.succ (.succ Tower.zero)))⟩

theorem upperSort_evidence :
    TowerMeaning .synthesize emptyTowerContext universe1 universe2 :=
  ⟨upperSort_hasType, upperSortResult_hasType⟩

end TowerRows

/-! ## The row-to-judgment map and proof-bearing tower decisions -/

def BoundaryRow.judgment : BoundaryRow → ExactJudgment
  | .positiveInhabitant =>
      .regularCheck .nil .nil RegularRows.positiveTerm RegularRows.positiveType
  | .selfApplication =>
      .regularCheck .nil .nil RegularRows.selfApplicationTerm RegularRows.positiveType
  | .lambdaAtNonFunction =>
      .regularCheck .nil .nil RegularRows.lambdaAtNonFunctionTerm .u0
  | .distinctIdentityEndpoints =>
      .regularCheck .nil .nil RegularRows.distinctIdentityTerm
        RegularRows.distinctIdentityType
  | .polymorphicModusPonens =>
      .tower .check emptyTowerContext TowerRows.modusPonensTerm
        TowerRows.modusPonensType
  | .typeLevelEquality =>
      .tower .check emptyTowerContext TowerRows.typeLevelEqualityTerm
        TowerRows.typeLevelEqualityType
  | .largeSigma =>
      .tower .check emptyTowerContext TowerRows.largeSigmaTerm
        TowerRows.largeSigmaType
  | .upperSortSynthesis =>
      .tower .synthesize emptyTowerContext TowerRows.universe1 TowerRows.universe2

inductive Resolution (judgment : ExactJudgment) where
  | established (evidence : judgment.Meaning)
  | refuted (obstruction : ¬ judgment.Meaning)

def BoundaryRow.towerResolution (row : BoundaryRow) : Resolution row.judgment :=
  match row with
  | .positiveInhabitant => .established RegularRows.positive_evidence
  | .selfApplication => .refuted RegularRows.selfApplication_obstruction
  | .lambdaAtNonFunction => .refuted RegularRows.lambdaAtNonFunction_obstruction
  | .distinctIdentityEndpoints => .refuted RegularRows.distinctIdentity_obstruction
  | .polymorphicModusPonens => .established TowerRows.modusPonens_evidence
  | .typeLevelEquality => .refuted TowerRows.typeLevelEquality_obstruction
  | .largeSigma => .refuted TowerRows.largeSigma_obstruction
  | .upperSortSynthesis => .established TowerRows.upperSort_evidence

theorem BoundaryRow.resolution_exclusive (row : BoundaryRow) :
    (Nonempty row.judgment.Meaning ∧ ¬ Nonempty (¬ row.judgment.Meaning)) ∨
      (Nonempty (¬ row.judgment.Meaning) ∧ ¬ Nonempty row.judgment.Meaning) := by
  cases resolution : row.towerResolution with
  | established evidence =>
      exact Or.inl
        ⟨⟨evidence⟩, fun obstruction =>
          obstruction.elim fun reject => reject evidence⟩
  | refuted obstruction =>
      exact Or.inr
        ⟨⟨obstruction⟩, fun evidence =>
          evidence.elim fun witness => obstruction witness⟩

/-! ## Axiom audit -/

#print axioms RegularRows.positive_evidence
#print axioms RegularRows.selfApplication_obstruction
#print axioms TowerRows.modusPonens_evidence
#print axioms TowerRows.typeLevelEquality_obstruction
#print axioms TowerRows.largeSigma_obstruction
#print axioms TowerRows.upperSort_evidence
#print axioms BoundaryRow.resolution_exclusive
#print axioms missingDeclarationContext_not_wellFormed

end BoundaryJudgments

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
