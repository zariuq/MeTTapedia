import Mettapedia.GSLT.LanguageDef.StructuralCoproductOperational
import Mettapedia.GSLT.LanguageDef.StructuralPatternBindingNaturality
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.IdentityInterface
import Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.EquationSite
import Mettapedia.Logic.Relation.ObservationTransport

/-!
# Conservativity of extensions, per observation class

An observer of a language reads its step relation.  Two classes of
observation behave differently under extension.

* **May-observations**: some successor, or some reduct, satisfies a claim.
* **Must-observations**: every successor, or every reduct, satisfies a claim.
  Determinism, at most one successor at every reduct, is one of them.

`ExactEmbedding` is the shape of the operational transport of a structural
coproduct: the steps of an embedded term are exactly the images of the steps
of the term.  Every may- and every must-observation above is invariant under
exact embeddings (`TransportInvariant`).  A structural coproduct therefore
conserves both classes on each summand, in the sense of
`ExtensionLayer.Conserves` (`leftSummands_conserve`, `rightSummands_conserve`).
The only hypothesis beyond the coproduct itself is the premise-evaluator square
of `StructuralCoproductOperational` on the summand's own rules.

Normal forms are the must-observation of the empty claim, so exact embeddings
conserve them (`isNormal_transport`).  Conversion is no observation of a term
and its reducts alone: an exact embedding conserves it when the larger step
relation is confluent (`ExactEmbedding.eqvGen_iff`), and not otherwise, since
a term outside the image can fork into two embedded terms
(`fork_conversion_not_conserved`, `fork_not_confluent`).  A confluent entry
into the image is the positive control (`entry_conversion_conserved`).

An inclusion of rewrite rows, or an overlapping union, only adds steps.
May-observations grow with added steps (`GrowsWithSteps`), so they are
preserved; must-observations shrink.  Neither class is conserved: a rule added
on an old term creates a new answer and falsifies a vacuous must-claim
(`inclusions_do_not_conserve_may`, `inclusions_do_not_conserve_must`), and an
added equation keeps every successor while falsifying a must-claim and
determinism (`adding_equation_preserves_may_only`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ExtensionConservativity

open Relation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.StructuralCoproduct
open Mettapedia.GSLT.LanguageDef.StructuralCoproductOperational
open Mettapedia.Logic.Relation (IsNormal Confluent)
open Mettapedia.Logic.Relation.ObservationTransport

/-! ## Structural coproducts conserve both classes -/

/-- One step of the premise-aware contextual engine, read as a relation. -/
def answerStep (base : BasePremiseEvaluator) (language : LanguageDef) (fuel : Nat)
    (term next : Pattern) : Prop :=
  next ∈ rewriteAt base language fuel term

section Embeddings

variable {name : String} {leftSymbols rightSymbols : LanguageDefSymbolMap}
  {left right : ValidatedLanguageDef}
  (coproduct : Compatibility name leftSymbols rightSymbols left right)
  {sourceBase targetBase : BasePremiseEvaluator}

/-- The left summand embeds its contextual engine exactly, at every fuel,
whenever the premise evaluators commute on its rules. -/
def leftEmbedding
    (commutes : RulePremiseEvaluatorsCommute leftSymbols left.language
      coproduct.combinedLanguage.language sourceBase targetBase)
    (fuel : Nat) :
    ExactEmbedding (answerStep sourceBase left.language fuel)
      (answerStep targetBase coproduct.combinedLanguage.language fuel) where
  embed := mapPattern leftSymbols
  injective := mapPattern_injective_of_constructor_injective leftSymbols
    coproduct.leftSymbolsInjective.constructor
  exact term next' := by
    unfold answerStep
    rw [StructuralCoproductOperational.Compatibility.left_rewriteAt_exact_onRules
      coproduct sourceBase targetBase commutes fuel term, List.mem_map]

/-- The right summand embeds its contextual engine exactly. -/
def rightEmbedding
    (commutes : RulePremiseEvaluatorsCommute rightSymbols right.language
      coproduct.combinedLanguage.language sourceBase targetBase)
    (fuel : Nat) :
    ExactEmbedding (answerStep sourceBase right.language fuel)
      (answerStep targetBase coproduct.combinedLanguage.language fuel) where
  embed := mapPattern rightSymbols
  injective := mapPattern_injective_of_constructor_injective rightSymbols
    coproduct.rightSymbolsInjective.constructor
  exact term next' := by
    unfold answerStep
    rw [StructuralCoproductOperational.Compatibility.right_rewriteAt_exact_onRules
      coproduct sourceBase targetBase commutes fuel term, List.mem_map]

/-- Exactness includes multiplicity: an embedded term has as many answers as
the term, in the same order. -/
theorem left_answer_count
    (commutes : RulePremiseEvaluatorsCommute leftSymbols left.language
      coproduct.combinedLanguage.language sourceBase targetBase)
    (fuel : Nat) (term : Pattern) :
    (rewriteAt targetBase coproduct.combinedLanguage.language fuel
        (mapPattern leftSymbols term)).length =
      (rewriteAt sourceBase left.language fuel term).length := by
  rw [StructuralCoproductOperational.Compatibility.left_rewriteAt_exact_onRules
    coproduct sourceBase targetBase commutes fuel term, List.length_map]

end Embeddings

/-- A structural coproduct with a given core as its left summand, together with
a premise evaluator on the coproduct that commutes with the core's evaluator
on the core's own rules. -/
structure LeftSummand (sourceBase : BasePremiseEvaluator) (core : ValidatedLanguageDef) where
  name : String
  leftSymbols : LanguageDefSymbolMap
  rightSymbols : LanguageDefSymbolMap
  right : ValidatedLanguageDef
  coproduct : Compatibility name leftSymbols rightSymbols core right
  targetBase : BasePremiseEvaluator
  commutes : RulePremiseEvaluatorsCommute leftSymbols core.language
    coproduct.combinedLanguage.language sourceBase targetBase

/-- A structural coproduct with a given core as its right summand. -/
structure RightSummand (sourceBase : BasePremiseEvaluator) (core : ValidatedLanguageDef) where
  name : String
  leftSymbols : LanguageDefSymbolMap
  rightSymbols : LanguageDefSymbolMap
  left : ValidatedLanguageDef
  coproduct : Compatibility name leftSymbols rightSymbols left core
  targetBase : BasePremiseEvaluator
  commutes : RulePremiseEvaluatorsCommute rightSymbols core.language
    coproduct.combinedLanguage.language sourceBase targetBase

/-- Coproduct extensions of a core on its left, as an extension layer. -/
def leftSummands (sourceBase : BasePremiseEvaluator) : ExtensionLayer ValidatedLanguageDef where
  Fiber := LeftSummand sourceBase

/-- Coproduct extensions of a core on its right, as an extension layer. -/
def rightSummands (sourceBase : BasePremiseEvaluator) : ExtensionLayer ValidatedLanguageDef where
  Fiber := RightSummand sourceBase

/-- **A structural coproduct conserves every transport-invariant observation on
its left summand.**  The observation of a core term inside the coproduct, with
the claim carried along the injection, equals the observation inside the core.
`May`, `Must`, `MayReach`, `MustReach` and `Deterministic` are instances. -/
theorem leftSummands_conserve (sourceBase : BasePremiseEvaluator)
    (observe : ObservationClass) (invariant : TransportInvariant observe)
    (fuel : Nat) (claim : Pattern → Prop) (term : Pattern) :
    (leftSummands sourceBase).Conserves
      (fun core => observe (answerStep sourceBase core.language fuel) claim term)
      (fun attached =>
        let summand : LeftSummand sourceBase attached.1 := attached.2
        observe (answerStep summand.targetBase summand.coproduct.combinedLanguage.language fuel)
          (imageClaim (mapPattern summand.leftSymbols) claim)
          (mapPattern summand.leftSymbols term)) := by
  intro attached
  let summand : LeftSummand sourceBase attached.1 := attached.2
  exact propext (invariant (leftEmbedding summand.coproduct summand.commutes fuel) claim term)

/-- **A structural coproduct conserves every transport-invariant observation on
its right summand.** -/
theorem rightSummands_conserve (sourceBase : BasePremiseEvaluator)
    (observe : ObservationClass) (invariant : TransportInvariant observe)
    (fuel : Nat) (claim : Pattern → Prop) (term : Pattern) :
    (rightSummands sourceBase).Conserves
      (fun core => observe (answerStep sourceBase core.language fuel) claim term)
      (fun attached =>
        let summand : RightSummand sourceBase attached.1 := attached.2
        observe (answerStep summand.targetBase summand.coproduct.combinedLanguage.language fuel)
          (imageClaim (mapPattern summand.rightSymbols) claim)
          (mapPattern summand.rightSymbols term)) := by
  intro attached
  let summand : RightSummand sourceBase attached.1 := attached.2
  exact propext (invariant (rightEmbedding summand.coproduct summand.commutes fuel) claim term)

/-! ## Inclusions and overlapping unions preserve may-observations only -/

/-- One step of the premise-free root engine, read as a relation. -/
def rootStep (language : LanguageDef) (term next : Pattern) : Prop :=
  next ∈ rewriteStep language term

/-- Ordered inclusions of rewrite rows over a language, as an extension layer.
The extended language keeps every rule of the base in order and may add rules
anywhere, including rules over the base's own constructors. -/
def inclusions : ExtensionLayer LanguageDef where
  Fiber base := {extended : LanguageDef // base.rewrites.Sublist extended.rewrites}

/-- **Inclusions preserve every observation that grows with steps.**  May and
reachable-may observations survive every ordered inclusion of rewrite rows. -/
theorem inclusions_preserve (observe : ObservationClass) (grows : GrowsWithSteps observe)
    (claim : Pattern → Prop) (term : Pattern) (attached : inclusions.Total) :
    observe (rootStep attached.1) claim term →
      observe (rootStep (attached.2 : inclusions.Fiber attached.1).1) claim term :=
  grows (fun source _ stepped =>
    (ModuleAlgebra.IdentityInterface.ordered_rewrite_answers_preserved
      (attached.2 : inclusions.Fiber attached.1).2 source).subset stepped)
    claim term

/-- An overlapping union keeps both sides' rewrite rows in order.  Each side
is an ordered inclusion into it, so its may-observations survive. -/
theorem overlappingUnion_preserves (observe : ObservationClass) (grows : GrowsWithSteps observe)
    (union left right : LanguageDef) (rows : union.rewrites = left.rewrites ++ right.rewrites)
    (claim : Pattern → Prop) (term : Pattern) :
    (observe (rootStep left) claim term → observe (rootStep union) claim term) ∧
      (observe (rootStep right) claim term → observe (rootStep union) claim term) := by
  constructor
  · exact grows (fun source _ stepped =>
      (ModuleAlgebra.IdentityInterface.ordered_rewrite_answers_preserved
        (rows ▸ List.sublist_append_left left.rewrites right.rewrites) source).subset
        stepped) claim term
  · exact grows (fun source _ stepped =>
      (ModuleAlgebra.IdentityInterface.ordered_rewrite_answers_preserved
        (rows ▸ List.sublist_append_right left.rewrites right.rewrites) source).subset
        stepped) claim term

/-- **An inclusion can give an old term a new answer and falsify a vacuous
must-claim.**  The base language has no rule for `A`; the extended language
keeps the base rules and adds `A ↦ B`. -/
theorem inclusion_gains_answer_and_breaks_must :
    ∃ (base : LanguageDef) (extended : inclusions.Fiber base),
      ¬ May (rootStep base) (fun next => next = .apply "B" []) (.apply "A" []) ∧
        May (rootStep extended.1) (fun next => next = .apply "B" []) (.apply "A" []) ∧
        Must (rootStep base) (fun next => next = .apply "A" []) (.apply "A" []) ∧
        ¬ Must (rootStep extended.1) (fun next => next = .apply "A" []) (.apply "A" []) := by
  obtain ⟨silent, answers⟩ :=
    ModuleAlgebra.IdentityInterface.inclusion_does_not_imply_reflection
  refine ⟨_, ⟨_, ModuleAlgebra.IdentityInterface.extra_rules_include_source⟩, ?_, ?_, ?_, ?_⟩
  · rintro ⟨next, stepped, _⟩
    rw [rootStep, silent] at stepped
    cases stepped
  · exact ⟨.apply "B" [], by rw [rootStep, answers]; simp, rfl⟩
  · intro next stepped
    rw [rootStep, silent] at stepped
    cases stepped
  · intro must
    have answered := must (.apply "B" []) (by rw [rootStep, answers]; simp)
    simp at answered

/-- **Inclusions do not conserve may-observations.** -/
theorem inclusions_do_not_conserve_may :
    ¬ inclusions.Conserves
      (fun base => May (rootStep base) (fun next => next = .apply "B" []) (.apply "A" []))
      (fun attached =>
        May (rootStep (attached.2 : inclusions.Fiber attached.1).1)
          (fun next => next = .apply "B" []) (.apply "A" [])) := by
  intro conserves
  obtain ⟨base, extended, notBefore, after, _, _⟩ := inclusion_gains_answer_and_breaks_must
  have same := conserves ⟨base, extended⟩
  dsimp only [ExtensionLayer.erase] at same
  rw [same] at after
  exact notBefore after

/-- **Inclusions do not conserve must-observations.** -/
theorem inclusions_do_not_conserve_must :
    ¬ inclusions.Conserves
      (fun base => Must (rootStep base) (fun next => next = .apply "A" []) (.apply "A" []))
      (fun attached =>
        Must (rootStep (attached.2 : inclusions.Fiber attached.1).1)
          (fun next => next = .apply "A" []) (.apply "A" [])) := by
  intro conserves
  obtain ⟨base, extended, _, _, before, notAfter⟩ := inclusion_gains_answer_and_breaks_must
  have same := conserves ⟨base, extended⟩
  dsimp only [ExtensionLayer.erase] at same
  rw [← same] at before
  exact notAfter before

section AddedEquation

open Mettapedia.OSLF.Framework.TypeSynthesis (langReduces)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData (schema)
open Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily
open Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.EquationSite

/-- **Adding an equation preserves may-observations only.**  In the sample
MeTTa program read as rewrites, adding the third equation keeps every
successor of `(g a)`; it falsifies the must-claim that every successor is `b`
and it makes `(g a)` nondeterministic. -/
theorem adding_equation_preserves_may_only :
    (∀ claim, May (langReduces (programLanguage "metta-program" sampleProgramPrefix)) claim
        (schema (call "g" (.symbol "a"))) →
      May (langReduces program) claim (schema (call "g" (.symbol "a")))) ∧
    Must (langReduces (programLanguage "metta-program" sampleProgramPrefix))
      (fun next => next = schema (.symbol "b")) (schema (call "g" (.symbol "a"))) ∧
    ¬ Must (langReduces program) (fun next => next = schema (.symbol "b"))
      (schema (call "g" (.symbol "a"))) ∧
    Functional (langReduces (programLanguage "metta-program" sampleProgramPrefix))
      (schema (call "g" (.symbol "a"))) ∧
    ¬ Functional (langReduces program) (schema (call "g" (.symbol "a"))) := by
  obtain ⟨keeps, prefixMust, fullNotMust⟩ := adding_equation_breaks_must
  refine ⟨fun claim => ?_, prefixMust, fullNotMust, ?_, ?_⟩
  · rintro ⟨next, stepped, holds⟩
    exact ⟨next, keeps next stepped, holds⟩
  · intro first second stepFirst stepSecond
    rw [prefixMust first stepFirst, prefixMust second stepSecond]
  · intro functional
    have toB : langReduces program (schema (call "g" (.symbol "a"))) (schema (.symbol "b")) :=
      (steps_iff _ program_noncontextual _ _).mpr (by rw [call_successors]; simp)
    have toC : langReduces program (schema (call "g" (.symbol "a"))) (schema (.symbol "c")) :=
      (steps_iff _ program_noncontextual _ _).mpr (by rw [call_successors]; simp)
    have same := functional _ _ toB toC
    revert same
    decide +kernel

end AddedEquation

#print axioms leftSummands_conserve
#print axioms rightSummands_conserve
#print axioms deterministic_transportInvariant
#print axioms inclusions_preserve
#print axioms inclusion_gains_answer_and_breaks_must
#print axioms inclusions_do_not_conserve_may
#print axioms inclusions_do_not_conserve_must
#print axioms adding_equation_preserves_may_only
#print axioms isNormal_transport
#print axioms ExactEmbedding.eqvGen_iff
#print axioms fork_conversion_not_conserved
#print axioms fork_not_confluent
#print axioms entry_conversion_conserved

end Mettapedia.GSLT.LanguageDef.ExtensionConservativity
