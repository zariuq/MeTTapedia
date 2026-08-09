import Mettapedia.GSLT.LanguageDef.ValidatedInferenceExtension

set_option linter.dupNamespace false

/-!
# Composing authored extension languages

Two extension languages over one core — a proof calculus and, say, a native
operation interface — should be authorable side by side and assembled into one
extension language.  `ExtensionLayer.product` already glues the *payloads*.
Nothing glues the *authoring languages*, and this module explains why and
supplies the structure that closes the gap.

## Where the gap is

A `CoGSLTLayer` carries an elaborator `Term → Option (Fiber base)` and nothing
else.  Suppose two of them, with fibres `F` and `G`, and suppose we want their
composite to have fibre `F × G`.  A document that mentions only left-hand
declarations must still elaborate to a *pair*, so the composite has to invent a
`G`.  Nothing in `CoGSLTLayer` supplies one, and the choice is not free:
`padding_is_authored` exhibits two right-hand layers over one carrier whose
composites disagree on a document containing no right-hand declaration at all.

The missing structure is not an independently selected unit or payload
algebra.  It is authored concatenation together with the law that elaboration
carries concatenation to payload merge.  The meaning of the authored empty
term is then the payload unit, and both neutral laws and associativity follow.
`GSLT.CompositionalElaboration.toPartialMonoid` proves this derivation.

## What then composes

A `CompositionalLayer` is an indexed family of exact elaborations from
compositional GSLTs satisfying that homomorphism law.  Every compositional
layer induces a `CoGSLTLayer`, and compositional layers are closed under
`product`:

* the two complete authored theories embed into a free mixed-document GSLT;
* payload merge is the product of the two derived partial monoids;
* quotation places the two canonical component terms in one mixed document;
* exact round trip and append preservation are theorems.

`product_elaborates_left_only` and `product_elaborates_right_only` are the
compatibility laws: the composite restricted to one side's documents is that
side's elaborator, padded by the meaning of the other side's authored empty
term.  That is what makes the assembly conservative on each component rather
than merely type-correct.

## Where it genuinely stops

Composition of *authored* extensions is total.  Composition of *admitted* ones
is not: `admission_not_closed_under_composition` exhibits two proof calculi,
each admitted against one language, whose merge is rejected.  The cause is name
collision, and it is not repairable by any choice of elaborator — two
declarations of one judgment head are ambiguous however they were authored.

`Compatible` names the overlap condition this forces, and
`append_isSome_of_compatible` discharges the part of it that the partial monoid
already sees.  The gluing law itself — compatible admitted calculi merge to an
admitted calculus — is `ExtensionGluing.gluing_of_compatible`.

So the extension architecture is a fibration over the core, with a fibrewise
partial monoid on authored declarations and a compatibility relation on
admitted ones.  Authored composition is unconditional; admitted composition
holds exactly on compatible overlaps.
-/

namespace Mettapedia.GSLT.LanguageDef.ExtensionComposition

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Extension
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uBase uFiber uFiberRight uGen uGenRight
universe uArtifactLeft uArtifactRight uObservationLeft uObservationRight

/-! ## The proof-calculus partial monoid

`ProofCalculus` already carries this structure; the associativity available
beside it is the conditional form, so the unconditional law is proved here. -/

/-- Authored proof calculi assemble as a partial monoid, failing exactly on a
conflict of rooted conversion authority. -/
def proofCalculusMonoid : PartialMonoid ProofCalculus where
  unit := .empty
  op := ProofCalculus.append?
  unit_op := ProofCalculus.empty_append
  op_unit := ProofCalculus.append_empty
  op_assoc := by
    rintro ⟨firstJudgments, firstRules, firstConversion⟩
      ⟨secondJudgments, secondRules, secondConversion⟩
      ⟨thirdJudgments, thirdRules, thirdConversion⟩
    cases firstConversion <;> cases secondConversion <;> cases thirdConversion <;>
      simp [ProofCalculus.append?, List.append_assoc]

/-! ## Folding a document

Elaboration of a declaration list is the fold of its generators through the
derived partial monoid.  The generic fold lives in `GSLT.Core.Composition`;
this specialization only removes the per-generator `Option`. -/

/-- Fold a generator list into a payload, failing on the first conflict. -/
def foldWith {Fiber : Type u} {Generator : Type v}
    (monoid : PartialMonoid Fiber) (interpret : Generator → Fiber) :
    List Generator → Option Fiber :=
  monoid.foldOption (fun generator => some (interpret generator))

@[simp] theorem foldWith_nil {Fiber : Type u} {Generator : Type v}
    (monoid : PartialMonoid Fiber) (interpret : Generator → Fiber) :
    foldWith monoid interpret [] = some monoid.unit :=
  rfl

@[simp] theorem foldWith_cons {Fiber : Type u} {Generator : Type v}
    (monoid : PartialMonoid Fiber) (interpret : Generator → Fiber)
    (generator : Generator) (rest : List Generator) :
    foldWith monoid interpret (generator :: rest) =
      (foldWith monoid interpret rest).bind fun tail =>
        monoid.op (interpret generator) tail :=
  rfl

/-- **The fold is a homomorphism of partial monoids.**  Concatenating documents
merges their payloads, and a conflict anywhere is a conflict overall.  This is
the law that makes side-by-side authoring meaningful. -/
theorem foldWith_append {Fiber : Type u} {Generator : Type v}
    (monoid : PartialMonoid Fiber) (interpret : Generator → Fiber)
    (first second : List Generator) :
    foldWith monoid interpret (first ++ second) =
      (foldWith monoid interpret first).bind fun leftValue =>
        (foldWith monoid interpret second).bind fun rightValue =>
          monoid.op leftValue rightValue :=
  PartialMonoid.foldOption_append monoid
    (fun generator => some (interpret generator)) first second

/-! ## Compositional layers

An indexed compositional layer is only a family of law-bearing
`CompositionalElaboration`s.  In particular, it does not carry a payload
partial monoid as independent data. -/

/-- A family of compositional authored GSLTs indexed by an unchanged base. -/
structure CompositionalLayer (Base : Type uBase) where
  /-- The payload attached over each base. -/
  Fiber : Base → Type uFiber
  /-- The authored language and its law-preserving exact elaboration. -/
  system : ∀ base, GSLT.CompositionalElaboration (Fiber base)

namespace CompositionalLayer

variable {Base : Type uBase}

/-- Every exact declaration codec supplies an indexed compositional layer.
The index is unchanged and does not influence raw decoding; contextual
admission may subsequently restrict the resulting payload fibre. -/
def ofCodec (Base : Type uBase) {Syntax : Type} {Payload : Type uFiber}
    (codec : ExactDeclarationCodec Syntax Payload) :
    CompositionalLayer.{uBase, uFiber} Base where
  Fiber := fun _ => List Payload
  system := fun _ => codec.compositionalElaboration

/-- The payload partial monoid forced by authored concatenation. -/
def monoid (layer : CompositionalLayer.{uBase, uFiber} Base) (base : Base) :
    PartialMonoid (layer.Fiber base) :=
  (layer.system base).toPartialMonoid

/-- Elaborate an authored term over one base. -/
def elaborate (layer : CompositionalLayer.{uBase, uFiber} Base) (base : Base) :
    (layer.system base).authoring.theory.Term → Option (layer.Fiber base) :=
  (layer.system base).elaboration.elaborate

/-- Canonical authored representative of a payload. -/
def quote (layer : CompositionalLayer.{uBase, uFiber} Base) (base : Base) :
    layer.Fiber base → (layer.system base).authoring.theory.Term :=
  (layer.system base).elaboration.quote

@[simp] theorem elaborate_quote
    (layer : CompositionalLayer.{uBase, uFiber} Base) (base : Base)
    (value : layer.Fiber base) :
    layer.elaborate base (layer.quote base value) = some value :=
  (layer.system base).elaboration.elaborate_quote value

/-! ### The composite -/

/-- **Two authored extension languages assemble into one.**  The source is the
generic product of the two complete compositional elaborations, applied
pointwise over the unchanged base.  The LanguageDef layer adds no assembly
law of its own. -/
def product
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base) :
    CompositionalLayer.{uBase, max uFiber uFiberRight} Base where
  Fiber := fun base => left.Fiber base × right.Fiber base
  system := fun base => (left.system base).product (right.system base)

@[simp] theorem product_fiber
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    (base : Base) :
    (left.product right).Fiber base = (left.Fiber base × right.Fiber base) :=
  rfl

/-- The composite restricted to a left-hand term is the left elaborator,
padded only by the right authored empty payload. -/
theorem product_elaborates_left_only
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    (base : Base) (source : (left.system base).authoring.theory.Term) :
    (left.product right).elaborate base [Sum.inl source] =
      (left.elaborate base source).map
        fun value => (value, (right.system base).emptyPayload) := by
  exact (left.system base).product_elaborates_left_only
    (right.system base) source

/-- And symmetrically on the right. -/
theorem product_elaborates_right_only
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    (base : Base) (source : (right.system base).authoring.theory.Term) :
    (left.product right).elaborate base [Sum.inr source] =
      (right.elaborate base source).map
        fun value => ((left.system base).emptyPayload, value) := by
  exact (left.system base).product_elaborates_right_only
    (right.system base) source

/-! ### The coGSLT extension induced by a compositional layer -/

/-- Forget only the compositional law, retaining the exact authored GSLT
elaboration. -/
def toCoGSLTLayer (layer : CompositionalLayer.{uBase, uFiber} Base) :
    CoGSLTLayer.{uBase, uFiber} Base where
  Fiber := layer.Fiber
  sourceGSLT := fun base => (layer.system base).authoring.theory
  elaborate := layer.elaborate
  quote := layer.quote
  elaborate_quote := layer.elaborate_quote
  elaborate_equation := fun base => (layer.system base).elaboration.equation
  elaborate_rewrite := fun base => (layer.system base).elaboration.rewrite

/-- Forgetting the compositional law from a codec-induced layer recovers the
ordinary coGSLT layer induced by that same codec, definitionally.  There is one
elaborator and one quotation map, not parallel authorities. -/
@[simp] theorem ofCodec_toCoGSLTLayer (Base : Type uBase)
    {Syntax : Type} {Payload : Type uFiber}
    (codec : ExactDeclarationCodec Syntax Payload) :
    (ofCodec Base codec).toCoGSLTLayer = codec.layer Base :=
  rfl

@[simp] theorem toCoGSLTLayer_fiber
    (layer : CompositionalLayer.{uBase, uFiber} Base) (base : Base) :
    layer.toCoGSLTLayer.Fiber base = layer.Fiber base :=
  rfl

/-- The composite coGSLT layer has exactly the product fibre. -/
theorem toCoGSLTLayer_product_fiber
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    (base : Base) :
    (left.product right).toCoGSLTLayer.Fiber base =
      (left.Fiber base × right.Fiber base) :=
  rfl

/-! ### Products of certified realizations -/

/-- Independent certified realizations assemble over the generic product
layer.  The artifact and the named observation are paired componentwise, so
adequacy of the composite is derived solely from adequacy of its components. -/
def productRealization
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {LeftObservation : Base → Type uObservationLeft}
    {RightObservation : Base → Type uObservationRight}
    (leftRealization : CoGSLTLayer.Realization left.toCoGSLTLayer
      LeftArtifact LeftObservation)
    (rightRealization : CoGSLTLayer.Realization right.toCoGSLTLayer
      RightArtifact RightObservation) :
    CoGSLTLayer.Realization (left.product right).toCoGSLTLayer
      (fun base => LeftArtifact base × RightArtifact base)
      (fun base => LeftObservation base × RightObservation base) :=
  leftRealization.product rightRealization

@[simp] theorem productRealization_compile
    (left : CompositionalLayer.{uBase, uFiber} Base)
    (right : CompositionalLayer.{uBase, uFiberRight} Base)
    {LeftArtifact : Base → Type uArtifactLeft}
    {RightArtifact : Base → Type uArtifactRight}
    {LeftObservation : Base → Type uObservationLeft}
    {RightObservation : Base → Type uObservationRight}
    (leftRealization : CoGSLTLayer.Realization left.toCoGSLTLayer
      LeftArtifact LeftObservation)
    (rightRealization : CoGSLTLayer.Realization right.toCoGSLTLayer
      RightArtifact RightObservation)
    (base : Base) (declarations : left.Fiber base × right.Fiber base) :
    (left.productRealization right leftRealization rightRealization).compile
        base declarations =
      (leftRealization.compile base declarations.1,
        rightRealization.compile base declarations.2) :=
  rfl

end CompositionalLayer

/-! ## The inference extension is compositional -/

/-- The generic partial-monoid fold is exactly the established calculus
elaborator. -/
theorem foldWith_proofCalculus_eq_elaborate :
    ∀ source : CalculusSyntax,
      foldWith proofCalculusMonoid elaborateDeclaration source =
        elaborate source
  | [] => rfl
  | declaration :: declarations => by
      change
        (foldWith proofCalculusMonoid elaborateDeclaration declarations).bind
            (fun tail =>
              (elaborateDeclaration declaration).append? tail) =
          (elaborate declarations).bind fun tail =>
            (elaborateDeclaration declaration).append? tail
      rw [foldWith_proofCalculus_eq_elaborate declarations]

/-- The one canonical compositional elaboration of authored proof-calculus
documents.  Both the general extension layer and the admitted calculus layer
below reuse this object; there is no second construction whose laws could
drift. -/
def calculusAuthoringGSLT : GSLT.CompositionalElaboration ProofCalculus where
  authoring := calculusSyntax
  elaboration :=
    { elaborate := elaborate
      equation := elaborate_equation
      rewrite := elaborate_rewrite
      quote := quote
      elaborate_quote := elaborate_quote }
  emptyPayload := .empty
  merge := ProofCalculus.append?
  elaborate_empty := elaborate_empty
  elaborate_append := elaborate_append

/-- The proof-calculus extension with its complete compositional structure.
Its atom theory is the authored calculus-declaration GSLT, not a newly
generated rewrite-free wrapper. -/
def calculusLayer : CompositionalLayer LanguageDef where
  Fiber := fun _ => ProofCalculus
  system := fun _ => calculusAuthoringGSLT

/-- The generic compositional construction recovers the established authored
calculus GSLT definitionally. -/
@[simp] theorem calculusLayer_sourceGSLT (language : LanguageDef) :
    calculusLayer.toCoGSLTLayer.sourceGSLT language = calculusSyntaxGSLT :=
  rfl

/-- The generic compositional construction uses the established calculus
elaborator, not a parallel decoder. -/
@[simp] theorem calculusLayer_elaborate (language : LanguageDef)
    (source : CalculusSyntax) :
    calculusLayer.toCoGSLTLayer.elaborate language source = elaborate source :=
  rfl

/-- Canonical quotation is also shared definitionally. -/
@[simp] theorem calculusLayer_quote (language : LanguageDef)
    (calculus : ProofCalculus) :
    calculusLayer.toCoGSLTLayer.quote language calculus = quote calculus :=
  rfl

/-! ## The empty meaning is semantic data

Why a bare `CoGSLTLayer` cannot be composed: the value the composite assigns to
a document that mentions no right-hand declaration still depends on the right
layer.  Two right-hand layers over one carrier make that dependence visible. -/

private def trivialMonoid : PartialMonoid Unit where
  unit := ()
  op := fun _ _ => some ()
  unit_op := fun _ => rfl
  op_unit := fun _ => rfl
  op_assoc := fun _ _ _ => rfl

private def trivialLayer : CompositionalLayer Unit where
  Fiber := fun _ => Unit
  system := fun _ =>
    { authoring := GSLT.freeDocumentCompositional (GSLT.discrete Unit)
      elaboration :=
        { elaborate := fun _ => some ()
          equation := by intro _ _ _; rfl
          rewrite := by intro _ _ _; rfl
          quote := fun _ => []
          elaborate_quote := fun _ => rfl }
      emptyPayload := ()
      merge := trivialMonoid.op
      elaborate_empty := rfl
      elaborate_append := by intro _ _; rfl }

private def orMonoid : PartialMonoid Bool where
  unit := false
  op := fun first second => some (first || second)
  unit_op := by intro value; simp
  op_unit := by intro value; simp
  op_assoc := by intro first second third; simp [Bool.or_assoc]

private def andMonoid : PartialMonoid Bool where
  unit := true
  op := fun first second => some (first && second)
  unit_op := by intro value; simp
  op_unit := by intro value; simp
  op_assoc := by intro first second third; simp [Bool.and_assoc]

private def orFlagLayer : CompositionalLayer Unit where
  Fiber := fun _ => Bool
  system := fun _ =>
    { authoring := GSLT.freeDocumentCompositional (GSLT.discrete Unit)
      elaboration :=
        { elaborate := foldWith orMonoid fun _ => true
          equation := by
            intro source target equivalent
            have equal := GSLT.DocumentEquiv.eq_of
              (fun {left right} component => by
                change left = right at component
                exact component) equivalent
            subst target
            rfl
          rewrite := by
            intro source target step
            rcases step with
              ⟨_, _, _, raw, _⟩
            exact (GSLT.RawDocumentStep.false_of_no_step
              (fun {left right} impossible => by
                change False at impossible
                exact impossible) raw).elim
          quote := fun flag => if flag then [()] else []
          elaborate_quote := by intro flag; cases flag <;> rfl }
      emptyPayload := false
      merge := orMonoid.op
      elaborate_empty := rfl
      elaborate_append := foldWith_append orMonoid (fun _ => true) }

private def andFlagLayer : CompositionalLayer Unit where
  Fiber := fun _ => Bool
  system := fun _ =>
    { authoring := GSLT.freeDocumentCompositional (GSLT.discrete Unit)
      elaboration :=
        { elaborate := foldWith andMonoid fun _ => false
          equation := by
            intro source target equivalent
            have equal := GSLT.DocumentEquiv.eq_of
              (fun {left right} component => by
                change left = right at component
                exact component) equivalent
            subst target
            rfl
          rewrite := by
            intro source target step
            rcases step with
              ⟨_, _, _, raw, _⟩
            exact (GSLT.RawDocumentStep.false_of_no_step
              (fun {left right} impossible => by
                change False at impossible
                exact impossible) raw).elim
          quote := fun flag => if flag then [] else [()]
          elaborate_quote := by intro flag; cases flag <;> rfl }
      emptyPayload := true
      merge := andMonoid.op
      elaborate_empty := rfl
      elaborate_append := foldWith_append andMonoid (fun _ => false) }

private theorem orComposite_left_only :
    (trivialLayer.product orFlagLayer).elaborate () [Sum.inl [()]] =
      some ((), false) :=
  rfl

private theorem andComposite_left_only :
    (trivialLayer.product andFlagLayer).elaborate () [Sum.inl [()]] =
      some ((), true) :=
  rfl

/-- **The meaning of an empty authored term matters.**  One and the same
left-hand document elaborates to different payloads under two composites whose
right-hand elaborators assign different meanings to their empty term.  A bare
`CoGSLTLayer` names neither composition nor its empty term, so it supplies no
canonical padding value. -/
theorem padding_is_authored :
    ((trivialLayer.product orFlagLayer).elaborate () [Sum.inl [()]]).map Prod.snd ≠
      ((trivialLayer.product andFlagLayer).elaborate () [Sum.inl [()]]).map
        Prod.snd := by
  intro equality
  rw [orComposite_left_only, andComposite_left_only] at equality
  exact Bool.noConfusion (Option.some.inj equality)

/-! ## Admission is where composition genuinely stops

Authored composition is total.  Admitted composition is not, and no elaborator
repairs it: two declarations of one judgment head are ambiguous however they
were written. -/

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private def canaryLanguage : LanguageDef :=
  LanguageDef.empty "extension-composition-canary"

private def canaryJudgment : JudgmentDecl := ⟨"Canary", 1⟩

private def canaryCalculus : ProofCalculus := { judgments := [canaryJudgment] }

private def mergedCalculus : ProofCalculus :=
  { judgments := [canaryJudgment, canaryJudgment] }

private theorem canaryLanguage_validate : canaryLanguage.validate = [] :=
  emptyLanguage_validate "extension-composition-canary"

private theorem canaryCalculus_valid :
    (Presentation.mk canaryLanguage canaryCalculus).isValidV2 = true := by
  have base : (Presentation.mk canaryLanguage canaryCalculus).isValidV1 = true := by
    simp [Presentation.isValidV1, Presentation.ruleIds, canaryCalculus,
      canaryLanguage_validate]
  unfold Presentation.isValidV2
  rw [base]
  decide

private theorem canaryCalculus_merge :
    proofCalculusMonoid.op canaryCalculus canaryCalculus = some mergedCalculus :=
  rfl

private theorem mergedCalculus_invalid :
    (Presentation.mk canaryLanguage mergedCalculus).isValidV2 = false := by
  have signature :
      (Presentation.mk canaryLanguage mergedCalculus).judgmentSignatureValid
        = false := by decide
  simp [Presentation.isValidV2, signature]

/-- **Admission is not closed under composition.**  Two proof calculi, each
admitted against one term language, merge successfully as authored data and are
then rejected.  Composition of extensions is therefore a fibration with a
compatibility condition, not an unconditional gluing. -/
theorem admission_not_closed_under_composition :
    ∃ (language : LanguageDef) (first second merged : ProofCalculus),
      (Presentation.mk language first).isValidV2 = true ∧
        (Presentation.mk language second).isValidV2 = true ∧
        proofCalculusMonoid.op first second = some merged ∧
        (Presentation.mk language merged).isValidV2 = false :=
  ⟨canaryLanguage, canaryCalculus, canaryCalculus, mergedCalculus,
    canaryCalculus_valid, canaryCalculus_valid, canaryCalculus_merge,
    mergedCalculus_invalid⟩

/-! ## The overlap condition

What compatible means for two authored proof calculi, and the part of it the
partial monoid already enforces. -/

/-- Two authored calculi overlap cleanly: no shared judgment head, no shared
rule identifier, and at most one rooted conversion authority. -/
structure Compatible (first second : ProofCalculus) : Prop where
  /-- Judgment heads are disjoint. -/
  judgmentHeads : ∀ head ∈ first.judgments.map JudgmentDecl.head,
    head ∉ second.judgments.map JudgmentDecl.head
  /-- Rule identifiers are disjoint. -/
  ruleIds : ∀ id ∈ first.rules.map RuleSchema.id,
    id ∉ second.rules.map RuleSchema.id
  /-- At most one side roots a conversion interface. -/
  conversion : first.conversion = none ∨ second.conversion = none

/-- Compatible calculi always merge as authored data. -/
theorem append_isSome_of_compatible {first second : ProofCalculus}
    (compatible : Compatible first second) :
    (proofCalculusMonoid.op first second).isSome := by
  cases compatible.conversion with
  | inl firstNone =>
      cases hsecond : second.conversion <;>
        simp [proofCalculusMonoid, ProofCalculus.append?, firstNone, hsecond]
  | inr secondNone =>
      cases hfirst : first.conversion <;>
        simp [proofCalculusMonoid, ProofCalculus.append?, hfirst, secondNone]

/-- The counterexample above is incompatible, as it must be: it declares one
judgment head twice. -/
theorem canary_not_compatible : ¬ Compatible canaryCalculus canaryCalculus := by
  intro compatible
  have member : canaryJudgment.head ∈
      canaryCalculus.judgments.map JudgmentDecl.head := by
    simp [canaryCalculus]
  exact compatible.judgmentHeads canaryJudgment.head member member

/-! ## Where this sits

Composition of authored extension languages is settled here: `product` is
total, its round trip is proved, and both restriction laws hold.  The
compatibility relation and the negative result are here too, so the boundary
between the two regimes is visible in one place.

The gluing law over that boundary is `ExtensionGluing.gluing_of_compatible`.

Two things this does **not** claim.  Nothing here compiles an extension into
core rewrites, so no interpreter/compiler agreement is asserted — that is the
staging theorem and it is untouched.  And a fibration with a gluing law on
pairwise overlaps is not yet descent: descent needs covers, and no notion of
cover is defined for language cores.
-/

end Mettapedia.GSLT.LanguageDef.ExtensionComposition
