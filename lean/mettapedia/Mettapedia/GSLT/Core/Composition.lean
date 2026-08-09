import Mettapedia.GSLT.Core.GSLT

set_option linter.dupNamespace false

/-!
# Composition internal to graph-structured lambda theories

A collection of declarations is not an auxiliary container around a GSLT.
It is itself a GSLT: its terms are finite documents, its equations act
pointwise, and its rewrites act at any declaration occurrence.

This module supplies two free constructions.

* `GSLT.disjointSum` combines two theories without inventing interactions.
* `GSLT.freeDocument` freely closes a theory under an empty document and
  concatenation.

Their composite, `GSLT.compositeDocuments`, is the canonical language in which
declarations from two theories may be interleaved.  The injections preserve and
reflect equations and rewrites, so a component theory is not merely serialized
inside the composite.
-/

namespace Mettapedia.GSLT

universe u v uBase uSource uSourceRight uArtifact uArtifactRight
  uObservation uObservationRight uLowered uFinal

/-! ## Partial composition algebras

The payload algebra below is generic: it is not specific to language
definitions or proof calculi.  A compositional elaboration derives one from
the equations of its authored GSLT; consumers do not select it independently.
-/

/-- A unit together with a partial associative merge.  Associativity is
unconditional, so both bracketings fail together or succeed with the same
result. -/
structure PartialMonoid (Carrier : Type u) where
  unit : Carrier
  op : Carrier → Carrier → Option Carrier
  unit_op : ∀ value, op unit value = some value
  op_unit : ∀ value, op value unit = some value
  op_assoc : ∀ first second third,
    (op first second).bind (fun merged => op merged third) =
      (op second third).bind (fun merged => op first merged)

/-- Two independent partial merges compose componentwise. -/
private theorem prod_bind_normal {Left : Type u} {Right : Type v}
    (leftFirst : Option Left) (rightFirst : Option Right)
    (leftNext : Left → Option Left) (rightNext : Right → Option Right) :
    ((leftFirst.bind fun leftValue =>
        rightFirst.bind fun rightValue => some (leftValue, rightValue)).bind
      fun merged =>
        (leftNext merged.1).bind fun leftValue =>
          (rightNext merged.2).bind fun rightValue => some (leftValue, rightValue))
      = (leftFirst.bind leftNext).bind fun leftValue =>
          (rightFirst.bind rightNext).bind fun rightValue =>
            some (leftValue, rightValue) := by
  cases leftFirst <;> cases rightFirst <;> simp

/-- The product of independent partial monoids. -/
def PartialMonoid.prod {Left : Type u} {Right : Type v}
    (left : PartialMonoid Left) (right : PartialMonoid Right) :
    PartialMonoid (Left × Right) where
  unit := (left.unit, right.unit)
  op := fun first second =>
    (left.op first.1 second.1).bind fun mergedLeft =>
      (right.op first.2 second.2).bind fun mergedRight =>
        some (mergedLeft, mergedRight)
  unit_op := by
    rintro ⟨leftValue, rightValue⟩
    simp [left.unit_op, right.unit_op]
  op_unit := by
    rintro ⟨leftValue, rightValue⟩
    simp [left.op_unit, right.op_unit]
  op_assoc := by
    rintro ⟨firstLeft, firstRight⟩ ⟨secondLeft, secondRight⟩ ⟨thirdLeft, thirdRight⟩
    rw [prod_bind_normal (left.op firstLeft secondLeft)
        (right.op firstRight secondRight)
        (fun value => left.op value thirdLeft)
        (fun value => right.op value thirdRight),
      prod_bind_normal (left.op secondLeft thirdLeft)
        (right.op secondRight thirdRight)
        (fun value => left.op firstLeft value)
        (fun value => right.op firstRight value),
      left.op_assoc firstLeft secondLeft thirdLeft,
      right.op_assoc firstRight secondRight thirdRight]

namespace PartialMonoid

/-- Fold possibly failing generator interpretations through a partial
monoid.  Failure of either an interpretation or a merge is retained. -/
def foldOption {Carrier : Type u} {Generator : Type v}
    (monoid : PartialMonoid Carrier) (interpret : Generator → Option Carrier) :
    List Generator → Option Carrier
  | [] => some monoid.unit
  | generator :: rest => do
      let head ← interpret generator
      let tail ← monoid.foldOption interpret rest
      monoid.op head tail

@[simp] theorem foldOption_nil {Carrier : Type u} {Generator : Type v}
    (monoid : PartialMonoid Carrier) (interpret : Generator → Option Carrier) :
    monoid.foldOption interpret [] = some monoid.unit :=
  rfl

@[simp] theorem foldOption_cons {Carrier : Type u} {Generator : Type v}
    (monoid : PartialMonoid Carrier) (interpret : Generator → Option Carrier)
    (generator : Generator) (rest : List Generator) :
    monoid.foldOption interpret (generator :: rest) =
      (interpret generator).bind fun head =>
        (monoid.foldOption interpret rest).bind fun tail =>
          monoid.op head tail :=
  rfl

/-- Folding is a homomorphism from document concatenation to partial merge. -/
theorem foldOption_append {Carrier : Type u} {Generator : Type v}
    (monoid : PartialMonoid Carrier) (interpret : Generator → Option Carrier)
    (first second : List Generator) :
    monoid.foldOption interpret (first ++ second) =
      (monoid.foldOption interpret first).bind fun leftValue =>
        (monoid.foldOption interpret second).bind fun rightValue =>
          monoid.op leftValue rightValue := by
  induction first with
  | nil =>
      rw [List.nil_append]
      cases hsecond : monoid.foldOption interpret second with
      | none => rfl
      | some value => exact (monoid.unit_op value).symm
  | cons generator rest inductionHypothesis =>
      simp only [List.cons_append, foldOption]
      cases hhead : interpret generator with
      | none => rfl
      | some head =>
          rw [inductionHypothesis]
          cases hrest : monoid.foldOption interpret rest with
          | none => rfl
          | some restValue =>
              cases hsecond : monoid.foldOption interpret second with
              | none => simp
              | some secondValue =>
                  exact (monoid.op_assoc head restValue secondValue).symm

end PartialMonoid

/-! ## Certified realizations

Staged compilation is independent of language-definition fibres.  It is a
map from semantic source objects to backend artifacts together with an
explicitly named observation and a proof that compilation preserves it.
The source, artifact, and observation may all vary over an index; a coGSLT
layer later instantiates the source family with its elaborated fibres. -/

/-- A family of certified realizations sharing one observation contract. -/
structure Realization {Base : Type uBase}
    (Source : Base → Type uSource)
    (Artifact : Base → Type uArtifact)
    (Observation : Base → Type uObservation) where
  compile : ∀ base, Source base → Artifact base
  observeSource : ∀ base, Source base → Observation base
  observeArtifact : ∀ base, Artifact base → Observation base
  adequate : ∀ base source,
    observeArtifact base (compile base source) = observeSource base source

/-- The unindexed case of a certified realization. -/
abbrev SimpleRealization (Source : Type uSource)
    (Artifact : Type uArtifact) (Observation : Type uObservation) :=
  Realization (fun _ : Unit => Source) (fun _ => Artifact)
    (fun _ => Observation)

namespace Realization

/-- The certificate is the common semantic interface for every realization. -/
@[simp] theorem observe_compile {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    (realization : Realization Source Artifact Observation) (base : Base)
    (source : Source base) :
    realization.observeArtifact base (realization.compile base source) =
      realization.observeSource base source :=
  realization.adequate base source

/-- The identity realization changes no representation and observes its
source directly.  It is the neutral stage for certified lowering. -/
def identity {Base : Type uBase}
    {Source : Base → Type uSource}
    {Observation : Base → Type uObservation}
    (observe : ∀ base, Source base → Observation base) :
    Realization Source Source Observation where
  compile := fun _ source => source
  observeSource := observe
  observeArtifact := observe
  adequate := by intros; rfl

/-- Continue a certified realization through one more lowering pass.  The
second pass may change the artifact representation, but must preserve the
same named observation. -/
def stage {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifact}
    {Lowered : Base → Type uLowered}
    {Observation : Base → Type uObservation}
    (first : Realization Source Artifact Observation)
    (lower : ∀ base, Artifact base → Lowered base)
    (observeLowered : ∀ base, Lowered base → Observation base)
    (lowerAdequate : ∀ base artifact,
      observeLowered base (lower base artifact) =
        first.observeArtifact base artifact) :
    Realization Source Lowered Observation where
  compile := fun base source => lower base (first.compile base source)
  observeSource := first.observeSource
  observeArtifact := observeLowered
  adequate := by
    intro base source
    rw [lowerAdequate, first.adequate]

/-- Compose two certified realizations whose observations agree at their
shared intermediate representation.  This is `stage` with the second
realization supplying the lowering function and its adequacy certificate. -/
def trans {Base : Type uBase}
    {Source : Base → Type uSource}
    {Intermediate : Base → Type uArtifact}
    {Artifact : Base → Type uLowered}
    {Observation : Base → Type uObservation}
    (first : Realization Source Intermediate Observation)
    (second : Realization Intermediate Artifact Observation)
    (middleAgreement : ∀ base intermediate,
      second.observeSource base intermediate =
        first.observeArtifact base intermediate) :
    Realization Source Artifact Observation :=
  first.stage second.compile second.observeArtifact (by
    intro base intermediate
    rw [second.adequate, middleAgreement])

/-- Choose between two certified backends source by source.  Selection changes
the artifact and performance, never the observation contract. -/
def select {Base : Type uBase}
    {Source : Base → Type uSource}
    {Left : Base → Type uArtifact}
    {Right : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (left : Realization Source Left Observation)
    (right : Realization Source Right Observation)
    (agree : ∀ base source,
      right.observeSource base source = left.observeSource base source)
    (selectBackend : ∀ base, Source base → Bool) :
    Realization Source (fun base => Left base ⊕ Right base) Observation where
  compile := fun base source =>
    if selectBackend base source then
      .inl (left.compile base source)
    else
      .inr (right.compile base source)
  observeSource := left.observeSource
  observeArtifact := fun base => Sum.elim
    (left.observeArtifact base) (right.observeArtifact base)
  adequate := by
    intro base source
    split
    · exact left.adequate base source
    · change right.observeArtifact base (right.compile base source) =
        left.observeSource base source
      rw [right.adequate, agree]

/-- Independent certified realizations compose componentwise. -/
def product {Base : Type uBase}
    {LeftSource : Base → Type uSource}
    {RightSource : Base → Type uSourceRight}
    {LeftArtifact : Base → Type uArtifact}
    {RightArtifact : Base → Type uArtifactRight}
    {LeftObservation : Base → Type uObservation}
    {RightObservation : Base → Type uObservationRight}
    (left : Realization LeftSource LeftArtifact LeftObservation)
    (right : Realization RightSource RightArtifact RightObservation) :
    Realization
      (fun base => LeftSource base × RightSource base)
      (fun base => LeftArtifact base × RightArtifact base)
      (fun base => LeftObservation base × RightObservation base) where
  compile := fun base source =>
    (left.compile base source.1, right.compile base source.2)
  observeSource := fun base source =>
    (left.observeSource base source.1, right.observeSource base source.2)
  observeArtifact := fun base artifacts =>
    (left.observeArtifact base artifacts.1,
      right.observeArtifact base artifacts.2)
  adequate := by
    intro base source
    rw [left.adequate, right.adequate]

/-- Weaken or transform a realization's named observation without changing
its compiler or artifact.  The new adequacy certificate is obtained by
applying the observation map to the original certificate.  In particular,
an exact bag realization may lawfully induce a support-only realization while
remaining explicit about the information that was forgotten. -/
def mapObservation {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    {MappedObservation : Base → Type uObservationRight}
    (realization : Realization Source Artifact Observation)
    (map : ∀ base, Observation base → MappedObservation base) :
    Realization Source Artifact MappedObservation where
  compile := realization.compile
  observeSource := fun base source =>
    map base (realization.observeSource base source)
  observeArtifact := fun base artifact =>
    map base (realization.observeArtifact base artifact)
  adequate := by
    intro base source
    rw [realization.adequate]

@[simp] theorem stage_compile {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifact}
    {Lowered : Base → Type uLowered}
    {Observation : Base → Type uObservation}
    (first : Realization Source Artifact Observation)
    (lower : ∀ base, Artifact base → Lowered base)
    (observeLowered : ∀ base, Lowered base → Observation base)
    (lowerAdequate : ∀ base artifact,
      observeLowered base (lower base artifact) =
        first.observeArtifact base artifact)
    (base : Base) (source : Source base) :
    (first.stage lower observeLowered lowerAdequate).compile base source =
      lower base (first.compile base source) :=
  rfl

@[simp] theorem identity_compile {Base : Type uBase}
    {Source : Base → Type uSource}
    {Observation : Base → Type uObservation}
    (observe : ∀ base, Source base → Observation base)
    (base : Base) (source : Source base) :
    (identity observe).compile base source = source :=
  rfl

@[simp] theorem trans_compile {Base : Type uBase}
    {Source : Base → Type uSource}
    {Intermediate : Base → Type uArtifact}
    {Artifact : Base → Type uLowered}
    {Observation : Base → Type uObservation}
    (first : Realization Source Intermediate Observation)
    (second : Realization Intermediate Artifact Observation)
    (middleAgreement : ∀ base intermediate,
      second.observeSource base intermediate =
        first.observeArtifact base intermediate)
    (base : Base) (source : Source base) :
    (first.trans second middleAgreement).compile base source =
      second.compile base (first.compile base source) :=
  rfl

/-- Identity is a left unit for the generated artifact. -/
@[simp] theorem identity_trans_compile {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    (realization : Realization Source Artifact Observation)
    (base : Base) (source : Source base) :
    ((identity realization.observeSource).trans realization
        (by intros; rfl)).compile base source =
      realization.compile base source :=
  rfl

/-- Identity is a right unit for the generated artifact. -/
@[simp] theorem trans_identity_compile {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    (realization : Realization Source Artifact Observation)
    (base : Base) (source : Source base) :
    (realization.trans (identity realization.observeArtifact)
        (by intros; rfl)).compile base source =
      realization.compile base source :=
  rfl

/-- Rebracketing certified stages does not change the generated artifact. -/
theorem trans_assoc_compile {Base : Type uBase}
    {Source : Base → Type uSource}
    {FirstArtifact : Base → Type uArtifact}
    {SecondArtifact : Base → Type uLowered}
    {ThirdArtifact : Base → Type uFinal}
    {Observation : Base → Type uObservation}
    (first : Realization Source FirstArtifact Observation)
    (second : Realization FirstArtifact SecondArtifact Observation)
    (third : Realization SecondArtifact ThirdArtifact Observation)
    (firstSecond : ∀ base artifact,
      second.observeSource base artifact = first.observeArtifact base artifact)
    (secondThird : ∀ base artifact,
      third.observeSource base artifact = second.observeArtifact base artifact)
    (base : Base) (source : Source base) :
    ((first.trans second firstSecond).trans third secondThird).compile
        base source =
      (first.trans (second.trans third secondThird) firstSecond).compile
        base source :=
  rfl

theorem select_compile_left {Base : Type uBase}
    {Source : Base → Type uSource}
    {Left : Base → Type uArtifact}
    {Right : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (left : Realization Source Left Observation)
    (right : Realization Source Right Observation)
    (agree : ∀ base source,
      right.observeSource base source = left.observeSource base source)
    (selectBackend : ∀ base, Source base → Bool)
    (base : Base) (source : Source base)
    (selected : selectBackend base source = true) :
    (left.select right agree selectBackend).compile base source =
      .inl (left.compile base source) := by
  simp [Realization.select, selected]

theorem select_compile_right {Base : Type uBase}
    {Source : Base → Type uSource}
    {Left : Base → Type uArtifact}
    {Right : Base → Type uArtifactRight}
    {Observation : Base → Type uObservation}
    (left : Realization Source Left Observation)
    (right : Realization Source Right Observation)
    (agree : ∀ base source,
      right.observeSource base source = left.observeSource base source)
    (selectBackend : ∀ base, Source base → Bool)
    (base : Base) (source : Source base)
    (selected : selectBackend base source = false) :
    (left.select right agree selectBackend).compile base source =
      .inr (right.compile base source) := by
  simp [Realization.select, selected]

@[simp] theorem product_compile {Base : Type uBase}
    {LeftSource : Base → Type uSource}
    {RightSource : Base → Type uSourceRight}
    {LeftArtifact : Base → Type uArtifact}
    {RightArtifact : Base → Type uArtifactRight}
    {LeftObservation : Base → Type uObservation}
    {RightObservation : Base → Type uObservationRight}
    (left : Realization LeftSource LeftArtifact LeftObservation)
    (right : Realization RightSource RightArtifact RightObservation)
    (base : Base) (source : LeftSource base × RightSource base) :
    (left.product right).compile base source =
      (left.compile base source.1, right.compile base source.2) :=
  rfl

@[simp] theorem mapObservation_compile {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    {MappedObservation : Base → Type uObservationRight}
    (realization : Realization Source Artifact Observation)
    (map : ∀ base, Observation base → MappedObservation base)
    (base : Base) (source : Source base) :
    (realization.mapObservation map).compile base source =
      realization.compile base source :=
  rfl

@[simp] theorem mapObservation_observeSource {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    {MappedObservation : Base → Type uObservationRight}
    (realization : Realization Source Artifact Observation)
    (map : ∀ base, Observation base → MappedObservation base)
    (base : Base) (source : Source base) :
    (realization.mapObservation map).observeSource base source =
      map base (realization.observeSource base source) :=
  rfl

@[simp] theorem mapObservation_observeArtifact {Base : Type uBase}
    {Source : Base → Type uSource}
    {Artifact : Base → Type uArtifact}
    {Observation : Base → Type uObservation}
    {MappedObservation : Base → Type uObservationRight}
    (realization : Realization Source Artifact Observation)
    (map : ∀ base, Observation base → MappedObservation base)
    (base : Base) (artifact : Artifact base) :
    (realization.mapObservation map).observeArtifact base artifact =
      map base (realization.observeArtifact base artifact) :=
  rfl

end Realization

namespace GSLT

/-! ## Discrete theories -/

/-- Any term grammar has a discrete GSLT: equality is syntactic and there are
no primitive rewrites.  This is the neutral atom theory for declaration kinds
that have no authored equations or syntax sugar. -/
def discrete (Term : Type*) : GSLT where
  Term := Term
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ impossible
    exact impossible.elim
  rewrites_resp_right := by
    intro _ _ _ impossible _
    exact impossible.elim

/-! ## Structural embeddings -/

/-- A faithful embedding of one GSLT into another.  Unlike the behavioral
`GSLT.Morphism`, this structure records the presentation-level facts needed by
language assembly: injectivity on terms and preservation/reflection of both
equations and one-step rewrites. -/
structure Embedding (source target : GSLT) where
  toFun : source.Term → target.Term
  injective : Function.Injective toFun
  equiv_iff : ∀ sourceTerm targetTerm,
    target.Equiv (toFun sourceTerm) (toFun targetTerm) ↔
      source.Equiv sourceTerm targetTerm
  step_iff : ∀ sourceTerm targetTerm,
    target.Step (toFun sourceTerm) (toFun targetTerm) ↔
      source.Step sourceTerm targetTerm

namespace Embedding

/-- An observation explicitly preserved by a structural embedding.  Structural
faithfulness alone speaks only about terms, equations, and one-step rewrites;
additional answer, trace, cost, or reflection observations must be named. -/
def Preserves {source target : GSLT} (embedding : Embedding source target)
    {Observation : Type*} (observeSource : source.Term → Observation)
    (observeTarget : target.Term → Observation) : Prop :=
  ∀ term, observeTarget (embedding.toFun term) = observeSource term

/-- A structural embedding together with one stated observation invariant. -/
structure Observed (source target : GSLT) (Observation : Type*) extends
    Embedding source target where
  observeSource : source.Term → Observation
  observeTarget : target.Term → Observation
  preserves : toEmbedding.Preserves observeSource observeTarget

/-- The identity structural embedding. -/
def id (system : GSLT) : Embedding system system where
  toFun := _root_.id
  injective := Function.injective_id
  equiv_iff := fun _ _ => Iff.rfl
  step_iff := fun _ _ => Iff.rfl

/-- Structural embeddings compose. -/
def comp {first second third : GSLT}
    (later : Embedding second third) (earlier : Embedding first second) :
    Embedding first third where
  toFun := later.toFun ∘ earlier.toFun
  injective := later.injective.comp earlier.injective
  equiv_iff := by
    intro source target
    exact (later.equiv_iff _ _).trans (earlier.equiv_iff _ _)
  step_iff := by
    intro source target
    exact (later.step_iff _ _).trans (earlier.step_iff _ _)

/-- Observation-carrying embeddings compose when their middle observation is
literally shared. -/
def Observed.comp {first second third : GSLT} {Observation : Type*}
    (later : Observed second third Observation)
    (earlier : Observed first second Observation)
    (middle : later.observeSource = earlier.observeTarget) :
    Observed first third Observation where
  toEmbedding := later.toEmbedding.comp earlier.toEmbedding
  observeSource := earlier.observeSource
  observeTarget := later.observeTarget
  preserves := by
    intro term
    change later.observeTarget (later.toFun (earlier.toFun term)) =
      earlier.observeSource term
    rw [later.preserves (earlier.toFun term), middle, earlier.preserves term]

/-- Every observation-carrying structural embedding is also a certified
realization of source terms as target terms.  The embedding still carries the
stronger equation-and-step reflection laws; the realization exposes its
staging contract. -/
def Observed.toRealization {source target : GSLT} {Observation : Type*}
    (embedding : Observed source target Observation) :
    Mettapedia.GSLT.SimpleRealization source.Term target.Term Observation where
  compile := fun _ term => embedding.toFun term
  observeSource := fun _ => embedding.observeSource
  observeArtifact := fun _ => embedding.observeTarget
  adequate := fun _ => embedding.preserves

end Embedding

/-! ## Disjoint sums -/

/-- Equations in a disjoint sum never identify terms from different summands. -/
inductive SumEquiv (left right : GSLT) :
    (left.Term ⊕ right.Term) → (left.Term ⊕ right.Term) → Prop where
  | left {source target : left.Term} :
      left.Equiv source target → SumEquiv left right (.inl source) (.inl target)
  | right {source target : right.Term} :
      right.Equiv source target → SumEquiv left right (.inr source) (.inr target)

namespace SumEquiv

theorem refl (left right : GSLT) :
    ∀ term, SumEquiv left right term term
  | .inl term => .left (left.equations.refl term)
  | .inr term => .right (right.equations.refl term)

theorem symm {left right : GSLT} {source target}
    (equivalent : SumEquiv left right source target) :
    SumEquiv left right target source := by
  cases equivalent with
  | left equivalent => exact .left (left.equations.symm equivalent)
  | right equivalent => exact .right (right.equations.symm equivalent)

theorem trans {left right : GSLT} {first second third}
    (firstSecond : SumEquiv left right first second)
    (secondThird : SumEquiv left right second third) :
    SumEquiv left right first third := by
  cases firstSecond <;> cases secondThird
  · exact .left (left.equations.trans ‹_› ‹_›)
  · exact .right (right.equations.trans ‹_› ‹_›)

end SumEquiv

/-- Rewrites in a disjoint sum are precisely rewrites of one summand. -/
inductive SumStep (left right : GSLT) :
    (left.Term ⊕ right.Term) → (left.Term ⊕ right.Term) → Prop where
  | left {source target : left.Term} :
      left.Step source target → SumStep left right (.inl source) (.inl target)
  | right {source target : right.Term} :
      right.Step source target → SumStep left right (.inr source) (.inr target)

/-- The coproduct presentation of two non-interacting GSLTs. -/
def disjointSum (left right : GSLT) : GSLT where
  Term := left.Term ⊕ right.Term
  equations :=
    { r := SumEquiv left right
      iseqv :=
        ⟨SumEquiv.refl left right,
          fun equivalent => equivalent.symm,
          fun firstSecond secondThird => firstSecond.trans secondThird⟩ }
  rewrites := SumStep left right
  rewrites_resp_left := by
    intro source source' target equivalent step
    cases equivalent <;> cases step
    · obtain ⟨next, rewrites, nextEquivalent⟩ :=
        left.rewrites_resp_left ‹left.Equiv _ _› ‹left.Step _ _›
      exact ⟨.inl next, .left rewrites, .left nextEquivalent⟩
    · obtain ⟨next, rewrites, nextEquivalent⟩ :=
        right.rewrites_resp_left ‹right.Equiv _ _› ‹right.Step _ _›
      exact ⟨.inr next, .right rewrites, .right nextEquivalent⟩
  rewrites_resp_right := by
    intro source target target' step equivalent
    cases step <;> cases equivalent
    · exact .left (left.rewrites_resp_right ‹left.Step _ _› ‹left.Equiv _ _›)
    · exact .right (right.rewrites_resp_right ‹right.Step _ _› ‹right.Equiv _ _›)

/-- The left theory embeds faithfully into the disjoint sum. -/
def disjointSumLeft (left right : GSLT) : Embedding left (disjointSum left right) where
  toFun := Sum.inl
  injective := by
    intro source target equal
    cases equal
    rfl
  equiv_iff := by
    intro source target
    constructor
    · intro equivalent
      cases equivalent
      assumption
    · exact SumEquiv.left
  step_iff := by
    intro source target
    constructor
    · intro step
      cases step
      assumption
    · exact SumStep.left

/-- The right theory embeds faithfully into the disjoint sum. -/
def disjointSumRight (left right : GSLT) : Embedding right (disjointSum left right) where
  toFun := Sum.inr
  injective := by
    intro source target equal
    cases equal
    rfl
  equiv_iff := by
    intro source target
    constructor
    · intro equivalent
      cases equivalent
      assumption
    · exact SumEquiv.right
  step_iff := by
    intro source target
    constructor
    · intro step
      cases step
      assumption
    · exact SumStep.right

/-! ## Interacting sums

`disjointSum` is the coproduct of theories that do not communicate.  Hosted
languages also need the next conservative construction: keep both component
theories unchanged, while admitting explicitly authored rewrites whose source
and target lie in different components.  The four compatibility laws below
are exactly what is required for those cross-rewrites to descend through the
two component equation relations.
-/

/-- Cross-rewrite data between two GSLTs.  Component-internal equations and
rewrites remain authoritative; this structure supplies only the two possible
directions of interaction and their equation-respect laws. -/
structure Interaction (left right : GSLT) where
  leftToRight : left.Term → right.Term → Prop
  rightToLeft : right.Term → left.Term → Prop
  leftToRight_resp_left : ∀ {source source' target},
    left.Equiv source source' → leftToRight source target →
      ∃ target', leftToRight source' target' ∧ right.Equiv target target'
  leftToRight_resp_right : ∀ {source target target'},
    leftToRight source target → right.Equiv target target' →
      leftToRight source target'
  rightToLeft_resp_left : ∀ {source source' target},
    right.Equiv source source' → rightToLeft source target →
      ∃ target', rightToLeft source' target' ∧ left.Equiv target target'
  rightToLeft_resp_right : ∀ {source target target'},
    rightToLeft source target → left.Equiv target target' →
      rightToLeft source target'

/-- Rewrites of an interacting sum are either internal to one component or an
explicitly authored crossing.  There is no constructor for an unrequested
interaction. -/
inductive InteractingStep (left right : GSLT)
    (interaction : Interaction left right) :
    (left.Term ⊕ right.Term) → (left.Term ⊕ right.Term) → Prop where
  | left {source target} : left.Step source target →
      InteractingStep left right interaction (.inl source) (.inl target)
  | right {source target} : right.Step source target →
      InteractingStep left right interaction (.inr source) (.inr target)
  | leftToRight {source target} : interaction.leftToRight source target →
      InteractingStep left right interaction (.inl source) (.inr target)
  | rightToLeft {source target} : interaction.rightToLeft source target →
      InteractingStep left right interaction (.inr source) (.inl target)

/-- Two component theories with authored cross-rewrites.  Both components
embed faithfully: interactions may leave or enter a component, but can never
manufacture a new rewrite whose two endpoints are both inside that component. -/
def interactingSum (left right : GSLT) (interaction : Interaction left right) :
    GSLT where
  Term := left.Term ⊕ right.Term
  equations :=
    { r := SumEquiv left right
      iseqv :=
        ⟨SumEquiv.refl left right,
          fun equivalent => equivalent.symm,
          fun firstSecond secondThird => firstSecond.trans secondThird⟩ }
  rewrites := InteractingStep left right interaction
  rewrites_resp_left := by
    intro source source' target equivalent step
    cases equivalent with
    | left equivalent =>
        cases step with
        | left rewrite =>
            obtain ⟨next, nextRewrite, nextEquivalent⟩ :=
              left.rewrites_resp_left equivalent rewrite
            exact ⟨.inl next, .left nextRewrite, .left nextEquivalent⟩
        | leftToRight crossing =>
            obtain ⟨next, nextCrossing, nextEquivalent⟩ :=
              interaction.leftToRight_resp_left equivalent crossing
            exact ⟨.inr next, .leftToRight nextCrossing, .right nextEquivalent⟩
    | right equivalent =>
        cases step with
        | right rewrite =>
            obtain ⟨next, nextRewrite, nextEquivalent⟩ :=
              right.rewrites_resp_left equivalent rewrite
            exact ⟨.inr next, .right nextRewrite, .right nextEquivalent⟩
        | rightToLeft crossing =>
            obtain ⟨next, nextCrossing, nextEquivalent⟩ :=
              interaction.rightToLeft_resp_left equivalent crossing
            exact ⟨.inl next, .rightToLeft nextCrossing, .left nextEquivalent⟩
  rewrites_resp_right := by
    intro source target target' step equivalent
    cases step with
    | left rewrite =>
        cases equivalent with
        | left equivalent =>
            exact .left (left.rewrites_resp_right rewrite equivalent)
    | right rewrite =>
        cases equivalent with
        | right equivalent =>
            exact .right (right.rewrites_resp_right rewrite equivalent)
    | leftToRight crossing =>
        cases equivalent with
        | right equivalent =>
            exact .leftToRight
              (interaction.leftToRight_resp_right crossing equivalent)
    | rightToLeft crossing =>
        cases equivalent with
        | left equivalent =>
            exact .rightToLeft
              (interaction.rightToLeft_resp_right crossing equivalent)

/-- The left component remains a faithful subtheory of an interacting sum. -/
def interactingSumLeft (left right : GSLT) (interaction : Interaction left right) :
    Embedding left (interactingSum left right interaction) where
  toFun := Sum.inl
  injective := by
    intro source target equal
    cases equal
    rfl
  equiv_iff := by
    intro source target
    constructor
    · intro equivalent
      cases equivalent
      assumption
    · exact SumEquiv.left
  step_iff := by
    intro source target
    constructor
    · intro step
      cases step
      assumption
    · exact InteractingStep.left

/-- The right component remains a faithful subtheory of an interacting sum. -/
def interactingSumRight (left right : GSLT) (interaction : Interaction left right) :
    Embedding right (interactingSum left right interaction) where
  toFun := Sum.inr
  injective := by
    intro source target equal
    cases equal
    rfl
  equiv_iff := by
    intro source target
    constructor
    · intro equivalent
      cases equivalent
      assumption
    · exact SumEquiv.right
  step_iff := by
    intro source target
    constructor
    · intro step
      cases step
      assumption
    · exact InteractingStep.right

/-! ## Interpreting communicating components

An interacting sum is presentation-level composition.  To interpret it into a
common payload, each component needs an elaboration and every authored crossing
must preserve the payload.  This is strictly more information than two
independent elaborations: without the crossing laws, a rewrite could silently
change meaning at the component boundary. -/

/-- Two component elaborations that agree along every authored cross-rewrite. -/
structure InteractionElaboration {left right : GSLT}
    (interaction : Interaction left right) (Payload : Type*) where
  left : Elaboration left Payload
  right : Elaboration right Payload
  leftToRight : ∀ {source target}, interaction.leftToRight source target →
    left.elaborate source = right.elaborate target
  rightToLeft : ∀ {source target}, interaction.rightToLeft source target →
    right.elaborate source = left.elaborate target

namespace InteractionElaboration

/-- The two component interpretations and their crossing laws induce one
elaboration from the complete interacting `(T,E,R)` theory. -/
def toElaboration {left right : GSLT}
    {interaction : Interaction left right} {Payload : Type*}
    (interpretation : InteractionElaboration interaction Payload) :
    Elaboration (interactingSum left right interaction) Payload where
  elaborate := Sum.elim interpretation.left.elaborate
    interpretation.right.elaborate
  equation := by
    intro source target equivalent
    cases equivalent with
    | left component => exact interpretation.left.equation component
    | right component => exact interpretation.right.equation component
  rewrite := by
    intro source target step
    cases step with
    | left component => exact interpretation.left.rewrite component
    | right component => exact interpretation.right.rewrite component
    | leftToRight crossing => exact interpretation.leftToRight crossing
    | rightToLeft crossing => exact interpretation.rightToLeft crossing

@[simp] theorem toElaboration_inl {left right : GSLT}
    {interaction : Interaction left right} {Payload : Type*}
    (interpretation : InteractionElaboration interaction Payload)
    (term : left.Term) :
    interpretation.toElaboration.elaborate (.inl term) =
      interpretation.left.elaborate term :=
  rfl

@[simp] theorem toElaboration_inr {left right : GSLT}
    {interaction : Interaction left right} {Payload : Type*}
    (interpretation : InteractionElaboration interaction Payload)
    (term : right.Term) :
    interpretation.toElaboration.elaborate (.inr term) =
      interpretation.right.elaborate term :=
  rfl

end InteractionElaboration

/-! ### Interaction canaries -/

private def oneWayCanaryInteraction :
    Interaction (discrete Bool) (discrete Unit) where
  leftToRight := fun source _ => source = true
  rightToLeft := fun _ _ => False
  leftToRight_resp_left := by
    intro source source' target equivalent crossing
    subst source'
    exact ⟨target, crossing, rfl⟩
  leftToRight_resp_right := by
    intro source target target' crossing equivalent
    subst target'
    exact crossing
  rightToLeft_resp_left := by
    intro source source' target equivalent crossing
    exact crossing.elim
  rightToLeft_resp_right := by
    intro source target target' crossing equivalent
    exact crossing.elim

/-- A nonconstant interpretation of the one-way canary: the left Boolean is
retained, and the right-hand unit denotes the only Boolean that can cross to
it. -/
private def oneWayCanaryElaboration :
    InteractionElaboration oneWayCanaryInteraction Bool where
  left :=
    { elaborate := some
      equation := by intro _ _ equal; subst equal; rfl
      rewrite := by intro _ _ impossible; exact impossible.elim }
  right :=
    { elaborate := fun _ => some true
      equation := by intro _ _ _; rfl
      rewrite := by intro _ _ impossible; exact impossible.elim }
  leftToRight := by
    intro source target crossing
    subst source
    rfl
  rightToLeft := by
    intro source target impossible
    exact impossible.elim

/-- Positive canary: the explicit left-to-right rewrite preserves the common
interpretation. -/
theorem interactingElaboration_preserves_authored_crossing :
    oneWayCanaryElaboration.toElaboration.elaborate (.inl true) =
      oneWayCanaryElaboration.toElaboration.elaborate (.inr ()) :=
  rfl

/-- Negative canary: no lawful interaction elaboration may assign opposite
observations to the endpoints of an authored crossing. -/
theorem interactingElaboration_rejects_changed_observation :
    ¬ ∃ interpretation : InteractionElaboration oneWayCanaryInteraction Bool,
        interpretation.left.elaborate true = some true ∧
          interpretation.right.elaborate () = some false := by
  rintro ⟨interpretation, leftMeaning, rightMeaning⟩
  have preserved := interpretation.leftToRight (source := true) (target := ()) rfl
  rw [leftMeaning, rightMeaning] at preserved
  exact Bool.noConfusion (Option.some.inj preserved)

/-- Positive canary: an authored crossing is a rewrite of the interacting
sum. -/
theorem interactingSum_authored_crossing :
    (interactingSum (discrete Bool) (discrete Unit)
      oneWayCanaryInteraction).Step (.inl true) (.inr ()) :=
  InteractingStep.leftToRight rfl

/-- Negative canary: the construction does not invent the reverse crossing. -/
theorem interactingSum_does_not_invent_reverse :
    ¬ (interactingSum (discrete Bool) (discrete Unit)
      oneWayCanaryInteraction).Step (.inr ()) (.inl true) := by
  intro step
  cases step with
  | rightToLeft impossible => exact impossible

/-! ## Free declaration documents -/

/-- Pointwise equations on finite documents. -/
inductive DocumentEquiv (system : GSLT) :
    List system.Term → List system.Term → Prop where
  | nil : DocumentEquiv system [] []
  | cons {source target : system.Term} {sources targets : List system.Term} :
      system.Equiv source target →
      DocumentEquiv system sources targets →
      DocumentEquiv system (source :: sources) (target :: targets)

namespace DocumentEquiv

theorem refl (system : GSLT) : ∀ document, DocumentEquiv system document document
  | [] => .nil
  | term :: terms => .cons (system.equations.refl term) (refl system terms)

theorem symm {system : GSLT} {source target}
    (equivalent : DocumentEquiv system source target) :
    DocumentEquiv system target source := by
  induction equivalent with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons (system.equations.symm head) inductionHypothesis

theorem trans {system : GSLT} {first second third}
    (firstSecond : DocumentEquiv system first second)
    (secondThird : DocumentEquiv system second third) :
    DocumentEquiv system first third := by
  induction firstSecond generalizing third with
  | nil =>
      cases secondThird
      exact .nil
  | cons head tail inductionHypothesis =>
      cases secondThird with
      | cons nextHead nextTail =>
          exact .cons (system.equations.trans head nextHead)
            (inductionHypothesis nextTail)

/-- Pointwise equivalence is preserved by concatenation. -/
theorem append {system : GSLT} {first first' second second'}
    (firstEquivalent : DocumentEquiv system first first')
    (secondEquivalent : DocumentEquiv system second second') :
    DocumentEquiv system (first ++ second) (first' ++ second') := by
  induction firstEquivalent with
  | nil => exact secondEquivalent
  | cons head _ inductionHypothesis =>
      exact .cons head inductionHypothesis

/-- Pointwise document equivalence is literal equality whenever the component
equations are literal equality. -/
theorem eq_of {system : GSLT} {source target : List system.Term}
    (componentEq : ∀ {left right}, system.Equiv left right → left = right)
    (equivalent : DocumentEquiv system source target) : source = target := by
  induction equivalent with
  | nil => rfl
  | cons head _ inductionHypothesis =>
      rw [componentEq head, inductionHypothesis]

/-- Interpreting a declaration document by concatenating per-declaration
results respects pointwise equations whenever the component interpreter does.
This is the eliminator used by mixed authored extension languages: component
equations need not be literal equality. -/
theorem flatMap_eq {system : GSLT} {Result : Type*}
    (interpret : system.Term → List Result)
    (componentEq : ∀ {left right}, system.Equiv left right →
      interpret left = interpret right)
    {source target : List system.Term}
    (equivalent : DocumentEquiv system source target) :
    source.flatMap interpret = target.flatMap interpret := by
  induction equivalent with
  | nil => rfl
  | cons head _ inductionHypothesis =>
      simp only [List.flatMap_cons]
      rw [componentEq head, inductionHypothesis]

end DocumentEquiv

/-- A primitive rewrite at one occurrence of a document. -/
inductive RawDocumentStep (system : GSLT) :
    List system.Term → List system.Term → Prop where
  | head {source target : system.Term} {rest : List system.Term} :
      system.Step source target →
      RawDocumentStep system (source :: rest) (target :: rest)
  | tail {head : system.Term} {source target : List system.Term} :
      RawDocumentStep system source target →
      RawDocumentStep system (head :: source) (head :: target)

namespace RawDocumentStep

/-- A primitive document step is stable under an untouched suffix. -/
theorem append_right {system : GSLT} {source target : List system.Term}
    (step : RawDocumentStep system source target) (suffix : List system.Term) :
    RawDocumentStep system (source ++ suffix) (target ++ suffix) := by
  induction step with
  | head rewrite => exact .head rewrite
  | tail _ inductionHypothesis => exact .tail inductionHypothesis

/-- A primitive document step is stable under an untouched prefix. -/
theorem append_left {system : GSLT} (context : List system.Term)
    {source target : List system.Term}
    (step : RawDocumentStep system source target) :
    RawDocumentStep system (context ++ source) (context ++ target) := by
  induction context with
  | nil => exact step
  | cons head rest inductionHypothesis =>
      simpa only [List.cons_append] using
        (RawDocumentStep.tail (head := head) inductionHypothesis)

/-- A document has no primitive rewrite when its component theory has none. -/
theorem false_of_no_step {system : GSLT} {source target : List system.Term}
    (componentNoStep : ∀ {left right}, system.Step left right → False)
    (step : RawDocumentStep system source target) : False := by
  induction step with
  | head rewrite => exact componentNoStep rewrite
  | tail _ inductionHypothesis => exact inductionHypothesis

end RawDocumentStep

/-- Document rewriting closed under the component equations on both ends. -/
def DocumentStep (system : GSLT)
    (source target : List system.Term) : Prop :=
  ∃ source' target',
    DocumentEquiv system source source' ∧
      RawDocumentStep system source' target' ∧
      DocumentEquiv system target' target

/-- The free finite-document GSLT on a component GSLT. -/
def freeDocument (system : GSLT) : GSLT where
  Term := List system.Term
  equations :=
    { r := DocumentEquiv system
      iseqv :=
        ⟨DocumentEquiv.refl system,
          fun equivalent => equivalent.symm,
          fun firstSecond secondThird => firstSecond.trans secondThird⟩ }
  rewrites := DocumentStep system
  rewrites_resp_left := by
    rintro source source' target sourceEquivalent
      ⟨middleSource, middleTarget, sourceMiddle, rewrite, middleTargetEquivalent⟩
    exact ⟨target,
      ⟨middleSource, middleTarget,
        sourceEquivalent.symm.trans sourceMiddle,
        rewrite, middleTargetEquivalent⟩,
      DocumentEquiv.refl system target⟩
  rewrites_resp_right := by
    rintro source target target'
      ⟨middleSource, middleTarget, sourceMiddle, rewrite, middleTargetEquivalent⟩
      targetEquivalent
    exact ⟨middleSource, middleTarget, sourceMiddle, rewrite,
      middleTargetEquivalent.trans targetEquivalent⟩

namespace DocumentStep

/-- Document rewriting is stable under an untouched suffix. -/
theorem append_right {system : GSLT} {source target : List system.Term}
    (step : DocumentStep system source target) (suffix : List system.Term) :
    DocumentStep system (source ++ suffix) (target ++ suffix) := by
  rcases step with
    ⟨middleSource, middleTarget, sourceMiddle, rewrite, middleTargetTarget⟩
  exact ⟨middleSource ++ suffix, middleTarget ++ suffix,
    sourceMiddle.append (DocumentEquiv.refl system suffix),
    rewrite.append_right suffix,
    middleTargetTarget.append (DocumentEquiv.refl system suffix)⟩

/-- Document rewriting is stable under an untouched prefix. -/
theorem append_left {system : GSLT} (context : List system.Term)
    {source target : List system.Term}
    (step : DocumentStep system source target) :
    DocumentStep system (context ++ source) (context ++ target) := by
  rcases step with
    ⟨middleSource, middleTarget, sourceMiddle, rewrite, middleTargetTarget⟩
  exact ⟨context ++ middleSource, context ++ middleTarget,
    (DocumentEquiv.refl system context).append sourceMiddle,
    rewrite.append_left context,
    (DocumentEquiv.refl system context).append middleTargetTarget⟩

end DocumentStep

/-- A component term embeds as a singleton document. -/
def singletonEmbedding (system : GSLT) : Embedding system (freeDocument system) where
  toFun := fun term => [term]
  injective := by
    intro source target equal
    exact List.cons.inj equal |>.1
  equiv_iff := by
    intro source target
    constructor
    · intro equivalent
      cases equivalent with
      | cons head tail => exact head
    · intro equivalent
      exact .cons equivalent .nil
  step_iff := by
    intro source target
    constructor
    · rintro ⟨middleSource, middleTarget, sourceMiddle, rewrite, middleTargetTarget⟩
      cases sourceMiddle with
      | cons sourceEquivalent sourceTail =>
          cases sourceTail
          cases rewrite with
          | head middleRewrite =>
              cases middleTargetTarget with
              | cons targetEquivalent targetTail =>
                  cases targetTail
                  obtain ⟨next, sourceRewrite, nextEquivalent⟩ :=
                    system.rewrites_resp_left
                      (system.equations.symm sourceEquivalent) middleRewrite
                  exact system.rewrites_resp_right sourceRewrite
                    (system.equations.trans
                      (system.equations.symm nextEquivalent) targetEquivalent)
          | tail impossible => cases impossible
    · intro rewrite
      exact ⟨[source], [target],
        .cons (system.equations.refl source) .nil,
        .head rewrite,
        .cons (system.equations.refl target) .nil⟩

/-! ## Concatenative GSLTs -/

/-- A GSLT whose term language includes an empty document and composition.
The algebraic laws live in `E`; contextual closure of composition lives in
`R`. -/
structure Compositional where
  theory : GSLT
  empty : theory.Term
  append : theory.Term → theory.Term → theory.Term
  empty_append : ∀ term, theory.Equiv (append empty term) term
  append_empty : ∀ term, theory.Equiv (append term empty) term
  append_assoc : ∀ first second third,
    theory.Equiv (append (append first second) third)
      (append first (append second third))
  append_equiv : ∀ {first first' second second'},
    theory.Equiv first first' → theory.Equiv second second' →
      theory.Equiv (append first second) (append first' second')
  append_step_left : ∀ {source target}, theory.Step source target →
    ∀ suffix, theory.Step (append source suffix) (append target suffix)
  append_step_right : ∀ context, ∀ {source target}, theory.Step source target →
    theory.Step (append context source) (append context target)

universe uPayload

/-- An exact elaboration that preserves authored composition.

The payload merge is named because it occurs in the preservation law.  Its
unit and associativity are not additional assumptions: they are forced by the
meaning of the authored empty term, the source monoid equations, exact
quotation, and `elaborate_append`. -/
structure CompositionalElaboration (Payload : Type uPayload) where
  /-- The authored `(T,E,R)` language, including empty and concatenation. -/
  authoring : Compositional
  /-- Exact interpretation of authored terms as payloads. -/
  elaboration : ExactElaboration authoring.theory Payload
  /-- The payload denoted by the authored empty term. -/
  emptyPayload : Payload
  /-- Partial combination of two elaborated payloads. -/
  merge : Payload → Payload → Option Payload
  /-- The authored empty term denotes `emptyPayload`. -/
  elaborate_empty :
    elaboration.elaborate authoring.empty = some emptyPayload
  /-- Elaboration is a homomorphism from authored concatenation to merge. -/
  elaborate_append : ∀ first second,
    elaboration.elaborate (authoring.append first second) =
      (elaboration.elaborate first).bind fun left =>
        (elaboration.elaborate second).bind fun right => merge left right

namespace CompositionalElaboration

/-- The payload partial monoid is derived from compositional elaboration.
There is no independently chosen algebra: the unit is the meaning of the
authored empty term and the laws follow from the source equations and the
append-homomorphism law. -/
def toPartialMonoid {Payload : Type u}
    (system : CompositionalElaboration Payload) : PartialMonoid Payload where
  unit := system.emptyPayload
  op := system.merge
  unit_op := by
    intro value
    calc
      system.merge system.emptyPayload value =
          system.elaboration.elaborate
            (system.authoring.append system.authoring.empty
              (system.elaboration.quote value)) := by
            symm
            simpa [system.elaborate_empty,
              system.elaboration.elaborate_quote] using
              system.elaborate_append system.authoring.empty
                (system.elaboration.quote value)
      _ = system.elaboration.elaborate (system.elaboration.quote value) :=
        system.elaboration.equation
          (system.authoring.empty_append (system.elaboration.quote value))
      _ = some value := system.elaboration.elaborate_quote value
  op_unit := by
    intro value
    calc
      system.merge value system.emptyPayload =
          system.elaboration.elaborate
            (system.authoring.append (system.elaboration.quote value)
              system.authoring.empty) := by
            symm
            simpa [system.elaborate_empty,
              system.elaboration.elaborate_quote] using
              system.elaborate_append (system.elaboration.quote value)
                system.authoring.empty
      _ = system.elaboration.elaborate (system.elaboration.quote value) :=
        system.elaboration.equation
          (system.authoring.append_empty (system.elaboration.quote value))
      _ = some value := system.elaboration.elaborate_quote value
  op_assoc := by
    intro first second third
    calc
      (system.merge first second).bind
          (fun merged => system.merge merged third) =
          system.elaboration.elaborate
            (system.authoring.append
              (system.authoring.append
                (system.elaboration.quote first)
                (system.elaboration.quote second))
              (system.elaboration.quote third)) := by
            symm
            rw [system.elaborate_append, system.elaborate_append,
              system.elaboration.elaborate_quote,
              system.elaboration.elaborate_quote,
              system.elaboration.elaborate_quote]
            rfl
      _ = system.elaboration.elaborate
            (system.authoring.append
              (system.elaboration.quote first)
              (system.authoring.append
                (system.elaboration.quote second)
                (system.elaboration.quote third))) :=
        system.elaboration.equation
          (system.authoring.append_assoc
            (system.elaboration.quote first)
            (system.elaboration.quote second)
            (system.elaboration.quote third))
      _ = (system.merge second third).bind
            (fun merged => system.merge first merged) := by
            rw [system.elaborate_append, system.elaborate_append,
              system.elaboration.elaborate_quote,
              system.elaboration.elaborate_quote,
              system.elaboration.elaborate_quote]
            rfl

@[simp] theorem toPartialMonoid_unit {Payload : Type u}
    (system : CompositionalElaboration Payload) :
    system.toPartialMonoid.unit = system.emptyPayload :=
  rfl

@[simp] theorem toPartialMonoid_op {Payload : Type u}
    (system : CompositionalElaboration Payload) :
    system.toPartialMonoid.op = system.merge :=
  rfl

end CompositionalElaboration

/-- Finite documents form the free compositional GSLT. -/
def freeDocumentCompositional (system : GSLT) : Compositional where
  theory := freeDocument system
  empty := []
  append := List.append
  empty_append := by
    intro document
    change List system.Term at document
    change DocumentEquiv system ([] ++ document) document
    simpa using DocumentEquiv.refl system document
  append_empty := by
    intro document
    change List system.Term at document
    change DocumentEquiv system (document ++ []) document
    simpa using DocumentEquiv.refl system document
  append_assoc := by
    intro first second third
    change List system.Term at first second third
    change DocumentEquiv system ((first ++ second) ++ third)
      (first ++ (second ++ third))
    rw [List.append_assoc]
    exact DocumentEquiv.refl system _
  append_equiv := fun firstEquivalent secondEquivalent =>
    firstEquivalent.append secondEquivalent
  append_step_left := fun step suffix => step.append_right suffix
  append_step_right := fun context _ _ step => step.append_left context

/-- Documents freely mixing declarations from two component GSLTs. -/
def compositeDocuments (left right : GSLT) : Compositional :=
  freeDocumentCompositional (disjointSum left right)

/-- The left component embeds into the mixed document theory. -/
def compositeDocumentsLeft (left right : GSLT) :
    Embedding left (compositeDocuments left right).theory :=
  Embedding.comp (singletonEmbedding (disjointSum left right))
    (disjointSumLeft left right)

/-- The right component embeds into the mixed document theory. -/
def compositeDocumentsRight (left right : GSLT) :
    Embedding right (compositeDocuments left right).theory :=
  Embedding.comp (singletonEmbedding (disjointSum left right))
    (disjointSumRight left right)

/-! ## Products of compositional elaborations -/

namespace CompositionalElaboration

private def productInterpret {Left : Type u} {Right : Type v}
    (left : CompositionalElaboration Left)
    (right : CompositionalElaboration Right) :
    left.authoring.theory.Term ⊕ right.authoring.theory.Term →
      Option (Left × Right) :=
  Sum.elim
    (fun source => (left.elaboration.elaborate source).map
      fun value => (value, right.emptyPayload))
    (fun source => (right.elaboration.elaborate source).map
      fun value => (left.emptyPayload, value))

private def productElaborate {Left : Type u} {Right : Type v}
    (left : CompositionalElaboration Left)
    (right : CompositionalElaboration Right) :
    List (left.authoring.theory.Term ⊕ right.authoring.theory.Term) →
      Option (Left × Right) :=
  (left.toPartialMonoid.prod right.toPartialMonoid).foldOption
    (productInterpret left right)

private theorem foldOption_equation {Carrier : Type u} {system : GSLT}
    (monoid : PartialMonoid Carrier)
    (interpret : system.Term → Option Carrier)
    (interpretEquation : ∀ {source target},
      system.Equiv source target → interpret source = interpret target) :
    ∀ {source target}, DocumentEquiv system source target →
      monoid.foldOption interpret source = monoid.foldOption interpret target
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [PartialMonoid.foldOption]
      rw [interpretEquation head,
        foldOption_equation monoid interpret interpretEquation tail]

private theorem foldOption_rawStep {Carrier : Type u} {system : GSLT}
    (monoid : PartialMonoid Carrier)
    (interpret : system.Term → Option Carrier)
    (interpretStep : ∀ {source target},
      system.Step source target → interpret source = interpret target) :
    ∀ {source target}, RawDocumentStep system source target →
      monoid.foldOption interpret source = monoid.foldOption interpret target
  | _, _, .head step => by
      simp only [PartialMonoid.foldOption]
      rw [interpretStep step]
  | _, _, .tail step => by
      simp only [PartialMonoid.foldOption]
      rw [foldOption_rawStep monoid interpret interpretStep step]

private theorem foldOption_step {Carrier : Type u} {system : GSLT}
    (monoid : PartialMonoid Carrier)
    (interpret : system.Term → Option Carrier)
    (interpretEquation : ∀ {source target},
      system.Equiv source target → interpret source = interpret target)
    (interpretStep : ∀ {source target},
      system.Step source target → interpret source = interpret target)
    {source target} (step : DocumentStep system source target) :
    monoid.foldOption interpret source = monoid.foldOption interpret target := by
  rcases step with
    ⟨middleSource, middleTarget, sourceMiddle, rewrite, middleTargetTarget⟩
  calc
    monoid.foldOption interpret source =
        monoid.foldOption interpret middleSource :=
      foldOption_equation monoid interpret interpretEquation sourceMiddle
    _ = monoid.foldOption interpret middleTarget :=
      foldOption_rawStep monoid interpret interpretStep rewrite
    _ = monoid.foldOption interpret target :=
      foldOption_equation monoid interpret interpretEquation middleTargetTarget

private theorem productInterpret_equation {Left : Type u} {Right : Type v}
    (left : CompositionalElaboration Left)
    (right : CompositionalElaboration Right) {source target}
    (equivalent : SumEquiv left.authoring.theory right.authoring.theory
      source target) :
    productInterpret left right source = productInterpret left right target := by
  cases equivalent with
  | left component =>
      simp only [productInterpret, Sum.elim_inl]
      rw [left.elaboration.equation component]
  | right component =>
      simp only [productInterpret, Sum.elim_inr]
      rw [right.elaboration.equation component]

private theorem productInterpret_step {Left : Type u} {Right : Type v}
    (left : CompositionalElaboration Left)
    (right : CompositionalElaboration Right) {source target}
    (step : SumStep left.authoring.theory right.authoring.theory source target) :
    productInterpret left right source = productInterpret left right target := by
  cases step with
  | left component =>
      simp only [productInterpret, Sum.elim_inl]
      rw [left.elaboration.rewrite component]
  | right component =>
      simp only [productInterpret, Sum.elim_inr]
      rw [right.elaboration.rewrite component]

/-- **Compositional elaborations are closed under product.**  Authored terms
are mixed documents over the disjoint sum of the two complete source GSLTs;
payloads and their derived partial monoids compose componentwise. -/
def product {Left : Type u} {Right : Type v}
    (left : CompositionalElaboration Left)
    (right : CompositionalElaboration Right) :
    CompositionalElaboration (Left × Right) where
  authoring := compositeDocuments left.authoring.theory right.authoring.theory
  elaboration :=
    { elaborate := productElaborate left right
      equation := foldOption_equation
        (system := disjointSum left.authoring.theory right.authoring.theory)
        _ _ (productInterpret_equation left right)
      rewrite := foldOption_step
        (system := disjointSum left.authoring.theory right.authoring.theory)
        _ _ (productInterpret_equation left right)
        (productInterpret_step left right)
      quote := fun value =>
        [Sum.inl (left.elaboration.quote value.1),
          Sum.inr (right.elaboration.quote value.2)]
      elaborate_quote := by
        rintro ⟨leftValue, rightValue⟩
        simp only [productElaborate, PartialMonoid.foldOption,
          productInterpret, Sum.elim_inl, Sum.elim_inr,
          PartialMonoid.prod]
        rw [left.elaboration.elaborate_quote,
          right.elaboration.elaborate_quote]
        have leftOpUnit (value : Left) :
            left.merge value left.emptyPayload = some value :=
          left.toPartialMonoid.op_unit value
        have rightUnitOp (value : Right) :
            right.merge right.emptyPayload value = some value :=
          right.toPartialMonoid.unit_op value
        have rightOpUnit (value : Right) :
            right.merge value right.emptyPayload = some value :=
          right.toPartialMonoid.op_unit value
        simp [leftOpUnit, rightUnitOp, rightOpUnit] }
  emptyPayload := (left.emptyPayload, right.emptyPayload)
  merge := (left.toPartialMonoid.prod right.toPartialMonoid).op
  elaborate_empty := rfl
  elaborate_append := by
    intro first second
    exact PartialMonoid.foldOption_append _ _ first second

/-- Restricting the product to a left term runs exactly the left elaborator
and pads only with the right authored empty payload. -/
theorem product_elaborates_left_only {Left : Type u} {Right : Type v}
    (left : CompositionalElaboration Left)
    (right : CompositionalElaboration Right)
    (source : left.authoring.theory.Term) :
    (left.product right).elaboration.elaborate [Sum.inl source] =
      (left.elaboration.elaborate source).map
        fun value => (value, right.emptyPayload) := by
  cases hsource : left.elaboration.elaborate source with
  | none =>
      simp [product, productElaborate, PartialMonoid.foldOption,
        productInterpret, hsource]
  | some value =>
      have leftOpUnit (item : Left) :
          left.merge item left.emptyPayload = some item :=
        left.toPartialMonoid.op_unit item
      have rightOpUnit (item : Right) :
          right.merge item right.emptyPayload = some item :=
        right.toPartialMonoid.op_unit item
      simp [product, productElaborate, PartialMonoid.foldOption,
        productInterpret, hsource, PartialMonoid.prod,
        leftOpUnit, rightOpUnit]

/-- The symmetric right restriction law. -/
theorem product_elaborates_right_only {Left : Type u} {Right : Type v}
    (left : CompositionalElaboration Left)
    (right : CompositionalElaboration Right)
    (source : right.authoring.theory.Term) :
    (left.product right).elaboration.elaborate [Sum.inr source] =
      (right.elaboration.elaborate source).map
        fun value => (left.emptyPayload, value) := by
  cases hsource : right.elaboration.elaborate source with
  | none =>
      simp [product, productElaborate, PartialMonoid.foldOption,
        productInterpret, hsource]
  | some value =>
      have leftOpUnit (item : Left) :
          left.merge item left.emptyPayload = some item :=
        left.toPartialMonoid.op_unit item
      have rightOpUnit (item : Right) :
          right.merge item right.emptyPayload = some item :=
        right.toPartialMonoid.op_unit item
      simp [product, productElaborate, PartialMonoid.foldOption,
        productInterpret, hsource, PartialMonoid.prod,
        leftOpUnit, rightOpUnit]

end CompositionalElaboration

/-! ## Contextual admission

Authored composition and contextual acceptance are different structures.
Concatenation always has a meaning through a `CompositionalElaboration`, while
an application-specific validator may reject the merged payload.  Sibling
gluing therefore requires a named compatibility relation; staged extension is
instead expressed relative to an already accumulated payload. -/

/-- Admission data for one compositional elaboration.

`Compatible` is deliberately supplied by the application.  Duplicate-free
proof calculi, disjoint database schemas, capability sets, and effect rows have
different overlap laws.  The class requires the useful fact common to them:
compatible admitted siblings merge to an admitted payload. -/
structure ContextualAdmission {Payload : Type uPayload}
    (system : CompositionalElaboration Payload) where
  Admitted : Payload → Prop
  Compatible : Payload → Payload → Prop
  glue : ∀ {first second},
    Admitted first → Admitted second → Compatible first second →
      ∃ merged, system.merge first second = some merged ∧ Admitted merged

namespace ContextualAdmission

/-- An increment is admitted over an accumulated payload when their authored
merge succeeds and the resulting whole is admitted. -/
def AdmittedOver {Payload : Type uPayload}
    {system : CompositionalElaboration Payload}
    (admission : ContextualAdmission system) (base increment : Payload) : Prop :=
  ∃ merged, system.merge base increment = some merged ∧
    admission.Admitted merged

/-- Compatible admitted siblings glue through the exact merge named by the
source elaboration. -/
theorem exists_glue {Payload : Type uPayload}
    {system : CompositionalElaboration Payload}
    (admission : ContextualAdmission system) {first second : Payload}
    (firstAdmitted : admission.Admitted first)
    (secondAdmitted : admission.Admitted second)
    (compatible : admission.Compatible first second) :
    ∃ merged, system.merge first second = some merged ∧
      admission.Admitted merged :=
  admission.glue firstAdmitted secondAdmitted compatible

/-- **Staged extensions compose.**  If `first` has already accumulated onto
`base`, and `second` is admitted over that exact accumulated payload, then
`first` and `second` can be combined into one increment admitted over `base`.
The theorem uses only the partial monoid forced by authored concatenation; it
does not assume that admission is closed under arbitrary composition. -/
theorem admittedOver_stack {Payload : Type uPayload}
    {system : CompositionalElaboration Payload}
    (admission : ContextualAdmission system)
    {base first accumulated second : Payload}
    (baseFirst : system.merge base first = some accumulated)
    (secondAdmitted : admission.AdmittedOver accumulated second) :
    ∃ combined, system.merge first second = some combined ∧
      admission.AdmittedOver base combined := by
  rcases secondAdmitted with ⟨total, accumulatedSecond, totalAdmitted⟩
  have associative := system.toPartialMonoid.op_assoc base first second
  change
    (system.merge base first).bind
        (fun merged => system.merge merged second) =
      (system.merge first second).bind
        (fun merged => system.merge base merged) at associative
  rw [baseFirst] at associative
  change system.merge accumulated second =
    (system.merge first second).bind
      (fun merged => system.merge base merged) at associative
  rw [accumulatedSecond] at associative
  cases firstSecond : system.merge first second with
  | none => simp [firstSecond] at associative
  | some combined =>
      refine ⟨combined, rfl, total, ?_, totalAdmitted⟩
      simpa [firstSecond] using associative.symm

end ContextualAdmission

/-! ## Positive and negative canaries -/

private inductive CanaryLeft where
  | before
  | after
deriving DecidableEq

private def canaryLeft : GSLT where
  Term := CanaryLeft
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => source = .before ∧ target = .after
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

private def canaryRight : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by aesop
  rewrites_resp_right := by aesop

/-- A component rewrite remains a rewrite inside a mixed document and under
both document contexts. -/
example :
    (compositeDocuments canaryLeft canaryRight).theory.Step
      [Sum.inr false, Sum.inl .before, Sum.inr true]
      [Sum.inr false, Sum.inl .after, Sum.inr true] := by
  change DocumentStep (disjointSum canaryLeft canaryRight)
    [Sum.inr false, Sum.inl .before, Sum.inr true]
    [Sum.inr false, Sum.inl .after, Sum.inr true]
  have core : DocumentStep (disjointSum canaryLeft canaryRight)
      [Sum.inl .before] [Sum.inl .after] :=
    ⟨[Sum.inl .before], [Sum.inl .after],
    .cons (.left rfl) .nil,
    .head (.left ⟨rfl, rfl⟩),
    .cons (.left rfl) .nil⟩
  have withSuffix := core.append_right
    ([Sum.inr true] : List (canaryLeft.Term ⊕ canaryRight.Term))
  have withContext := withSuffix.append_left
    ([Sum.inr false] : List (canaryLeft.Term ⊕ canaryRight.Term))
  change DocumentStep (disjointSum canaryLeft canaryRight)
    [Sum.inr false, Sum.inl .before, Sum.inr true]
    [Sum.inr false, Sum.inl .after, Sum.inr true] at withContext
  exact withContext

/-- The disjoint sum invents no cross-component rewrite. -/
example :
    ¬ (disjointSum canaryLeft canaryRight).Step (.inl .before) (.inr false) := by
  intro step
  cases step

/-- Reflection prevents an embedding from manufacturing a component step. -/
example (source target : canaryLeft.Term) :
    (compositeDocuments canaryLeft canaryRight).theory.Step
        ((compositeDocumentsLeft canaryLeft canaryRight).toFun source)
        ((compositeDocumentsLeft canaryLeft canaryRight).toFun target) ↔
      canaryLeft.Step source target :=
  (compositeDocumentsLeft canaryLeft canaryRight).step_iff source target

private def canaryLeftObservation : canaryLeft.Term → Bool
  | .before => false
  | .after => true

private def canarySumObservation :
    (canaryLeft.Term ⊕ canaryRight.Term) → Bool
  | .inl term => canaryLeftObservation term
  | .inr _ => false

/-- A disjoint-sum embedding can carry a specifically chosen observation
invariant in addition to its structural laws. -/
private def canaryObservedEmbedding :
    Embedding.Observed canaryLeft (disjointSum canaryLeft canaryRight) Bool where
  toEmbedding := disjointSumLeft canaryLeft canaryRight
  observeSource := canaryLeftObservation
  observeTarget := canarySumObservation
  preserves := fun _ => rfl

example (term : canaryLeft.Term) :
    canarySumObservation (Sum.inl term) = canaryLeftObservation term :=
  canaryObservedEmbedding.preserves term

/-- Structural faithfulness does not imply preservation of an arbitrary
observation.  The observation law is genuine additional content. -/
theorem embedding_does_not_choose_observation :
    ¬ (disjointSumLeft canaryLeft canaryRight).Preserves
      (fun _ => true) (fun _ => false) := by
  intro preserves
  have contradiction := preserves CanaryLeft.before
  simp at contradiction

end GSLT

end Mettapedia.GSLT
