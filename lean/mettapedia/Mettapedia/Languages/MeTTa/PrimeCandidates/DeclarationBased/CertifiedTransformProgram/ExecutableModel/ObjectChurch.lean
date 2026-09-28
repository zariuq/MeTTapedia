import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectCoherence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ComputationSchemas

/-!
# The annotation of the object package

The object package's root computation is presented by rewrite schemas read off
its declarations (`objectRules_presents`): the recursor `num-rec`, addition, the
iterated power set and the iterator by structural recursion, the identity
eliminator's linear rule, the definitions by one equation, and the decoder of
the proposition codes. Their left sides are first-order and left-linear
(`objectSchemas_firstOrder`, by evaluation).

Its annotation `objectChurch` is derived from that presentation
(`ChurchRules.ofSchemas`): declared types elaborated, and as root steps the
instances of the elaborated schemas, each right-hand side elaborated against the
declared type of its left side's head. Nothing is annotated by hand.

* **Erasure**: an annotated root step erases to a root step of the object package
  (`objectChurch.erase_step`), and the annotated declared types erase to the
  declared types.
* **Root lifting** (`objectChurch_lift`): every root step of the erasure of an
  annotated term is the erasure of an annotated root step of that term.
* **Coherence** (`objectChurch_coherence`): given the injectivity and
  no-confusion of its type formers, two annotated terms with one erasure, typed
  at one type, are equal at it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open AlgebraicSchema (SchemaFamily)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName eqAtTelescope transportTelescope composeTelescope)

/-- The declared computations of the executable package, by kind. -/
def computationSpecs : List (DeclName × DeclaredComputation Tower.Head) :=
  [(numRecName, .iota numRecName ctors),
   (addN, .recursion addN ctors addEntries 1 0 addBody),
   (powN, .recursion powN ctors powEntries 0 1 powBody),
   (jName, .eliminator jName),
   (eqAtName, .definition eqAtName eqAtTele eqAtRhs),
   (sucMoveName, .definition sucMoveName eqAtTelescope sucMoveRhs),
   (keepName, .definition keepName keepTele keepRhs),
   (transportName, .definition transportName transportTelescope transportRhs),
   (composeName, .definition composeName composeTelescope composeRhs),
   (iterName, .recursion iterName ctors iterEntries 0 5 iterBody),
   (returnIterName, .definition returnIterName returnIterTele returnIterRhs),
   (sucStepName, .definition sucStepName eqAtTelescope sucStepRhs)]

/-- The executable package's table of computations is the table of its declared
computations. -/
theorem computations_eq_specs :
    computations = computationSpecs.map fun p => (p.1, p.2.computation) :=
  rfl

/-- The left sides of the executable package's schemas are first-order and
left-linear. -/
theorem computationSpecs_check : (computationSpecs.all fun p => p.2.check) = true := by
  decide

namespace CodeModel

/-- The rewrite schemas of the object package. -/
def objectSchemas : SchemaFamily Tower.Head :=
  schemaUnion (schemaUnionAll (computationSpecs.map fun p => (p.1, p.2.schemas)))
    (decoderSchema programCodes.decoders)

/-- **The object package's root steps are exactly the instances of its schemas.** -/
theorem objectRules_presents : Presents objectRules.computation objectSchemas := by
  have base : Presents rules.computation
      (schemaUnionAll (computationSpecs.map fun p => (p.1, p.2.schemas))) := by
    intro n l r
    have filtered : computations.filter (fun entry => (fun _ => true) entry.1) = computations :=
      List.filter_eq_self.mpr fun _ _ => rfl
    change (RootComputation.unionAll
      (computations.filter fun entry => (fun _ => true) entry.1)).step l r ↔ _
    rw [filtered, computations_eq_specs]
    exact DeclaredComputation.presents_unionAll computationSpecs
  intro n l r
  exact Presents.union base (decoder_presents programCodes.decoders)

/-- **The left sides of the object package's schemas are first-order and
left-linear.** -/
theorem objectSchemas_firstOrder : FirstOrderFamily objectSchemas :=
  FirstOrderFamily.union
    (DeclaredComputation.firstOrder_unionAll computationSpecs computationSpecs_check)
    (decoder_firstOrder programCodes.decoders)

/-- **The annotation of the object package**, derived from its declarations. -/
def objectChurch : ChurchRules objectRules :=
  ChurchRules.ofSchemas objectRules objectSchemas objectRules_presents

/-- The annotated declared types are the elaborated declared types. -/
theorem objectChurch_constantType (c : DeclName) :
    objectChurch.constantType c = elabDeclarations objectRules.constantType c :=
  rfl

/-- The declared types the object package's schemas are elaborated with. -/
abbrev objectDecls : DeclName → Option (CTm Tower.Head 0) :=
  elabDeclarations objectRules.constantType

/-- An instance of an elaborated schema of a declared computation is an annotated
root step of the object package. -/
theorem objectChurch_step_of_spec {p : DeclName × DeclaredComputation Tower.Head}
    (mem : p ∈ computationSpecs) {k n : Nat} {L R : Tm Tower.Head k} (rule : p.2.schemas L R)
    (σ : CSub Tower.Head k n) :
    objectChurch.computation.step ((elabLeft objectDecls L).subst σ)
      ((elabRight objectDecls L R).subst σ) :=
  CSchemaStep.instantiate ⟨L, R, Or.inl (DeclaredComputation.schemaUnionAll_of_mem rule mem),
    rfl, rfl⟩ σ

/-- An instance of an elaborated decoding schema is an annotated root step of the
object package. -/
theorem objectChurch_step_of_decoder {k n : Nat} {L R : Tm Tower.Head k}
    (rule : decoderSchema programCodes.decoders L R) (σ : CSub Tower.Head k n) :
    objectChurch.computation.step ((elabLeft objectDecls L).subst σ)
      ((elabRight objectDecls L R).subst σ) :=
  CSchemaStep.instantiate ⟨L, R, Or.inr rule, rfl, rfl⟩ σ

/-- **Root lifting for the object package**: every root step of the erasure of an
annotated term is the erasure of an annotated root step of that term. -/
theorem objectChurch_lift {n : Nat} {l : CTm Tower.Head n} {r₀ : Tm Tower.Head n}
    (step : objectRules.computation.step l.erase r₀) :
    ∃ r, objectChurch.computation.step l r ∧ r.erase = r₀ :=
  ChurchRules.ofSchemas_lift objectSchemas objectRules_presents objectSchemas_firstOrder step

/-- **Coherence of annotations for the object package**, at its derived
annotation: given the injectivity and no-confusion of the annotated type formers,
two annotated terms with one erasure, typed at one type, are equal at it. -/
theorem objectChurch_coherence (formers : CFormerFacts objectChurch) {n : Nat}
    {Γ : CCtx Tower.Head n} (formed : CCtxFormed objectChurch Γ) {t t' A : CTm Tower.Head n}
    (typing : CTyped objectChurch Γ t A) (typing' : CTyped objectChurch Γ t' A)
    (same : t.erase = t'.erase) : CEqual objectChurch Γ t t' A :=
  object_coherence objectChurch formers formed typing typing' same

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
