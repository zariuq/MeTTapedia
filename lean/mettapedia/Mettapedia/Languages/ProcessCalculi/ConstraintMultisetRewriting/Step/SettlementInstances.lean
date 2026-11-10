import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SettlementCoverage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PermissionsInterface
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityFramesStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeInstance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionSplitting

/-!
# Answer coverage of the exhaustive instances of the step

Every instance listed here is exhaustive: it covers its answers (`SettlementCoverage.CoversAnswers`).
Where an instance settles by an identity it covers in the strong same-target form.

## Identity settlements: the strong form

* the first-order step of the run layer (`firstOrder_covers`), and so the step over rational trees
  (`rational_covers`) and the first-order step with located occurrences (`located_covers`);
* the helper step at declaration frames (`helper_covers`);
* the dependent full step (`dependent_covers`);
* the three steps with disequations over those presteps (`firstOrderWith_covers`,
  `dependentWith_covers`, `helperWith_covers`), and the one-frame step with disequations
  (`disequality_covers`);
* every restriction of a covering step, so every permitted step (`permitted_covers`,
  `permitted_coversAnswers`), and the relabelling control of the permissions (`relabel_covers`).

## Disequation frames (`extends_frames`)

A morphism of disequation frames whose target keeps exactly the transported disequations extends
there whenever it extends in the base: the faithful extension separates what the frame separated, so
it is a morphism into the frame its disequations leave. Hence a step with disequations covers its
answers when the underlying prepared settlement extends at every preparation, for every step
(`withDisequations_coversAnswers`).

## The native step: the general form (`native_coversAnswers`)

The native step settles into the solver's active frame, which adds the helpers the solver returned.
Its settlement is the assignment of an injective extension of declarations
(`ContextualConditionalExecution.Firing.resultFrame_assignment`), and every assignment of such an
extension extends (`extension_extends`): a solution into `b` lifts, through the frame `b` with the
complementary declarations as fresh names, by the faithful inclusion of `b`
(`extension_faithful`). So the native step covers its answers after extending their frames, and so
do guarded native firings with disequations (`PreparedStep.nativeGuarded_coversAnswers`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SettlementCoverage

open Interface (Frames)
open EvidenceInterface (RetractsSettlement)

universe uO uT uH uOcc uS uF

/-! ## Identity settlements -/

section FirstOrder

universe uA uB uC uD

variable {T : Type uA} {S : Type uB} {O : Type uC} [DecidableEq O] (A : SubstitutionAction T S)
  (label : O → T)

/-- **The first-order step covers in the strong form.** -/
theorem firstOrder_covers : CoversSettlement (AnnotatedRuns.firstOrder A label).toStep :=
  covers_of_retracts (EvidenceInterface.firstOrder_retracts A label)

theorem firstOrder_coversAnswers : CoversAnswers (AnnotatedRuns.firstOrder A label).toStep :=
  CoversSettlement.coversAnswers (firstOrder_covers A label)

/-- **The first-order step with disequations covers in the strong form.** -/
theorem firstOrderWith_covers : CoversSettlement (DisequalityFrames.firstOrderWith A label) :=
  covers_of_retracts (EvidenceInterface.withDisequations_retracts _
    (EvidenceInterface.firstOrderPrestep_retracts A label))

/-- **The first-order step with located occurrences covers in the strong form.** -/
theorem located_covers {H : Type uD} [DecidableEq H] (space : O → H) (payload : O → T) :
    CoversSettlement (Spaces.located A space payload).toStep :=
  firstOrder_covers _ _

end FirstOrder

/-- **The one-frame step with disequations covers in the strong form.** -/
theorem disequality_covers {T : Type*} {S : Type*} {O : Type*} [DecidableEq O] (A : SubstitutionAction T S)
    (label : O → T) : CoversSettlement (Disequality.step A label).toStep := by
  apply covers_of_retracts
  intro _ f _
  exact ⟨(Disequality.frames A).id f.target, fun t => EvidenceInterface.id_retraction (X := Disequality.frames A) t⟩

/-- **The relabelling control of the permissions covers in the strong form**: its settlement is the
identity of the trivial action. -/
theorem relabel_covers : CoversSettlement PermissionsInterface.Controls.relabel.step.toStep := by
  apply covers_of_retracts
  intro _ _ _
  exact ⟨(), fun _ => rfl⟩

/-- **The step over rational trees covers in the strong form.** -/
theorem rational_covers (σ : Mettapedia.Logic.LP.LPSignature) {O : Type} [DecidableEq O]
    (label : O → Rational.RTree σ) : CoversSettlement (Rational.rationalStep σ label).toStep :=
  firstOrder_covers _ _

section Helper

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {O : Type} [DecidableEq O]

/-- **The helper step covers in the strong form.** -/
theorem helper_covers : CoversSettlement (Interface.Helpers.helperStep (S := S) (O := O)).toStep :=
  covers_of_retracts EvidenceInterface.helper_retracts

variable (S O) in
/-- **The helper step with disequations covers in the strong form.** -/
theorem helperWith_covers : CoversSettlement (DisequalityFrames.Contextual.withDisequations S O) :=
  covers_of_retracts (EvidenceInterface.helperWith_retracts S O)

end Helper

section Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open Interface.DependentFull

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  (levels : LevelModel rules L) (O : Type) [DecidableEq O]

/-- **The dependent full step covers in the strong form.** -/
theorem dependent_covers : CoversSettlement (step levels O).toStep :=
  covers_of_retracts (EvidenceInterface.dependent_retracts levels O)

/-- **The dependent full step with disequations covers in the strong form.** -/
theorem dependentWith_covers : CoversSettlement (DisequalityFrames.Dependent.withDisequations levels O) :=
  covers_of_retracts (EvidenceInterface.dependentWith_retracts levels O)

end Dependent

section Permitted

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  {P : Interface.Step X O State Firing} {N : Type} (space : O → N)
  (Γ : MeTTaCalculus.InteractionTypes.Rights N)

/-- **Permissions keep answer coverage.** -/
theorem permitted_coversAnswers (covers : CoversAnswers P) :
    CoversAnswers (Permissions.permitted P space Γ) :=
  coversAnswers_restrict covers _

/-- **Permissions keep the strong form.** -/
theorem permitted_covers (covers : CoversSettlement P) :
    CoversSettlement (Permissions.permitted P space Γ) :=
  covers_restrict covers _

end Permitted

/-! ## Disequation frames -/

section Disequations

open DisequalityFrames (Frame Morphism frames Separates separates_applyStore separates_of_reflects
  image toImage)

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}

/-- **Extension lifts to disequation frames**: a morphism of disequation frames whose target keeps
exactly the transported disequations extends there when it extends in the base. -/
theorem extends_frames {D R : Frame X} (settle : Morphism X D R)
    (store : R.store = X.applyStore settle.1 D.store) (base : Extends X settle.1) :
    Extends (frames X) settle := by
  intro B σ
  obtain ⟨c, j, τ, faithful, agree⟩ := base σ.1
  have separated : Separates X j B.store := separates_of_reflects (fun same => faithful same) B.separated
  refine ⟨image j B.store separated, toImage B j separated, ⟨τ, fun d ρ later => ?_⟩, faithful, agree⟩
  rw [store]
  refine (separates_applyStore settle.1 (X.comp ρ τ) D.store).mpr ?_
  refine EvidenceInterface.separates_of_equivalent (g := X.comp (X.comp ρ j) σ.1) (fun t => ?_)
    (σ.2 d (X.comp ρ j) ((separates_applyStore j ρ B.store).mp later))
  have left : X.act (X.comp (X.comp ρ τ) settle.1) t = X.act ρ (X.act (X.comp τ settle.1) t) :=
    (X.act_comp _ _ t).trans ((X.act_comp ρ τ _).trans (congrArg (X.act ρ) (X.act_comp τ settle.1 t).symm))
  have right : X.act (X.comp (X.comp ρ j) σ.1) t = X.act ρ (X.act (X.comp j σ.1) t) :=
    (X.act_comp _ _ t).trans ((X.act_comp ρ j _).trans (congrArg (X.act ρ) (X.act_comp j σ.1 t).symm))
  have moved := X.preserves ρ ((X.equivalence _).symm (agree t))
  exact (congrArg₂ (fun u v => X.E u v) left right).mpr moved

variable {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **The step with disequations covers its answers** when the step's prepared settlement extends at
every preparation; its guards play no part. -/
theorem withDisequations_coversAnswers {P : Interface.Step X O State Firing}
    [P.Guarded] [P.Exact] (reflects : P.Reflects)
    (extend : ∀ {s : State} (f : Firing s) (p : P.Prepares f), Extends X (P.preparedSettle f p)) :
    CoversAnswers (P.withDisequations reflects) := by
  apply coversAnswers_of_extends
  intro _ f _
  exact extends_frames _ rfl (extend f.base _)

end Disequations

/-! ## The native step -/

section Native

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature}

/-- **The assignment of an extension of declarations is faithful**: instantiation along it is
injective on observations. -/
theorem extension_faithful {V : Type} {source : V → MetaArity S}
    (extension : ContextualGuardMatching.Extension source) :
    Faithful (Frames.contextual S) (a := ⟨V, source⟩) (b := ⟨extension.Names, extension.declarations⟩)
      extension.assignment := by
  intro u v same
  obtain ⟨Γ, sort, t⟩ := u
  obtain ⟨Γ', sort', t'⟩ := v
  change (⟨Γ, sort, instantiate extension.assignment t⟩ : Observation S extension.declarations) =
    ⟨Γ', sort', instantiate extension.assignment t'⟩ at same
  have contexts : Γ = Γ' := congrArg Sigma.fst same
  subst contexts
  have inner := eq_of_heq (Sigma.mk.inj same).2
  have sorts : sort = sort' := congrArg Sigma.fst inner
  subst sorts
  have terms := eq_of_heq (Sigma.mk.inj inner).2
  have equal := ContextualGuardMatching.Extension.instantiate_injective _ terms
  subst equal
  rfl

/-- **Every assignment along an extension of declarations extends**: a morphism out of the source
lifts through the frame with the complementary declarations as fresh names, along the faithful
inclusion of its target. -/
theorem extension_extends {V : Type} {source : V → MetaArity S}
    (extension : ContextualGuardMatching.Extension source) :
    Extends (Frames.contextual S) (a := ⟨V, source⟩) (a' := ⟨extension.Names, extension.declarations⟩)
      extension.assignment := by
  intro b σ
  let lifted := ContextualGuardMatching.Extension.withLocals extension.complementDeclarations b.arity
  refine ⟨⟨lifted.Names, lifted.declarations⟩, lifted.assignment, extension.liftModel σ,
    extension_faithful lifted, fun t => ?_⟩
  show instantiateObservation (Assignment.compose lifted.assignment σ) t =
    instantiateObservation (Assignment.compose (extension.liftModel σ) extension.assignment) t
  rw [extension.liftModel_square σ]
  rfl

variable {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- **The native settlement extends**: it is the assignment of the solver's result frame. -/
theorem native_extends {s : Interface.NativeState S O Γ sort} (f : Interface.NativeFiring s)
    (realized : (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep.Admits f) :
    Extends (Frames.contextual S) (Interface.native.settle f realized) := by
  intro b σ
  obtain ⟨c, j, τ, faithful, agree⟩ := extension_extends (f.pinned realized).firing.resultFrame σ
  refine ⟨c, j, τ, faithful, fun t => ?_⟩
  have square := agree t
  rw [(f.pinned realized).firing.resultFrame_assignment] at square
  exact square

/-- **The native step covers its answers**, after extending their frames by the helpers it mints. -/
theorem native_coversAnswers :
    CoversAnswers (Interface.native (S := S) (O := O) (Γ := Γ) (sort := sort)).toStep := by
  apply coversAnswers_of_extends
  intro _ f realized
  exact native_extends f realized

end Native

#print axioms firstOrder_covers
#print axioms firstOrderWith_covers
#print axioms located_covers
#print axioms rational_covers
#print axioms disequality_covers
#print axioms relabel_covers
#print axioms helper_covers
#print axioms helperWith_covers
#print axioms dependent_covers
#print axioms dependentWith_covers
#print axioms permitted_coversAnswers
#print axioms extends_frames
#print axioms withDisequations_coversAnswers
#print axioms extension_faithful
#print axioms extension_extends
#print axioms native_extends
#print axioms native_coversAnswers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SettlementCoverage
