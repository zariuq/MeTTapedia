import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RepresentedPaths
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRuns

/-!
# Authored execution paths through a represented semantic profile

Exact source codecs cover represented states and candidates. The existing
source execution equivalence recovers their complete admitted paths. Mapping
those paths into the semantic carrier preserves execution. The separate
candidate-coverage law supplies reflection of every permitted semantic path
from a represented state. No codec of the whole semantic carrier is required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.RepresentedRuns

open Interface

universe uO uT uH uOcc uS uF uR uC

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {E : EffectCore X O State Firing} {Represented : Type uR} {Candidate : Represented → Type uC}
  (R : E.Representation Represented Candidate) (allow : E.Admission)
  (code : Encoding Represented Candidate) (decision : Decisions R.effect (R.admission allow))

abbrev Source := ExecutionObject (effectQueries R.effect (R.admission allow) code decision)

noncomputable def interpretRun (start : EffectCore.EventObject R.effect (R.admission allow)) :
    @Quiver.PathStar (Source R allow code decision) _ (code.state.view (sort := ()) start) →
      @Quiver.PathStar (EffectCore.EventObject E allow) _ (R.state start) :=
  (R.mapEvents allow).pathStar start ∘ (executionRunEquiv R.effect (R.admission allow) code decision start).symm

/-- The interpretation retains the whole represented path, rather than
selecting another semantic run with the same final state. -/
theorem interpret_encoded_run (start : EffectCore.EventObject R.effect (R.admission allow))
    (path : Quiver.PathStar start) :
    interpretRun R allow code decision start
      ((executionMap R.effect (R.admission allow) code decision).pathStar start path) =
        (R.mapEvents allow).pathStar start path := by
  exact congrArg ((R.mapEvents allow).pathStar start)
    ((executionRunEquiv R.effect (R.admission allow) code decision start).symm_apply_apply path)

theorem covers_semantic_runs (coverage : R.Covers allow)
    (start : EffectCore.EventObject R.effect (R.admission allow)) :
    Function.Surjective (interpretRun R allow code decision start) :=
  (R.path_surjective allow coverage start).comp
    (executionRunEquiv R.effect (R.admission allow) code decision start).symm.surjective

theorem faithful_semantic_runs
    (faithful : ∀ start : Represented, Function.Injective (R.firing (s := start)))
    (start : EffectCore.EventObject R.effect (R.admission allow)) :
    Function.Injective (interpretRun R allow code decision start) :=
  (Prefunctor.pathStar_injective _ (R.star_injective allow faithful) start).comp
    (executionRunEquiv R.effect (R.admission allow) code decision start).symm.injective

theorem unique_source_run (coverage : R.Covers allow)
    (faithful : ∀ start : Represented, Function.Injective (R.firing (s := start)))
    (start : EffectCore.EventObject R.effect (R.admission allow))
    (path : @Quiver.PathStar (EffectCore.EventObject E allow) _ (R.state start)) :
    ∃! source : @Quiver.PathStar (Source R allow code decision) _ (code.state.view (sort := ()) start),
      interpretRun R allow code decision start source = path :=
  (show Function.Bijective (interpretRun R allow code decision start) from
    ⟨faithful_semantic_runs R allow code decision faithful start,
      covers_semantic_runs R allow code decision coverage start⟩).existsUnique path

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.RepresentedRuns
