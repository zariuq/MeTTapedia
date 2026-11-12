import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.VectorAppend

/-!
# Computing dependent publication: vector append and subsequent use

The first application uses the actual definition-elimination update for
m = zero, retaining the typed input ys : vec k and requesting vec(add m k).
Only the declared, typed zero-addition equation is used; no normalization
or confluence theorem is inferred from root determinism.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Vector

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open ProgrammingOnTheStep.VectorPackage
open NativeTypesOnTheStep.VectorAppend

def sourceType : TypeOver callFrame :=
  ⟨vecC (.var 2), u0, .sort _,
    vtyped (vec_typed (Derivable.var (R := rules) (Γ := callFrame.raw) 2))⟩

def sourceValue : TotalTerm callFrame := ⟨sourceType, ⟨.var 1, Derivable.var 1⟩⟩

def output : Output callFrame := ⟨sourceValue, callType⟩

def schema : Schema vlevels Nat callFrame where
  helpers := .nil _
  takes := []
  reads := []
  outputs := [.value output]
  tells := [matchNil]
  guards := []
  queries := []

def pick : Pick schema := ⟨⟨[], [], [0]⟩, rfl⟩

theorem compiled_is_actual_append : schema.compile (state := callState) pick = vappendFiring := rfl

/-- The actual computational elimination update; no chosen semantic settler. -/
def update : ContextualDependentUpdate.Update vlevels (schema.compile (state := callState) pick).information :=
  ContextualDependentUpdate.definition vlevels zeroTerm []

theorem update_finishes : update.remaining = [] := rfl

theorem output_license : output.At update.answer := by
  have kTyped : Typed vrules ctxKY.raw (.var 1) natC := Derivable.var 1
  have zeroTyped : Typed vrules ctxKY.raw zeroC natC := vtyped (zero_typed _)
  have addConst : Typed vrules ctxKY.raw (.const addN) (.pi natC (.pi natC natC)) :=
    vtyped (.const declared_add addTy_typed (.sort _))
  have vecConst : Typed vrules ctxKY.raw (.const vecN) (.pi natC U0) :=
    vtyped (.const declared_vec vecTy_typed (.sort _))
  have computes : Equal vrules ctxKY.raw (addC zeroC (.var 1)) (.var 1) natC :=
    .root (NativeTypesOnTheStep.declare_step (AddStep.zero _))
      (.appElim (.appElim addConst zeroTyped) kTyped) kTyped
  have types : Equal vrules ctxKY.raw (vecC (.var 1)) (vecC (addC zeroC (.var 1))) U0 :=
    .appCong (.refl vecConst) (.symm computes)
  exact .subEqual types (.sort _)

def application : Application vlevels Nat callState :=
  ⟨schema, pick, ctxKY, update.answer, .residual update (by
    intro candidate member
    obtain rfl := List.mem_singleton.mp member
    exact output_license)⟩

theorem source_admitted : schema.Admits (state := callState) pick := by
  apply application.basis.native_checks_iff.mp
  have existing := NativeTypesOnTheStep.VectorAppend.vappend_admitsAfterMatch
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl⟩,
    existing.2.1, existing.2.2.1, existing.2.2.2, ?_⟩
  intro candidate member
  obtain rfl := List.mem_singleton.mp member
  exact output_license

theorem native_admitted : (realizationStep vlevels Nat).Admits application :=
  (realization_admits_iff application).mpr source_admitted

abbrev published : State vrules Nat := (realizationStep vlevels Nat).result application native_admitted

theorem result_is_source_publication : published = application.sourceResult source_admitted :=
  realization_result application source_admitted

theorem published_frame : published.frame = ctxKY := rfl

theorem published_knowledge : published.knowledge = [] := rfl

theorem published_occurrences : published.present = {0} := by decide

theorem published_type : (published.label 0).1.code = vecC (addC zeroC (.var ⟨1, by decide⟩)) := rfl

theorem published_value : (published.label 0).2.code = .var ⟨0, by decide⟩ := rfl

/-- The requested result type is interpreted through an explicitly typed
computing equation. The normalized target type remains available to the next action. -/
def consumedType : TypeOver ctxKY := vecK.reindex (projectionHom ctxK vecK)

def consumeOutput : Output published.frame := ⟨published.label 0, consumedType⟩

def consumeSchema : Schema vlevels Nat published.frame where
  helpers := .nil _
  takes := [published.label 0]
  reads := []
  outputs := [.value consumeOutput]
  tells := []
  guards := []
  queries := []

def consumePick : Pick consumeSchema := ⟨⟨[0], [], [1]⟩, rfl⟩

theorem consume_license : consumeOutput.At (𝟙 published.frame) := by
  have kTyped : Typed vrules ctxKY.raw (.var 1) natC := Derivable.var 1
  have zeroTyped : Typed vrules ctxKY.raw zeroC natC := vtyped (zero_typed _)
  have addConst : Typed vrules ctxKY.raw (.const addN) (.pi natC (.pi natC natC)) :=
    vtyped (.const declared_add addTy_typed (.sort _))
  have vecConst : Typed vrules ctxKY.raw (.const vecN) (.pi natC U0) :=
    vtyped (.const declared_vec vecTy_typed (.sort _))
  have computes : Equal vrules ctxKY.raw (addC zeroC (.var 1)) (.var 1) natC :=
    .root (NativeTypesOnTheStep.declare_step (AddStep.zero _))
      (.appElim (.appElim addConst zeroTyped) kTyped) kTyped
  exact .subEqual (.appCong (.refl vecConst) computes) (.sort _)

def consumeApplication : Application vlevels Nat published :=
  ⟨consumeSchema, consumePick, published.frame, 𝟙 _,
    .residual (ContextualDependentUpdate.Update.pending vlevels _) (by
      intro candidate member
      obtain rfl := List.mem_singleton.mp member
      exact consume_license)⟩

theorem consume_models : (frames vlevels).Models (𝟙 published.frame)
    consumeApplication.compile.information := by
  intro equation member
  have same : equation = (published.label 0, published.label 0) := by
    change equation ∈ [(published.label 0, (published.label 0).reindex (𝟙 published.frame))] at member
    simpa only [reindex_id, List.mem_singleton] using member
  subst equation
  exact ((frames vlevels).equivalence published.frame).refl _

theorem consume_admitted : (realizationStep vlevels Nat).Admits consumeApplication := by
  refine ⟨⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl⟩, ?_⟩, ?_,
    ⟨published.frame, 𝟙 _, consume_models⟩, ?_⟩
  · intro candidate member
    obtain rfl := List.mem_singleton.mp member
    exact consume_license
  · apply (DependentFull.enabled_iff consumeApplication.compile).mpr
    decide
  · intro target substitution _
    exact ⟨(fun _ member => nomatch member), (fun _ member => nomatch member)⟩

def run : (realizationStep vlevels Nat).Run callState :=
  .cons application native_admitted
    (.cons consumeApplication consume_admitted
      (.nil ((realizationStep vlevels Nat).result consumeApplication consume_admitted)))

theorem two_actual_events : run.word.length = 2 := rfl

theorem final_occurrences : run.last.present = {1} := by decide

theorem final_type : (run.last.label 1).1.code = vecC (.var ⟨1, by decide⟩) := rfl

theorem final_value : (run.last.label 1).2.code = .var ⟨0, by decide⟩ := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Vector

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Vector.source_admitted
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Vector.consume_admitted
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Vector.final_type
