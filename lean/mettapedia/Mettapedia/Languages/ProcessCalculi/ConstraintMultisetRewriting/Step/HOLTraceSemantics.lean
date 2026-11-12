import Mettapedia.Languages.HOLLight.RunSourceReadback
import Mathlib.Logic.Relation

/-!
# The source trace operation and generated equivalence

The independent HOL definition compares every Boolean observation which
respects the selected generating equations. Its interpreted relation is
exactly the equivalence closure of those equations. Quantification uses the
source model's full function domains, not a selected collection of tests.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTraceSemantics

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ReferenceBooleanSemantics ModelInterpretation

universe u v w

def Respects {Carrier : Type u} (generators : Carrier → Carrier → Prop) (observe : Carrier → Prop) : Prop :=
  ∀ left right, generators left right → (observe left ↔ observe right)

def Observational {Carrier : Type u} (generators : Carrier → Carrier → Prop) (left right : Carrier) : Prop :=
  ∀ observe : Carrier → Prop, Respects generators observe → (observe left ↔ observe right)

theorem respects_eqvGen {Carrier : Type u} {generators : Carrier → Carrier → Prop}
    {observe : Carrier → Prop} (respects : Respects generators observe) {left right : Carrier}
    (related : Relation.EqvGen generators left right) : observe left ↔ observe right := by
  induction related with
  | rel left right generator => exact respects left right generator
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

theorem observational_iff_eqvGen {Carrier : Type u} (generators : Carrier → Carrier → Prop)
    (left right : Carrier) : Observational generators left right ↔ Relation.EqvGen generators left right := by
  constructor
  · intro same
    have preserves : Respects generators (Relation.EqvGen generators left) := by
      intro one two generator
      exact ⟨fun before => .trans _ _ _ before (.rel _ _ generator),
        fun after => .trans _ _ _ after (.symm _ _ (.rel _ _ generator))⟩
    exact (same _ preserves).mp (.refl _)
  · intro related observe respects
    exact respects_eqvGen respects related

theorem descends_iff {Carrier : Type u} (generators : Carrier → Carrier → Prop) (observe : Carrier → Prop) :
    Respects (Observational generators) observe ↔ Respects generators observe := by
  constructor
  · intro respects left right generator
    exact respects left right ((observational_iff_eqvGen _ _ _).mpr (.rel _ _ generator))
  · intro respects left right related
    exact respects_eqvGen respects ((observational_iff_eqvGen _ _ _).mp related)

theorem eqvGen_map {Carrier : Type u} {Other : Type v}
    {generators : Carrier → Carrier → Prop} {other : Other → Other → Prop}
    (map : Carrier → Other) (preserves : ∀ left right, generators left right → other (map left) (map right))
    {left right : Carrier} (related : Relation.EqvGen generators left right) :
    Relation.EqvGen other (map left) (map right) := by
  induction related with
  | rel left right generator => exact .rel _ _ (preserves left right generator)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem eqvGen_equiv {Carrier : Type u} {Other : Type v} (code : Carrier ≃ Other)
    (generators : Other → Other → Prop) (left right : Other) :
    Relation.EqvGen (fun one two => generators (code one) (code two)) (code.symm left) (code.symm right) ↔
      Relation.EqvGen generators left right := by
  constructor
  · intro related
    simpa only [Equiv.apply_symm_apply] using eqvGen_map code (fun _ _ proof => proof) related
  · intro related
    exact eqvGen_map code.symm (by intro one two proof; simpa only [Equiv.apply_symm_apply] using proof) related

theorem eqvGen_false_iff {Carrier : Type u} (left right : Carrier) :
    Relation.EqvGen (fun _ _ : Carrier => False) left right ↔ left = right := by
  constructor
  · intro related
    induction related with
    | rel _ _ impossible => exact impossible.elim
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ first second => exact first.trans second
  · rintro rfl
    exact .refl _

structure Signature where
  run : HOL.Ty AtomicTy
  trace : HOL.ClosedTerm Symbol
    ((run.arr (run.arr .prop)).arr (run.arr (run.arr .prop)))

namespace Signature

variable (signature : Signature)

abbrev relationType := signature.run.arr (signature.run.arr .prop)
abbrev observerType := signature.run.arr .prop

def applyTrace {context : HOL.Ctx AtomicTy} (generators : HOL.Term Symbol context signature.relationType)
    (left right : HOL.Term Symbol context signature.run) : HOL.Term Symbol context .prop :=
  .app (.app (.app (HOL.weakenCtx _ signature.trace) generators) left) right

def meaningFormula : HOL.ClosedFormula Symbol :=
  universal (type := signature.relationType) (universal (type := signature.run)
    (universal (type := signature.run)
      (.eq (signature.applyTrace (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
        (universal (type := signature.observerType)
          (implication
            (universal (type := signature.run) (universal (type := signature.run)
              (implication
                (.app (.app (.var (.vs (.vs (.vs (.vs (.vs .vz)))))) (.var (.vs .vz))) (.var .vz))
                (.eq (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
                  (.app (.var (.vs (.vs .vz))) (.var .vz))))))
            (.eq (.app (.var .vz) (.var (.vs (.vs .vz))))
              (.app (.var .vz) (.var (.vs .vz)))))))))

abbrev Carrier (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.run

def traceValue (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    (signature.Carrier model → signature.Carrier model → ULift.{w+1} Prop) →
      signature.Carrier model → signature.Carrier model → ULift.{w+1} Prop :=
  model.denote signature.trace (fun index => nomatch index)

theorem denote_trace (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (valuation : model.Valuation []) :
    model.denote signature.trace valuation = signature.traceValue model := by
  apply congrArg (model.denote signature.trace)
  funext type index
  exact nomatch index

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
  (full : model.FullDomains) (meanings : Meanings model)
include full meanings

theorem formula_meaning : model.models signature.meaningFormula ↔
    ∀ generators left right, (signature.traceValue model generators left right).down ↔
      Observational (fun one two => (generators one two).down) left right := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [meaningFormula, applyTrace, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_implication model meanings,
    HOL.HenkinModel.denote_weakenCtx, HOL.HenkinModel.denote, HOL.PreModel.denote,
    HOL.PreModel.extend, signature.denote_trace model]
  simp only [admitted, forall_true_left]
  have propositions (left right : ULift.{w+1} Prop) :
      model.Eqv .prop left right ↔ (left.down ↔ right.down) :=
    (model.eqv_iff_eq_of_fullDomains full (a := .prop) left right).trans
      ⟨fun same => same ▸ Iff.rfl, fun same => ULift.ext left right (propext same)⟩
  dsimp only [relationType, observerType, HOL.Ty.denote]
  simp only [propositions]
  have observers (generators : signature.Carrier model → signature.Carrier model → ULift.{w+1} Prop)
      (left right : signature.Carrier model) :
      (∀ observe : signature.Carrier model → ULift.{w+1} Prop,
        (∀ one two, (generators one two).down → ((observe one).down ↔ (observe two).down)) →
          ((observe left).down ↔ (observe right).down)) ↔
        Observational (fun one two => (generators one two).down) left right := by
    constructor
    · intro all observe respects
      exact all (fun value => .up (observe value)) respects
    · intro all observe respects
      exact all (fun value => (observe value).down) respects
  simp only [observers]

theorem trace_iff_eqvGen (meaning : model.models signature.meaningFormula)
    (generators : signature.Carrier model → signature.Carrier model → ULift.{w+1} Prop)
    (left right : signature.Carrier model) :
    (signature.traceValue model generators left right).down ↔
      Relation.EqvGen (fun one two => (generators one two).down) left right :=
  ((signature.formula_meaning model full meanings).mp meaning generators left right).trans
    (observational_iff_eqvGen _ _ _)

end Signature

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTraceSemantics
