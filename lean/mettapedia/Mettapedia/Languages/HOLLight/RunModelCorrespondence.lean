import Mettapedia.Languages.HOLLight.ListSourceReadback

/-!
# Interpreted finite event words and pullbacks

The source path and pullback operations are closed typed terms. Their four
recursion equations are interpreted in the same model as the list constructors.
The resulting path relation agrees in both directions with finite labelled
runs. Pullback is the right fold in execution order, including the empty word.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RunModelCorrespondence

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReferenceBooleanSemantics ModelInterpretation

universe w u v

/-- Finite runs retain their complete event word as well as their endpoints. -/
inductive WordRun {State : Type u} {Event : Type v}
    (step : State → Event → State → Prop) : List Event → State → State → Prop where
  | nil (state : State) : WordRun step [] state state
  | cons {event events source middle target} :
      step source event middle → WordRun step events middle target →
      WordRun step (event :: events) source target

namespace WordRun

variable {State : Type u} {Event : Type v} {step : State → Event → State → Prop}

theorem nil_iff {source target : State} : WordRun step [] source target ↔ source = target := by
  constructor
  · intro run; cases run; rfl
  · rintro rfl; exact .nil _

theorem cons_iff {event : Event} {events : List Event} {source target : State} :
    WordRun step (event :: events) source target ↔
      ∃ middle, step source event middle ∧ WordRun step events middle target := by
  constructor
  · intro run; cases run with | cons first rest => exact ⟨_, first, rest⟩
  · rintro ⟨middle, first, rest⟩; exact .cons first rest

theorem append_iff {first second : List Event} {source target : State} :
    WordRun step (first ++ second) source target ↔
      ∃ middle, WordRun step first source middle ∧ WordRun step second middle target := by
  induction first generalizing source with
  | nil =>
      simp only [List.nil_append, nil_iff]
      constructor
      · intro run; exact ⟨source, rfl, run⟩
      · rintro ⟨middle, rfl, run⟩; exact run
  | cons event events ih =>
      simp only [List.cons_append, cons_iff, ih]
      constructor
      · rintro ⟨next, firstStep, middle, firstRun, secondRun⟩
        exact ⟨middle, ⟨next, firstStep, firstRun⟩, secondRun⟩
      · rintro ⟨middle, ⟨next, firstStep, firstRun⟩, secondRun⟩
        exact ⟨next, firstStep, middle, firstRun, secondRun⟩

end WordRun

/-- Equivalences of the state and event carriers preserve the full word and
all intermediate states. Surjectivity is essential for reflection. -/
theorem wordRun_transport {State : Type u} {Event : Type v}
    {OtherState : Type*} {OtherEvent : Type*}
    (states : OtherState ≃ State) (events : OtherEvent ≃ Event)
    (step : State → Event → State → Prop) (word : List Event) (source target : State) :
    WordRun (fun s e t => step (states s) (events e) (states t))
      (word.map events.symm) (states.symm source) (states.symm target) ↔
      WordRun step word source target := by
  induction word generalizing source with
  | nil =>
      simp only [List.map_nil, WordRun.nil_iff, Equiv.apply_eq_iff_eq]
  | cons event word ih =>
      simp only [List.map_cons, WordRun.cons_iff, Equiv.apply_symm_apply]
      constructor
      · rintro ⟨middle, first, rest⟩
        refine ⟨states middle, first, ?_⟩
        apply (ih (states middle)).mp
        simpa only [Equiv.symm_apply_apply] using rest
      · rintro ⟨middle, first, rest⟩
        exact ⟨states.symm middle, by simpa only [Equiv.apply_symm_apply] using first,
          (ih middle).mpr rest⟩

structure Signature where
  lists : ListModelCategoricity.Signature
  state : HOL.Ty AtomicTy
  value : HOL.Ty AtomicTy
  path : HOL.ClosedTerm Symbol
    ((state.arr (lists.element.arr (state.arr .prop))).arr
      (lists.sequence.arr (state.arr (state.arr .prop))))
  pullback : HOL.ClosedTerm Symbol
    ((lists.element.arr (value.arr value)).arr (lists.sequence.arr (value.arr value)))

namespace Signature

variable (signature : Signature)

abbrev stepType := signature.state.arr (signature.lists.element.arr (signature.state.arr .prop))
abbrev backType := signature.lists.element.arr (signature.value.arr signature.value)

def applyPath {context : HOL.Ctx AtomicTy}
    (step : HOL.Term Symbol context signature.stepType)
    (events : HOL.Term Symbol context signature.lists.sequence)
    (source target : HOL.Term Symbol context signature.state) : HOL.Term Symbol context .prop :=
  .app (.app (.app (.app (HOL.weakenCtx _ signature.path) step) events) source) target

def applyBack {context : HOL.Ctx AtomicTy}
    (back : HOL.Term Symbol context signature.backType)
    (events : HOL.Term Symbol context signature.lists.sequence)
    (value : HOL.Term Symbol context signature.value) : HOL.Term Symbol context signature.value :=
  .app (.app (.app (HOL.weakenCtx _ signature.pullback) back) events) value

def pathNil : HOL.ClosedFormula Symbol :=
  universal (type := signature.stepType) (universal (type := signature.state)
    (universal (type := signature.state)
      (.eq (signature.applyPath (.var (.vs (.vs .vz)))
        (HOL.weakenCtx _ signature.lists.nil) (.var (.vs .vz)) (.var .vz))
        (.eq (.var (.vs .vz)) (.var .vz)))))

def pathCons : HOL.ClosedFormula Symbol :=
  universal (type := signature.stepType) (universal (type := signature.lists.element)
    (universal (type := signature.lists.sequence) (universal (type := signature.state)
      (universal (type := signature.state)
        (.eq
          (signature.applyPath (.var (.vs (.vs (.vs (.vs .vz)))))
            (.app (.app (HOL.weakenCtx _ signature.lists.cons) (.var (.vs (.vs (.vs .vz)))))
              (.var (.vs (.vs .vz)))) (.var (.vs .vz)) (.var .vz))
          (existential (type := signature.state)
            (conjunction
              (.app (.app (.app (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
                (.var (.vs (.vs .vz)))) (.var (.vs (.vs (.vs (.vs .vz)))))) (.var .vz))
              (signature.applyPath (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
                (.var (.vs (.vs (.vs .vz)))) (.var .vz) (.var (.vs .vz))))))))))

def pullbackNil : HOL.ClosedFormula Symbol :=
  universal (type := signature.backType) (universal (type := signature.value)
    (.eq (signature.applyBack (.var (.vs .vz)) (HOL.weakenCtx _ signature.lists.nil) (.var .vz))
      (.var .vz)))

def pullbackCons : HOL.ClosedFormula Symbol :=
  universal (type := signature.backType) (universal (type := signature.lists.element)
    (universal (type := signature.lists.sequence) (universal (type := signature.value)
      (.eq
        (signature.applyBack (.var (.vs (.vs (.vs .vz))))
          (.app (.app (HOL.weakenCtx _ signature.lists.cons) (.var (.vs (.vs .vz))))
            (.var (.vs .vz))) (.var .vz))
        (.app (.app (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))))
          (signature.applyBack (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)) (.var .vz)))))))

abbrev State (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.state

abbrev Value (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.value

def pathValue (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    (signature.State model → signature.lists.Element model → signature.State model → ULift.{w+1} Prop) →
      signature.lists.Carrier model → signature.State model → signature.State model → ULift.{w+1} Prop :=
  model.denote signature.path (fun index => nomatch index)

def backValue (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    (signature.lists.Element model → signature.Value model → signature.Value model) →
      signature.lists.Carrier model → signature.Value model → signature.Value model :=
  model.denote signature.pullback (fun index => nomatch index)

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

theorem denote_path (valuation : model.Valuation []) :
    model.denote signature.path valuation = signature.pathValue model := by
  apply congrArg (model.denote signature.path)
  funext type index
  exact nomatch index

theorem denote_pullback (valuation : model.Valuation []) :
    model.denote signature.pullback valuation = signature.backValue model := by
  apply congrArg (model.denote signature.pullback)
  funext type index
  exact nomatch index

variable (full : model.FullDomains) (meanings : Meanings model)
include full meanings

theorem pathNil_meaning : model.models signature.pathNil ↔
    ∀ step source target,
      (signature.pathValue model step (signature.lists.empty model) source target).down ↔
        source = target := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [pathNil, applyPath, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    signature.denote_path model, signature.lists.denote_nil model]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, forall_true_left]
  rfl

theorem pathCons_meaning : model.models signature.pathCons ↔
    ∀ step event events source target,
      (signature.pathValue model step (signature.lists.prepend model event events) source target).down ↔
        ∃ middle, (step source event middle).down ∧
          (signature.pathValue model step events middle target).down := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [pathCons, applyPath, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_existential model meanings, denote_conjunction model meanings,
    HOL.HenkinModel.denote_weakenCtx, HOL.HenkinModel.denote, HOL.PreModel.denote,
    HOL.PreModel.extend, signature.denote_path model, signature.lists.denote_cons model]
  simp only [admitted, forall_true_left, true_and]
  rfl

theorem pullbackNil_meaning : model.models signature.pullbackNil ↔
    ∀ back value, signature.backValue model back (signature.lists.empty model) value = value := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [pullbackNil, applyBack, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    signature.denote_pullback model, signature.lists.denote_nil model]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, forall_true_left]
  rfl

theorem pullbackCons_meaning : model.models signature.pullbackCons ↔
    ∀ back event events value,
      signature.backValue model back (signature.lists.prepend model event events) value =
        back event (signature.backValue model back events value) := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [pullbackCons, applyBack, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    signature.denote_pullback model, signature.lists.denote_cons model]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, forall_true_left]
  rfl

theorem path_iff (nilEquation : model.models signature.pathNil)
    (consEquation : model.models signature.pathCons)
    (lists : ListSourceReadback.Correspondence signature.lists model)
    (step : signature.State model → signature.lists.Element model → signature.State model → ULift.{w+1} Prop)
    (events : List (signature.lists.Element model)) (source target : signature.State model) :
    (signature.pathValue model step (lists.equivalence events) source target).down ↔
      WordRun (fun s e t => (step s e t).down) events source target := by
  induction events generalizing source with
  | nil =>
      rw [lists.nil, (signature.pathNil_meaning model full meanings).mp nilEquation]
      exact WordRun.nil_iff.symm
  | cons event events ih =>
      rw [lists.cons, (signature.pathCons_meaning model full meanings).mp consEquation]
      simp only [ih, WordRun.cons_iff]

theorem pullback_eq_foldr (nilEquation : model.models signature.pullbackNil)
    (consEquation : model.models signature.pullbackCons)
    (lists : ListSourceReadback.Correspondence signature.lists model)
    (back : signature.lists.Element model → signature.Value model → signature.Value model)
    (events : List (signature.lists.Element model)) (value : signature.Value model) :
    signature.backValue model back (lists.equivalence events) value = events.foldr back value := by
  induction events with
  | nil => exact lists.nil ▸ (signature.pullbackNil_meaning model full meanings).mp nilEquation back value
  | cons event events ih =>
      rw [lists.cons, (signature.pullbackCons_meaning model full meanings).mp consEquation, ih]
      rfl

end Signature

end Mettapedia.Languages.HOLLight.RunModelCorrespondence
