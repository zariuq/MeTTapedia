import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PreparedWords
import Mettapedia.Languages.HOLLight.RunSourceReadback

/-!
# Interpreted recursion equations for complete prepared-event words

The target and domain are closed source terms over the actual source list
carrier. Four checked recursion equations identify their meanings with the
native result fold and prefix checks. The list equivalence comes from the
source datatype's separation, injectivity and full induction laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordSemantics

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ReferenceBooleanSemantics ModelInterpretation

universe w

structure Signature where
  runs : RunModelCorrespondence.Signature
  target : HOL.ClosedTerm Symbol
    ((runs.state.arr (runs.lists.element.arr runs.state)).arr
      (runs.lists.sequence.arr (runs.state.arr runs.state)))
  domain : HOL.ClosedTerm Symbol
    ((runs.state.arr (runs.lists.element.arr .prop)).arr
      ((runs.state.arr (runs.lists.element.arr runs.state)).arr
        ((runs.state.arr (runs.lists.element.arr .prop)).arr
          (runs.lists.sequence.arr (runs.state.arr .prop)))))

namespace Signature

variable (signature : Signature)

abbrev resultType := signature.runs.state.arr (signature.runs.lists.element.arr signature.runs.state)
abbrev predicateType := signature.runs.state.arr (signature.runs.lists.element.arr .prop)

def applyTarget {context : HOL.Ctx AtomicTy} (result : HOL.Term Symbol context signature.resultType)
    (events : HOL.Term Symbol context signature.runs.lists.sequence)
    (source : HOL.Term Symbol context signature.runs.state) : HOL.Term Symbol context signature.runs.state :=
  .app (.app (.app (HOL.weakenCtx _ signature.target) result) events) source

def applyDomain {context : HOL.Ctx AtomicTy} (prepare : HOL.Term Symbol context signature.predicateType)
    (result : HOL.Term Symbol context signature.resultType) (allow : HOL.Term Symbol context signature.predicateType)
    (events : HOL.Term Symbol context signature.runs.lists.sequence)
    (source : HOL.Term Symbol context signature.runs.state) : HOL.Term Symbol context .prop :=
  .app (.app (.app (.app (.app (HOL.weakenCtx _ signature.domain) prepare) result) allow) events) source

def targetNil : HOL.ClosedFormula Symbol :=
  universal (type := signature.resultType) (universal (type := signature.runs.state)
    (.eq (signature.applyTarget (.var (.vs .vz)) (HOL.weakenCtx _ signature.runs.lists.nil) (.var .vz))
      (.var .vz)))

def targetCons : HOL.ClosedFormula Symbol :=
  universal (type := signature.resultType) (universal (type := signature.runs.lists.element)
    (universal (type := signature.runs.lists.sequence) (universal (type := signature.runs.state)
      (.eq
        (signature.applyTarget (.var (.vs (.vs (.vs .vz))))
          (.app (.app (HOL.weakenCtx _ signature.runs.lists.cons) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))
          (.var .vz))
        (signature.applyTarget (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz))
          (.app (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz)) (.var (.vs (.vs .vz)))))))))

def domainNil : HOL.ClosedFormula Symbol :=
  universal (type := signature.predicateType) (universal (type := signature.resultType)
    (universal (type := signature.predicateType) (universal (type := signature.runs.state)
      (signature.applyDomain (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var (.vs .vz))
        (HOL.weakenCtx _ signature.runs.lists.nil) (.var .vz)))))

def domainCons : HOL.ClosedFormula Symbol :=
  universal (type := signature.predicateType) (universal (type := signature.resultType)
    (universal (type := signature.predicateType) (universal (type := signature.runs.lists.element)
      (universal (type := signature.runs.lists.sequence) (universal (type := signature.runs.state)
        (.eq
          (signature.applyDomain (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
            (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs (.vs (.vs .vz))))
            (.app (.app (HOL.weakenCtx _ signature.runs.lists.cons) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))
            (.var .vz))
          (conjunction
            (.app (.app (.var (.vs (.vs (.vs (.vs (.vs .vz)))))) (.var .vz)) (.var (.vs (.vs .vz))))
            (conjunction
              (.app (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz)) (.var (.vs (.vs .vz))))
              (signature.applyDomain (.var (.vs (.vs (.vs (.vs (.vs .vz))))))
                (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz))
                (.app (.app (.var (.vs (.vs (.vs (.vs .vz))))) (.var .vz)) (.var (.vs (.vs .vz)))))))))))))

abbrev State (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) := signature.runs.State model
abbrev Event (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) := signature.runs.lists.Element model

def targetValue (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    (signature.State model → signature.Event model → signature.State model) →
      signature.runs.lists.Carrier model → signature.State model → signature.State model :=
  model.denote signature.target (fun index => nomatch index)

def domainValue (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    (signature.State model → signature.Event model → ULift.{w+1} Prop) →
      (signature.State model → signature.Event model → signature.State model) →
      (signature.State model → signature.Event model → ULift.{w+1} Prop) →
      signature.runs.lists.Carrier model → signature.State model → ULift.{w+1} Prop :=
  model.denote signature.domain (fun index => nomatch index)

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)

theorem denote_target (valuation : model.Valuation []) :
    model.denote signature.target valuation = signature.targetValue model := by
  apply congrArg (model.denote signature.target)
  funext type index
  exact nomatch index

theorem denote_domain (valuation : model.Valuation []) :
    model.denote signature.domain valuation = signature.domainValue model := by
  apply congrArg (model.denote signature.domain)
  funext type index
  exact nomatch index

variable (full : model.FullDomains) (meanings : Meanings model)
include full meanings

theorem targetNil_meaning : model.models signature.targetNil ↔
    ∀ result source, signature.targetValue model result (signature.runs.lists.empty model) source = source := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [targetNil, applyTarget, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    signature.denote_target model, signature.runs.lists.denote_nil model]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, forall_true_left]
  rfl

theorem targetCons_meaning : model.models signature.targetCons ↔
    ∀ result event events source,
      signature.targetValue model result (signature.runs.lists.prepend model event events) source =
        signature.targetValue model result events (result source event) := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [targetCons, applyTarget, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    signature.denote_target model, signature.runs.lists.denote_cons model]
  simp only [model.eqv_iff_eq_of_fullDomains full, admitted, forall_true_left]
  rfl

theorem domainNil_meaning : model.models signature.domainNil ↔
    ∀ prepare result allow source,
      (signature.domainValue model prepare result allow (signature.runs.lists.empty model) source).down := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [domainNil, applyDomain, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    signature.denote_domain model, signature.runs.lists.denote_nil model]
  simp only [admitted, forall_true_left]
  rfl

theorem domainCons_meaning : model.models signature.domainCons ↔
    ∀ prepare result allow event events source,
      (signature.domainValue model prepare result allow (signature.runs.lists.prepend model event events) source).down ↔
        (prepare source event).down ∧ (allow source event).down ∧
          (signature.domainValue model prepare result allow events (result source event)).down := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [domainCons, applyDomain, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, denote_conjunction model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    signature.denote_domain model, signature.runs.lists.denote_cons model]
  simp only [admitted, forall_true_left]
  rfl

theorem target_eq_fold
    (nilEquation : model.models signature.targetNil) (consEquation : model.models signature.targetCons)
    (lists : ListSourceReadback.Correspondence signature.runs.lists model)
    (result : signature.State model → signature.Event model → signature.State model)
    (events : List (signature.Event model)) (source : signature.State model) :
    signature.targetValue model result (lists.equivalence events) source = PreparedWords.target result events source := by
  induction events generalizing source with
  | nil => rw [lists.nil, (signature.targetNil_meaning model full meanings).mp nilEquation]; rfl
  | cons event events ih =>
      rw [lists.cons, (signature.targetCons_meaning model full meanings).mp consEquation, ih]
      rfl

theorem domain_iff_checks
    (nilEquation : model.models signature.domainNil) (consEquation : model.models signature.domainCons)
    (lists : ListSourceReadback.Correspondence signature.runs.lists model)
    (prepare : signature.State model → signature.Event model → ULift.{w+1} Prop)
    (result : signature.State model → signature.Event model → signature.State model)
    (allow : signature.State model → signature.Event model → ULift.{w+1} Prop)
    (events : List (signature.Event model)) (source : signature.State model) :
    (signature.domainValue model prepare result allow (lists.equivalence events) source).down ↔
      PreparedWords.Domain (fun state event => (prepare state event).down) result
        (fun state event => (allow state event).down) events source := by
  induction events generalizing source with
  | nil =>
      exact ⟨fun _ => trivial, fun _ => by
        rw [lists.nil]
        exact (signature.domainNil_meaning model full meanings).mp nilEquation _ _ _ _⟩
  | cons event events ih =>
      rw [lists.cons, (signature.domainCons_meaning model full meanings).mp consEquation, ih]
      rfl

end Signature

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLPreparedWordSemantics
