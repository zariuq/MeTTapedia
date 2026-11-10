import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedTransportEffect
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLSemanticEffectSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLStoreRelations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-! # The transported-equation profile and its actual indexed consumers

The received predicate preserves and reflects transported membership and
the occurrence update. Literal Lean constructors satisfy this profile;
the reverse statement concerns equation membership, not list identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTransportEffectSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLFrameCoding HOLFramesCoding HOLStoreRelations
open HOLOccurrenceCoding (finiteValue)
open MeTTaCalculus.OccurrenceCommits (Commit fire)

universe w uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)
  {O : Type uOcc} [DecidableEq O] (occurrences : HOLOccurrenceCoding.Coding model O)
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem result_predicate_iff {m b : Obj} (settle : Hom m b)
    (information : EquationStore (Tm m)) (next : EquationStore (Tm b)) :
    (∀ x y, (storeValue model code next x y).down ↔
      (model.constDen HOLLoadedMapStore.symbol (actionValue model X code)
        (code.morphisms.symm (HOLFrameEncoding.encodeHom settle)) (storeValue model code information) x y).down) ↔
      ∀ equation, equation ∈ next ↔ equation ∈ X.applyStore settle information := by
  have image := HOLStoreSpecialization.transport_function model X code full equations settle information
  constructor
  · intro agrees
    apply (value_equal_iff model code next (X.applyStore settle information)).mp
    funext x y
    apply ULift.ext
    exact propext ((agrees x y).trans (iff_of_eq (congrArg ULift.down (congrFun (congrFun image x) y))))
  · intro agrees x y
    have same := (value_equal_iff model code next (X.applyStore settle information)).mpr agrees
    exact iff_of_eq (congrArg ULift.down (congrFun (congrFun (same.trans image.symm) x) y))

noncomputable def effectValue {a m b : Obj} (extension : Hom a m) (settle : Hom m b)
    (old : EquationStore (Tm a)) (information : EquationStore (Tm m)) (next : EquationStore (Tm b))
    (present after : Finset O) (commit : Commit O Unit) : HOL.Ty.denote.{0,w+1} model.Carrier .prop :=
  model.constDen HOLLoadedTransportEffect.symbol (termsValue model code) (homValue model code) (actionValue model X code)
    (code.objects.symm (some a)) (code.objects.symm (some m)) (code.objects.symm (some b))
    (code.morphisms.symm (HOLFrameEncoding.encodeHom extension)) (code.morphisms.symm (HOLFrameEncoding.encodeHom settle))
    (storeValue model code old) (storeValue model code information) (storeValue model code next)
    (finiteValue model occurrences present) (finiteValue model occurrences commit.taken)
    (finiteValue model occurrences commit.kept) (finiteValue model occurrences commit.made) (finiteValue model occurrences after)

include full equations in
theorem transport_iff {a m b : Obj} (extension : Hom a m) (settle : Hom m b)
    (old : EquationStore (Tm a)) (information : EquationStore (Tm m)) (next : EquationStore (Tm b))
    (present after : Finset O) (commit : Commit O Unit) :
    (effectValue model X code occurrences extension settle old information next present after commit).down ↔
      (∀ equation ∈ old, (X.act extension equation.1, X.act extension equation.2) ∈ information) ∧
      (∀ equation, equation ∈ next ↔ equation ∈ X.applyStore settle information) ∧ after = fire present commit := by
  have evaluated := HOLLoadedTransportEffect.operational_meaning model full equations
    (termsValue model code) (homValue model code) (actionValue model X code)
    (code.objects.symm (some a)) (code.objects.symm (some m)) (code.objects.symm (some b))
    (code.morphisms.symm (HOLFrameEncoding.encodeHom extension)) (code.morphisms.symm (HOLFrameEncoding.encodeHom settle))
    (storeValue model code old) (storeValue model code information) (storeValue model code next)
    (finiteValue model occurrences present) (finiteValue model occurrences commit.taken)
    (finiteValue model occurrences commit.kept) (finiteValue model occurrences commit.made) (finiteValue model occurrences after)
  refine (iff_of_eq (congrArg ULift.down evaluated)).trans ?_
  unfold HOLTransportEffectBody.Contract
  rw [transported_inclusion_iff model X code extension old information,
    result_predicate_iff model X code full equations settle information next,
    HOLSemanticEffectSpecialization.occurrences_iff model occurrences full equations present after commit]
  have validExtension : (homValue model code (code.objects.symm (some a)) (code.objects.symm (some m))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom extension))).down := by
    simpa only [homValue, Equiv.apply_symm_apply] using HOLFrameEncoding.hom_encoded extension
  have validSettle : (homValue model code (code.objects.symm (some m)) (code.objects.symm (some b))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom settle))).down := by
    simpa only [homValue, Equiv.apply_symm_apply] using HOLFrameEncoding.hom_encoded settle
  simp only [HOLStoreSpecialization.finite_store_typed model code full equations,
    validExtension, validSettle, true_and]

include full equations in
theorem implies_semantic {a m b : Obj} (extension : Hom a m) (settle : Hom m b)
    (old : EquationStore (Tm a)) (information : EquationStore (Tm m)) (next : EquationStore (Tm b))
    (present after : Finset O) (commit : Commit O Unit)
    (transported : (effectValue model X code occurrences extension settle old information next present after commit).down) :
    (HOLSemanticEffectSpecialization.effectValue model X code occurrences extension settle old information next present after commit).down := by
  obtain ⟨contains, same, update⟩ := (transport_iff model X code occurrences full equations extension settle old information next present after commit).mp transported
  apply (HOLSemanticEffectSpecialization.semantic_iff model X code occurrences full equations extension settle old information next present after commit).mpr
  refine ⟨fun _ sigma solved => Frames.models_of_transport X old information extension contains sigma solved, ?_, update⟩
  intro c sigma solved
  apply (Frames.models_applyStore (X := X) settle sigma information).mp
  exact fun equation member => solved equation ((same equation).mpr member)

include full equations in
theorem implies_exact {a m b : Obj} (extension : Hom a m) (settle : Hom m b)
    (old : EquationStore (Tm a)) (information : EquationStore (Tm m)) (next : EquationStore (Tm b))
    (present after : Finset O) (commit : Commit O Unit)
    (transported : (effectValue model X code occurrences extension settle old information next present after commit).down) :
    (model.constDen HOLLoadedExact.symbol (homValue model code) (equalValue model X code)
      (actionValue model X code) (compositionValue model X code)
      (code.objects.symm (some m)) (code.objects.symm (some b))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom settle)) (storeValue model code information) (storeValue model code next)).down := by
  have same := ((transport_iff model X code occurrences full equations extension settle old information next present after commit).mp transported).2.1
  apply (HOLExactSpecialization.exact_iff model X code full equations settle information next).mpr
  intro c sigma solved
  have image := (Frames.models_applyStore (X := X) settle sigma information).mpr solved
  exact fun equation member => image equation ((same equation).mp member)

include full equations in
theorem literal_preparation {State : Type uS} {Firing : State → Type uF}
    (P : Step X O State Firing) [P.LiteralInformation] [P.LiteralKnowledge]
    {s : State} (f : Firing s) (p : P.Prepares f) :
    (effectValue model X code occurrences (P.extension f) (P.preparedSettle f p)
      (P.knowledge s) (P.information f) (P.knowledge (P.preparedResult f p))
      (P.present s) (P.present (P.preparedResult f p)) ((P.selection f).commit (T := Unit))).down := by
  apply (transport_iff model X code occurrences full equations (P.extension f) (P.preparedSettle f p)
    (P.knowledge s) (P.information f) (P.knowledge (P.preparedResult f p))
    (P.present s) (P.present (P.preparedResult f p)) ((P.selection f).commit (T := Unit))).mpr
  exact ⟨P.transported f, fun equation => by rw [P.knowledge_preparedResult f p], P.present_preparedResult f p⟩

#print axioms transport_iff
#print axioms implies_semantic
#print axioms implies_exact
#print axioms literal_preparation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTransportEffectSpecialization
