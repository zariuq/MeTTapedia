import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLParallelBodies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLModelsSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Coexistence

/-!
# Loaded HOL coexistence agrees with the indexed shared calculus

The equation-list representation maps to the existing HOL membership
predicate. Occurrence identities map to the inhabited raw domain, whose
invalid sentinel remains absent. Both loaded parallel operations agree
with actual native configuration coexistence over arbitrary frames.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelAgreement

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLParallelBodies

universe w uO uT uH uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O]

theorem store_append {a : Obj} (left right : EquationStore (Tm a)) :
    HOLFrameEncoding.store (left ++ right) = fun x y =>
      HOLFrameEncoding.store left x y ∨ HOLFrameEncoding.store right x y := by
  funext x y
  apply propext
  simp only [HOLFrameEncoding.store, List.mem_append, or_and_right, exists_or]

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLParallelDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)
  (code : HOLFrameCoding.Coding model Obj Tm Hom)

include full equations in
theorem store_tensor {a : Obj} (left right : Configuration (Tm a) O) :
    model.constDen Store.symbol (HOLFrameCoding.storeValue model code left.equations)
      (HOLFrameCoding.storeValue model code right.equations) =
        HOLFrameCoding.storeValue model code (Coexistence.tensor left right).equations := by
  funext x y
  rw [store_meaning model full equations]
  change ULift.up (HOLFrameEncoding.store left.equations (code.terms x) (code.terms y) ∨
    HOLFrameEncoding.store right.equations (code.terms x) (code.terms y)) =
      ULift.up (HOLFrameEncoding.store (left.equations ++ right.equations) (code.terms x) (code.terms y))
  rw [store_append]

include full equations in
theorem present_tensor (occurrences : HOLOccurrenceCoding.Coding model O)
    {a : Obj} (left right : Configuration (Tm a) O) :
    model.constDen Present.symbol (HOLOccurrenceCoding.finiteValue model occurrences left.present)
      (HOLOccurrenceCoding.finiteValue model occurrences right.present) =
        HOLOccurrenceCoding.finiteValue model occurrences (Coexistence.tensor left right).present := by
  funext occurrence
  rw [present_meaning model full equations]
  apply ULift.ext
  apply propext
  cases same : occurrences occurrence <;>
    simp [HOLOccurrenceCoding.finiteValue, HOLOccurrenceCoding.predicateValue,
      HOLOccurrenceCoding.finitePredicate, same, Coexistence.tensor]

include full equations in
theorem models_tensor (X : Frames Tm Hom) {a b : Obj} (map : Hom a b)
    (left right : Configuration (Tm a) O) :
    (model.constDen HOLLoadedModels.symbol (HOLFrameCoding.homValue model code)
      (HOLFrameCoding.equalValue model X code) (HOLFrameCoding.actionValue model X code)
      (code.objects.symm (some a)) (code.objects.symm (some b))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom map))
      (model.constDen Store.symbol (HOLFrameCoding.storeValue model code left.equations)
        (HOLFrameCoding.storeValue model code right.equations))).down ↔
          X.Models map left.equations ∧ X.Models map right.equations := by
  rw [store_tensor model full equations code]
  exact (HOLModelsSpecialization.models_iff model X code full
    (original_equations model equations) map _).trans (Coexistence.models_tensor X map left right)

omit [DecidableEq O] in
theorem invalid_occurrence_absent (occurrences : HOLOccurrenceCoding.Coding model O) (state : Finset O) :
    ¬(HOLOccurrenceCoding.finiteValue model occurrences state (occurrences.symm none)).down :=
  HOLOccurrenceCoding.invalid_absent model occurrences state

theorem constructed_agreement
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc}) :
    ∃ (actual : HOL.HenkinModel.{0,0,(max uO uT uH uOcc)+1} AtomicTy Symbol)
      (encoding : HOLFrameCoding.Coding actual Obj Tm Hom)
      (occurrences : HOLOccurrenceCoding.Coding actual O),
      actual.Carrier = (HOLFrameDomains.initial Obj Tm Hom O other prior).Carrier ∧ actual.FullDomains ∧
      (∀ (a : Obj) (left right : Configuration (Tm a) O),
        actual.constDen Store.symbol (HOLFrameCoding.storeValue actual encoding left.equations)
          (HOLFrameCoding.storeValue actual encoding right.equations) =
            HOLFrameCoding.storeValue actual encoding (Coexistence.tensor left right).equations) ∧
      (∀ (a : Obj) (left right : Configuration (Tm a) O),
        actual.constDen Present.symbol (HOLOccurrenceCoding.finiteValue actual occurrences left.present)
          (HOLOccurrenceCoding.finiteValue actual occurrences right.present) =
            HOLOccurrenceCoding.finiteValue actual occurrences (Coexistence.tensor left right).present) := by
  obtain ⟨actual, same, preserves, equations⟩ :=
    HOLParallelDefinitions.defining_equations_have_constructed_model (HOLFrameDomains.initial Obj Tm Hom O other prior)
  have actualFull := preserves (ModelInterpretation.model_fullDomains _ _ _)
  let encoding := (HOLFrameCoding.initialCoding (Obj := Obj) (Tm := Tm) (Hom := Hom) O other prior).changeModel actual same
  let occurrences := HOLOccurrenceCoding.changeModel (HOLOccurrenceCoding.initialCoding Obj Tm Hom O other prior) actual same
  exact ⟨actual, encoding, occurrences, same, actualFull,
    fun _ left right => store_tensor actual actualFull equations encoding left right,
    fun _ left right => present_tensor actual actualFull equations occurrences left right⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelAgreement
