import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalConstructorInterpretation
import Mettapedia.TypeTheory.ContextualTelescopeUniverseLift
import Mettapedia.TypeTheory.ContextualSumUniverseLift

/-!
# Primitive model data on lifted contextual carriers

Finite declaration telescopes, their dependent families and their exact
supplied sections are lifted along with the actual local product and sum
operations. The change of carrier sizes assumes no internal universe type.
Declaration realization and generated interpretation are proved separately.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

universe u c s t m uc vs wt ms
variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}}

namespace ModelData

/-- Each declaration retains its own supplied parameter telescope. -/
def universeLift (model : ModelData S C) :
    ModelData S (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C) where
  products := liftProducts model.products
  sums := liftStableSums model.sums
  typeParameters symbol := liftContext (model.typeParameters symbol)
  typeFamily symbol := ULift.up (model.typeFamily symbol)
  termParameters symbol := liftContext (model.termParameters symbol)
  termType symbol := ULift.up (model.termType symbol)
  termValue symbol := ULift.up (model.termValue symbol)

@[simp] theorem universeLift_familyAt (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (symbol : S.TypeSymbol) (σ : C.toCwf.Sub Γ (model.typeParameters symbol).1) :
    model.universeLift.familyAt symbol (ULift.up σ) =
      (ULift.up (model.familyAt symbol σ) : ULift.{wt} _) := rfl

@[simp] theorem universeLift_primitiveAt (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (symbol : S.TermSymbol) (σ : C.toCwf.Sub Γ (model.termParameters symbol).1) :
    (model.universeLift.{u, c, s, t, m, uc, vs, wt, ms} : ModelData S
      (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)).primitiveAt symbol (ULift.up σ) =
      liftValue (model.primitiveAt symbol σ) := rfl

theorem universeLift_application_value (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (f : C.toCwf.Tm Γ (model.products.pi A B)) (a : C.toCwf.Tm Γ A) :
    (⟨(Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up B) (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up a)),
      (model.universeLift.{u, c, s, t, m, uc, vs, wt, ms} : ModelData S
        (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)).products.app (ULift.up f) (ULift.up a)⟩ :
      Value (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up Γ)) =
      liftValue (⟨C.toCwf.tySub B (selfExtend C.toCwf a), model.products.app f a⟩ :
        Value C.toCwf Γ) := by
  apply liftedValue_eq
  · exact congrArg (C.toCwf.tySub B) (selfExtend_readout (ULift.up a))
  · exact products_app_readout model.products (ULift.up f) (ULift.up a)

theorem universeLift_second_value (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (p : C.toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    (⟨(Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up B)
        (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf)
          ((model.universeLift.{u, c, s, t, m, uc, vs, wt, ms} : ModelData S
            (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)).sums.operations.fst (ULift.up p))),
      model.universeLift.sums.operations.snd (ULift.up p)⟩ :
      Value (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up Γ)) =
      liftValue (⟨C.toCwf.tySub B (selfExtend C.toCwf (model.sums.operations.fst p)),
        model.sums.operations.snd p⟩ : Value C.toCwf Γ) := by
  apply liftedValue_eq
  · exact congrArg (C.toCwf.tySub B) (selfExtend_readout (ULift.up (model.sums.operations.fst p)))
  · exact sums_snd_readout model.sums.operations (ULift.up p)

theorem universeLift_pair_value (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A)) (a : C.toCwf.Tm Γ A)
    (b : C.toCwf.Tm Γ (C.toCwf.tySub B (selfExtend C.toCwf a)))
    (b' : (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).Tm (ULift.up Γ)
      ((Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up B) (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up a))))
    (bodies : HEq b'.down b) :
    (⟨ULift.up (model.sums.operations.sigma A B),
      (model.universeLift.{u, c, s, t, m, uc, vs, wt, ms} : ModelData S
        (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)).sums.operations.pair (ULift.up a) b'⟩ :
      Value (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up Γ)) =
      liftValue (⟨model.sums.operations.sigma A B, model.sums.operations.pair a b⟩ :
        Value C.toCwf Γ) := by
  apply liftedValue_eq
  · rfl
  · have second : cast (congrArg (C.toCwf.Tm Γ)
        (congrArg (C.toCwf.tySub B) (selfExtend_readout (ULift.up a)))) b'.down = b :=
      eq_of_heq ((cast_heq _ _).trans bodies)
    change HEq (model.sums.operations.pair a _) (model.sums.operations.pair a b)
    exact heq_of_eq (congrArg (model.sums.operations.pair a) second)

theorem universeLift_elimination_value (model : ModelData S C) {Γ : C.toCwf.Ctx}
    (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (M : C.toCwf.Ty (sumContext model.sums A B))
    (body : C.toCwf.Tm (tupleContext A B) (C.toCwf.tySub M (pack model.sums A B)))
    (body' : (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).Tm
      (tupleContext (ULift.up A) (ULift.up B))
      ((Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up M) (pack (liftStableSums model.sums) (ULift.up A) (ULift.up B))))
    (bodies : HEq body'.down body) (p : C.toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    (⟨(Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up M) (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up p)),
      (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tmSub
        (eliminate (liftStableSums model.sums) (ULift.up A) (ULift.up B) (ULift.up M) body')
        (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up p))⟩ :
      Value (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up Γ)) =
      liftValue (⟨C.toCwf.tySub M (selfExtend C.toCwf p),
        C.toCwf.tmSub (eliminate model.sums A B M body) (selfExtend C.toCwf p)⟩ :
          Value C.toCwf Γ) := by
  apply liftedValue_eq
  · exact congrArg (C.toCwf.tySub M) (selfExtend_readout (ULift.up p))
  · have transported : cast (congrArg (C.toCwf.Tm (tupleContext A B))
        (congrArg (C.toCwf.tySub M) (pack_down model.sums (ULift.up A) (ULift.up B))))
        body'.down = body := eq_of_heq ((cast_heq _ _).trans bodies)
    have resultSection := elimination_down model.sums (ULift.up A) (ULift.up B) (ULift.up M) body'
    have completeSection := resultSection.trans
      (congrArg (eliminate model.sums A B M) transported)
    change HEq (C.toCwf.tmSub
      (eliminate (liftStableSums model.sums) (ULift.up A) (ULift.up B) (ULift.up M) body').down
      (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up p)).down) _
    exact (heq_of_eq (congrArg
      (fun sectionValue => C.toCwf.tmSub sectionValue
        (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up p)).down) completeSection)).trans
          (term_action_eq _ (selfExtend_readout (ULift.up p)))

end ModelData
end Mettapedia.TypeTheory.Calculi.NativeDependent.External
