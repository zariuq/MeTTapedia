import Mettapedia.Languages.HOLLight.ExactFormulaReadback
import Mettapedia.Languages.HOLLight.ReferenceBooleanSemantics

/-!
# Product carriers read from the source projection laws

The native state uses nested source products. Three exact received equations
identify each product carrier with the pair of its component carriers. This
does not assume that the source type operator was represented by Lean pairs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceProducts

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open ReferenceBooleanSemantics ProofExecution TypeFamilySemantics

universe w

structure Signature where
  first : HOL.Ty AtomicTy
  second : HOL.Ty AtomicTy
  pair : HOL.Ty AtomicTy
  constructor : HOL.ClosedTerm Symbol (first.arr (second.arr pair))
  left : HOL.ClosedTerm Symbol (pair.arr first)
  right : HOL.ClosedTerm Symbol (pair.arr second)

namespace Signature

variable (signature : Signature)

def firstLaw : HOL.ClosedFormula Symbol :=
  universal (type := signature.first) (universal (type := signature.second)
    (.eq (.app (HOL.weakenCtx _ signature.left)
      (.app (.app (HOL.weakenCtx _ signature.constructor) (.var (.vs .vz))) (.var .vz)))
      (.var (.vs .vz))))

def secondLaw : HOL.ClosedFormula Symbol :=
  universal (type := signature.first) (universal (type := signature.second)
    (.eq (.app (HOL.weakenCtx _ signature.right)
      (.app (.app (HOL.weakenCtx _ signature.constructor) (.var (.vs .vz))) (.var .vz)))
      (.var .vz)))

def pairLaw : HOL.ClosedFormula Symbol :=
  universal (type := signature.pair)
    (.eq (.app (.app (HOL.weakenCtx _ signature.constructor)
      (.app (HOL.weakenCtx _ signature.left) (.var .vz)))
      (.app (HOL.weakenCtx _ signature.right) (.var .vz))) (.var .vz))

abbrev First (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.first

abbrev Second (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.second

abbrev Pair (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  HOL.Ty.denote.{0,w+1} model.Carrier signature.pair

def empty (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) : model.Valuation [] :=
  fun index => nomatch index

theorem empty_unique (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (valuation : model.Valuation []) : @valuation = @empty model := by
  funext type index
  exact nomatch index

def construct (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  model.denote signature.constructor (empty model)

def projectFirst (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  model.denote signature.left (empty model)

def projectSecond (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  model.denote signature.right (empty model)

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (full : model.FullDomains) (meanings : Meanings model)

include full meanings

theorem firstLaw_meaning : model.models signature.firstLaw ↔
    ∀ first second, signature.projectFirst model (signature.construct model first second) = first := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [firstLaw, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    admitted, forall_true_left, model.eqv_iff_eq_of_fullDomains full,
    empty_unique model, projectFirst, construct]

theorem secondLaw_meaning : model.models signature.secondLaw ↔
    ∀ first second, signature.projectSecond model (signature.construct model first second) = second := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [secondLaw, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    admitted, forall_true_left, model.eqv_iff_eq_of_fullDomains full,
    empty_unique model, projectSecond, construct]

theorem pairLaw_meaning : model.models signature.pairLaw ↔
    ∀ pair, signature.construct model (signature.projectFirst model pair)
      (signature.projectSecond model pair) = pair := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [pairLaw, HOL.HenkinModel.models, HOL.PreModel.models,
    denote_universal model meanings, HOL.HenkinModel.denote_weakenCtx,
    HOL.HenkinModel.denote, HOL.PreModel.denote, HOL.PreModel.extend,
    admitted, forall_true_left, model.eqv_iff_eq_of_fullDomains full,
    empty_unique model, projectFirst, projectSecond, construct]

/-- Both inverse laws are earned from the three source projection equations. -/
def equivalence (first : model.models signature.firstLaw) (second : model.models signature.secondLaw)
    (pairs : model.models signature.pairLaw) :
    signature.Pair model ≃ signature.First model × signature.Second model where
  toFun pair := (signature.projectFirst model pair, signature.projectSecond model pair)
  invFun pair := signature.construct model pair.1 pair.2
  left_inv := (signature.pairLaw_meaning model full meanings).mp pairs
  right_inv pair := Prod.ext
    ((signature.firstLaw_meaning model full meanings).mp first pair.1 pair.2)
    ((signature.secondLaw_meaning model full meanings).mp second pair.1 pair.2)

end Signature

structure Readings (signature : Signature) (state : Registered.State) where
  first : ExactFormulaReadback.ReadFact state signature.firstLaw
  second : ExactFormulaReadback.ReadFact state signature.secondLaw
  pair : ExactFormulaReadback.ReadFact state signature.pairLaw

noncomputable def receivedEquivalence (signature : Signature)
    (commands : List Registered.Command) (state : Registered.State)
    (accepted : Registered.replayFrom SourceProfileModels.policy
      (Registered.empty SourceProfile.primitiveContext) commands = some state)
    (readings : Readings signature state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    let model := (SourceProfileModels.sourceReplayFrame commands state accepted).frame.model other assignment
    signature.Pair model ≃ signature.First model × signature.Second model := by
  let frame := (SourceProfileModels.sourceReplayFrame commands state accepted).frame
  exact signature.equivalence (frame.model other assignment) (frame.model_fullDomains other assignment)
    (replay_meanings commands state accepted other assignment)
    (ExactFormulaReadback.read_models frame other assignment _ readings.first)
    (ExactFormulaReadback.read_models frame other assignment _ readings.second)
    (ExactFormulaReadback.read_models frame other assignment _ readings.pair)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceProducts
