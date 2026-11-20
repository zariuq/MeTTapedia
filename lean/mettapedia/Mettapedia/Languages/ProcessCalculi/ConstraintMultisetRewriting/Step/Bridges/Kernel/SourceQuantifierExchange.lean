import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeReceivedFrame
import Mettapedia.Logic.HOL.Soundness

/-!
# Source equality certificates for universal-binder exchange

Two source definitions can differ by the order of independent universal
binders. This is stronger than renaming bound variables. The certificate
below uses the actual source Boolean symbols and is interpreted in the one
supplied source frame. Its congruence rules permit an exchange inside a
predicate passed to a function, including a choice operator.

These are equality certificates, not directed evaluation steps. They do not
identify separate source signatures or supply a declaration-history transport.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceQuantifierExchange

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ReferenceBooleanSemantics TypeFamilySemantics

universe w

/-- Exchange the two nearest typed variables, retaining every older variable. -/
def exchange {context : HOL.Ctx AtomicTy} {first second : HOL.Ty AtomicTy} :
    HOL.Rename AtomicTy (second :: first :: context) (first :: second :: context)
  | _, .vz => .vs .vz
  | _, .vs .vz => .vz
  | _, .vs (.vs index) => .vs (.vs index)

theorem exchange_valuation (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    {context : HOL.Ctx AtomicTy} {first second : HOL.Ty AtomicTy}
    (valuation : model.Valuation context)
    (left : HOL.Ty.denote model.Carrier first) (right : HOL.Ty.denote model.Carrier second) :
    (HOL.Soundness.renameVal model exchange (model.extend (model.extend valuation right) left) :
      model.Valuation (second :: first :: context)) =
      (model.extend (model.extend valuation left) right : model.Valuation (second :: first :: context)) := by
  funext type index
  cases index with
  | vz => rfl
  | vs index => cases index <;> rfl

theorem denote_exchange (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    {context : HOL.Ctx AtomicTy} {first second type : HOL.Ty AtomicTy}
    (body : HOL.Term Symbol (second :: first :: context) type)
    (valuation : model.Valuation context)
    (left : HOL.Ty.denote model.Carrier first) (right : HOL.Ty.denote model.Carrier second) :
    model.denote (HOL.rename exchange body) (model.extend (model.extend valuation right) left) =
      model.denote body (model.extend (model.extend valuation left) right) := by
  rw [HOL.Soundness.denote_rename, exchange_valuation]

/-- The source quantifiers range over their actual admissible domains. No
full-domain or decidability hypothesis is added for this exchange. -/
theorem universal_exchange (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (meanings : Meanings model) {context : HOL.Ctx AtomicTy} {first second : HOL.Ty AtomicTy}
    (body : HOL.Formula Symbol (second :: first :: context)) (valuation : model.Valuation context) :
    model.denote (universal (universal body)) valuation =
      model.denote (universal (universal (HOL.rename exchange body))) valuation := by
  apply ULift.ext
  apply propext
  simp only [denote_universal model meanings, ULift.down_up]
  constructor
  · intro holds right rightAdmissible left leftAdmissible
    rw [denote_exchange]
    exact holds left leftAdmissible right rightAdmissible
  · intro holds left leftAdmissible right rightAdmissible
    have result := holds right rightAdmissible left leftAdmissible
    rwa [denote_exchange] at result

/-- A finite equality derivation in the source applicative/lambda fragment.
The only noncongruence generator is universal-binder exchange. There is no
generator for arbitrary function-argument permutation or evaluation. -/
inductive Certificate : {context : HOL.Ctx AtomicTy} → {type : HOL.Ty AtomicTy} →
    HOL.Term Symbol context type → HOL.Term Symbol context type → Type where
  | refl {context type} (term : HOL.Term Symbol context type) : Certificate term term
  | symm {context type} {first second : HOL.Term Symbol context type} :
      Certificate first second → Certificate second first
  | trans {context type} {first second third : HOL.Term Symbol context type} :
      Certificate first second → Certificate second third → Certificate first third
  | universalExchange {context first second}
      (body : HOL.Formula Symbol (second :: first :: context)) :
      Certificate (universal (universal body))
        (universal (universal (HOL.rename exchange body)))
  | app {context domain codomain} {first second : HOL.Term Symbol context (.arr domain codomain)}
      {argument other : HOL.Term Symbol context domain} :
      Certificate first second → Certificate argument other →
        Certificate (.app first argument) (.app second other)
  | lam {context domain codomain} {first second : HOL.Term Symbol (domain :: context) codomain} :
      Certificate first second → Certificate (.lam first) (.lam second)
  | eq {context type} {first second other another : HOL.Term Symbol context type} :
      Certificate first second → Certificate other another →
        Certificate (.eq first other) (.eq second another)

theorem Certificate.denotes {context : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    {first second : HOL.Term Symbol context type} (certificate : Certificate first second)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (meanings : Meanings model)
    (valuation : model.Valuation context) : model.denote first valuation = model.denote second valuation := by
  induction certificate with
  | refl => rfl
  | symm _ ih => exact (ih valuation).symm
  | trans _ _ firstIH secondIH => exact (firstIH valuation).trans (secondIH valuation)
  | universalExchange body => exact universal_exchange model meanings body valuation
  | @app context domain codomain function other argument another _ _ functionIH argumentIH =>
      change (model.denote function valuation) (model.denote argument valuation) =
        (model.denote other valuation) (model.denote another valuation)
      rw [functionIH valuation, argumentIH valuation]
  | lam _ ih =>
      funext value
      exact ih (model.extend valuation value)
  | eq _ _ firstIH secondIH =>
      change ULift.up (model.Eqv _ (model.denote _ valuation) (model.denote _ valuation)) = _
      rw [firstIH valuation, secondIH valuation]
      rfl

/-- Source readback and the conversion use exactly the supplied carried frame. -/
theorem Certificate.in_received_frame {state : ProofExecution.Registered.State}
    (profile : SourceProfileModels.ProfileFrame.{w} state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {context : HOL.Ctx AtomicTy} {type : HOL.Ty AtomicTy}
    {first second : HOL.Term Symbol context type} (certificate : Certificate first second)
    (valuation : (profile.frame.model other assignment).Valuation context) :
    (profile.frame.model other assignment).denote first valuation =
      (profile.frame.model other assignment).denote second valuation :=
  certificate.denotes _ (NativeReceivedFrame.meanings profile other assignment) valuation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceQuantifierExchange
