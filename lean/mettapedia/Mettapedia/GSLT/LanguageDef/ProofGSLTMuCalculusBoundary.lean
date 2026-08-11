import Mettapedia.Logic.ModalMuCalculus

/-!
# The positivity boundary for fixed-point checking

Parity-game and cyclic-proof accounts of the modal mu-calculus require every
bound fixed-point variable to occur positively in its body.  The general
formula datatype also represents expressions outside that fragment, so the
condition must be checked explicitly before a parity authority is applied.

The one-state fixture below is a negative canary.  The body `not X` has no
fixed point, although the unrestricted pre-fixed and post-fixed clauses still
assign different meanings to `mu X. not X` and `nu X. not X`.  Therefore an
eventual parity checker must consume the positivity evidence; it cannot be an
authority for arbitrary values of `Formula`.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT.MuCalculusBoundary

open Mettapedia.Logic.ModalMuCalculus

universe uAction

/-- Every fixed-point binder in a formula has a body positive in the variable
introduced by that binder. -/
def fixedPointsPositive {Action : Type uAction} :
    {n : Nat} -> Formula Action n -> Bool
  | _, .tt | _, .ff | _, .var _ => true
  | _, .neg formula => fixedPointsPositive formula
  | _, .conj left right | _, .disj left right =>
      fixedPointsPositive left && fixedPointsPositive right
  | _, .diamond _ formula | _, .box _ formula =>
      fixedPointsPositive formula
  | _, .mu body | _, .nu body =>
      body.isPositive && fixedPointsPositive body

/-! ## Positive and negative syntax witnesses -/

def negativeBody : Formula Unit 1 :=
  .neg (.var 0)

theorem negativeBody_is_not_positive :
    negativeBody.isPositive = false := by
  rfl

theorem negativeMu_is_rejected :
    fixedPointsPositive (Formula.mu negativeBody) = false := by
  rfl

theorem eventuallyTop_is_positive :
    fixedPointsPositive
      (Formula.eventually () (Formula.tt : Formula Unit 0)) =
      true := by
  rfl

theorem alwaysTop_is_positive :
    fixedPointsPositive (Formula.always () (Formula.tt : Formula Unit 0)) =
      true := by
  rfl

/-! ## The nonmonotone one-state counterexample -/

def singletonLTS : LTS Unit Unit where
  trans := fun _ _ _ => False

def negativeOperator (states : Set Unit) : Set Unit :=
  { state |
    satisfies singletonLTS (Env.empty.extend states) negativeBody state }

theorem negativeOperator_membership (states : Set Unit) :
    () ∈ negativeOperator states <-> () ∉ states := by
  simp [negativeOperator, negativeBody, satisfies, Env.extend]

/-- The negative body has no fixed point, so it is outside the standard
modal-mu-calculus fixed-point semantics used by parity games. -/
theorem negativeOperator_has_no_fixedPoint :
    ¬ exists states : Set Unit, negativeOperator states = states := by
  rintro ⟨states, fixed⟩
  have membership := Set.ext_iff.mp fixed ()
  rw [negativeOperator_membership] at membership
  by_cases member : () ∈ states <;> simp [member] at membership

/-- The unrestricted least-pre-fixed-point clause nevertheless assigns the
negative formula a truth value.  This is not a fixed-point witness. -/
theorem negativeMu_satisfies :
    satisfies singletonLTS Env.empty (Formula.mu negativeBody) () := by
  intro states preFixed
  by_contra missing
  apply missing
  apply preFixed ()
  simp [negativeBody, satisfies, Env.extend, missing]

/-- The unrestricted greatest-post-fixed-point clause assigns the dual value,
again without producing a fixed point. -/
theorem negativeNu_does_not_satisfy :
    ¬ satisfies singletonLTS Env.empty (Formula.nu negativeBody) () := by
  rintro ⟨states, member, postFixed⟩
  have body := postFixed () member
  simp [negativeBody, satisfies, Env.extend, member] at body

/-- The syntactic positivity gate separates accepted temporal examples from
the concrete no-fixed-point counterexample. -/
theorem positivity_gate_is_nontrivial :
    fixedPointsPositive
        (Formula.eventually () (Formula.tt : Formula Unit 0)) =
        true /\
      fixedPointsPositive (Formula.mu negativeBody) = false /\
      ¬ exists states : Set Unit, negativeOperator states = states :=
  ⟨eventuallyTop_is_positive, negativeMu_is_rejected,
    negativeOperator_has_no_fixedPoint⟩

end Mettapedia.GSLT.LanguageDef.ProofGSLT.MuCalculusBoundary
