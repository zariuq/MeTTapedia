import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigid

/-!
# Decomposing dependent pairs: the second component is heterogeneous

Two pairs are equal at a dependent pair type exactly when their first components are equal and
their second components are equal at the type the family takes at the left first component
(`equal_pair_iff`). The right second component has the family's type at the right first
component. So, read as equations of the store, the decomposition yields a homogeneous first
equation and a **heterogeneous** second equation whose type equation is entailed by the first
(`second_types_of_first`): it is postponed until the first is solved, as in Abel and Pientka's
treatment of dependent pairs and Gundry and McBride's twins. Rigid pair constructors are not
compared with neutral pairs here: pair eta equates them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigid

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization

variable {Head : Type} {R : Rules Head}

/-- **The type equation of the second components follows from the first components.** -/
theorem second_types_of_first {n : Nat} {Γ : Ctx Head n} {A a a' : Tm Head n}
    {B : Tm Head (n + 1)} {v : Head} (family : Typed R (.snoc Γ A) B (.head v))
    (hv : R.isUniverse v) (typedA : Typed R Γ a A) (firsts : Equal R Γ a a' A) :
    TypeEq R Γ (inst0 a B) (inst0 a' B) :=
  ⟨v, hv, Typed.instantiateEq family typedA firsts⟩

/-- **Dependent pairs decompose**: equal first components, and equal second components at the
family's type at the left first component. -/
theorem equal_pair_iff {n : Nat} {Γ : Ctx Head n} {A a a' b b' : Tm Head n}
    {B : Tm Head (n + 1)} {u v : Head}
    (pairType : Typed R Γ (.sigma A B) (.head u)) (hu : R.isUniverse u)
    (family : Typed R (.snoc Γ A) B (.head v)) (hv : R.isUniverse v)
    (typedA : Typed R Γ a A) (typedB : Typed R Γ b (inst0 a B))
    (typedA' : Typed R Γ a' A) (typedB' : Typed R Γ b' (inst0 a' B)) :
    Equal R Γ (.pair a b) (.pair a' b') (.sigma A B) ↔
      Equal R Γ a a' A ∧ Equal R Γ b b' (inst0 a B) := by
  constructor
  · intro same
    have leftFirst : Equal R Γ (.fst (.pair a b)) a A := .betaFst pairType hu typedA typedB
    have rightFirst : Equal R Γ (.fst (.pair a' b')) a' A := .betaFst pairType hu typedA' typedB'
    have firsts : Equal R Γ a a' A :=
      .trans (.symm leftFirst) (.trans (.fstCong same) rightFirst)
    have leftTyped : Typed R Γ (.pair a b) (.sigma A B) := .pairIntro pairType hu typedA typedB
    have projected : Equal R Γ (inst0 (.fst (.pair a b)) B) (inst0 a B) (.head v) :=
      Typed.instantiateEq family (.fstElim leftTyped) leftFirst
    have seconds : Equal R Γ (.snd (.pair a b)) (.snd (.pair a' b')) (inst0 a B) :=
      .convEq (.sndCong same) projected hv
    have rightTypes : Equal R Γ (inst0 a' B) (inst0 a B) (.head v) :=
      Typed.instantiateEq family typedA' (.symm firsts)
    have leftSecond : Equal R Γ (.snd (.pair a b)) b (inst0 a B) :=
      .betaSnd pairType hu typedA typedB
    have rightSecond : Equal R Γ (.snd (.pair a' b')) b' (inst0 a B) :=
      .convEq (.betaSnd pairType hu typedA' typedB') rightTypes hv
    exact ⟨firsts, .trans (.symm leftSecond) (.trans seconds rightSecond)⟩
  · rintro ⟨firsts, seconds⟩
    exact .pairCong pairType hu firsts seconds

end ContextualDependentRigid
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
