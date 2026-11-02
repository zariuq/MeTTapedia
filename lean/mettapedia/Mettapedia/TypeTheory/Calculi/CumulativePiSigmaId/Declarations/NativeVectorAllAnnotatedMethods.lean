import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllAnnotatedFormation

/-!
# The original dependent-pair cons program at its complete interface

The recursively supplied object is a type, not a witness. The branch forms
the Sigma of a head predicate witness and that recursive type. Typed beta
equalities compare its explicit universe annotation with the native recursor's
universe-valued motive applications.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated.Formation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies

variable (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    {n : Nat} {ambient : CCtx Tower.Head n}

theorem natural_atBound : CTyped (Profile.church element result enabled) ambient (.const natName)
    (Profile.motiveSort element result) := by
  refine .cumul (Profile.natural_typed element result enabled) ?_
  change ∀ valuation : Nat → Nat, 0 ≤ (Profile.recursorLevel element result).eval valuation
  exact fun _ => Nat.zero_le _

theorem element_atBound {A : CTm Tower.Head n}
    (typed : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element)) :
    CTyped (Profile.church element result enabled) ambient A (Profile.motiveSort element result) := by
  refine .cumul typed ?_
  change ∀ valuation : Nat → Nat, element.eval valuation ≤ max (element.eval valuation) (result.eval valuation + 1)
  exact fun _ => Nat.le_max_left _ _

theorem product_atBound {A : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)}
    (domain : CTyped (Profile.church element result enabled) ambient A (Profile.motiveSort element result))
    (codomain : CTyped (Profile.church element result enabled) (.snoc ambient A) B (Profile.motiveSort element result)) :
    CTyped (Profile.church element result enabled) ambient (.pi A B) (Profile.motiveSort element result) := by
  refine .cumul (.piForm domain (.sort _) codomain (.sort _) (.sorts _ _)) ?_
  change ∀ valuation : Nat → Nat,
    max ((Profile.recursorLevel element result).eval valuation) ((Profile.recursorLevel element result).eval valuation) ≤
      (Profile.recursorLevel element result).eval valuation
  exact fun _ => max_le_iff.mpr ⟨le_rfl, le_rfl⟩

theorem productEqual_atBound {A A' : CTm Tower.Head n} {B B' : CTm Tower.Head (n + 1)}
    (domain : CEqual (Profile.church element result enabled) ambient A A' (Profile.motiveSort element result))
    (codomain : CEqual (Profile.church element result enabled) (.snoc ambient A) B B' (Profile.motiveSort element result)) :
    CEqual (Profile.church element result enabled) ambient (.pi A B) (.pi A' B') (Profile.motiveSort element result) := by
  refine .cumulEq (.piCong domain (.sort _) codomain (.sort _) (.sorts _ _)) ?_
  change ∀ valuation : Nat → Nat,
    max ((Profile.recursorLevel element result).eval valuation) ((Profile.recursorLevel element result).eval valuation) ≤
      (Profile.recursorLevel element result).eval valuation
  exact fun _ => max_le_iff.mpr ⟨le_rfl, le_rfl⟩

def evidenceArrow (result : LevelExpr Nat) {n : Nat} : CTm Tower.Head n :=
  .pi (resultSort result) (resultSort result)

def afterHead (result : LevelExpr Nat) {n : Nat} (A length : CTm Tower.Head n) : CTm Tower.Head n :=
  .pi (vector A length) (evidenceArrow result)

def afterLength (result : LevelExpr Nat) {n : Nat} (A length : CTm Tower.Head n) : CTm Tower.Head n :=
  .pi A (afterHead result (A.rename wk) (length.rename wk))

def canonicalConsType (result : LevelExpr Nat) {n : Nat} (A : CTm Tower.Head n) : CTm Tower.Head n :=
  .pi (.const natName) (afterLength result (A.rename wk) (.var 0))

theorem evidenceArrow_type : CTyped (Profile.church element result enabled) ambient (evidenceArrow result)
    (Profile.motiveSort element result) :=
  product_atBound element result enabled (resultSort_typed element result enabled) (resultSort_typed element result enabled)

theorem afterHead_type {A length : CTm Tower.Head n}
    (elementTyped : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element))
    (lengthTyped : CTyped (Profile.church element result enabled) ambient length (.const natName)) :
    CTyped (Profile.church element result enabled) ambient (afterHead result A length) (Profile.motiveSort element result) :=
  product_atBound element result enabled
    (element_atBound element result enabled (Profile.vector_typed element result enabled elementTyped lengthTyped))
    (evidenceArrow_type element result enabled)

theorem afterLength_type {A length : CTm Tower.Head n}
    (elementTyped : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element))
    (lengthTyped : CTyped (Profile.church element result enabled) ambient length (.const natName)) :
    CTyped (Profile.church element result enabled) ambient (afterLength result A length) (Profile.motiveSort element result) :=
  product_atBound element result enabled (element_atBound element result enabled elementTyped)
    (afterHead_type element result enabled elementTyped.weaken lengthTyped.weaken)

theorem canonicalConsType_type {A : CTm Tower.Head n}
    (typed : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element)) :
    CTyped (Profile.church element result enabled) ambient (canonicalConsType result A) (Profile.motiveSort element result) :=
  product_atBound element result enabled (natural_atBound element result enabled)
    (afterLength_type element result enabled typed.weaken (.var 0))

def lengthContext (ambient : CCtx Tower.Head n) : CCtx Tower.Head (n + 1) := .snoc ambient (.const natName)
def headContext (ambient : CCtx Tower.Head n) (A : CTm Tower.Head n) : CCtx Tower.Head (n + 2) :=
  .snoc (lengthContext ambient) (A.rename wk)
def tailContext (ambient : CCtx Tower.Head n) (A : CTm Tower.Head n) : CCtx Tower.Head (n + 3) :=
  .snoc (headContext ambient A) (vector (weaken2 A) (.var 1))
def typeContext (result : LevelExpr Nat) (ambient : CCtx Tower.Head n) (A : CTm Tower.Head n) : CCtx Tower.Head (n + 4) :=
  .snoc (tailContext ambient A) (resultSort result)

theorem consBody_typed {A predicate : CTm Tower.Head n}
    (predicateTyped : CTyped (Profile.church element result enabled) ambient predicate (.pi A (resultSort result))) :
    CTyped (Profile.church element result enabled) (typeContext result ambient A)
      (.sigma (.app (weaken4 predicate) (.var 2)) (.var 1)) (resultSort result) := by
  have raised : CTyped (Profile.church element result enabled) (typeContext result ambient A)
      (weaken4 predicate) (.pi (weaken4 A) (resultSort result)) :=
    (((predicateTyped.weaken (E := .const natName)).weaken (E := A.rename wk)).weaken
      (E := vector (weaken2 A) (.var 1))).weaken (E := resultSort result)
  have headTyped : CTyped (Profile.church element result enabled) (typeContext result ambient A) (.var 2) (weaken4 A) := .var 2
  have atHead := CDerivable.appElim raised headTyped
  have tailType : CTyped (Profile.church element result enabled)
      (.snoc (typeContext result ambient A) (.app (weaken4 predicate) (.var 2))) (.var 1) (resultSort result) := .var 1
  refine .cumul (.sigmaForm atHead (.sort _) tailType (.sort _) (.sorts _ _)) ?_
  change ∀ valuation : Nat → Nat, max (result.eval valuation) (result.eval valuation) ≤ result.eval valuation
  exact fun _ => max_le_iff.mpr ⟨le_rfl, le_rfl⟩

theorem consCase_canonical {A predicate : CTm Tower.Head n}
    (elementTyped : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element))
    (predicateTyped : CTyped (Profile.church element result enabled) ambient predicate (.pi A (resultSort result))) :
    CTyped (Profile.church element result enabled) ambient (consCase result A predicate) (canonicalConsType result A) := by
  apply CDerivable.lamIntro (Profile.natural_typed element result enabled) (.sort _)
    (canonicalConsType_type element result enabled elementTyped) (.sort _)
  apply CDerivable.lamIntro elementTyped.weaken (.sort _)
    (afterLength_type element result enabled elementTyped.weaken (.var 0)) (.sort _)
  apply CDerivable.lamIntro
    (Profile.vector_typed element result enabled elementTyped.weaken.weaken (.var 1)) (.sort _)
    (afterHead_type element result enabled elementTyped.weaken.weaken (.var 1)) (.sort _)
  apply CDerivable.lamIntro (resultSort_typed element result enabled) (.sort _)
    (evidenceArrow_type element result enabled) (.sort _)
  exact consBody_typed element result enabled predicateTyped

theorem universeMotive_rename {n m : Nat} (result : LevelExpr Nat) (A : CTm Tower.Head n) (rho : Ren n m) :
    (universeMotive result A).rename rho = universeMotive result (A.rename rho) := by
  simp only [universeMotive, motiveInner, vector, resultSort, CTm.rename, CTm.rename_comp]
  rfl

theorem canonicalConsType_equal {A : CTm Tower.Head n}
    (elementTyped : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element)) :
    CEqual (Profile.church element result enabled) ambient (canonicalConsType result A)
      (Programs.Annotated.Append.methodType A (universeMotive result A)) (Profile.motiveSort element result) := by
  simp only [canonicalConsType, afterLength, afterHead, evidenceArrow, Programs.Annotated.Append.methodType,
    universeMotive_rename]
  apply productEqual_atBound element result enabled (.refl (natural_atBound element result enabled))
  apply productEqual_atBound element result enabled (.refl (element_atBound element result enabled elementTyped.weaken))
  apply productEqual_atBound element result enabled
    (.refl (element_atBound element result enabled
      (Profile.vector_typed element result enabled elementTyped.weaken.weaken (.var 1))))
  apply productEqual_atBound element result enabled
    ((motive_beta element result enabled elementTyped.weaken.weaken.weaken (.var 2) (.var 0)).symm)
  exact (motive_beta element result enabled elementTyped.weaken.weaken.weaken.weaken
    (Profile.successor_typed element result enabled (.var 3))
    (Profile.cons_typed element result enabled elementTyped.weaken.weaken.weaken.weaken (.var 3) (.var 2) (.var 1))).symm

theorem consCase_typed {A predicate : CTm Tower.Head n}
    (elementTyped : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element))
    (predicateTyped : CTyped (Profile.church element result enabled) ambient predicate (.pi A (resultSort result))) :
    CTyped (Profile.church element result enabled) ambient (consCase result A predicate)
      (Programs.Annotated.Append.methodType A (universeMotive result A)) :=
  .conv (consCase_canonical element result enabled elementTyped predicateTyped)
    (canonicalConsType_equal element result enabled elementTyped) (.sort _)

theorem allType_typed {A predicate length value : CTm Tower.Head n}
    (elementTyped : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element))
    (predicateTyped : CTyped (Profile.church element result enabled) ambient predicate (.pi A (resultSort result)))
    (lengthTyped : CTyped (Profile.church element result enabled) ambient length (.const natName))
    (valueTyped : CTyped (Profile.church element result enabled) ambient value (vector A length)) :
    CTyped (Profile.church element result enabled) ambient (allType result A predicate length value) (resultSort result) := by
  have base := CDerivable.conv (unit_typed element result enabled)
    (motive_beta element result enabled elementTyped (Profile.zero_typed element result enabled)
      (Profile.nil_typed element result enabled elementTyped)).symm (.sort _)
  have applied := Profile.eliminate_typed element result enabled elementTyped
    (motive_typed element result enabled elementTyped) base
    (consCase_typed element result enabled elementTyped predicateTyped) lengthTyped valueTyped
  exact .conv applied (motive_beta element result enabled elementTyped lengthTyped valueTyped) (.sort _)

#print axioms consCase_typed
#print axioms allType_typed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated.Formation
