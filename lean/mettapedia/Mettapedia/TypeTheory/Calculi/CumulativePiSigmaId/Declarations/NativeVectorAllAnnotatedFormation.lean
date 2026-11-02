import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllAnnotatedProfile
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllAnnotatedSyntax

/-!
# Formation of the universe-valued Vector predicate program

The result universe is explicit in the motive and the recursive-type binder.
The existing program is its exact parameter-zero specialization. Source typing
uses the raised Nat/Vector profile and ordinary typed beta conversion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated.Formation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies

def resultSort (result : LevelExpr Nat) {n : Nat} : CTm Tower.Head n := .head (.sort result)

def motiveInner (result : LevelExpr Nat) {n : Nat} (A length : CTm Tower.Head n) : CTm Tower.Head n :=
  .lam (vector A length) (resultSort result)

def universeMotive (result : LevelExpr Nat) {n : Nat} (A : CTm Tower.Head n) : CTm Tower.Head n :=
  .lam (.const natName) (motiveInner result (A.rename wk) (.var 0))

def consCase (result : LevelExpr Nat) {n : Nat} (A predicate : CTm Tower.Head n) : CTm Tower.Head n :=
  .lam (.const natName) (.lam (A.rename wk)
    (.lam (vector (weaken2 A) (.var 1))
      (.lam (resultSort result) (.sigma (.app (weaken4 predicate) (.var 2)) (.var 1)))))

def unitType {n : Nat} : CTm Tower.Head n := .id (.const natName) (.const zeroName) (.const zeroName)

def allType (result : LevelExpr Nat) {n : Nat} (A predicate length value : CTm Tower.Head n) : CTm Tower.Head n :=
  Programs.Annotated.Append.eliminate A (universeMotive result A) unitType (consCase result A predicate) length value

theorem original_motive {n : Nat} (A : CTm Tower.Head n) :
    universeMotive (.param 0) A = Annotated.universeMotive A := rfl
theorem original_cons {n : Nat} (A predicate : CTm Tower.Head n) :
    consCase (.param 0) A predicate = Annotated.consCase A predicate := rfl
theorem original_all {n : Nat} (A predicate length value : CTm Tower.Head n) :
    allType (.param 0) A predicate length value = Annotated.allType A predicate length value := rfl

variable (element result : LevelExpr Nat) (enabled : Programs.ComputationProfiles.Selection)
    {n : Nat} {ambient : CCtx Tower.Head n}

theorem resultSort_typed : CTyped (Profile.church element result enabled) ambient (resultSort result)
    (Profile.motiveSort element result) := by
  refine .cumul (.headType (.sort result)) ?_
  change ∀ valuation : Nat → Nat, result.eval valuation + 1 ≤ max (element.eval valuation) (result.eval valuation + 1)
  exact fun _ => Nat.le_max_right _ _

theorem motiveInner_type {A length : CTm Tower.Head n}
    (elementTyped : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element))
    (lengthTyped : CTyped (Profile.church element result enabled) ambient length (.const natName)) :
    CIsType (Profile.church element result enabled) ambient
      (.pi (vector A length) (Profile.motiveSort element result)) :=
  CIsType.pi (Profile.levelModel element result enabled)
    ⟨.sort element, .sort _, Profile.vector_typed element result enabled elementTyped lengthTyped⟩
    ⟨.sort (.succ (Profile.recursorLevel element result)), .sort _, .headType (.sort _)⟩

theorem motiveInner_typed {A length : CTm Tower.Head n}
    (elementTyped : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element))
    (lengthTyped : CTyped (Profile.church element result enabled) ambient length (.const natName)) :
    CTyped (Profile.church element result enabled) ambient (motiveInner result A length)
      (.pi (vector A length) (Profile.motiveSort element result)) := by
  obtain ⟨formationLevel, allowed, formed⟩ := motiveInner_type element result enabled elementTyped lengthTyped
  exact .lamIntro (Profile.vector_typed element result enabled elementTyped lengthTyped) (.sort _)
    formed allowed (resultSort_typed element result enabled)

theorem motive_type {A : CTm Tower.Head n}
    (typed : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element)) :
    CIsType (Profile.church element result enabled) ambient (Profile.familyType element result A) :=
  CIsType.pi (Profile.levelModel element result enabled)
    ⟨.sort Tower.zero, .sort _, Profile.natural_typed element result enabled⟩
    (motiveInner_type element result enabled typed.weaken (.var 0))

theorem motive_typed {A : CTm Tower.Head n}
    (typed : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element)) :
    CTyped (Profile.church element result enabled) ambient (universeMotive result A)
      (Profile.familyType element result A) := by
  obtain ⟨formationLevel, allowed, formed⟩ := motive_type element result enabled typed
  exact .lamIntro (Profile.natural_typed element result enabled) (.sort _) formed allowed
    (motiveInner_typed element result enabled typed.weaken (.var 0))

theorem motiveInner_substitute {n m : Nat} (result : LevelExpr Nat) (A length : CTm Tower.Head n)
    (images : CSub Tower.Head n m) :
    (motiveInner result A length).subst images = motiveInner result (A.subst images) (length.subst images) := rfl

theorem motive_beta {A length value : CTm Tower.Head n}
    (elementTyped : CTyped (Profile.church element result enabled) ambient A (Profile.elementSort element))
    (lengthTyped : CTyped (Profile.church element result enabled) ambient length (.const natName))
    (valueTyped : CTyped (Profile.church element result enabled) ambient value (vector A length)) :
    CEqual (Profile.church element result enabled) ambient
      (.app (.app (universeMotive result A) length) value) (resultSort result)
      (Profile.motiveSort element result) := by
  obtain ⟨formationLevel, allowed, formed⟩ := motive_type element result enabled elementTyped
  have first := CDerivable.betaPi formed allowed
    (motiveInner_typed element result enabled elementTyped.weaken (.var 0)) lengthTyped
  have opened : CTm.inst0 length (motiveInner result (A.rename wk) (.var 0)) = motiveInner result A length := by
    rw [CTm.inst0, motiveInner_substitute]
    rw [show CTm.subst length.subst0 (A.rename wk) = A from CTm.inst0_rename_wk length A]
    rfl
  have openedType : CTm.inst0 length
      (.pi (vector (A.rename wk) (.var 0)) (Profile.motiveSort element result)) =
      .pi (vector A length) (Profile.motiveSort element result) := by
    change CTm.pi (vector (CTm.inst0 length (A.rename wk)) length) (Profile.motiveSort element result) = _
    rw [CTm.inst0_rename_wk]
  rw [opened] at first
  change CEqual (Profile.church element result enabled) ambient
    (.app (universeMotive result A) length) (motiveInner result A length)
    (CTm.inst0 length (.pi (vector (A.rename wk) (.var 0)) (Profile.motiveSort element result))) at first
  rw [openedType] at first
  have applied := CDerivable.appCong first (.refl valueTyped)
  obtain ⟨innerUniverse, innerAllowed, innerFormed⟩ := motiveInner_type element result enabled elementTyped lengthTyped
  have second := CDerivable.betaPi innerFormed innerAllowed
    (resultSort_typed element result enabled) valueTyped
  exact .trans applied second

theorem unit_typed : CTyped (Profile.church element result enabled) ambient unitType (resultSort result) := by
  refine .cumul (.idForm (Profile.natural_typed element result enabled) (.sort _)
    (Profile.zero_typed element result enabled) (Profile.zero_typed element result enabled)) ?_
  change ∀ valuation : Nat → Nat, 0 ≤ result.eval valuation
  exact fun _ => Nat.zero_le _

#print axioms motive_typed
#print axioms motive_beta

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Annotated.Formation
