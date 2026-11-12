import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.SetExtensionality

/-!
# Extensional equality of sets, computed from the codes and kept outside the knowledge

Sets over `U0` are the predicates `U0 → U0` of `ProgrammingOnTheStep.SetExtensionality`. Their
extensional equality is a type computed from the codes of the two sets by the structure of their
type, as observational type theory computes equality, but here it is an ordinary type of the
calculus:

  `setEq S T = Π (X : U0). Σ (_ : S X → T X). (T X → S X)`.

A proof of it is a typed term, so it can be the label of a row of the step. Nothing is added to the
knowledge, which still equates terms only up to typed βη conversion.

* `setEq_formed`: the code is a type of `U1` whenever `S` and `T` are sets.
* `s_beta`, `t_beta`: membership in a comprehension is definitional: `S A` and `Σ A Ground` are
  equal in the knowledge, by β. Comprehension needs no evidence; extensionality does.
* `setEq_normal`, `evidence_typed`: from a forward and a backward map, `λX. (f X, g X)` is a proof
  of `setEq S T` for the two sets of `SetExtensionality`.
* `respType`: what a family of sets must carry to be transported: a term of
  `Π (S T : U0 → U0). setEq S T → P S → P T`. Transport is defined only for families with one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace EqualityOnTheStep

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.SetExtensionality (small U0 sCode tCode setType swapCode swapType
  swapBackType setType_formed s_typed t_typed swap_typed swapBack_typed)

/-! ## Levels -/

/-- The level of `U1`. -/
abbrev large : Tower.Head := .sort (.succ Tower.zero)

theorem large_of_one_zero :
    Tower.rules.cumulative (.sort (.max (.succ Tower.zero) Tower.zero)) large := by
  change LevelTower.Cumulative (.sort (.max (.succ Tower.zero) Tower.zero)) (.sort (.succ Tower.zero))
  intro valuation
  simp [LevelExpr.eval]

theorem large_of_one_one :
    Tower.rules.cumulative (.sort (.max (.succ Tower.zero) (.succ Tower.zero))) large := by
  change LevelTower.Cumulative (.sort (.max (.succ Tower.zero) (.succ Tower.zero)))
    (.sort (.succ Tower.zero))
  intro valuation
  simp [LevelExpr.eval]

/-- Sets, at the level `U1`. -/
theorem setType_large {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ setType (.head large) :=
  .cumul (setType_formed Γ) large_of_one_one

/-! ## The swaps' types are formed -/

theorem swapType_formed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ swapType (.head large) := by
  have pairs : Typed Tower.rules (.snoc (.snoc (.snoc Γ U0) (.sigma (.var 0) ground)) ground) (.var 2) U0 :=
    Derivable.var 2
  have codomain : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma (.var 0) ground)) (.sigma ground (.var 2)) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) pairs (.sort _) (.sorts _ _)) collapse
  have domain : Typed Tower.rules (.snoc Γ U0) (.sigma (.var 0) ground) U0 :=
    .cumul (.sigmaForm (Derivable.var 0) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
  exact .cumul (.piForm (.headType (.sort _)) (.sort _)
    (.cumul (.piForm domain (.sort _) codomain (.sort _) (.sorts _ _)) collapse) (.sort _) (.sorts _ _))
    large_of_one_zero

theorem swapBackType_formed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ swapBackType (.head large) := by
  have pairs : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma ground (.var 1))) (.var 1) U0 :=
    Derivable.var 1
  have codomain : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma ground (.var 1))) (.sigma (.var 1) ground) U0 :=
    .cumul (.sigmaForm pairs (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
  have domain : Typed Tower.rules (.snoc Γ U0) (.sigma ground (.var 1)) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 1) (.sort _) (.sorts _ _)) collapse
  exact .cumul (.piForm (.headType (.sort _)) (.sort _)
    (.cumul (.piForm domain (.sort _) codomain (.sort _) (.sorts _ _)) collapse) (.sort _) (.sorts _ _))
    large_of_one_zero

/-! ## Extensional equality of sets -/

/-- **Extensional equality of two sets**, computed from their codes:
`Π (X : U0). Σ (_ : S X → T X). (T X → S X)`. -/
def setEq {n : Nat} (S T : Tower.Tm n) : Tower.Tm n :=
  .pi U0 (.sigma
    (.pi (.app (Presentation.rename wk S) (.var 0))
      (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1)))
    (.pi (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk S))) (.var 2))))

/-- The forward map's type `S X → T X`, over `X : U0`. -/
theorem setEqForward_formed {n : Nat} {Γ : Tower.Ctx n} {S T : Tower.Tm n}
    (tS : Typed Tower.rules Γ S setType) (tT : Typed Tower.rules Γ T setType) :
    Typed Tower.rules (.snoc Γ U0)
      (.pi (.app (Presentation.rename wk S) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1))) U0 := by
  have S1 : Typed Tower.rules (.snoc Γ U0) (Presentation.rename wk S) setType := tS.weaken
  have T1 : Typed Tower.rules (.snoc Γ U0) (Presentation.rename wk T) setType := tT.weaken
  have X1 : Typed Tower.rules (.snoc Γ U0) (.var 0) U0 := Derivable.var 0
  have SX : Typed Tower.rules (.snoc Γ U0) (.app (Presentation.rename wk S) (.var 0)) U0 :=
    Derivable.appElim S1 X1
  have T2 : Typed Tower.rules (.snoc (.snoc Γ U0) (.app (Presentation.rename wk S) (.var 0)))
      (Presentation.rename wk (Presentation.rename wk T)) setType := T1.weaken
  have X2 : Typed Tower.rules (.snoc (.snoc Γ U0) (.app (Presentation.rename wk S) (.var 0))) (.var 1) U0 :=
    Derivable.var 1
  have TX2 : Typed Tower.rules (.snoc (.snoc Γ U0) (.app (Presentation.rename wk S) (.var 0)))
      (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1)) U0 := Derivable.appElim T2 X2
  exact .cumul (.piForm SX (.sort _) TX2 (.sort _) (.sorts _ _)) collapse

/-- The backward map's type `T X → S X`, over `X : U0` and the forward map. -/
theorem setEqBackward_formed {n : Nat} {Γ : Tower.Ctx n} {S T : Tower.Tm n}
    (tS : Typed Tower.rules Γ S setType) (tT : Typed Tower.rules Γ T setType) :
    Typed Tower.rules (.snoc (.snoc Γ U0) (.pi (.app (Presentation.rename wk S) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1))))
      (.pi (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1))
        (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk S))) (.var 2))) U0 := by
  have S1 : Typed Tower.rules (.snoc Γ U0) (Presentation.rename wk S) setType := tS.weaken
  have T1 : Typed Tower.rules (.snoc Γ U0) (Presentation.rename wk T) setType := tT.weaken
  have T2' : Typed Tower.rules (.snoc (.snoc Γ U0) (.pi (.app (Presentation.rename wk S) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1))))
      (Presentation.rename wk (Presentation.rename wk T)) setType := T1.weaken
  have X2' : Typed Tower.rules (.snoc (.snoc Γ U0) (.pi (.app (Presentation.rename wk S) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1)))) (.var 1) U0 :=
    Derivable.var 1
  have TX2' : Typed Tower.rules (.snoc (.snoc Γ U0) (.pi (.app (Presentation.rename wk S) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1))))
      (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1)) U0 := Derivable.appElim T2' X2'
  have S3 : Typed Tower.rules (.snoc (.snoc (.snoc Γ U0) (.pi (.app (Presentation.rename wk S) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1))))
        (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1)))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk S))) setType :=
    S1.weaken.weaken
  have X3 : Typed Tower.rules (.snoc (.snoc (.snoc Γ U0) (.pi (.app (Presentation.rename wk S) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1))))
        (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1))) (.var 2) U0 :=
    Derivable.var 2
  have SX3 := Derivable.appElim S3 X3
  exact .cumul (.piForm TX2' (.sort _) SX3 (.sort _) (.sorts _ _)) collapse

/-- The body of `setEq S T`, over `X : U0`. -/
theorem setEqBody_formed {n : Nat} {Γ : Tower.Ctx n} {S T : Tower.Tm n}
    (tS : Typed Tower.rules Γ S setType) (tT : Typed Tower.rules Γ T setType) :
    Typed Tower.rules (.snoc Γ U0)
      (.sigma (.pi (.app (Presentation.rename wk S) (.var 0))
          (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1)))
        (.pi (.app (Presentation.rename wk (Presentation.rename wk T)) (.var 1))
          (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk S))) (.var 2)))) U0 :=
  .cumul (.sigmaForm (setEqForward_formed tS tT) (.sort _) (setEqBackward_formed tS tT) (.sort _) (.sorts _ _))
    collapse

/-- **`setEq S T` is a type of `U1`** when `S` and `T` are sets. -/
theorem setEq_formed {n : Nat} {Γ : Tower.Ctx n} {S T : Tower.Tm n}
    (tS : Typed Tower.rules Γ S setType) (tT : Typed Tower.rules Γ T setType) :
    Typed Tower.rules Γ (setEq S T) (.head large) :=
  .cumul (.piForm (.headType (.sort _)) (.sort _) (setEqBody_formed tS tT) (.sort _) (.sorts _ _))
    large_of_one_zero

/-! ## Comprehension is definitional -/

theorem sBody_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules (.snoc Γ U0) (.sigma (.var 0) ground) U0 :=
  .cumul (.sigmaForm (Derivable.var 0) (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse

theorem tBody_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules (.snoc Γ U0) (.sigma ground (.var 1)) U0 :=
  .cumul (.sigmaForm (ground_typed _) (.sort _) (Derivable.var 1) (.sort _) (.sorts _ _)) collapse

/-- **Membership in `S` is definitional**: `S A` is `Σ (_ : A). Ground` in the knowledge. -/
theorem s_beta {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} (tA : Typed Tower.rules Γ A U0) :
    Equal Tower.rules Γ (.app sCode A) (.sigma A ground) U0 :=
  Derivable.betaPi (setType_formed Γ) (.sort _) (sBody_typed Γ) tA

/-- **Membership in `T` is definitional**: `T A` is `Σ (_ : Ground). A` in the knowledge. -/
theorem t_beta {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} (tA : Typed Tower.rules Γ A U0) :
    Equal Tower.rules Γ (.app tCode A) (.sigma ground (Presentation.rename wk A)) U0 :=
  Derivable.betaPi (setType_formed Γ) (.sort _) (tBody_typed Γ) tA

/-! ## The two sets are extensionally equal -/

/-- The β-normal form of `setEq S T`:
`Π (X : U0). Σ (_ : Σ X Ground → Σ Ground X). (Σ Ground X → Σ X Ground)`. -/
def stNormal {n : Nat} : Tower.Tm n :=
  .pi U0 (.sigma (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2)))
    (.pi (.sigma ground (.var 2)) (.sigma (.var 2) ground)))

theorem stForward_formed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules (.snoc Γ U0) (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2))) U0 := by
  have X : Typed Tower.rules (.snoc (.snoc (.snoc Γ U0) (.sigma (.var 0) ground)) ground) (.var 2) U0 :=
    Derivable.var 2
  have codomain : Typed Tower.rules (.snoc (.snoc Γ U0) (.sigma (.var 0) ground)) (.sigma ground (.var 2)) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) X (.sort _) (.sorts _ _)) collapse
  exact .cumul (.piForm (sBody_typed Γ) (.sort _) codomain (.sort _) (.sorts _ _)) collapse

theorem stSigma_formed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules (.snoc Γ U0) (.sigma (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2)))
      (.pi (.sigma ground (.var 2)) (.sigma (.var 2) ground))) U0 := by
  have X3 : Typed Tower.rules (.snoc (.snoc (.snoc Γ U0)
      (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2)))) ground) (.var 2) U0 := Derivable.var 2
  have domain : Typed Tower.rules (.snoc (.snoc Γ U0) (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2))))
      (.sigma ground (.var 2)) U0 :=
    .cumul (.sigmaForm (ground_typed _) (.sort _) X3 (.sort _) (.sorts _ _)) collapse
  have Y3 : Typed Tower.rules (.snoc (.snoc (.snoc Γ U0)
      (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2)))) (.sigma ground (.var 2))) (.var 2) U0 :=
    Derivable.var 2
  have codomain : Typed Tower.rules (.snoc (.snoc (.snoc Γ U0)
      (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2)))) (.sigma ground (.var 2)))
      (.sigma (.var 2) ground) U0 :=
    .cumul (.sigmaForm Y3 (.sort _) (ground_typed _) (.sort _) (.sorts _ _)) collapse
  have backward : Typed Tower.rules (.snoc (.snoc Γ U0) (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2))))
      (.pi (.sigma ground (.var 2)) (.sigma (.var 2) ground)) U0 :=
    .cumul (.piForm domain (.sort _) codomain (.sort _) (.sorts _ _)) collapse
  exact .cumul (.sigmaForm (stForward_formed Γ) (.sort _) backward (.sort _) (.sorts _ _)) collapse

theorem stNormal_formed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ stNormal (.head large) :=
  .cumul (.piForm (.headType (.sort _)) (.sort _) (stSigma_formed Γ) (.sort _) (.sorts _ _))
    large_of_one_zero

/-- **`setEq S T` is its β-normal form** in the knowledge. -/
theorem setEq_normal {n : Nat} (Γ : Tower.Ctx n) :
    Equal Tower.rules Γ (setEq sCode tCode) stNormal (.head large) := by
  show Equal Tower.rules Γ (.pi U0 (.sigma (.pi (.app sCode (.var 0)) (.app tCode (.var 1)))
    (.pi (.app tCode (.var 1)) (.app sCode (.var 2))))) stNormal (.head large)
  have X1 : Typed Tower.rules (.snoc Γ U0) (.var 0) U0 := Derivable.var 0
  have X2 : Typed Tower.rules (.snoc (.snoc Γ U0) (.app sCode (.var 0))) (.var 1) U0 := Derivable.var 1
  have forward : Equal Tower.rules (.snoc Γ U0) (.pi (.app sCode (.var 0)) (.app tCode (.var 1)))
      (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2))) U0 :=
    .cumulEq (.piCong (s_beta X1) (.sort _) (t_beta X2) (.sort _) (.sorts _ _)) collapse
  have Y2 : Typed Tower.rules (.snoc (.snoc Γ U0) (.pi (.app sCode (.var 0)) (.app tCode (.var 1))))
      (.var 1) U0 := Derivable.var 1
  have Y3 : Typed Tower.rules (.snoc (.snoc (.snoc Γ U0) (.pi (.app sCode (.var 0)) (.app tCode (.var 1))))
      (.app tCode (.var 1))) (.var 2) U0 := Derivable.var 2
  have backward : Equal Tower.rules (.snoc (.snoc Γ U0) (.pi (.app sCode (.var 0)) (.app tCode (.var 1))))
      (.pi (.app tCode (.var 1)) (.app sCode (.var 2)))
      (.pi (.sigma ground (.var 2)) (.sigma (.var 2) ground)) U0 :=
    .cumulEq (.piCong (t_beta Y2) (.sort _) (s_beta Y3) (.sort _) (.sorts _ _)) collapse
  have body : Equal Tower.rules (.snoc Γ U0)
      (.sigma (.pi (.app sCode (.var 0)) (.app tCode (.var 1))) (.pi (.app tCode (.var 1)) (.app sCode (.var 2))))
      (.sigma (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2)))
        (.pi (.sigma ground (.var 2)) (.sigma (.var 2) ground))) U0 :=
    .cumulEq (.sigmaCong forward (.sort _) backward (.sort _) (.sorts _ _)) collapse
  have sorts : Equal Tower.rules Γ U0 U0 (.head (.sort (.succ Tower.zero))) := .refl (.headType (.sort _))
  exact .cumulEq (.piCong sorts (.sort _) body (.sort _) (.sorts _ _)) large_of_one_zero

/-- **The evidence**: `λX. (f X, g X)`, a forward and a backward map paired at every `X`. -/
def evidence {n : Nat} (f g : Tower.Tm n) : Tower.Tm n :=
  .lam (.pair (.app (Presentation.rename wk f) (.var 0)) (.app (Presentation.rename wk g) (.var 0)))

theorem evidence_normal {n : Nat} {Γ : Tower.Ctx n} {f g : Tower.Tm n}
    (tf : Typed Tower.rules Γ f swapType) (tg : Typed Tower.rules Γ g swapBackType) :
    Typed Tower.rules Γ (evidence f g) stNormal := by
  have f1 : Typed Tower.rules (.snoc Γ U0) (Presentation.rename wk f) swapType := tf.weaken
  have g1 : Typed Tower.rules (.snoc Γ U0) (Presentation.rename wk g) swapBackType := tg.weaken
  have X1 : Typed Tower.rules (.snoc Γ U0) (.var 0) U0 := Derivable.var 0
  have fX : Typed Tower.rules (.snoc Γ U0) (.app (Presentation.rename wk f) (.var 0))
      (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2))) := Derivable.appElim f1 X1
  have gX : Typed Tower.rules (.snoc Γ U0) (.app (Presentation.rename wk g) (.var 0))
      (.pi (.sigma ground (.var 1)) (.sigma (.var 1) ground)) := Derivable.appElim g1 X1
  have body : Typed Tower.rules (.snoc Γ U0)
      (.pair (.app (Presentation.rename wk f) (.var 0)) (.app (Presentation.rename wk g) (.var 0)))
      (.sigma (.pi (.sigma (.var 0) ground) (.sigma ground (.var 2)))
        (.pi (.sigma ground (.var 2)) (.sigma (.var 2) ground))) :=
    .pairIntro (stSigma_formed Γ) (.sort _) fX gX
  exact .lamIntro (stNormal_formed Γ) (.sort _) body

/-- **From a forward and a backward map, a proof that `S` and `T` have the same members.** -/
theorem evidence_typed {n : Nat} {Γ : Tower.Ctx n} {f g : Tower.Tm n}
    (tf : Typed Tower.rules Γ f swapType) (tg : Typed Tower.rules Γ g swapBackType) :
    Typed Tower.rules Γ (evidence f g) (setEq sCode tCode) :=
  .conv (evidence_normal tf tg) (.symm (setEq_normal Γ)) (.sort _)

/-! ## Families of sets and their respect terms -/

/-- Families of sets: `(U0 → U0) → U1`. Families valued in `U0` are among them by cumulativity;
`U1` admits the identity type of sets, which reads the code of a set. -/
def famType {n : Nat} : Tower.Tm n := .pi setType (.head large)

/-- The level of `famType`. -/
abbrev famLevel : Tower.Head := .sort (.max (.succ Tower.zero) (.succ (.succ Tower.zero)))

theorem famType_formed {n : Nat} (Γ : Tower.Ctx n) : Typed Tower.rules Γ famType (.head famLevel) :=
  .piForm (setType_large Γ) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

theorem small_large : Tower.rules.cumulative small large := by
  change LevelTower.Cumulative (.sort Tower.zero) (.sort (.succ Tower.zero))
  intro valuation
  simp [LevelExpr.eval]

/-- A family applied to a set is a type of `U1`. -/
theorem famApp_typed {n : Nat} {Γ : Tower.Ctx n} {P S : Tower.Tm n}
    (tP : Typed Tower.rules Γ P famType) (tS : Typed Tower.rules Γ S setType) :
    Typed Tower.rules Γ (.app P S) (.head large) :=
  Derivable.appElim tP tS

/-- **The respect type of a family** `P`: `Π (S T : U0 → U0). setEq S T → P S → P T`. A family is
transported along extensional equality only with a term of this type. -/
def respType {n : Nat} (P : Tower.Tm n) : Tower.Tm n :=
  .pi setType (.pi setType (.pi (setEq (.var 1) (.var 0))
    (.pi (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk P))) (.var 2))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (Presentation.rename wk P)))) (.var 2)))))

/-- The innermost layer of `respType P`: `P S → P T`, over `S T : U0 → U0, e : setEq S T`. -/
theorem respInner_formed {n : Nat} {Γ : Tower.Ctx n} {P : Tower.Tm n}
    (tP : Typed Tower.rules Γ P famType) :
    Typed Tower.rules (.snoc (.snoc (.snoc Γ setType) setType) (setEq (.var 1) (.var 0)))
      (.pi (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk P))) (.var 2))
        (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
          (Presentation.rename wk P)))) (.var 2))) (.head large) := by
  have P3 : Typed Tower.rules (.snoc (.snoc (.snoc Γ setType) setType) (setEq (.var 1) (.var 0)))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk P))) famType :=
    tP.weaken.weaken.weaken
  have S3 : Typed Tower.rules (.snoc (.snoc (.snoc Γ setType) setType) (setEq (.var 1) (.var 0)))
      (.var 2) setType := Derivable.var 2
  have PS : Typed Tower.rules (.snoc (.snoc (.snoc Γ setType) setType) (setEq (.var 1) (.var 0)))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk P))) (.var 2))
      (.head large) :=
    famApp_typed P3 S3
  have P4 : Typed Tower.rules (.snoc (.snoc (.snoc (.snoc Γ setType) setType) (setEq (.var 1) (.var 0)))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk P))) (.var 2)))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk P))))
      famType := P3.weaken
  have T4 : Typed Tower.rules (.snoc (.snoc (.snoc (.snoc Γ setType) setType) (setEq (.var 1) (.var 0)))
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk P))) (.var 2)))
      (.var 2) setType := Derivable.var 2
  have PT := famApp_typed P4 T4
  exact .cumul (.piForm PS (.sort _) PT (.sort _) (.sorts _ _)) large_of_one_one

/-- The third layer of `respType P`: `setEq S T → P S → P T`, over `S T : U0 → U0`. -/
theorem respThird_formed {n : Nat} {Γ : Tower.Ctx n} {P : Tower.Tm n}
    (tP : Typed Tower.rules Γ P famType) :
    Typed Tower.rules (.snoc (.snoc Γ setType) setType)
      (.pi (setEq (.var 1) (.var 0))
        (.pi (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk P))) (.var 2))
          (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
            (Presentation.rename wk P)))) (.var 2)))) (.head large) := by
  have equal : Typed Tower.rules (.snoc (.snoc Γ setType) setType) (setEq (.var 1) (.var 0)) (.head large) :=
    setEq_formed (Derivable.var 1) (Derivable.var 0)
  exact .cumul (.piForm equal (.sort _) (respInner_formed tP) (.sort _) (.sorts _ _)) large_of_one_one

/-- The second layer of `respType P`, over `S : U0 → U0`. -/
theorem respSecond_formed {n : Nat} {Γ : Tower.Ctx n} {P : Tower.Tm n}
    (tP : Typed Tower.rules Γ P famType) :
    Typed Tower.rules (.snoc Γ setType)
      (.pi setType (.pi (setEq (.var 1) (.var 0))
        (.pi (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk P))) (.var 2))
          (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
            (Presentation.rename wk P)))) (.var 2))))) (.head large) :=
  .cumul (.piForm (setType_large _) (.sort _) (respThird_formed tP) (.sort _) (.sorts _ _)) large_of_one_one

/-- **`respType P` is a type of `U1`** for every family `P`. -/
theorem respType_formed {n : Nat} {Γ : Tower.Ctx n} {P : Tower.Tm n}
    (tP : Typed Tower.rules Γ P famType) : Typed Tower.rules Γ (respType P) (.head large) :=
  .cumul (.piForm (setType_large _) (.sort _) (respSecond_formed tP) (.sort _) (.sorts _ _)) large_of_one_one

end EqualityOnTheStep

#print axioms EqualityOnTheStep.setEq_formed
#print axioms EqualityOnTheStep.s_beta
#print axioms EqualityOnTheStep.t_beta
#print axioms EqualityOnTheStep.setEq_normal
#print axioms EqualityOnTheStep.evidence_typed
#print axioms EqualityOnTheStep.respType_formed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
