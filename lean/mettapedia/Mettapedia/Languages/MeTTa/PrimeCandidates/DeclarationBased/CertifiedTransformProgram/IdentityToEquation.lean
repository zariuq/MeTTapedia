import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Controls

/-!
# Equations and identities in the certified-transform program

The source proofs state equality with the represented `eq@num`, whose
reflexivity and substitution are assumptions.  The dependent programs state
it with identity types.

* From identity to equation there is a typed program: `J` transports the
  reflexivity assumption along an identity proof.  At reflexivity it computes
  to the reflexivity assumption.
* From equation to identity there is no conversion: `Holds (eq a b)` never
  converts to `Id num a b` (`CertifiedTransformProgram.Controls.equation_not_identity`).
  That excludes conversion only; it says nothing about programs from equation
  evidence to identity evidence.  The identity profile (`IdentityEquality`)
  reads equations as identity types, and there the translated source proof is
  identity evidence at every index.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityToEquation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open SetProfile (numTy eqNumNative holdsName)
open CertifiedTransformProgram.Package
open CertifiedTransformProgram.Controls (equation reflPredicate)
open CertifiedTransformProgram.Execution (Runs patternValues)
open Mettapedia.Logic

/-- `λ y p. Holds (eq a y)`, the motive over a point `a`. -/
def equationMotive {n : Nat} (point : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (equation (rename wk (rename wk point)) (.var 1)))

/-- `refl@ a`. -/
def reflEvidence {n : Nat} (point : Tower.Tm n) : Tower.Tm n :=
  .app (.const SetProfile.reflName) point

/-- `J num a (λ y p. Holds (eq a y)) (refl@ a) b e`. -/
def identityToEquation {n : Nat} (point endpoint path : Tower.Tm n) : Tower.Tm n :=
  jApp numT point (equationMotive point) (reflEvidence point) endpoint path

/-- The reflexivity assumption applied to a number proves its equation. -/
theorem reflEvidence_typed {n : Nat} {Γ : Tower.Ctx n} {point : Tower.Tm n}
    (pointTyped : Typing R Γ point numT) :
    Typing R Γ (reflEvidence point) (equation point point) := by
  have decoded : Conv R.headEq
      (liftClosed (FormationSensitiveHOLGenericProofFamily.proof holdsName
        SetProfile.reflCode) : Tower.Tm n)
      (.pi numT (.app (.const holdsName) (.app (liftClosed reflPredicate) (.var 0))))
      R.computation :=
    .rel _ _ (.root (RootStep.inherited (RootStep.inherited (RootStep.declared
      (FormationSensitiveHOLGenericProofFamily.DecoderStep.universal numTy
        (liftClosed reflPredicate))))))
  have predicateTyped : Typing R (.snoc Γ numT) (liftClosed reflPredicate) (.pi numT propT) :=
    Typing.lamIntro (pi_at numT_typed propT_typed) (isUniverseAt Tower.zero)
      (eqNum_typed (Typing.var 0) (Typing.var 0))
  have piFormed : Typing R Γ
      (.pi numT (.app (.const holdsName) (.app (liftClosed reflPredicate) (.var 0)))) U0 :=
    pi_at numT_typed (proof_typed (Typing.appElim (B := propT) predicateTyped (Typing.var 0)))
  have constant := Typing.conv (CertifiedTransformProgram.Execution.assumption_typed (Γ := Γ) 1)
    piFormed (isUniverseAt Tower.zero) decoded
  have applied := Typing.appElim constant pointTyped
  have reduced : (inst0 point (.app (.const holdsName) (.app (liftClosed reflPredicate) (.var 0))) :
      Tower.Tm n) = .app (.const holdsName) (.app (.lam (eqNumNative (.var 0) (.var 0))) point) :=
    rfl
  rw [reduced] at applied
  have beta : Conv R.headEq
      (.app (.const holdsName) (.app (.lam (eqNumNative (.var 0) (.var 0))) point) : Tower.Tm n)
      (equation point point) R.computation :=
    .rel _ _ (.congAppArg (.betaPi _ _))
  exact Typing.conv applied (proof_typed (eqNum_typed pointTyped pointTyped))
    (isUniverseAt Tower.zero) beta

/-- The context `a b : num, e : Id num a b`. -/
abbrev identityContext : Tower.Ctx 3 :=
  .snoc (.snoc (.snoc .nil numT) numT) (.id numT (.var 1) (.var 0))

/-- At an open identity proof `e : Id num a b`, the program proves `Holds (eq a b)`. -/
theorem identityToEquation_open_typed :
    Typing R identityContext (identityToEquation (.var 2) (.var 1) (.var 0))
      (equation (.var 2) (.var 1)) := by
  have pointTyped : Typing R identityContext (.var 2) numT := Typing.var 2
  have motiveFormed₂ : Typing R (.snoc identityContext numT)
      (.pi (.id numT (.var 3) (.var 0)) U0) U1 :=
    pi_at (raise (id_at numT_typed (Typing.var 3) (Typing.var 0))) U0_typed
  have motiveFormed : Typing R identityContext
      (.pi numT (.pi (.id numT (.var 3) (.var 0)) U0)) U1 :=
    pi_at (raise numT_typed) motiveFormed₂
  have motiveTyped : Typing R identityContext (equationMotive (.var 2))
      (.pi numT (.pi (.id numT (.var 3) (.var 0)) U0)) :=
    Typing.lamIntro motiveFormed (isUniverseAt level1)
      (Typing.lamIntro motiveFormed₂ (isUniverseAt level1)
        (proof_typed (eqNum_typed (Typing.var 4) (Typing.var 1))))
  have reflCaseFormed : Typing R identityContext
      (.app (.app (equationMotive (.var 2)) (.var 2)) (.refl (.var 2))) U0 :=
    Typing.appElim (B := U0) (Typing.appElim motiveTyped pointTyped) (Typing.reflIntro pointTyped)
  have reflCase := Typing.conv (reflEvidence_typed pointTyped) reflCaseFormed
    (isUniverseAt Tower.zero) (.symm _ _ (beta_two _ _ _))
  have j0 := j_typed identityContext
  rw [jType_eq] at j0
  have j1 := Typing.appElim j0 numT_typed
  have j2 := Typing.appElim j1 pointTyped
  have j3 := Typing.appElim j2 motiveTyped
  have j4 := Typing.appElim j3 reflCase
  have j5 := Typing.appElim j4 (Typing.var 1)
  have j6 := Typing.appElim j5 (Typing.var 0)
  exact Typing.conv j6 (proof_typed (eqNum_typed (Typing.var 2) (Typing.var 1)))
    (isUniverseAt Tower.zero) (beta_two _ _ _)

/-- Identity evidence yields equation evidence, at every typed instance. -/
theorem identityToEquation_typed {n : Nat} {Γ : Tower.Ctx n} {point endpoint path : Tower.Tm n}
    (pointTyped : Typing R Γ point numT) (endpointTyped : Typing R Γ endpoint numT)
    (pathTyped : Typing R Γ path (.id numT point endpoint)) :
    Typing R Γ (identityToEquation point endpoint path) (equation point endpoint) := by
  have morphism : FormationSensitive.CtxMor R identityContext Γ
      (patternValues ![point, endpoint, path]) := by
    intro index
    fin_cases index
    · exact pathTyped
    · exact endpointTyped
    · exact pointTyped
  exact identityToEquation_open_typed.substitute morphism

/-- At reflexivity the program computes to the reflexivity assumption. -/
theorem identityToEquation_refl {n : Nat} (point : Tower.Tm n) :
    Runs (identityToEquation point point (.refl point)) (reflEvidence point) :=
  CertifiedTransformProgram.Execution.Runs.equation listed_jIota
    (patternValues ![numT, point, equationMotive point, reflEvidence point])

#print axioms reflEvidence_typed
#print axioms identityToEquation_open_typed
#print axioms identityToEquation_typed
#print axioms identityToEquation_refl

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityToEquation
