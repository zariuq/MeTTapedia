import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Basic

/-!
# Realizations of the source document's assumptions

The zero-add document assumes induction, reflexivity and substitution for
`num`.  Each stays declared under its name, and each is realized by a program:

* reflexivity `refl@num` by native reflexivity, `λ x. refl x`;
* substitution `subst@num` by identity elimination,
  `λ P x y e h. id:eliminate num x (λ y p. Holds (P y)) h y e`;
* induction `num-ind` by the recursor,
  `λ P z s x. num-rec (λ m. Holds (P m)) z s x`.

Each realization is typed, in the program's own rules, at the dependent reading
of its proposition.  Reading a proposition as that type uses the proof-family
decoders and, when the proposition mentions an equation, the equation decoder.
Induction mentions no equation, so its realization is typed at the represented
proposition itself in the program's own rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Realizations

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence
open SetProfile (numTy holdsName zeroNative sucNative)
open CertifiedTransformProgram.Package CertifiedTransformProgram.IdentityEquality
open FormationSensitiveHOLIdentityEquality (decode decodes decodes_equationFree)
open Mettapedia.Logic

/-- The proof family of the program. -/
abbrev Holds {n : Nat} (proposition : Tower.Tm n) : Tower.Tm n :=
  FormationSensitiveHOLGenericProofFamily.proof holdsName proposition

/-- A predicate `P : num → prop` read as the family `λ m. Holds (P m)`. -/
theorem predicateFamily_typed {n : Nat} {Γ : Tower.Ctx n} {predicate : Tower.Tm n}
    (typed : Typing R Γ predicate (.pi numT propT)) :
    Typing R Γ (.lam (Holds (.app (Presentation.rename wk predicate) (.var 0)))) (.pi numT U0) :=
  Typing.lamIntro (pi_at (raise numT_typed) U0_typed) (isUniverseAt level1)
    (proof_typed (Typing.appElim (B := propT) (typed.weaken (extension := numT)) (Typing.var 0)))

/-- A represented closed proposition is a small type of its proof family. -/
theorem holds_formed {formula : HOL.Formula SetProfile.SetConst []} {code : Tower.Tm 0}
    (represented : FormationSensitiveHOLInterface.represent SetProfile.signature formula = some code) :
    Typing R .nil (Holds code) U0 :=
  proof_typed (include_profile
    (FormationSensitiveHOLInterface.represent_typed SetProfile.signature formula represented))

/-! ## Reflexivity -/

/-- `λ x. refl x`. -/
def reflRealization : Tower.Tm 0 := .lam (.refl (.var 0))

theorem reflRealization_typed :
    Typing identityRules .nil reflRealization (Holds SetProfile.reflCode) :=
  FormationSensitiveHOLIdentityEquality.refl_realizes SetProfile.signature holdsName proofToIdentity
    SetProfile.holdsName_fresh identity_decodes numTy

/-! ## Substitution -/

/-- `λ y p. Holds (P y)`, under the five binders `P x y e h`. -/
def substMotive : Tower.Tm 5 := .lam (.lam (Holds (.app (.var 6) (.var 1))))

/-- `λ P x y e h. id:eliminate num x (λ y p. Holds (P y)) h y e`. -/
def substRealization : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam (jApp numT (.var 3) substMotive (.var 0) (.var 2) (.var 1))))))

/-- `Π P : num → prop. Π x y : num. Id num x y → Holds (P x) → Holds (P y)`. -/
def substDecoded : Tower.Tm 0 :=
  .pi (.pi numT propT) (.pi numT (.pi numT (.pi (.id numT (.var 1) (.var 0))
    (.pi (Holds (.app (.var 3) (.var 2))) (Holds (.app (.var 4) (.var 2)))))))

theorem substAxiom_decoded :
    decode SetProfile.signature holdsName SetProfile.substAxiom = some substDecoded :=
  rfl

/-- The context `P x y e h` of the realization's body. -/
abbrev substContext : Tower.Ctx 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil (.pi numT propT)) numT) numT)
    (.id numT (.var 1) (.var 0))) (Holds (.app (.var 3) (.var 2)))

theorem substBody_typed :
    Typing R substContext (jApp numT (.var 3) substMotive (.var 0) (.var 2) (.var 1))
      (Holds (.app (.var 4) (.var 2))) := by
  have motiveFormed₂ : Typing R (.snoc substContext numT)
      (.pi (.id numT (.var 4) (.var 0)) U0) U1 :=
    pi_at (raise (id_at numT_typed (Typing.var 4) (Typing.var 0))) U0_typed
  have motiveFormed : Typing R substContext (.pi numT (.pi (.id numT (.var 4) (.var 0)) U0)) U1 :=
    pi_at (raise numT_typed) motiveFormed₂
  have motiveTyped : Typing R substContext substMotive
      (.pi numT (.pi (.id numT (.var 4) (.var 0)) U0)) :=
    Typing.lamIntro motiveFormed (isUniverseAt level1)
      (Typing.lamIntro motiveFormed₂ (isUniverseAt level1)
        (proof_typed (Typing.appElim (B := propT) (Typing.var 6) (Typing.var 1))))
  have reflCaseFormed : Typing R substContext
      (.app (.app substMotive (.var 3)) (.refl (.var 3))) U0 :=
    Typing.appElim (B := U0) (Typing.appElim motiveTyped (Typing.var 3))
      (Typing.reflIntro (Typing.var 3))
  have reflCase : Typing R substContext (.var 0)
      (.app (.app substMotive (.var 3)) (.refl (.var 3))) :=
    Typing.conv (Typing.var 0) reflCaseFormed (isUniverseAt Tower.zero)
      (.symm _ _ (beta_two _ _ _))
  have j0 := j_typed substContext
  rw [jType_eq] at j0
  have j1 := Typing.appElim j0 numT_typed
  have j2 := Typing.appElim j1 (Typing.var 3)
  have j3 := Typing.appElim j2 motiveTyped
  have j4 := Typing.appElim j3 reflCase
  have j5 := Typing.appElim j4 (Typing.var 2)
  have j6 := Typing.appElim j5 (Typing.var 1)
  exact Typing.conv j6 (proof_typed (Typing.appElim (B := propT) (Typing.var 4) (Typing.var 2)))
    (isUniverseAt Tower.zero) (beta_two _ _ _)

/-- The realization has the dependent reading of substitution as its type. -/
theorem substRealization_decoded : Typing R .nil substRealization substDecoded := by
  have formed₅ : Typing R (.snoc (.snoc (.snoc (.snoc .nil (.pi numT propT)) numT) numT)
      (.id numT (.var 1) (.var 0)))
      (.pi (Holds (.app (.var 3) (.var 2))) (Holds (.app (.var 4) (.var 2)))) U0 :=
    pi_at (proof_typed (Typing.appElim (B := propT) (Typing.var 3) (Typing.var 2)))
      (proof_typed (Typing.appElim (B := propT) (Typing.var 4) (Typing.var 2)))
  have formed₄ : Typing R (.snoc (.snoc (.snoc .nil (.pi numT propT)) numT) numT)
      (.pi (.id numT (.var 1) (.var 0))
        (.pi (Holds (.app (.var 3) (.var 2))) (Holds (.app (.var 4) (.var 2))))) U0 :=
    pi_at (id_at numT_typed (Typing.var 1) (Typing.var 0)) formed₅
  have formed₃ := pi_at (Γ := .snoc (.snoc .nil (.pi numT propT)) numT) numT_typed formed₄
  have formed₂ := pi_at (Γ := .snoc .nil (.pi numT propT)) numT_typed formed₃
  have formed₁ := pi_at (Γ := .nil) (pi_at numT_typed propT_typed) formed₂
  exact Typing.lamIntro formed₁ (isUniverseAt Tower.zero)
    (Typing.lamIntro formed₂ (isUniverseAt Tower.zero)
      (Typing.lamIntro formed₃ (isUniverseAt Tower.zero)
        (Typing.lamIntro formed₄ (isUniverseAt Tower.zero)
          (Typing.lamIntro formed₅ (isUniverseAt Tower.zero) substBody_typed))))

/-- Identity elimination realizes substitution under the identity reading. -/
theorem substRealization_typed :
    Typing identityRules .nil substRealization (Holds SetProfile.substCode) :=
  Typing.conv (toIdentity substRealization_decoded)
    (toIdentity (holds_formed (formula := SetProfile.substAxiom) rfl))
    (isUniverseAt Tower.zero)
    (.symm _ _ (toIdentity_runs (decodes SetProfile.signature holdsName proofToIdentity
      identity_decodes SetProfile.substAxiom rfl substAxiom_decoded)))

/-! ## Induction -/

/-- `λ m. Holds (P m)`, under the four binders `P z s x`. -/
def inductionMotive : Tower.Tm 4 := .lam (Holds (.app (.var 4) (.var 0)))

/-- `λ P z s x. num-rec (λ m. Holds (P m)) z s x`. -/
def inductionRealization : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (numRecApp inductionMotive (.var 2) (.var 1) (.var 0)))))

/-- `Π P. Holds (P zero) → (Π v. Holds (P v) → Holds (P (suc v))) → Π x. Holds (P x)`. -/
def inductionDecoded : Tower.Tm 0 :=
  .pi (.pi numT propT) (.pi (Holds (.app (.var 0) zeroNative))
    (.pi (.pi numT (.pi (Holds (.app (.var 2) (.var 0))) (Holds (.app (.var 3) (sucNative (.var 1))))))
      (.pi numT (Holds (.app (.var 3) (.var 0))))))

theorem inductionAxiom_decoded :
    decode SetProfile.signature holdsName SetProfile.inductionAxiom = some inductionDecoded :=
  rfl

/-- The context `P z s x` of the realization's body. -/
abbrev inductionContext : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil (.pi numT propT)) (Holds (.app (.var 0) zeroNative)))
    (.pi numT (.pi (Holds (.app (.var 2) (.var 0))) (Holds (.app (.var 3) (sucNative (.var 1)))))))
    numT

theorem inductionBody_typed :
    Typing R inductionContext (numRecApp inductionMotive (.var 2) (.var 1) (.var 0))
      (Holds (.app (.var 3) (.var 0))) := by
  have motiveTyped : Typing R inductionContext inductionMotive (.pi numT U0) :=
    predicateFamily_typed (Γ := inductionContext) (predicate := .var 3) (Typing.var 3)
  have r1 := Typing.appElim (numRec_typed inductionContext) motiveTyped
  have baseTyped : Typing R inductionContext (.var 2) (.app inductionMotive zeroNative) :=
    Typing.conv (Typing.var 2) (Typing.appElim (B := U0) motiveTyped zeroNative_typed)
      (isUniverseAt Tower.zero) (.symm _ _ (.rel _ _ (.betaPi _ _)))
  have r2 := Typing.appElim r1 baseTyped
  have shiftedFamily := predicateFamily_typed (Γ := .snoc inductionContext numT) (Typing.var 4)
  have shiftedFamily₂ := predicateFamily_typed
    (Γ := .snoc (.snoc inductionContext numT) (.app (.lam (Holds (.app (.var 5) (.var 0)))) (.var 0)))
    (Typing.var 5)
  have stepFormed : Typing R inductionContext
      (.pi numT (.pi (.app (.lam (Holds (.app (.var 5) (.var 0)))) (.var 0))
        (.app (.lam (Holds (.app (.var 6) (.var 0)))) (sucNative (.var 1))))) U0 :=
    pi_at numT_typed (pi_at (Typing.appElim (B := U0) shiftedFamily (Typing.var 0))
      (Typing.appElim (B := U0) shiftedFamily₂ (sucNative_typed (Typing.var 1))))
  have stepTyped : Typing R inductionContext (.var 1)
      (.pi numT (.pi (.app (.lam (Holds (.app (.var 5) (.var 0)))) (.var 0))
        (.app (.lam (Holds (.app (.var 6) (.var 0)))) (sucNative (.var 1))))) :=
    Typing.conv (Typing.var 1) stepFormed (isUniverseAt Tower.zero)
      (Conv.congPi (.refl _) (Conv.congPi (.symm _ _ (.rel _ _ (.betaPi _ _)))
        (.symm _ _ (.rel _ _ (.betaPi _ _)))))
  have r3 := Typing.appElim r2 stepTyped
  have r4 := Typing.appElim r3 (Typing.var 0)
  exact Typing.conv r4 (proof_typed (Typing.appElim (B := propT) (Typing.var 3) (Typing.var 0)))
    (isUniverseAt Tower.zero) (.rel _ _ (.betaPi _ _))

/-- The realization has the dependent reading of induction as its type. -/
theorem inductionRealization_decoded : Typing R .nil inductionRealization inductionDecoded := by
  have formed₄ : Typing R (.snoc (.snoc (.snoc .nil (.pi numT propT))
      (Holds (.app (.var 0) zeroNative)))
      (.pi numT (.pi (Holds (.app (.var 2) (.var 0))) (Holds (.app (.var 3) (sucNative (.var 1)))))))
      (.pi numT (Holds (.app (.var 3) (.var 0)))) U0 :=
    pi_at numT_typed (proof_typed (Typing.appElim (B := propT) (Typing.var 3) (Typing.var 0)))
  have stepType : Typing R (.snoc (.snoc .nil (.pi numT propT)) (Holds (.app (.var 0) zeroNative)))
      (.pi numT (.pi (Holds (.app (.var 2) (.var 0))) (Holds (.app (.var 3) (sucNative (.var 1))))))
      U0 :=
    pi_at numT_typed (pi_at (proof_typed (Typing.appElim (B := propT) (Typing.var 2) (Typing.var 0)))
      (proof_typed (Typing.appElim (B := propT) (Typing.var 3) (sucNative_typed (Typing.var 1)))))
  have formed₃ := pi_at stepType formed₄
  have formed₂ := pi_at (Γ := .snoc .nil (.pi numT propT))
    (proof_typed (Typing.appElim (B := propT) (Typing.var 0) zeroNative_typed)) formed₃
  have formed₁ := pi_at (Γ := .nil) (pi_at numT_typed propT_typed) formed₂
  exact Typing.lamIntro formed₁ (isUniverseAt Tower.zero)
    (Typing.lamIntro formed₂ (isUniverseAt Tower.zero)
      (Typing.lamIntro formed₃ (isUniverseAt Tower.zero)
        (Typing.lamIntro formed₄ (isUniverseAt Tower.zero) inductionBody_typed)))

/-- The recursor realizes induction in the program's own rules, without the
equation decoder: induction mentions no equation. -/
theorem inductionRealization_typed_program :
    Typing R .nil inductionRealization (Holds SetProfile.inductionCode) :=
  Typing.conv inductionRealization_decoded
    (holds_formed (formula := SetProfile.inductionAxiom) rfl) (isUniverseAt Tower.zero)
    (.symm _ _ (stepStar_implies_conv (decodes_equationFree SetProfile.signature holdsName
      proofToPackage SetProfile.inductionAxiom rfl rfl inductionAxiom_decoded)))

theorem inductionRealization_typed :
    Typing identityRules .nil inductionRealization (Holds SetProfile.inductionCode) :=
  toIdentity inductionRealization_typed_program

#print axioms reflRealization_typed
#print axioms substRealization_decoded
#print axioms substRealization_typed
#print axioms inductionRealization_decoded
#print axioms inductionRealization_typed_program

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Realizations
