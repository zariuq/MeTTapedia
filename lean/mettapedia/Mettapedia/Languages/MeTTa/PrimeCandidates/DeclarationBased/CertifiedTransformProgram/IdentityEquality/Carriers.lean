import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Realizations
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Preservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms

/-!
# Equality facts at every carrier

The proof library publishes reflexivity `refl@T` and substitution `subst@T`
for each carrier `T` it is given, and expands symmetry, transitivity,
congruence and calculations into them.  Under the identity reading both are
realized at every simple type, including function types:

* reflexivity by `λ x. refl x` (`FormationSensitiveHOLIdentityEquality.refl_realizes`);
* substitution by identity elimination at the carrier,
  `λ P x y e h. id:eliminate T x (λ y p. Holds (P y)) h y e`.

Identity elimination is typed at an arbitrary carrier by instantiating the
declared telescope of `id:eliminate` with the actual arguments.  At `num` the
realization is the one the zero-add document links.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Carriers

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence
open FormationSensitiveHOLInterface (typeAt typeAt_rename)
open SetProfile (holdsName)
open CertifiedTransformProgram.Package CertifiedTransformProgram.IdentityEquality
open CertifiedTransformProgram.IdentityEquality.Realizations
open FormationSensitiveHOLIdentityEquality (decode decodes)
open Mettapedia.Logic

/-! ## Identity elimination at any carrier -/

/-- `id:eliminate A x P d y e : P y e`, for every carrier `A`, point `x`,
motive `P`, method `d : P x (refl x)`, endpoint `y` and path `e : Id A x y`. -/
theorem j_at {n : Nat} {Γ : Tower.Ctx n}
    {base point motive method endpoint path : Tower.Tm n} {shiftedBase shiftedPoint : Tower.Tm (n + 1)}
    (baseShift : rename wk base = shiftedBase) (pointShift : rename wk point = shiftedPoint)
    (baseTyped : Typing R Γ base U0) (pointTyped : Typing R Γ point base)
    (motiveTyped : Typing R Γ motive
      (.pi base (.pi (.id shiftedBase shiftedPoint (.var 0)) U0)))
    (methodTyped : Typing R Γ method (.app (.app motive point) (.refl point)))
    (endpointTyped : Typing R Γ endpoint base)
    (pathTyped : Typing R Γ path (.id base point endpoint)) :
    Typing R Γ (jApp base point motive method endpoint path)
      (.app (.app motive endpoint) path) := by
  subst baseShift pointShift
  have empty : FormationSensitive.CtxMor R (.nil : Tower.Ctx 0) Γ (fun index => Fin.elim0 index) :=
    fun index => Fin.elim0 index
  have morphism : FormationSensitive.CtxMor R Preservation.jDeclarationTelescope Γ
      (consSub path (consSub endpoint (consSub method (consSub motive
        (consSub point (consSub base (fun index => Fin.elim0 index))))))) :=
    (((((empty.extend (type := U0) baseTyped).extend (type := .var 0) pointTyped).extend
      (type := .pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) U0)) motiveTyped).extend
      (type := .app (.app (.var 0) (.var 1)) (.refl (.var 1))) methodTyped).extend
      (type := .var 3) endpointTyped).extend (type := .id (.var 4) (.var 3) (.var 0)) pathTyped
  have spine := j_typed Γ
  rw [Preservation.jType_close] at spine
  exact FormationCheckedTelescopePrograms.apply_typed morphism spine

/-! ## Substitution at a carrier -/

section Carrier

variable (type : HOL.Ty SetProfile.SetBase)

/-- The interpreted carrier of a simple type, at any depth. -/
abbrev carrier {n : Nat} : Tower.Tm n := typeAt SetProfile.types n type

theorem carrier_typed {n : Nat} {Γ : Tower.Ctx n} : Typing R Γ (carrier type) U0 :=
  include_profile (SetProfile.simple_formed type Γ)

/-- `subst@T : ∀ P : T → prop. ∀ x y : T. x = y → P x → P y`. -/
def substitution : HOL.Formula SetProfile.SetConst [] :=
  .all (σ := .arr type .prop) (.all (σ := type) (.all (σ := type)
    (.imp (.eq (.var (.vs .vz)) (.var .vz))
      (.imp (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (.app (.var (.vs (.vs .vz))) (.var .vz))))))

theorem substitution_num : substitution SetProfile.numTy = SetProfile.substAxiom := rfl

/-- `λ P x y e h. id:eliminate T x (λ y p. Holds (P y)) h y e`. -/
def substRealizationAt : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam
    (jApp (carrier type) (.var 3) substMotive (.var 0) (.var 2) (.var 1))))))

theorem substRealizationAt_num : substRealizationAt SetProfile.numTy = substRealization := rfl

/-- `Π P : T → prop. Π x y : T. Id T x y → Holds (P x) → Holds (P y)`. -/
def substDecodedAt : Tower.Tm 0 :=
  .pi (.pi (carrier type) propT) (.pi (carrier type) (.pi (carrier type)
    (.pi (.id (carrier type) (.var 1) (.var 0))
      (.pi (Holds (.app (.var 3) (.var 2))) (Holds (.app (.var 4) (.var 2)))))))

theorem substitution_decoded :
    decode SetProfile.signature holdsName (substitution type) = some (substDecodedAt type) :=
  rfl

/-- The contexts `P`, `P x`, `P x y`, `P x y e` and `P x y e h` of the realization. -/
abbrev context₁ : Tower.Ctx 1 := .snoc .nil (.pi (carrier type) propT)
abbrev context₂ : Tower.Ctx 2 := .snoc (context₁ type) (carrier type)
abbrev context₃ : Tower.Ctx 3 := .snoc (context₂ type) (carrier type)
abbrev context₄ : Tower.Ctx 4 := .snoc (context₃ type) (.id (carrier type) (.var 1) (.var 0))
abbrev substContextAt : Tower.Ctx 5 := .snoc (context₄ type) (Holds (.app (.var 3) (.var 2)))

theorem substBodyAt_typed :
    Typing R (substContextAt type)
      (jApp (carrier type) (.var 3) substMotive (.var 0) (.var 2) (.var 1))
      (Holds (.app (.var 4) (.var 2))) := by
  have predicate : Typing R (substContextAt type) (.var 4) (.pi (carrier type) propT) := by
    have raw := Typing.var (R := R) (Γ := substContextAt type) 4
    change Typing R _ _ (rename wk (rename wk (rename wk (rename wk (rename wk
      (.pi (carrier type) propT)))))) at raw
    simpa only [Presentation.rename, typeAt_rename] using raw
  have point : Typing R (substContextAt type) (.var 3) (carrier type) := by
    have raw := Typing.var (R := R) (Γ := substContextAt type) 3
    change Typing R _ _ (rename wk (rename wk (rename wk (rename wk (carrier type))))) at raw
    simpa only [typeAt_rename] using raw
  have endpoint : Typing R (substContextAt type) (.var 2) (carrier type) := by
    have raw := Typing.var (R := R) (Γ := substContextAt type) 2
    change Typing R _ _ (rename wk (rename wk (rename wk (carrier type)))) at raw
    simpa only [typeAt_rename] using raw
  have path : Typing R (substContextAt type) (.var 1) (.id (carrier type) (.var 3) (.var 2)) := by
    have raw := Typing.var (R := R) (Γ := substContextAt type) 1
    change Typing R _ _ (rename wk (rename wk (.id (carrier type) (.var 1) (.var 0)))) at raw
    simp only [Presentation.rename, typeAt_rename] at raw
    exact raw
  -- The motive `λ y p. Holds (P y)` over the carrier.
  have motiveFormed₂ : Typing R (.snoc (substContextAt type) (carrier type))
      (.pi (.id (carrier type) (.var 4) (.var 0)) U0) U1 := by
    have shiftedPoint : Typing R (.snoc (substContextAt type) (carrier type)) (.var 4)
        (carrier type) := by
      have lifted := point.weaken (extension := carrier type)
      simp only [typeAt_rename] at lifted
      exact lifted
    have newest : Typing R (.snoc (substContextAt type) (carrier type)) (.var 0)
        (carrier type) := by
      simpa only [Ctx.lookup_snoc_zero, typeAt_rename] using
        Typing.var (R := R) (Γ := .snoc (substContextAt type) (carrier type)) 0
    exact pi_at (raise (id_at (carrier_typed type) shiftedPoint newest)) U0_typed
  have motiveFormed : Typing R (substContextAt type)
      (.pi (carrier type) (.pi (.id (carrier type) (.var 4) (.var 0)) U0)) U1 :=
    pi_at (raise (carrier_typed type)) motiveFormed₂
  have motiveBody : Typing R (.snoc (.snoc (substContextAt type) (carrier type))
      (.id (carrier type) (.var 4) (.var 0))) (Holds (.app (.var 6) (.var 1))) U0 := by
    have predicate' : Typing R (.snoc (.snoc (substContextAt type) (carrier type))
        (.id (carrier type) (.var 4) (.var 0))) (.var 6) (.pi (carrier type) propT) := by
      have lifted := (predicate.weaken (extension := carrier type)).weaken
        (extension := .id (carrier type) (.var 4) (.var 0))
      simp only [Presentation.rename, typeAt_rename] at lifted
      exact lifted
    have argument : Typing R (.snoc (.snoc (substContextAt type) (carrier type))
        (.id (carrier type) (.var 4) (.var 0))) (.var 1) (carrier type) := by
      have raw := Typing.var (R := R) (Γ := .snoc (.snoc (substContextAt type) (carrier type))
        (.id (carrier type) (.var 4) (.var 0))) 1
      change Typing R _ _ (rename wk (rename wk (carrier type))) at raw
      simpa only [typeAt_rename] using raw
    exact proof_typed (Typing.appElim (B := propT) predicate' argument)
  have motiveTyped : Typing R (substContextAt type) substMotive
      (.pi (carrier type) (.pi (.id (carrier type) (.var 4) (.var 0)) U0)) :=
    Typing.lamIntro motiveFormed (isUniverseAt level1)
      (Typing.lamIntro motiveFormed₂ (isUniverseAt level1) motiveBody)
  have atPoint : Typing R (substContextAt type) (.app substMotive (.var 3))
      (.pi (.id (carrier type) (.var 3) (.var 3)) U0) := by
    have applied := Typing.appElim motiveTyped point
    have shape : (inst0 (.var 3) (.pi (.id (carrier type) (.var 4) (.var 0)) U0) : Tower.Tm 5) =
        .pi (.id (carrier type) (.var 3) (.var 3)) U0 := by
      simp only [inst0, Presentation.subst, FormationSensitiveHOLInterface.typeAt_subst]
      rfl
    rw [shape] at applied
    exact applied
  have reflCaseFormed : Typing R (substContextAt type)
      (.app (.app substMotive (.var 3)) (.refl (.var 3))) U0 :=
    Typing.appElim (B := U0) atPoint (Typing.reflIntro point)
  have reflCase : Typing R (substContextAt type) (.var 0)
      (.app (.app substMotive (.var 3)) (.refl (.var 3))) :=
    Typing.conv (Typing.var 0) reflCaseFormed (isUniverseAt Tower.zero)
      (.symm _ _ (beta_two _ _ _))
  have eliminated := j_at (typeAt_rename SetProfile.types wk type) rfl (carrier_typed type) point
    motiveTyped reflCase endpoint path
  exact Typing.conv eliminated
    (proof_typed (Typing.appElim (B := propT) predicate endpoint))
    (isUniverseAt Tower.zero) (beta_two _ _ _)

/-- The realization has the dependent reading of substitution at `T`. -/
theorem substRealizationAt_decoded :
    Typing R .nil (substRealizationAt type) (substDecodedAt type) := by
  have predicate₄ : Typing R (context₄ type) (.var 3) (.pi (carrier type) propT) := by
    have raw := Typing.var (R := R) (Γ := context₄ type) 3
    change Typing R _ _ (rename wk (rename wk (rename wk (rename wk
      (.pi (carrier type) propT))))) at raw
    simpa only [Presentation.rename, typeAt_rename] using raw
  have point₄ : Typing R (context₄ type) (.var 2) (carrier type) := by
    have raw := Typing.var (R := R) (Γ := context₄ type) 2
    change Typing R _ _ (rename wk (rename wk (rename wk (carrier type)))) at raw
    simpa only [typeAt_rename] using raw
  have predicate₅ : Typing R (substContextAt type) (.var 4) (.pi (carrier type) propT) := by
    have lifted := predicate₄.weaken (extension := Holds (.app (.var 3) (.var 2)))
    simp only [Presentation.rename, typeAt_rename] at lifted
    exact lifted
  have endpoint₅ : Typing R (substContextAt type) (.var 2) (carrier type) := by
    have raw := Typing.var (R := R) (Γ := substContextAt type) 2
    change Typing R _ _ (rename wk (rename wk (rename wk (carrier type)))) at raw
    simpa only [typeAt_rename] using raw
  have formed₅ : Typing R (context₄ type)
      (.pi (Holds (.app (.var 3) (.var 2))) (Holds (.app (.var 4) (.var 2)))) U0 :=
    pi_at (proof_typed (Typing.appElim (B := propT) predicate₄ point₄))
      (proof_typed (Typing.appElim (B := propT) predicate₅ endpoint₅))
  have point₃ : Typing R (context₃ type) (.var 1) (carrier type) := by
    have raw := Typing.var (R := R) (Γ := context₃ type) 1
    change Typing R _ _ (rename wk (rename wk (carrier type))) at raw
    simpa only [typeAt_rename] using raw
  have endpoint₃ : Typing R (context₃ type) (.var 0) (carrier type) := by
    simpa only [Ctx.lookup_snoc_zero, typeAt_rename] using
      Typing.var (R := R) (Γ := context₃ type) 0
  have formed₄ := pi_at (Γ := context₃ type) (id_at (carrier_typed type) point₃ endpoint₃) formed₅
  have formed₃ := pi_at (Γ := context₂ type) (carrier_typed type) formed₄
  have formed₂ := pi_at (Γ := context₁ type) (carrier_typed type) formed₃
  have formed₁ := pi_at (Γ := .nil) (pi_at (carrier_typed type) propT_typed) formed₂
  exact Typing.lamIntro formed₁ (isUniverseAt Tower.zero)
    (Typing.lamIntro formed₂ (isUniverseAt Tower.zero)
      (Typing.lamIntro formed₃ (isUniverseAt Tower.zero)
        (Typing.lamIntro formed₄ (isUniverseAt Tower.zero)
          (Typing.lamIntro formed₅ (isUniverseAt Tower.zero) (substBodyAt_typed type)))))

theorem substitution_represented :
    ∃ code, FormationSensitiveHOLInterface.represent SetProfile.signature (substitution type) =
      some code :=
  ⟨_, rfl⟩

/-- Identity elimination realizes substitution at every carrier, under the
identity reading. -/
theorem substRealizationAt_typed {code : Tower.Tm 0}
    (represented : FormationSensitiveHOLInterface.represent SetProfile.signature
      (substitution type) = some code) :
    Typing identityRules .nil (substRealizationAt type) (Holds code) :=
  Typing.conv (toIdentity (substRealizationAt_decoded type))
    (toIdentity (holds_formed represented)) (isUniverseAt Tower.zero)
    (.symm _ _ (toIdentity_runs (decodes SetProfile.signature holdsName proofToIdentity
      identity_decodes (substitution type) represented (substitution_decoded type))))

end Carrier

#print axioms j_at
#print axioms substRealizationAt_decoded
#print axioms substRealizationAt_typed

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Carriers
