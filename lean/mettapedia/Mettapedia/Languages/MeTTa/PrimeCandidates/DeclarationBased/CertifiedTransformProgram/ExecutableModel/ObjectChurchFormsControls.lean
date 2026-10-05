import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchForms

/-!
# Controls: the weak-head forms of the object package's annotated types

* **Positive: a universe variable matches itself as a neutral type** (`forms_varVar`), and
  not as a type former (`varVar_not_formersMatch`).
* **Positive: `Π num num` matches itself as a dependent function type with equal
  components** (`forms_piNumNum`).
* **Positive: the relation separates a universe variable from `Π num num`**, within `num`
  (`not_varEq_piNumNum_within`).
* **The least environment separates a universe variable, and a stuck decoder, from
  `Π num num`.** `X` and `holds x` denote the least element over the least environment, and
  `Π num num` a type with the tag of dependent function types
  (`bot_separates_varPi`, `holdsVar_bot`); soundness then refutes both equations in the whole
  package (`not_varEq_piNumNum`, `not_holdsVarEq_piNumNum`).
* **Negative: the relation read off the neutral side observes nothing.** Over the least
  environment, `X` is related to `Π num num` at every type token of the denotation of `X`
  (`neutralSide_vacuous`); at the tag of dependent function types, read off `Π num num`, it
  is not (`formerSide_separates`).
* **Negative: no environment separates `set` from the ground head.** The rigid neutral type
  `set` and the head `legacyGround` denote alike in every environment
  (`set_legacyGround_denote_alike`); the relation's ground clause separates them
  (`not_setEq_legacyGround_within`).
* **Two neutral types.** Two distinct universe variables match as neutral types
  (`forms_distinct_vars`), although they are not equal (`not_varEq_var`): the least
  environment does not separate them (`bot_same_vars`), an environment sending one of them
  to the numbers does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain

namespace CodeModel
namespace FormsControls

/-! ## Contexts and types -/

/-- The context `X : U₀`. -/
abbrev ctxX : CCtx Tower.Head 1 := .snoc .nil cU0

/-- The context `X : U₀, Y : U₀`. -/
abbrev ctxXY : CCtx Tower.Head 2 := .snoc ctxX cU0

/-- The context `x : prop`. -/
abbrev ctxP : CCtx Tower.Head 1 := .snoc .nil (.const propN)

/-- `Π (_ : num). num`. -/
abbrev cPiNumNum {n : Nat} : CTm Tower.Head n := .pi cnum cnum

/-- The decoder at a variable: `holds x`. -/
abbrev cHoldsVar : CTm Tower.Head 1 := .app (.const holdsN) (.var 0)

/-- The least environment. -/
abbrev botEnv (n : Nat) : Env n := fun _ => Ideal.bot

/-- No constant. -/
abbrev noConsts : DeclName → Bool := fun _ => false

theorem noConsts_adequate :
    ∀ {c : DeclName}, noConsts c = true → ConstAdequateAt objectChurchReading objectHeadReduction c :=
  fun h => absurd h Bool.false_ne_true

theorem numOnly_adequate :
    ∀ {c : DeclName}, allowedIn [numN] c = true →
      ConstAdequateAt objectChurchReading objectHeadReduction c :=
  consts_allowedIn fun c hc => by
    rw [List.mem_singleton] at hc
    subst hc
    exact constAdequateAt_num objectExtension

theorem setOnly_adequate :
    ∀ {c : DeclName}, allowedIn [setN] c = true →
      ConstAdequateAt objectChurchReading objectHeadReduction c :=
  consts_allowedIn fun c hc => by
    rw [List.mem_singleton] at hc
    subst hc
    exact constAdequateAt_set objectExtension

theorem ctxX_formed_within {A : DeclName → Bool} : CCtxFormed (objectChurch.restrict A) ctxX :=
  .snoc .nil ⟨_, .sort _, cU0_typed_within⟩

theorem ctxX_formed : CCtxFormed objectChurch ctxX :=
  .snoc .nil ⟨_, .sort _, .headType (.sort Tower.zero)⟩

theorem ctxXY_formed : CCtxFormed objectChurch ctxXY :=
  .snoc ctxX_formed ⟨_, .sort _, .headType (.sort Tower.zero)⟩

theorem ctxP_formed : CCtxFormed objectChurch ctxP :=
  .snoc .nil ⟨_, .sort _, const_U0_typed (by decide)⟩

theorem var_neutral {n : Nat} (i : Fin n) : Neutral objectRoles (CTm.var i : CTm Tower.Head n).erase :=
  .var i

/-- The least element has no tag. -/
theorem not_mem_bot_tag (k : Kind) : ¬ Ideal.bot.Mem (.tag k) := fun h => by
  have e : ent [] (.tag k) = true := h
  rw [ent_nil_tag] at e
  cases e

/-! ## Positive: matching forms -/

/-- **A universe variable matches itself as a neutral type.** -/
theorem forms_varVar : CFormsMatch objectChurch objectRoles ctxX (.var 0) (.var 0) :=
  ObjectExtension.formsMatch_within (X := objectExtension) noConsts_adequate ⟨_, .sort Tower.zero, .refl (.var 0)⟩
    ctxX_formed_within (.inr (.inr (.inr (.inr (.inl (var_neutral 0))))))
    (.inr (.inr (.inr (.inr (.inl (var_neutral 0))))))

/-- A universe variable does not match itself as a type former. -/
theorem varVar_not_formersMatch : ¬ CFormersMatch objectChurch ctxX (.var 0) (.var 0) := by
  rintro (⟨_, _, e, -⟩ | ⟨_, _, _, _, e, -⟩ | ⟨_, _, _, _, e, -⟩ | ⟨_, _, _, _, _, _, e, -⟩) <;>
    cases e

/-- **`Π num num` matches itself as a dependent function type with equal components.** -/
theorem forms_piNumNum :
    ∃ D E, (cPiNumNum : CTm Tower.Head 0) = .pi D E ∧ CTypeEq objectChurch .nil cnum D ∧
      CTypeEq objectChurch (.snoc .nil cnum) cnum E := by
  have m := ObjectExtension.formsMatch_within (X := objectExtension) numOnly_adequate
    ⟨_, .sort Tower.zero, .refl (cpiT_within (cnum_typed_within (by decide))
      (cnum_typed_within (by decide)))⟩ .nil (.inr (.inl ⟨_, _, rfl⟩)) (.inr (.inl ⟨_, _, rfl⟩))
  exact (m.formers_left (.pi _ _)).pi_left

/-- **The relation separates a universe variable from `Π num num`**, within `num`. -/
theorem not_varEq_piNumNum_within :
    ¬ CTypeEq (objectChurch.restrict (allowedIn [numN])) ctxX (.var 0) cPiNumNum := fun equal =>
  ObjectExtension.neutral_not_former_within (X := objectExtension) numOnly_adequate equal ctxX_formed_within
    (var_neutral 0) (.pi _ _)

/-! ## The least environment -/

/-- **The least environment separates `X` from `Π num num`**: `X` denotes the least element
there, and `Π num num` a type with the tag of dependent function types. -/
theorem bot_separates_varPi :
    cinterp objectChurchReading (.var 0 : CTm Tower.Head 1) (botEnv 1) ≠
      cinterp objectChurchReading cPiNumNum (botEnv 1) := by
  intro e
  have h : (cinterp objectChurchReading (cPiNumNum : CTm Tower.Head 1) (botEnv 1)).Mem (.tag .pi) :=
    Ideal.mem_former_tag _ _ _
  rw [← e] at h
  exact not_mem_bot_tag .pi h

/-- **A universe variable is not `Π num num`**, in the whole package, by soundness over the
least environment. -/
theorem not_varEq_piNumNum : ¬ CTypeEq objectChurch ctxX (.var 0) cPiNumNum := by
  rintro ⟨u, -, e⟩
  exact bot_separates_varPi
    (objectChurch_soundnessFacts.equality e _ (Fits.bot objectChurch_soundnessFacts ctxX_formed))

/-- The decoder at a variable is a neutral type: it is stuck on the variable. -/
theorem holdsVar_neutral : Neutral objectRoles cHoldsVar.erase :=
  Neutral.stuck_single (before := []) (after := []) objectRoles_holds rfl (.var 0)

/-- **The decoder at a variable denotes no dependent function type** over the least
environment: its denotation is the least element projected twice. -/
theorem holdsVar_bot : ¬ (cinterp objectChurchReading cHoldsVar (botEnv 1)).Mem (.tag .pi) := by
  intro h
  change (Ideal.app (objectChurchReading.const holdsN) Ideal.bot).Mem _ at h
  rw [objectChurchReading_holds, Ideal.app_holdsConst] at h
  exact not_mem_bot_tag .pi (Ideal.projT_le _ _ _ (Ideal.projT_le _ _ _ h))

/-- **A stuck decoder is not `Π num num`**, in the whole package, by soundness over the least
environment. -/
theorem not_holdsVarEq_piNumNum : ¬ CTypeEq objectChurch ctxP cHoldsVar cPiNumNum := by
  rintro ⟨u, -, e⟩
  have h := objectChurch_soundnessFacts.equality e _ (Fits.bot objectChurch_soundnessFacts ctxP_formed)
  have hmem : (cinterp objectChurchReading (cPiNumNum : CTm Tower.Head 1) (botEnv 1)).Mem (.tag .pi) :=
    Ideal.mem_former_tag _ _ _
  rw [← h] at hmem
  exact holdsVar_bot hmem

/-! ## Negative: the neutral side observes nothing -/

/-- **The relation read off the neutral side observes nothing**: over the least environment,
`X` is related to `Π num num` at every type token of the denotation of `X`. -/
theorem neutralSide_vacuous :
    ∀ r, (cinterp objectChurchReading (.var 0 : CTm Tower.Head 1) (botEnv 1)).Mem r →
      RT objectHeadReduction ctxX false r (.var 0) (.var 0) cPiNumNum :=
  fun _ hr => RT.of_vacuous hr

/-- **The relation read off the former's side separates**: at the tag of dependent function
types, `Π num num` is not related to `X`, which takes no head step. -/
theorem formerSide_separates :
    ¬ RT objectHeadReduction ctxX false (.tag .pi) cPiNumNum cPiNumNum (.var 0) := by
  intro h
  obtain ⟨D, E, D', E', hp⟩ := RT.ty_pi_iff.1 h
  have e := objectHeadReduction.red_normal (objectExtension.neutralNormal (var_neutral 0))
    hp.2.1.1
  cases e

/-! ## Negative: no environment separates `set` from the ground head -/

/-- **`set` and the ground head denote alike in every environment.** -/
theorem set_legacyGround_denote_alike {n : Nat} (ρ : Env n) :
    cinterp objectChurchReading (cset : CTm Tower.Head n) ρ =
      cinterp objectChurchReading (.head .legacyGround) ρ := by
  rw [cinterp_cset]
  rfl

/-- `set` is a neutral type: a rigid constant. -/
theorem set_neutral {n : Nat} : Neutral objectRoles (cset : CTm Tower.Head n).erase :=
  Neutral.rigid [] objectRoles_setRigid

/-- **The relation separates `set` from the ground head**, within `set`: its ground clause
reduces both to one ground type, and each is normal. -/
theorem not_setEq_legacyGround_within :
    ¬ CTypeEq (objectChurch.restrict (allowedIn [setN])) (.nil : CCtx Tower.Head 0) cset
      (.head .legacyGround) := fun equal =>
  ObjectExtension.neutral_not_former_within (X := objectExtension) setOnly_adequate equal .nil set_neutral (.head _)

/-! ## Two neutral types -/

/-- **Two distinct universe variables match as neutral types.** -/
theorem forms_distinct_vars : CFormsMatch objectChurch objectRoles ctxXY (.var 1) (.var 0) :=
  .inr (.inr ⟨var_neutral 1, var_neutral 0⟩)

/-- **The least environment does not separate two universe variables.** -/
theorem bot_same_vars :
    cinterp objectChurchReading (.var 1 : CTm Tower.Head 2) (botEnv 2) =
      cinterp objectChurchReading (.var 0) (botEnv 2) :=
  rfl

/-- The environment sending `X` to the least element and `Y` to the numbers. -/
abbrev envXY : Env 2 := Env.cons Ideal.natI (Env.cons Ideal.bot Env.nil)

theorem envXY_fits : Fits objectChurchReading ctxXY envXY :=
  Fits.cons (Fits.cons trivial Ideal.typeGenerated_univIdeal
      (Ideal.le_antisymm (Ideal.projT_le _ _) (Ideal.bot_le _)))
    Ideal.typeGenerated_univIdeal (Ideal.projT_univ_eq_self_iff.2 Ideal.typeGenerated_natI)

/-- **Two distinct universe variables are not equal types**: an environment sending one of
them to the numbers separates them. -/
theorem not_varEq_var : ¬ CTypeEq objectChurch ctxXY (.var 1) (.var 0) := by
  rintro ⟨u, -, e⟩
  have h : Ideal.bot = Ideal.natI := objectChurch_soundnessFacts.equality e envXY envXY_fits
  have hmem : Ideal.natI.Mem (.tag .nat) := Ideal.mem_principal_tag.2 rfl
  rw [← h] at hmem
  exact not_mem_bot_tag .nat hmem

end FormsControls
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
