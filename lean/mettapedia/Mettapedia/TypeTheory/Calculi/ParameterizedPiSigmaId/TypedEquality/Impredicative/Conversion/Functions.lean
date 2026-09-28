import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Formers

/-!
# Dependent functions in the conversion model

A dependent function type denotes, at every world reached by a morphism, the
functions that send related valid arguments to related results. Its realizers
are Girard's clause over the valid arguments: at a realizer type reducing to
`Π D C`, terms reaching weak-head normal functions, related by the generic
equality, whose applications, after every renaming into a formed context, to
arguments realizing a valid argument, realize the result (`PiPack.real_rel_pi`).

**The generic equality comes from the applications.** Two terms reaching
weak-head normal functions are related by the generic equality at `Π D C` when
their weakened applications to the fresh variable are related at `C`
(`convTm_pi_of_app`): the applications reduce, typed, to the applications of
the normal forms, which the generic equality relates since it respects typed
reduction; the normal forms are then related by extensionality, and the terms
by expansion. The fresh variable realizes the daimon, a valid argument of every
domain, so the clause of the applications gives the generic equality
(`PiPack.real_of_clause`).

**Abstractions.** An abstraction of realizers realizes an abstraction when its
body, instantiated at the realizers of a valid argument, realizes the
instantiated body of the value: each application β-reduces, typed, to the
instantiated body, and the application of the value and its instantiated body
are related values, so they have the same realizers.

**Applications.** Realizers of a function applied to realizers of a valid
argument realize the application, at the codomain instantiated at the first
argument (`DenN.pi_app_real`).

From these: validity of λ-abstraction and application, their congruences, β
and η.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization hiding World
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open ValueSide (universeAt)

variable {Head L : Type} [LevelOrder L]

/-! ## Functions on the realizer side -/

section Realizers

variable {T : RealizerSide Head L}

/-- A λ-abstraction of a dependent function type, renamed and applied to an
argument of the renamed domain, reduces, typed, to its body instantiated at the
argument. -/
theorem RedTm.lam_app {m k : Nat} {Δ : Ctx Head m} {Θ : Ctx Head k} {ρ : Ren m k}
    {D : Tm Head m} {b C : Tm Head (m + 1)} {u : Head}
    (pi : Typed T.R Δ (.pi D C) (.head u)) (hu : T.R.isUniverse u)
    (body : Typed T.R (.snoc Δ D) b C) (ren : CtxRen Δ Θ ρ) {s : Tm Head k}
    (ts : Typed T.R Θ s (Presentation.rename ρ D)) :
    RedTm T.R T.roles Θ (.app (Presentation.rename ρ (.lam b)) s)
      (inst0 s (Presentation.rename (liftRen ρ) b))
      (inst0 s (Presentation.rename (liftRen ρ) C)) :=
  RedTm.beta (Typed.rename pi ren) hu (Typed.rename body (CtxRen.snoc ren D)) ts

/-- A λ-abstraction of a dependent function type, weakened and applied to the
fresh variable, reduces, typed, to its body. -/
theorem RedTm.lam_var {m : Nat} {Δ : Ctx Head m} {D : Tm Head m} {b C : Tm Head (m + 1)}
    {u : Head} (pi : Typed T.R Δ (.pi D C) (.head u)) (hu : T.R.isUniverse u)
    (body : Typed T.R (.snoc Δ D) b C) :
    RedTm T.R T.roles (.snoc Δ D) (.app (Presentation.rename wk (.lam b)) (.var 0)) b C := by
  have h := RedTm.lam_app pi hu body (CtxRen.wk Δ D)
    (Derivable.var (R := T.R) (Γ := .snoc Δ D) 0)
  rwa [inst0_var_rename_liftRen_wk, inst0_var_rename_liftRen_wk] at h

/-- Typed reduction of a function, weakened and applied to the fresh variable of
its domain. -/
theorem RedTm.app_var {m : Nat} {Δ : Ctx Head m} {t w D : Tm Head m} {C : Tm Head (m + 1)}
    (red : RedTm T.R T.roles Δ t w (.pi D C)) :
    RedTm T.R T.roles (.snoc Δ D) (.app (Presentation.rename wk t) (.var 0))
      (.app (Presentation.rename wk w) (.var 0)) C := by
  have h := (red.rename (CtxRen.wk Δ D)).app (Derivable.var (R := T.R) (Γ := .snoc Δ D) 0)
  rwa [inst0_var_rename_liftRen_wk] at h

/-- **The generic equality at a dependent function type from the application
to the fresh variable**: two terms reaching weak-head normal functions are
related when their weakened applications to the fresh variable are. -/
theorem convTm_pi_of_app {m : Nat} {Δ : Ctx Head m} {X t t' D : Tm Head m}
    {C : Tm Head (m + 1)} (hX : RedTy T.R T.roles Δ X (.pi D C)) (fn : FunNf T Δ X t)
    (fn' : FunNf T Δ X t')
    (app : T.E.convTm (.snoc Δ D) (.app (Presentation.rename wk t) (.var 0))
      (.app (Presentation.rename wk t') (.var 0)) C) :
    T.E.convTm Δ t t' X := by
  obtain ⟨w, r, fw⟩ := fn
  obtain ⟨w', r', fw'⟩ := fn'
  have e := hX.typeEq
  have r₁ := r.conv e
  have r₁' := r'.conv e
  obtain ⟨typeD, typeC⟩ := IsType.pi_parts hX.targetType
  have eta := T.laws.convTm_etaPi typeD typeC r₁.target fw r₁'.target fw'
    (T.reduce (RedTm.app_var r₁) (RedTm.app_var r₁') app)
  exact T.laws.convTm_conv (T.laws.convTm_expand r₁ r₁' eta) e.symm

/-- Equal arguments instantiate the codomain of a type reducing to `Π D C` at
equal types. -/
theorem pi_codEq_here {m : Nat} {Δ : Ctx Head m} {X D : Tm Head m} {C : Tm Head (m + 1)}
    (hX : RedTy T.R T.roles Δ X (.pi D C)) {s s' : Tm Head m} (ts : Typed T.R Δ s D)
    (e : Equal T.R Δ s s' D) : TypeEq T.R Δ (Presentation.inst0 s C) (Presentation.inst0 s' C) := by
  obtain ⟨-, v, hv, tC⟩ := IsType.pi_parts hX.targetType
  exact TypeEq.of_instantiateEq tC hv ts e

end Realizers

variable {M : NModel Head L}

/-! ## Functions in a world -/

namespace PiPack

variable {n : Nat} {ξ : World M.reading n} (Q : ValueSide.PiPack M.value ξ)

/-- **The realizers of a function from the clause of its applications**: at a
realizer type reducing to `Π D C` of a formed context, two terms reaching
weak-head normal functions are related by the realizers of a function when
their applications satisfy the clause at every valid argument, provided the
domain has a valid value at the world itself. -/
theorem real_of_clause {f : Tm Head n} {m : Nat} {Δ : Ctx Head m} {X t t' D : Tm Head m}
    {C : Tm Head (m + 1)} (hX : RedTy M.side.R M.side.roles Δ X (.pi D C))
    (formed : CtxFormed M.side.R Δ) {v : Tm Head n} (hv : (Q.dom (Morph.id ξ)).Val v)
    (fn : FunNf M.side Δ X t) (fn' : FunNf M.side Δ X t')
    (app : ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren n k} (w : Morph ξ ξ' ρ)
      {a : Tm Head k} (ha : (Q.dom w).Val a),
      AppClause ((Q.dom w).real a) ((Q.cod w ha).real (.app (Presentation.rename ρ f) a))
        Δ D C t t') :
    (Q.real f).rel Δ X t t' := by
  refine (PiPack.real_rel_pi Q f hX).mpr ⟨fn, fn', ?_, app⟩
  obtain ⟨typeD, -⟩ := IsType.pi_parts hX.targetType
  have world : Normalization.World M.side.toSetting Δ (.snoc Δ D) wk :=
    ⟨CtxRen.wk Δ D, .snoc formed typeD⟩
  have h := app (Morph.id ξ) hv world
    (((Q.dom (Morph.id ξ)).real v).var 0 (Derivable.var (R := M.side.R) (Γ := .snoc Δ D) 0))
  rw [inst0_var_rename_liftRen_wk] at h
  exact convTm_pi_of_app hX fn fn' (((Q.cod (Morph.id ξ) hv).real _).escape h)

end PiPack

section World

variable (laws : M.Laws)
include laws

/-- Related functions send related arguments to results related at the codomain
instantiated at the first argument, and their realizers applied to related
realizers of the arguments realize the result. -/
theorem DenN.pi_app_real {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : NPack M n} (den : DenN M ξ (.pi A B) P) {f a : Tm Head n}
    {m : Nat} {Δ : Ctx Head m} (formed : CtxFormed M.side.R Δ) {X t t' D : Tm Head m}
    {C : Tm Head (m + 1)} (hX : RedTy M.side.R M.side.roles Δ X (.pi D C))
    (hf : (P.real f).rel Δ X t t') {s s' : Tm Head m}
    (ha : ∀ {PA : NPack M n}, DenN M ξ A PA → PA.Val a ∧ (PA.real a).rel Δ D s s')
    {PB : NPack M n} (denB : DenN M ξ (inst0 a B) PB) :
    (PB.real (.app f a)).rel Δ (inst0 s C) (.app t s) (.app t' s') := by
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.pi_inv laws.value den
  have domI : DenN M ξ A (Q.dom (Morph.id ξ)) := ⟨l, interprets.dom_id⟩
  obtain ⟨va, hs⟩ := ha domI
  rw [ValueSide.DenS.deterministic laws.value denB ⟨l, interprets.cod_id va⟩]
  obtain ⟨-, -, -, app⟩ := (PiPack.real_rel_pi Q f hX).mp hf
  have h := app (Morph.id ξ) va ⟨CtxRen.id Δ, formed⟩ (by rwa [rename_id])
  simp only [rename_id, liftRen_id] at h
  exact h

/-! ## Abstractions under valuations -/

/-- Under related valuations, abstractions are related at a dependent function
type when their bodies are related under all related valuations for the
extended context. -/
theorem DenN.pi_lam {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {body body' B : Tm Head (n + 1)}
    (bodies : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head (n + 1) m}
      {Δ : Ctx Head r} {ς ς' : Sub Head (n + 1) r}, EqSubstN M (.snoc Γ A) ξ σ σ' Δ ς ς' →
        ∀ {P : NPack M m}, DenN M ξ (Presentation.subst σ B) P →
          P.rel (Presentation.subst σ body) (Presentation.subst σ' body'))
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r} (e : EqSubstN M Γ ξ σ σ' Δ ς ς')
    (typeA : IsType M.side.R Δ (Presentation.subst ς A)) {P : NPack M m}
    (den : DenN M ξ (Presentation.subst σ (.pi A B)) P) :
    P.rel (Presentation.subst σ (.lam body)) (Presentation.subst σ' (.lam body')) := by
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.pi_inv laws.value den
  refine ValueSide.PiPack.rel_lam laws.value interprets.cod ?_
  intro k ξ' ρ w a b ha hab
  have domI := interprets.dom w
  have codI := interprets.cod w ha
  rw [rename_subst] at domI
  rw [inst0_rename_subst_liftSub] at codI
  rw [inst0_rename_subst_liftSub, inst0_rename_subst_liftSub]
  exact bodies ((EqSubstN.rename laws e w).consVar typeA ⟨l, domI⟩ hab) ⟨l, codI⟩

/-- **Under related valuations, the realizer instances of an abstraction realize
its first value at a dependent function type** when, under all related
valuations for the extended context, the body is related to itself, with
related realizer instances. -/
theorem DenN.pi_lam_real {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {body body' B : Tm Head (n + 1)}
    (bodies : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head (n + 1) m}
      {Δ : Ctx Head r} {ς ς' : Sub Head (n + 1) r}, EqSubstN M (.snoc Γ A) ξ σ σ' Δ ς ς' →
        ∀ {P : NPack M m}, DenN M ξ (Presentation.subst σ B) P →
          P.Related (Presentation.subst σ body) (Presentation.subst σ' body') Δ
            (Presentation.subst ς B) (Presentation.subst ς body) (Presentation.subst ς' body'))
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
    {ς ς' : Sub Head n r} (e : EqSubstN M Γ ξ σ σ' Δ ς ς')
    {u : Head} (hu : M.side.R.isUniverse u)
    (typePi : Typed M.side.R Δ (Presentation.subst ς (.pi A B)) (.head u)) {P : NPack M m}
    (den : DenN M ξ (Presentation.subst σ (.pi A B)) P) :
    (P.real (Presentation.subst σ (.lam body))).rel Δ (Presentation.subst ς (.pi A B))
      (Presentation.subst ς (.lam body)) (Presentation.subst ς' (.lam body')) := by
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.pi_inv laws.value den
  have formed := e.formed
  obtain ⟨typeA, -⟩ := IsType.pi_parts ⟨u, hu, typePi⟩
  have hX : RedTy M.side.R M.side.roles Δ (Presentation.subst ς (.pi A B))
      (.pi (Presentation.subst ς A) (Presentation.subst (liftSub ς) B)) :=
    RedTy.refl ⟨u, hu, typePi⟩
  -- The body at the daimon, realized by the fresh variable: the typings of the bodies.
  have domI₀ := interprets.dom (Morph.id ξ)
  rw [rename_subst] at domI₀
  have star := ValueSide.DenS.star_val laws.value ⟨l, domI₀⟩
  have codI₀ := interprets.cod (Morph.id ξ) star
  rw [inst0_rename_subst_liftSub] at codI₀
  have fresh := (bodies ((EqSubstN.rename laws e (Morph.id ξ)).consVar typeA ⟨l, domI₀⟩ star)
    ⟨l, codI₀⟩).2
  rw [consSub_var_wk, consSub_var_wk] at fresh
  obtain ⟨tBody, tBody'⟩ := (ECand.typed _) fresh
  have tLam : Typed M.side.R Δ (Presentation.subst ς (.lam body))
      (Presentation.subst ς (.pi A B)) := .lamIntro typePi hu tBody
  have tLam' : Typed M.side.R Δ (Presentation.subst ς' (.lam body'))
      (Presentation.subst ς (.pi A B)) := .lamIntro typePi hu tBody'
  refine PiPack.real_of_clause Q hX formed star ⟨_, .refl tLam, .inl ⟨_, rfl⟩⟩
    ⟨_, .refl tLam', .inl ⟨_, rfl⟩⟩ ?_
  intro k ξ' ρ w a ha k' Θ ρr world s s' hs
  have domI := interprets.dom w
  have codI := interprets.cod w ha
  rw [rename_subst] at domI
  rw [inst0_rename_subst_liftSub] at codI
  -- The body under the valuation extended by the argument and its realizers.
  have hs' : ((Q.dom w).real a).rel Θ
      (Presentation.subst (fun i => Presentation.rename ρr (ς i)) A) s s' := by
    rw [← rename_subst]
    exact hs
  have e' := (((EqSubstN.rename laws e w).renameReal world.1 world.2).cons ⟨l, domI⟩ ⟨ha, hs'⟩)
  obtain ⟨rel, real⟩ := bodies e' ⟨l, codI⟩
  -- The application of the value and its instantiated body have one realizer.
  have related : (Q.cod w ha).rel (.app (Presentation.rename ρ (Presentation.subst σ (.lam body))) a)
      (Presentation.subst (consSub a fun i => Presentation.rename ρ (σ i)) body) := by
    have red : WhRed M.rules M.roles
        (.app (Presentation.rename ρ (Presentation.subst σ (.lam body))) a)
        (Presentation.subst (consSub a fun i => Presentation.rename ρ (σ i)) body) := by
      rw [← inst0_rename_subst_liftSub]
      exact .single (WhStep.beta _ a)
    exact (ValueSide.InterpAt.expansive laws.value codI).left red
      (ValueSide.InterpAt.per laws.value codI |>.refl_left rel)
  rw [ValueSide.InterpAt.real_eq_of_rel laws.value codI related]
  -- Both applications of the realizers reduce, typed, to the instantiated bodies.
  obtain ⟨ts, ts'⟩ := ((Q.dom w).real a).typed hs
  have eC := pi_codEq hX world.1 ts (((Q.dom w).real a).equal hs)
  have redL := RedTm.lam_app (T := M.side) typePi hu tBody world.1 ts
  have redR := (RedTm.lam_app (T := M.side) typePi hu tBody' world.1 ts').conv eC.symm
  simp only [inst0_rename_subst_liftSub] at redL redR ⊢
  exact ((Q.cod w ha).real _).expand redL redR real

end World

/-! ## Abstraction and application -/

section Rules

variable (laws : M.Laws)
include laws

/-- Abstraction. -/
theorem ValidTmN.lam {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {body B : Tm Head (n + 1)}
    (validPi : ValidTyN M Γ (.pi A B)) (validBody : ValidTmN M (.snoc Γ A) body B) :
    ValidTmN M Γ (.lam body) (.pi A B) := by
  obtain ⟨_, rel⟩ := validBody
  refine ⟨validPi, fun {_ _ _ _ _ _ _ _} e {_} den => ?_⟩
  obtain ⟨_, _, _, types⟩ := validPi e
  obtain ⟨u, hu, typePi, -⟩ := types.typed
  obtain ⟨typeA, -⟩ := IsType.pi_parts ⟨u, hu, typePi⟩
  exact ⟨DenN.pi_lam laws (fun {_ _ _ _ _ _ _ _} e' {_} den' => (rel e' den').1) e typeA den,
    DenN.pi_lam_real laws rel e hu typePi den⟩

/-- Application. -/
theorem ValidTmN.app {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n} {B : Tm Head (n + 1)}
    (validG : ValidTmN M Γ g (.pi A B)) (validA : ValidTmN M Γ a A)
    (validB : ValidTyN M (.snoc Γ A) B) :
    ValidTmN M Γ (.app g a) (Presentation.inst0 a B) := by
  refine ⟨ValidTyN.inst0 validB validA, fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  obtain ⟨_, denPi, _, types⟩ := validG.1 e
  obtain ⟨relG, realG⟩ := validG.2 e denPi
  rw [subst_inst0] at den
  rw [subst_inst0]
  refine ⟨ValueSide.DenS.pi_app laws.value denPi relG (fun denA => (validA.2 e denA).1) den, ?_⟩
  exact DenN.pi_app_real laws denPi e.formed (RedTy.refl types.left) realG
    (fun denA => ⟨ValueSide.DenS.refl_left laws.value denA (validA.2 e denA).1,
      (validA.2 e denA).2⟩) den

/-! ## Congruences -/

/-- Congruence of abstraction. -/
theorem ValidEqN.lam {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {body body' B : Tm Head (n + 1)} (validPi : ValidTyN M Γ (.pi A B))
    (eqBody : ValidEqN M (.snoc Γ A) body body' B) :
    ValidEqN M Γ (.lam body) (.lam body') (.pi A B) := by
  obtain ⟨validBody, validBody', rel⟩ := eqBody
  refine ⟨ValidTmN.lam laws validPi validBody, ValidTmN.lam laws validPi validBody',
    fun {_ _ _ _ _ _ _ _} e {_} den => ?_⟩
  obtain ⟨_, _, _, types⟩ := validPi e
  obtain ⟨u, hu, typePi, -⟩ := types.typed
  obtain ⟨typeA, -⟩ := IsType.pi_parts ⟨u, hu, typePi⟩
  exact ⟨DenN.pi_lam laws (fun {_ _ _ _ _ _ _ _} e' {_} den' => (rel e' den').1) e typeA den,
    DenN.pi_lam_real laws rel e hu typePi den⟩

/-- Congruence of application. -/
theorem ValidEqN.app {n : Nat} {Γ : Ctx Head n} {f g a b A : Tm Head n} {B : Tm Head (n + 1)}
    (eqG : ValidEqN M Γ f g (.pi A B)) (eqA : ValidEqN M Γ a b A)
    (validB : ValidTyN M (.snoc Γ A) B) :
    ValidEqN M Γ (.app f a) (.app g b) (Presentation.inst0 a B) := by
  obtain ⟨validF, validG, relFG⟩ := eqG
  obtain ⟨validLeft, validRight, relAB⟩ := eqA
  have validAppF := ValidTmN.app laws validF validLeft validB
  -- The second application, at the codomain instantiated at the first argument.
  have validAppG : ValidTmN M Γ (.app g b) (Presentation.inst0 a B) := by
    refine ⟨validAppF.1, fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
    obtain ⟨_, denPi, _, types⟩ := validF.1 e
    obtain ⟨relG, realG⟩ := validG.2 e denPi
    have hX := RedTy.refl (roles := M.side.roles) types.left
    rw [subst_inst0] at den
    rw [subst_inst0]
    -- The two arguments are related under the first valuation.
    have hab : ∀ {PA : NPack M _}, DenN M ξ (Presentation.subst σ A) PA →
        PA.rel (Presentation.subst σ a) (Presentation.subst σ b) := fun denA =>
      ValueSide.DenS.trans laws.value denA (relAB e denA).1
        (ValueSide.DenS.symm laws.value denA (validRight.2 e denA).1)
    have denB := ValueSide.DenS.pi_cod laws.value denPi hab den
    refine ⟨ValueSide.DenS.pi_app laws.value denPi relG (fun denA => (validRight.2 e denA).1)
      denB, ?_⟩
    have real := DenN.pi_app_real laws denPi e.formed hX realG
      (fun denA => ⟨ValueSide.DenS.refl_left laws.value denA (validRight.2 e denA).1,
        (validRight.2 e denA).2⟩) denB
    -- The realizer instances of the arguments are typed-equal.
    obtain ⟨PA, denA, -, -⟩ := validLeft.1 e
    have rab := (relAB e denA).2
    have rb := (validRight.2 e denA).2
    rw [← ValueSide.DenS.real_eq_of_rel laws.value denA (hab denA)] at rb
    have eba := (PA.real _).equal ((PA.real _).trans rb ((PA.real _).symm rab))
    have eC := pi_codEq_here hX (((PA.real _).typed rb).1) eba
    exact (P.real _).conv e.formed eC real
  refine ⟨validAppF, validAppG, fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  obtain ⟨_, denPi, _, types⟩ := validF.1 e
  rw [subst_inst0] at den
  rw [subst_inst0]
  refine ⟨ValueSide.DenS.pi_app laws.value denPi (relFG e denPi).1 (fun denA => (relAB e denA).1)
    den, ?_⟩
  exact DenN.pi_app_real laws denPi e.formed (RedTy.refl types.left) (relFG e denPi).2
    (fun denA => ⟨ValueSide.DenS.refl_left laws.value denA (relAB e denA).1, (relAB e denA).2⟩)
    den

/-! ## β and η -/

/-- β for functions: an applied abstraction weak-head reduces to its
instantiated body, on the value side and, typed, on the realizer side. -/
theorem ValidEqN.beta {n : Nat} {Γ : Ctx Head n} {A a : Tm Head n} {body B : Tm Head (n + 1)}
    (validPi : ValidTyN M Γ (.pi A B)) (validBody : ValidTmN M (.snoc Γ A) body B)
    (validA : ValidTmN M Γ a A) :
    ValidEqN M Γ (.app (.lam body) a) (Presentation.inst0 a body) (Presentation.inst0 a B) := by
  have validInst := ValidTmN.inst0 validBody validA
  -- Both β-steps of the realizer instances, at the first instance of the type.
  have steps : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {Δ : Ctx Head r}
      {ς ς' : Sub Head n r}, EqSubstN M Γ ξ σ σ' Δ ς ς' →
      RedTm M.side.R M.side.roles Δ (Presentation.subst ς (.app (.lam body) a))
          (Presentation.subst ς (Presentation.inst0 a body)) (Presentation.subst ς (Presentation.inst0 a B)) ∧
        RedTm M.side.R M.side.roles Δ (Presentation.subst ς' (.app (.lam body) a))
          (Presentation.subst ς' (Presentation.inst0 a body)) (Presentation.subst ς (Presentation.inst0 a B)) := by
    intro m r ξ σ σ' Δ ς ς' e
    obtain ⟨PPi, denPi, _, types⟩ := validPi e
    obtain ⟨u, hu, typePi, -⟩ := types.typed
    obtain ⟨typeA, -⟩ := IsType.pi_parts ⟨u, hu, typePi⟩
    obtain ⟨PA, denA, -, -⟩ := validA.1 e
    have ra := (validA.2 e denA).2
    obtain ⟨ta, ta'⟩ := (PA.real _).typed ra
    obtain ⟨PB, denB, -, -⟩ := validBody.1 (e.consVar typeA denA
      (ValueSide.DenS.star_val laws.value denA))
    have fresh := (validBody.2 (e.consVar typeA denA (ValueSide.DenS.star_val laws.value denA))
      denB).2
    rw [consSub_var_wk, consSub_var_wk] at fresh
    obtain ⟨tBody, tBody'⟩ := (ECand.typed _) fresh
    have hX := RedTy.refl (roles := M.side.roles) ⟨u, hu, typePi⟩
    have eC := pi_codEq_here hX ta ((PA.real _).equal ra)
    have redL := RedTm.beta (roles := M.side.roles) typePi hu tBody ta
    have redR := (RedTm.beta (roles := M.side.roles) typePi hu tBody' ta').conv eC.symm
    simp only [subst_inst0]
    exact ⟨redL, redR⟩
  refine ⟨⟨validInst.1, fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩, validInst,
    fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  · obtain ⟨h, hr⟩ := validInst.2 e den
    have expansive := ValueSide.DenS.expansive laws.value den
    have beta : ∀ {k : Nat} (τ : Sub Head n k), WhRed M.rules M.roles
        (Presentation.subst τ (.app (.lam body) a))
        (Presentation.subst τ (Presentation.inst0 a body)) :=
      fun τ => by
        rw [subst_inst0]
        exact .single (WhStep.beta _ _)
    have related : P.rel (Presentation.subst σ (.app (.lam body) a))
        (Presentation.subst σ (Presentation.inst0 a body)) :=
      expansive.left (beta σ) (ValueSide.DenS.refl_left laws.value den h)
    refine ⟨expansive.left (beta σ) (expansive.right (beta σ') h), ?_⟩
    rw [ValueSide.DenS.real_eq_of_rel laws.value den related]
    obtain ⟨redL, redR⟩ := steps e
    exact (P.real _).expand redL redR hr
  · obtain ⟨h, hr⟩ := validInst.2 e den
    have beta : WhRed M.rules M.roles (Presentation.subst σ (.app (.lam body) a))
        (Presentation.subst σ (Presentation.inst0 a body)) := by
      rw [subst_inst0]
      exact .single (WhStep.beta _ _)
    have expansive := ValueSide.DenS.expansive laws.value den
    have related : P.rel (Presentation.subst σ (.app (.lam body) a))
        (Presentation.subst σ (Presentation.inst0 a body)) :=
      expansive.left beta (ValueSide.DenS.refl_left laws.value den h)
    refine ⟨expansive.left beta h, ?_⟩
    rw [ValueSide.DenS.real_eq_of_rel laws.value den related]
    exact (P.real _).expand_left (steps e).1 hr

/-- η for functions: functions are equal when their applications to a fresh
variable are. -/
theorem ValidEqN.etaPi {n : Nat} {Γ : Ctx Head n} {f g A : Tm Head n} {B : Tm Head (n + 1)}
    (validF : ValidTmN M Γ f (.pi A B)) (validG : ValidTmN M Γ g (.pi A B))
    (eqApps : ValidEqN M (.snoc Γ A) (.app (Presentation.rename wk f) (.var 0))
      (.app (Presentation.rename wk g) (.var 0)) B) :
    ValidEqN M Γ f g (.pi A B) := by
  obtain ⟨_, _, relApps⟩ := eqApps
  have apps : ∀ {k : Nat} (x : Tm Head k) (τ : Sub Head n k) (t : Tm Head n),
      Presentation.subst (consSub x τ) (.app (Presentation.rename wk t) (.var 0)) =
        .app (Presentation.subst τ t) x := by
    intro k x τ t
    simp only [Presentation.subst, subst_consSub_rename_wk, consSub_zero]
  refine ⟨validF, validG, fun {_ _ ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.pi_inv laws.value den
  obtain ⟨_, _, _, types⟩ := validF.1 e
  have hX := RedTy.refl (roles := M.side.roles) types.left
  have domI₀ := interprets.dom_id
  have star := ValueSide.DenS.star_val laws.value ⟨l, domI₀⟩
  -- The clause of the applications, at every valid argument and realizer world.
  have clause : ∀ {k : Nat} {ξ' : World M.reading k} {ρ : Ren _ k} (w : Morph ξ ξ' ρ)
      {a : Tm Head k} (ha : (Q.dom w).Val a),
      AppClause ((Q.dom w).real a) ((Q.cod w ha).real
          (.app (Presentation.rename ρ (Presentation.subst σ f)) a)) Δ
        (Presentation.subst ς A) (Presentation.subst (liftSub ς) B)
        (Presentation.subst ς f) (Presentation.subst ς' g) := by
    intro k ξ' ρ w a ha k' Θ ρr world s s' hs
    have domI := interprets.dom w
    have codI := interprets.cod w ha
    rw [rename_subst] at domI
    rw [inst0_rename_subst_liftSub] at codI
    have hs' : ((Q.dom w).real a).rel Θ
        (Presentation.subst (fun i => Presentation.rename ρr (ς i)) A) s s' := by
      rw [← rename_subst]
      exact hs
    have e' := (((EqSubstN.rename laws e w).renameReal world.1 world.2).cons ⟨l, domI⟩ ⟨ha, hs'⟩)
    have h := (relApps e' ⟨l, codI⟩).2
    rw [apps, apps, apps] at h
    rw [inst0_rename_subst_liftSub, rename_subst, rename_subst, rename_subst]
    exact h
  have relF := (validF.2 e ⟨l, ValueSide.PiPack.Interprets.pi interprets⟩)
  have relG := (validG.2 e ⟨l, ValueSide.PiPack.Interprets.pi interprets⟩)
  obtain ⟨fnF, -, -, -⟩ := (PiPack.real_rel_pi Q _ hX).mp relF.2
  obtain ⟨-, fnG, -, -⟩ := (PiPack.real_rel_pi Q _ hX).mp relG.2
  refine ⟨?_, PiPack.real_of_clause Q hX e.formed star fnF fnG clause⟩
  intro k ξ' ρ w a b ha hab
  have domI := interprets.dom w
  have codI := interprets.cod w ha
  rw [rename_subst] at domI
  rw [inst0_rename_subst_liftSub] at codI
  have h := (relApps (((EqSubstN.rename laws e w).consVar
    (IsType.pi_parts types.left).1 ⟨l, domI⟩ hab)) ⟨l, codI⟩).1
  rw [apps, apps] at h
  rw [rename_subst, rename_subst]
  exact h

end Rules

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
