import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Formation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Transport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Families

/-!
# Dependent functions in model SN

A dependent function type denotes, at every world reached by a morphism, the
functions that send related valid arguments to related results. Its realizers
are the strongly normalizing terms that send, after any renaming, every
realizer of every valid argument to a realizer of the result
(`PiPack.mem_real`).

The relation is closed under weak-head expansion, so an abstraction is such a
function as soon as its body relates the instances at related arguments. On the
realizer side, an abstraction realizes a function when its body, instantiated
at a realizer of a valid argument, realizes the instantiated body of the
function: an applied abstraction is a realizer as soon as its contractum is,
and the application and the instantiated body are related values, so they have
the same realizers. The body of the realizing abstraction is itself strongly
normalizing: it is the realizer instance of the body under the valuation
extended by the daimon, a valid value of every type, realized by a fresh
variable, which realizes every value.

Related functions applied at the world itself to related arguments give results
related at the codomain instantiated at the argument, and their realizers
applied to realizers of the argument realize the result. At related arguments
the codomain has one denotation.

From these: validity of λ-abstraction and application, their congruences, β
and η.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelSN

open Normalization (WhStep inst0_rename_subst_liftSub)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open StrongNormalization
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SNModel Head L}

/-! ## Values and realizers of valid terms -/

/-- The realizer instances of a valid term under related valuations are strongly
normalizing. -/
theorem ValidTmS.real_sn {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (valid : ValidTmS M Γ t A)
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) : SN M.realizers.rules (Presentation.subst ς t) := by
  obtain ⟨P, den, _, _⟩ := valid.1 e
  exact (P.real _).sn (valid.2 e den).2

/-- Under related valuations, the second instance of a valid term is a valid
value of the type's pack at the first valuation. -/
theorem ValidTmS.val_right (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (valid : ValidTmS M Γ t A) {m r : Nat} {ξ : World M.reading m}
    {σ σ' : Sub Head n m} {ς : Sub Head n r} (e : EqSubstS M Γ ξ σ σ' ς) {P : Pack M.value m}
    (den : DenS M.value ξ (Presentation.subst σ A) P) : P.Val (Presentation.subst σ' t) :=
  den.refl_right laws.value (valid.2 e den).1

/-! ## Functions in a world -/

section World

variable (laws : M.Laws)
include laws

/-- An abstraction of realizers with a strongly normalizing body `t` realizes an
abstraction when, at every world reached by a morphism, the abstraction's body
instantiated at a valid argument is related to itself and realized by `t`
instantiated, after any renaming, at any realizer of the argument. -/
theorem PiPack.real_lam {l : L} {n : Nat} {ξ : World M.reading n}
    {Q : ValueSide.PiPack M.value ξ} {B : Tm Head (n + 1)}
    (codInterp : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a : Tm Head m} (ha : (Q.dom w).Val a),
      InterpAt M.value l ξ' (Presentation.inst0 a (Presentation.rename (liftRen ρ) B))
        (Q.cod w ha))
    {body : Tm Head (n + 1)} {r : Nat} {t : Tm Head (r + 1)} (sn : SN M.realizers.rules t)
    (bodies : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a : Tm Head m} (ha : (Q.dom w).Val a) {r' : Nat} (ρr : Ren r r') {u : Tm Head r'},
        ((Q.dom w).real a).mem u →
          (Q.cod w ha).Val (Presentation.inst0 a (Presentation.rename (liftRen ρ) body)) ∧
            ((Q.cod w ha).real
                (Presentation.inst0 a (Presentation.rename (liftRen ρ) body))).mem
              (Presentation.inst0 u (Presentation.rename (liftRen ρr) t))) :
    (Q.real (.lam body)).mem (.lam t) := by
  refine (PiPack.mem_real Q).mpr ⟨SN.lam (RootShape.spineHeaded M.realizers.shape) sn, ?_⟩
  intro m ξ' ρ w a ha r' ρr u hu
  obtain ⟨rel, real⟩ := bodies w ha ρr hu
  have related : (Q.cod w ha).rel (.app (Presentation.rename ρ (.lam body)) a)
      (Presentation.inst0 a (Presentation.rename (liftRen ρ) body)) :=
    (InterpAt.expansive laws.value (codInterp w ha)).left (.single (WhStep.beta _ a)) rel
  rw [InterpAt.real_eq_of_rel laws.value (codInterp w ha) related]
  exact KCand.beta M.realizers.shape _ (SN.of_subst (subst0 u) ((KCand.sn _) real))
    ((KCand.sn _) hu) real

/-- A realizer of a function applied to a realizer of a valid argument realizes
the application at the codomain instantiated at the argument. -/
theorem DenS.pi_app_real {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack M.value n} (den : DenS M.value ξ (.pi A B) P)
    {f a : Tm Head n} {r : Nat} {t u : Tm Head r} (hf : (P.real f).mem t)
    (ha : ∀ {PA : Pack M.value n}, DenS M.value ξ A PA → PA.Val a)
    (hu : ∀ {PA : Pack M.value n}, DenS M.value ξ A PA → (PA.real a).mem u)
    {PB : Pack M.value n} (denB : DenS M.value ξ (Presentation.inst0 a B) PB) :
    (PB.real (.app f a)).mem (.app t u) := by
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.pi_inv laws.value den
  have domI : DenS M.value ξ A (Q.dom (Morph.id ξ)) := ⟨l, interprets.dom_id⟩
  have ha' := ha domI
  rw [DenS.deterministic laws.value denB ⟨l, interprets.cod_id ha'⟩]
  have h := ((PiPack.mem_real Q).mp hf).2 (Morph.id ξ) ha' idRen u (hu domI)
  simp only [rename_id] at h
  exact h

/-- Related functions applied to related arguments give results related at a
denotation of the codomain instantiated at the first argument. -/
theorem DenS.pi_app_exists {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack M.value n} (den : DenS M.value ξ (.pi A B) P)
    {f g a b : Tm Head n} (hfg : P.rel f g)
    (hab : ∀ {PA : Pack M.value n}, DenS M.value ξ A PA → PA.rel a b) :
    ∃ PB, DenS M.value ξ (Presentation.inst0 a B) PB ∧ PB.rel (.app f a) (.app g b) :=
  ValueSide.DenS.pi_app_exists laws.value den hfg hab

/-! ## Abstractions under valuations -/

/-- Under related valuations, abstractions are related at a dependent function
type when their bodies are related under all related valuations for the
extended context. -/
theorem DenS.pi_lam {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {body body' B : Tm Head (n + 1)}
    (bodies : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head (n + 1) m}
      {ς : Sub Head (n + 1) r}, EqSubstS M (.snoc Γ A) ξ σ σ' ς → ∀ {P : Pack M.value m},
        DenS M.value ξ (Presentation.subst σ B) P →
          P.rel (Presentation.subst σ body) (Presentation.subst σ' body'))
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) {P : Pack M.value m}
    (den : DenS M.value ξ (Presentation.subst σ (.pi A B)) P) :
    P.rel (Presentation.subst σ (.lam body)) (Presentation.subst σ' (.lam body')) := by
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.pi_inv laws.value den
  refine PiPack.rel_lam laws.value interprets.cod ?_
  intro k ξ' ρ w a b ha hab
  have domI := interprets.dom w
  have codI := interprets.cod w ha
  rw [rename_subst] at domI
  rw [inst0_rename_subst_liftSub] at codI
  rw [inst0_rename_subst_liftSub, inst0_rename_subst_liftSub]
  exact bodies (EqSubstS.cons ((e.rename laws w).renameReal wk) ⟨l, domI⟩ hab
    (((Q.dom w).real a).var_mem (RootShape.spineHeaded M.realizers.shape) 0)) ⟨l, codI⟩

/-- Under related valuations, the realizer instance of an abstraction realizes
its first value at a dependent function type when, under all related valuations
for the extended context, the body is related to itself and its realizer
instance realizes its first value. -/
theorem DenS.pi_lam_real {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {body B : Tm Head (n + 1)}
    (bodies : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head (n + 1) m}
      {ς : Sub Head (n + 1) r}, EqSubstS M (.snoc Γ A) ξ σ σ' ς → ∀ {P : Pack M.value m},
        DenS M.value ξ (Presentation.subst σ B) P →
          P.rel (Presentation.subst σ body) (Presentation.subst σ' body) ∧
            (P.real (Presentation.subst σ body)).mem (Presentation.subst ς body))
    {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} {ς : Sub Head n r}
    (e : EqSubstS M Γ ξ σ σ' ς) {P : Pack M.value m}
    (den : DenS M.value ξ (Presentation.subst σ (.pi A B)) P) :
    (P.real (Presentation.subst σ (.lam body))).mem (Presentation.subst ς (.lam body)) := by
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.pi_inv laws.value den
  -- The realizer instance of the body is strongly normalizing: it realizes the
  -- body under the valuation extended by the daimon, realized by a fresh variable.
  have sn : SN M.realizers.rules (Presentation.subst (liftSub ς) body) := by
    have domI := interprets.dom (Morph.id ξ)
    rw [rename_subst] at domI
    have star := InterpAt.star_val laws.value domI
    have codI := interprets.cod (Morph.id ξ) star
    rw [inst0_rename_subst_liftSub] at codI
    exact (KCand.sn _) (bodies (EqSubstS.cons ((e.rename laws (Morph.id ξ)).renameReal wk)
      ⟨l, domI⟩ star
      (((Q.dom (Morph.id ξ)).real _).var_mem (RootShape.spineHeaded M.realizers.shape) 0))
      ⟨l, codI⟩).2
  refine PiPack.real_lam laws interprets.cod sn ?_
  intro k ξ' ρ w a ha r' ρr u hu
  have domI := interprets.dom w
  have codI := interprets.cod w ha
  rw [rename_subst] at domI
  rw [inst0_rename_subst_liftSub] at codI
  rw [inst0_rename_subst_liftSub, inst0_rename_subst_liftSub]
  obtain ⟨rel, real⟩ :=
    bodies (EqSubstS.cons ((e.rename laws w).renameReal ρr) ⟨l, domI⟩ ha hu) ⟨l, codI⟩
  exact ⟨DenS.refl_left laws.value ⟨l, codI⟩ rel, real⟩

end World

/-- A weakened function applied to the fresh variable, under an extended
substitution. -/
theorem subst_consSub_app_rename_wk {n m : Nat} (a : Tm Head m) (σ : Sub Head n m)
    (f : Tm Head n) :
    Presentation.subst (consSub a σ) (.app (Presentation.rename wk f) (.var 0)) =
      .app (Presentation.subst σ f) a := by
  show Tm.app (Presentation.subst (consSub a σ) (Presentation.rename wk f)) (consSub a σ 0) = _
  rw [subst_consSub_rename_wk]
  rfl

/-! ## Abstraction and application -/

section Rules

variable (laws : M.Laws)
include laws

/-- Abstraction. -/
theorem ValidTmS.lam {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {body B : Tm Head (n + 1)}
    (validPi : ValidTyS M Γ (.pi A B)) (validBody : ValidTmS M (.snoc Γ A) body B) :
    ValidTmS M Γ (.lam body) (.pi A B) := by
  obtain ⟨_, rel⟩ := validBody
  exact ⟨validPi, fun {_ _ _ _ _ _} e {_} den =>
    ⟨DenS.pi_lam laws (fun {_ _ _ _ _ _} e' {_} den' => (rel e' den').1) e den,
      DenS.pi_lam_real laws rel e den⟩⟩

/-- Application. -/
theorem ValidTmS.app {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n} {B : Tm Head (n + 1)}
    (validG : ValidTmS M Γ g (.pi A B)) (validA : ValidTmS M Γ a A)
    (validB : ValidTyS M (.snoc Γ A) B) :
    ValidTmS M Γ (.app g a) (Presentation.inst0 a B) := by
  refine ⟨ValidTyS.inst0 validB validA, fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  obtain ⟨_, denPi, _, _⟩ := validG.1 e
  obtain ⟨relG, realG⟩ := validG.2 e denPi
  rw [subst_inst0] at den
  exact ⟨DenS.pi_app laws.value denPi relG (fun denA => (validA.2 e denA).1) den,
    DenS.pi_app_real laws denPi realG (fun denA => denA.refl_left laws.value (validA.2 e denA).1)
      (fun denA => (validA.2 e denA).2) den⟩

/-! ## Congruences -/

/-- Congruence of abstraction. -/
theorem ValidEqS.lam {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {body body' B : Tm Head (n + 1)} (validPi : ValidTyS M Γ (.pi A B))
    (eqBody : ValidEqS M (.snoc Γ A) body body' B) :
    ValidEqS M Γ (.lam body) (.lam body') (.pi A B) := by
  obtain ⟨validBody, validBody', rel⟩ := eqBody
  exact ⟨ValidTmS.lam laws validPi validBody, ValidTmS.lam laws validPi validBody',
    fun {_ _ _ _ _ _} e {_} den => DenS.pi_lam laws rel e den⟩

/-- Congruence of application. -/
theorem ValidEqS.app {n : Nat} {Γ : Ctx Head n} {f g a b A : Tm Head n} {B : Tm Head (n + 1)}
    (eqG : ValidEqS M Γ f g (.pi A B)) (eqA : ValidEqS M Γ a b A)
    (validB : ValidTyS M (.snoc Γ A) B) :
    ValidEqS M Γ (.app f a) (.app g b) (Presentation.inst0 a B) := by
  obtain ⟨validF, validG, relFG⟩ := eqG
  obtain ⟨validLeft, validRight, relAB⟩ := eqA
  have validAppF := ValidTmS.app laws validF validLeft validB
  obtain ⟨_, relAppG⟩ := ValidTmS.app laws validG validRight validB
  -- At related valuations, the codomain at the first argument is the codomain at
  -- the second.
  have codEq : ∀ {m r : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}
      {ς : Sub Head n r}, EqSubstS M Γ ξ σ σ' ς → ∀ {P : Pack M.value m},
        DenS M.value ξ (Presentation.subst σ (Presentation.inst0 a B)) P →
          DenS M.value ξ (Presentation.subst σ (Presentation.inst0 b B)) P := by
    intro m r ξ σ σ' ς e P den
    obtain ⟨_, denPi, _, _⟩ := validF.1 e
    rw [subst_inst0] at den ⊢
    exact DenS.pi_cod laws.value denPi
      (fun denA => denA.trans laws.value (relAB e denA)
        (denA.symm laws.value (validRight.2 e denA).1)) den
  refine ⟨validAppF, ⟨validAppF.1, fun {_ _ _ _ _ _} e {_} den => relAppG e (codEq e den)⟩,
    fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  obtain ⟨_, denPi, _, _⟩ := validF.1 e
  rw [subst_inst0] at den
  exact DenS.pi_app laws.value denPi (relFG e denPi) (relAB e) den

/-! ## β and η -/

/-- β for functions: an applied abstraction weak-head reduces to its
instantiated body, and its realizer instance is a β-redex whose contractum
realizes the instantiated body. -/
theorem ValidEqS.beta {n : Nat} {Γ : Ctx Head n} {A a : Tm Head n} {body B : Tm Head (n + 1)}
    (validBody : ValidTmS M (.snoc Γ A) body B) (validA : ValidTmS M Γ a A) :
    ValidEqS M Γ (.app (.lam body) a) (Presentation.inst0 a body)
      (Presentation.inst0 a B) := by
  have validInst := ValidTmS.inst0 validBody validA
  refine ⟨⟨validInst.1, fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩, validInst,
    fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  · obtain ⟨h, hr⟩ := validInst.2 e den
    rw [subst_inst0 σ, subst_inst0 σ'] at h
    rw [subst_inst0 σ, subst_inst0 ς] at hr
    have expansive := den.expansive laws.value
    have related : P.rel (Presentation.subst σ (.app (.lam body) a))
        (Presentation.inst0 (Presentation.subst σ a)
          (Presentation.subst (liftSub σ) body)) :=
      expansive.left (.single (WhStep.beta _ _)) (den.refl_left laws.value h)
    refine ⟨expansive.left (.single (WhStep.beta _ _)) (expansive.right
      (.single (WhStep.beta _ _)) h), ?_⟩
    rw [den.real_eq_of_rel laws.value related]
    exact KCand.beta M.realizers.shape _ (SN.of_subst _ ((KCand.sn _) hr)) (validA.real_sn e) hr
  · have h := (validInst.2 e den).1
    rw [subst_inst0 σ] at h
    exact (den.expansive laws.value).left (.single (WhStep.beta _ _)) h

/-- η for functions: functions are equal when their applications to a fresh
variable are. -/
theorem ValidEqS.etaPi {n : Nat} {Γ : Ctx Head n} {f g A : Tm Head n} {B : Tm Head (n + 1)}
    (validF : ValidTmS M Γ f (.pi A B)) (validG : ValidTmS M Γ g (.pi A B))
    (eqApps : ValidEqS M (.snoc Γ A) (.app (Presentation.rename wk f) (.var 0))
      (.app (Presentation.rename wk g) (.var 0)) B) :
    ValidEqS M Γ f g (.pi A B) := by
  obtain ⟨_, _, relApps⟩ := eqApps
  refine ⟨validF, validG, fun {_ _ ξ σ σ' ς} e {P} den => ?_⟩
  obtain ⟨l, Q, rfl, interprets⟩ := ValueSide.DenS.pi_inv laws.value den
  intro k ξ' ρ w a b ha hab
  have domI := interprets.dom w
  have codI := interprets.cod w ha
  rw [rename_subst] at domI
  rw [inst0_rename_subst_liftSub] at codI
  have h := relApps (EqSubstS.cons ((e.rename laws w).renameReal wk) ⟨l, domI⟩ hab
    (((Q.dom w).real a).var_mem (RootShape.spineHeaded M.realizers.shape) 0)) ⟨l, codI⟩
  rw [subst_consSub_app_rename_wk, subst_consSub_app_rename_wk] at h
  rw [rename_subst, rename_subst]
  exact h

end Rules

end ModelSN
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
