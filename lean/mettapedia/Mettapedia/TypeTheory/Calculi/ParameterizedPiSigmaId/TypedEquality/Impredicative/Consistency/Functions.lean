import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Formation

/-!
# Dependent functions in the consistency model

A dependent function type denotes the functions that send related arguments to
related results, at every world reached by a morphism. The model's relations
are closed under weak-head expansion, so an abstraction is such a function as
soon as its body relates the instances at related arguments: applied to an
argument, it β-reduces to its instantiated body. Related functions applied at
the world itself to related arguments give results related at the codomain
instantiated at the argument, and at related arguments the codomain has one
denotation.

From these: validity of λ-abstraction and application, their congruences, β
and η. β holds by weak-head expansion alone, so it needs only the validity of
the instantiated body.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-! ## Functions in a world -/

/-- Abstractions are related at a dependent function type when, at every world
reached by a morphism, their bodies instantiated at related arguments are
related at the codomain. -/
theorem PiRel.rel_lam {l : L} {n : Nat} {ξ : World M.reading n} {P : PiRel Head ξ} {B : Tm Head (n + 1)}
    (codInterp : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a : Tm Head m} (ha : P.dom w a a),
      InterpAt M l ξ' (Presentation.inst0 a (Presentation.rename (liftRen ρ) B)) (P.cod w ha))
    {body body' : Tm Head (n + 1)}
    (bodies : ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a b : Tm Head m} (ha : P.dom w a a), P.dom w a b →
        P.cod w ha (Presentation.inst0 a (Presentation.rename (liftRen ρ) body))
          (Presentation.inst0 b (Presentation.rename (liftRen ρ) body'))) :
    P.rel (.lam body) (.lam body') := by
  intro m ξ' ρ w a b ha hab
  exact (codInterp w ha).expandLeft (Relation.ReflTransGen.single (WhStep.beta _ a))
    ((codInterp w ha).expandRight (Relation.ReflTransGen.single (WhStep.beta _ b))
      (bodies w ha hab))

/-- Related functions send related arguments to results related at the
codomain instantiated at the argument. -/
theorem Den.pi_app (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {R : Rel Head n} (den : Den M ξ (.pi A B) R) {f g a b : Tm Head n}
    (hfg : R f g) (hab : ∀ {RA : Rel Head n}, Den M ξ A RA → RA a b) {RB : Rel Head n}
    (denB : Den M ξ (Presentation.inst0 a B) RB) : RB (.app f a) (.app g b) := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨P, rfl, domInterp, codInterp, -⟩ := InterpAt.pi_inv laws interp
  have domI := domInterp (Morph.id ξ)
  rw [rename_id] at domI
  have hab' : P.dom (Morph.id ξ) a b := hab ⟨l, domI⟩
  have ha := Den.refl_left laws ⟨l, domI⟩ hab'
  have codI := codInterp (Morph.id ξ) ha
  rw [liftRen_id, rename_id] at codI
  have h := hfg (Morph.id ξ) ha hab'
  simp only [rename_id] at h
  rw [Den.deterministic laws denB ⟨l, codI⟩]
  exact h

/-- Related functions applied to related arguments give results related at a
denotation of the codomain instantiated at the first argument. -/
theorem Den.pi_app_exists (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {R : Rel Head n} (den : Den M ξ (.pi A B) R) {f g a b : Tm Head n}
    (hfg : R f g) (hab : ∀ {RA : Rel Head n}, Den M ξ A RA → RA a b) :
    ∃ RB, Den M ξ (Presentation.inst0 a B) RB ∧ RB (.app f a) (.app g b) := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨P, rfl, domInterp, codInterp, -⟩ := InterpAt.pi_inv laws interp
  have domI := domInterp (Morph.id ξ)
  rw [rename_id] at domI
  have hab' : P.dom (Morph.id ξ) a b := hab ⟨l, domI⟩
  have ha := Den.refl_left laws ⟨l, domI⟩ hab'
  have codI := codInterp (Morph.id ξ) ha
  rw [liftRen_id, rename_id] at codI
  have h := hfg (Morph.id ξ) ha hab'
  simp only [rename_id] at h
  exact ⟨_, ⟨l, codI⟩, h⟩

/-- At related arguments, the codomain of a dependent function type has one
denotation. -/
theorem Den.pi_cod (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {R : Rel Head n} (den : Den M ξ (.pi A B) R) {a b : Tm Head n}
    (hab : ∀ {RA : Rel Head n}, Den M ξ A RA → RA a b) {RB : Rel Head n}
    (denB : Den M ξ (Presentation.inst0 a B) RB) : Den M ξ (Presentation.inst0 b B) RB := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨P, -, domInterp, codInterp, codRespect⟩ := InterpAt.pi_inv laws interp
  have domI := domInterp (Morph.id ξ)
  rw [rename_id] at domI
  have hab' : P.dom (Morph.id ξ) a b := hab ⟨l, domI⟩
  have ha := Den.refl_left laws ⟨l, domI⟩ hab'
  have hb := Den.refl_right laws ⟨l, domI⟩ hab'
  have codA := codInterp (Morph.id ξ) ha
  have codB := codInterp (Morph.id ξ) hb
  rw [liftRen_id, rename_id] at codA codB
  rw [Den.deterministic laws denB ⟨l, codA⟩, codRespect (Morph.id ξ) ha hb hab']
  exact ⟨l, codB⟩

/-- Under related substitutions, abstractions are related at a dependent
function type when their bodies are related under all related substitutions
for the extended context. -/
theorem Den.pi_lam (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {body body' B : Tm Head (n + 1)}
    (bodies : ∀ {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head (n + 1) m},
      EqSubst M (.snoc Γ A) ξ σ σ' → ∀ {R : Rel Head m}, Den M ξ (Presentation.subst σ B) R →
        R (Presentation.subst σ body) (Presentation.subst σ' body'))
    {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m} (e : EqSubst M Γ ξ σ σ')
    {R : Rel Head m} (den : Den M ξ (Presentation.subst σ (.pi A B)) R) :
    R (Presentation.subst σ (.lam body)) (Presentation.subst σ' (.lam body')) := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨P, rfl, domInterp, codInterp, -⟩ := InterpAt.pi_inv laws interp
  refine PiRel.rel_lam codInterp ?_
  intro k ξ' ρ w a b ha hab
  have domI := domInterp w
  have codI := codInterp w ha
  rw [rename_subst] at domI
  rw [inst0_rename_subst_liftSub] at codI
  rw [inst0_rename_subst_liftSub, inst0_rename_subst_liftSub]
  exact bodies (EqSubst.cons (EqSubst.rename laws e w) ⟨l, domI⟩ hab) ⟨l, codI⟩

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

/-- Abstraction. -/
theorem ValidTm.lam (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {body B : Tm Head (n + 1)} (validPi : ValidTy M Γ (.pi A B))
    (validBody : ValidTm M (.snoc Γ A) body B) : ValidTm M Γ (.lam body) (.pi A B) := by
  obtain ⟨_, rel⟩ := validBody
  exact ⟨validPi, fun {_ _ _ _} e {_} den => Den.pi_lam laws rel e den⟩

/-- Application. -/
theorem ValidTm.app (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n}
    {B : Tm Head (n + 1)} (validG : ValidTm M Γ g (.pi A B)) (validA : ValidTm M Γ a A)
    (validB : ValidTy M (.snoc Γ A) B) : ValidTm M Γ (.app g a) (Presentation.inst0 a B) := by
  have validInst : ValidTy M Γ (Presentation.inst0 a B) := ValidTy.inst0 validB validA
  obtain ⟨validPi, relG⟩ := validG
  obtain ⟨_, relA⟩ := validA
  refine ⟨validInst, fun {_ ξ σ σ'} e {R} den => ?_⟩
  obtain ⟨_, denPi, _⟩ := validPi e
  rw [subst_inst0] at den
  exact Den.pi_app laws denPi (relG e denPi) (relA e) den

/-! ## Congruences -/

/-- Congruence of abstraction. -/
theorem ValidEq.lam (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    {body body' B : Tm Head (n + 1)} (validPi : ValidTy M Γ (.pi A B))
    (eqBody : ValidEq M (.snoc Γ A) body body' B) :
    ValidEq M Γ (.lam body) (.lam body') (.pi A B) := by
  obtain ⟨validBody, validBody', rel⟩ := eqBody
  exact ⟨ValidTm.lam laws validPi validBody, ValidTm.lam laws validPi validBody',
    fun {_ _ _ _} e {_} den => Den.pi_lam laws rel e den⟩

/-- Congruence of application. -/
theorem ValidEq.app (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {f g a b A : Tm Head n}
    {B : Tm Head (n + 1)} (eqG : ValidEq M Γ f g (.pi A B)) (eqA : ValidEq M Γ a b A)
    (validB : ValidTy M (.snoc Γ A) B) :
    ValidEq M Γ (.app f a) (.app g b) (Presentation.inst0 a B) := by
  obtain ⟨validF, validG, relFG⟩ := eqG
  obtain ⟨validLeft, validRight, relAB⟩ := eqA
  obtain ⟨validInst, relAppF⟩ := ValidTm.app laws validF validLeft validB
  obtain ⟨_, relAppG⟩ := ValidTm.app laws validG validRight validB
  obtain ⟨validPi, _⟩ := validF
  obtain ⟨_, relB⟩ := validRight
  refine ⟨⟨validInst, relAppF⟩, ⟨validInst, fun {_ ξ σ σ'} e {R} den => ?_⟩,
    fun {_ ξ σ σ'} e {R} den => ?_⟩
  · obtain ⟨_, denPi, _⟩ := validPi e
    apply relAppG e
    rw [subst_inst0] at den ⊢
    exact Den.pi_cod laws denPi
      (fun {_} denA => Den.trans laws denA (relAB e denA) (Den.symm laws denA (relB e denA)))
      den
  · obtain ⟨_, denPi, _⟩ := validPi e
    rw [subst_inst0] at den
    exact Den.pi_app laws denPi (relFG e denPi) (relAB e) den

/-! ## β and η -/

/-- β for functions: an applied abstraction weak-head reduces to its
instantiated body. -/
theorem ValidEq.beta {n : Nat} {Γ : Ctx Head n} {A a : Tm Head n}
    {body B : Tm Head (n + 1)} (validBody : ValidTm M (.snoc Γ A) body B)
    (validA : ValidTm M Γ a A) :
    ValidEq M Γ (.app (.lam body) a) (Presentation.inst0 a body) (Presentation.inst0 a B) := by
  obtain ⟨validInst, rel⟩ := ValidTm.inst0 validBody validA
  refine ⟨⟨validInst, fun {_ ξ σ σ'} e {R} den => ?_⟩, ⟨validInst, rel⟩,
    fun {_ ξ σ σ'} e {R} den => ?_⟩
  · have h := rel e den
    rw [subst_inst0 σ, subst_inst0 σ'] at h
    exact Den.expandLeft den (Relation.ReflTransGen.single (WhStep.beta _ _))
      (Den.expandRight den (Relation.ReflTransGen.single (WhStep.beta _ _)) h)
  · have h := rel e den
    rw [subst_inst0 σ] at h
    exact Den.expandLeft den (Relation.ReflTransGen.single (WhStep.beta _ _)) h

/-- η for functions: functions are equal when their applications to a fresh
variable are. -/
theorem ValidEq.etaPi (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {f g A : Tm Head n}
    {B : Tm Head (n + 1)} (validF : ValidTm M Γ f (.pi A B))
    (validG : ValidTm M Γ g (.pi A B))
    (eqApps : ValidEq M (.snoc Γ A) (.app (Presentation.rename wk f) (.var 0))
      (.app (Presentation.rename wk g) (.var 0)) B) :
    ValidEq M Γ f g (.pi A B) := by
  obtain ⟨_, _, relApps⟩ := eqApps
  refine ⟨validF, validG, fun {_ ξ σ σ'} e {R} den => ?_⟩
  obtain ⟨l, interp⟩ := den
  obtain ⟨P, rfl, domInterp, codInterp, -⟩ := InterpAt.pi_inv laws interp
  intro k ξ' ρ w a b ha hab
  have domI := domInterp w
  have codI := codInterp w ha
  rw [rename_subst] at domI
  rw [inst0_rename_subst_liftSub] at codI
  have h := relApps (EqSubst.cons (EqSubst.rename laws e w) ⟨l, domI⟩ hab) ⟨l, codI⟩
  rw [subst_consSub_app_rename_wk, subst_consSub_app_rename_wk] at h
  rw [rename_subst, rename_subst]
  exact h

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
