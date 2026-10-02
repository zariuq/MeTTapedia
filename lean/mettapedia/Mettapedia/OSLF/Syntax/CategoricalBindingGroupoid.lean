import Mettapedia.OSLF.Syntax.CategoricalBindingTheorem
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The groupoid of models is the groupoid of structure-preserving functors

A natural transformation between the classifying functors of two models is
determined by its components at the one-metavariable contexts, and those
components form a map of models. The operator law is naturality at an
operator applied to the metavariables of its arity. The evaluation law is
naturality at a metavariable of arity `Γ ⊢ s` applied to nullary
metavariables, one for each variable of `Γ`. Conversely a map of models is
determined by its function-object components: its sort components are read off
through evaluation at the empty context.

So the isomorphisms of two models are exactly the natural isomorphisms of
their classifying functors, compatibly with identities and composition. With
the reconstruction of every structure-preserving functor from its own model,
the groupoid of models is equivalent to the groupoid of structure-preserving
functors.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext (Object EquationPresentation)

universe u v

variable {S : Signature}

/-! ## Generic operator and evaluation terms -/

/-- The first metavariable of a context, applied to the variables its slot
binds. -/
def metaHead (a : MetaArity S) (L : List (MetaArity S)) :
    Term (withMetas S (a :: L)) (a.1 ++ []) a.2 :=
  Term.op (S := withMetas S (a :: L))
    (Sum.inr (MetaOp.mk (M := a :: L) ⟨0, Nat.succ_pos L.length⟩))
    (prefixArgs (T := withMetas S (a :: L)) (Γ := []) a.1)

/-- The metavariables of a context, each applied to its own dependency
variables, as the arguments of an operator of that arity in the empty
context. -/
def metaArgs : (L : List (MetaArity S)) → Args (withMetas S L) L []
  | [] => .nil
  | a :: L => .cons (metaHead a L) (instIntoArgs (tailArrow a ⟨L⟩) (metaArgs L))

/-- An operator applied to the metavariables of its arity. -/
def opTerm {s : S.Srt} (o : S.Op s) : Term (withMetas S (S.arity o)) [] s :=
  Term.op (S := withMetas S (S.arity o)) (Sum.inl o) (metaArgs (S.arity o))

/-- A nullary metavariable for each variable of a context. -/
abbrev nullaries (Γ : Ctx S) : List (MetaArity S) := Γ.map fun b => ([], b)

/-- A metavariable of arity `Γ ⊢ s` in front of nullary metavariables for the
variables of `Γ`. -/
abbrev evalObj (Γ : Ctx S) (s : S.Srt) : Object S := consObj (Γ, s) ⟨nullaries Γ⟩

/-- The metavariable of arity `Γ ⊢ s` applied to the nullary metavariables. -/
def evalTerm (Γ : Ctx S) (s : S.Srt) : Term (withMetas S (evalObj Γ s).arities) [] s :=
  Term.op (S := withMetas S (evalObj Γ s).arities)
    (Sum.inr (MetaOp.mk (M := (evalObj Γ s).arities) ⟨0, Nat.succ_pos (nullaries Γ).length⟩))
    (instIntoArgs (tailArrow (Γ, s) ⟨nullaries Γ⟩) (metaArgs (nullaries Γ)))

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Model

variable (M : Model S D)

/-! ## Their interpretation -/

/-- The prefix variables of an extended environment are the projections of
the binder context. -/
theorem extendEnv_injPrefix {N : List (MetaArity S)} {Z : D} :
    ∀ (bs : List S.Srt) {Γ : Ctx S} (ρ : M.Env Z Γ) {γ : S.Srt} (v : Var bs γ),
      M.extendEnv bs ρ γ (injPrefix (S := withMetas S N) bs v) = fst _ _ ≫ projectVar M.sort v
  | _ :: _, _, _, _, .zero => rfl
  | _ :: bs, _, ρ, γ, .succ w => by
      change lift (fst _ _ ≫ snd _ _) (snd _ _) ≫
          M.extendEnv bs ρ γ (injPrefix (S := withMetas S N) bs w) =
        fst _ _ ≫ snd _ _ ≫ projectVar M.sort w
      rw [extendEnv_injPrefix bs ρ w, lift_fst_assoc, Category.assoc]

/-- A metavariable applied to the variables its slot binds reads the binder
context. -/
theorem tupleCtx_prefixArgs {N : List (MetaArity S)} (bs : List S.Srt) {Γ : Ctx S} {Z : D}
    (m : M.ctx bs ⊗ Z ⟶ M.family N) (ρ : M.Env Z Γ) :
    M.tupleCtx bs (FreeBindingTerms.foldArgs (M.kripke N).toRaw
        (prefixArgs (T := withMetas S N) (Γ := Γ) bs)) (M.ctx bs ⊗ Z) m (M.extendEnv bs ρ) =
      fst _ _ := by
  rw [M.tupleCtx_foldArgs]
  symm
  refine M.tupleEnv_unique _ _ fun γ v => ?_
  rw [argsToSub_prefixArgs]
  exact (M.extendEnv_injPrefix (N := N) bs ρ v).symm

theorem metaHead_value (a : MetaArity S) (L : List (MetaArity S)) {Z : D}
    (m : M.ctx a.1 ⊗ Z ⟶ M.family (a :: L)) (ρ : M.Env Z []) :
    (M.interp (a :: L) (metaHead a L)).value (M.ctx a.1 ⊗ Z) m (M.extendEnv a.1 ρ) =
      lift (fst _ _) (m ≫ fst _ _) ≫ M.eval a.1 a.2 := by
  change lift (M.tupleCtx a.1 (FreeBindingTerms.foldArgs (M.kripke (a :: L)).toRaw
      (prefixArgs (T := withMetas S (a :: L)) (Γ := []) a.1)) _ m (M.extendEnv a.1 ρ))
      (m ≫ fst _ _) ≫ M.eval a.1 a.2 = _
  rw [M.tupleCtx_prefixArgs]

/-- Instantiated arguments are the arguments at the restaged stage. -/
theorem tupleArgs_instIntoArgs {X Y : Object S} (σ : X ⟶ Y) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args (withMetas S Y.arities) arity Γ) (Z : D) (m : Z ⟶ M.family X.arities)
      (ρ : M.Env Z Γ),
      M.tupleArgs (FreeBindingTerms.foldArgs (M.kripke X.arities).toRaw (instIntoArgs σ args))
          Z m ρ =
        M.tupleArgs (FreeBindingTerms.foldArgs (M.kripke Y.arities).toRaw args) Z
          (m ≫ M.assignHom σ) ρ
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons (bs := bs) head tail, Z, m, ρ => by
      show lift _ _ = lift _ _
      rw [tupleArgs_instIntoArgs σ tail Z m ρ]
      congr 2
      have restaged := M.interp_instInto_value σ head (M.ctx bs ⊗ Z) (snd _ _ ≫ m)
        (M.extendEnv bs ρ)
      rw [Category.assoc] at restaged
      exact restaged

theorem tupleCtx_instIntoArgs {X Y : Object S} (σ : X ⟶ Y) :
    ∀ (bs : List S.Srt) {Γ : Ctx S}
      (args : Args (withMetas S Y.arities) (bs.map fun b => ([], b)) Γ) (Z : D)
      (m : Z ⟶ M.family X.arities) (ρ : M.Env Z Γ),
      M.tupleCtx bs (FreeBindingTerms.foldArgs (M.kripke X.arities).toRaw (instIntoArgs σ args))
          Z m ρ =
        M.tupleCtx bs (FreeBindingTerms.foldArgs (M.kripke Y.arities).toRaw args) Z
          (m ≫ M.assignHom σ) ρ
  | [], _, .nil, _, _, _ => rfl
  | _ :: bs, _, .cons head tail, Z, m, ρ => by
      show lift _ _ = lift _ _
      rw [tupleCtx_instIntoArgs σ bs tail Z m ρ]
      congr 1
      exact M.interp_instInto_value σ head Z m ρ

/-- The metavariable arguments tuple to the stage itself. -/
theorem tupleArgs_metaArgs : ∀ (L : List (MetaArity S)) {Z : D} (m : Z ⟶ M.family L)
    (ρ : M.Env Z []),
    M.tupleArgs (FreeBindingTerms.foldArgs (M.kripke L).toRaw (metaArgs L)) Z m ρ = m
  | [], _, _, _ => toUnit_unique _ _
  | a :: L, Z, m, ρ => by
      have tail := M.tupleArgs_instIntoArgs (X := consObj a ⟨L⟩) (Y := ⟨L⟩) (tailArrow a ⟨L⟩)
        (metaArgs L) Z m ρ
      rw [tupleArgs_metaArgs L, M.assignHom_tailArrow] at tail
      change lift (M.curry ((M.interp (a :: L) (metaHead a L)).value
          (M.ctx a.1 ⊗ Z) (snd _ _ ≫ m) (M.extendEnv a.1 ρ)))
        (M.tupleArgs (FreeBindingTerms.foldArgs (M.kripke (a :: L)).toRaw
          (instIntoArgs (tailArrow a ⟨L⟩) (metaArgs L))) Z m ρ) = m
      rw [M.metaHead_value, tail, Category.assoc, lift_fst_snd_comp]
      change lift (M.curry (M.uncurry (m ≫ fst _ _))) (m ≫ snd _ _) = m
      rw [M.curry_uncurry, ← comp_lift, lift_fst_snd, Category.comp_id]

/-- **An operator applied to the metavariables of its arity is the operator.** -/
theorem pointValue_opTerm {s : S.Srt} (o : S.Op s) :
    M.pointValue (M.interp (S.arity o) (opTerm o)) = M.op o := by
  change M.tupleArgs (FreeBindingTerms.foldArgs (M.kripke (S.arity o)).toRaw
    (metaArgs (S.arity o))) _ (𝟙 _) _ ≫ M.op o = M.op o
  rw [M.tupleArgs_metaArgs, Category.id_comp]

/-- The nullary family of a context is its context product. -/
def nullariesIso : ∀ Γ : Ctx S, M.family (nullaries Γ) ≅ M.ctx Γ
  | [] => Iso.refl _
  | γ :: Γ => tensorIso (M.emptyPowerIso γ) (nullariesIso Γ)

theorem comp_emptyPower {γ : S.Srt} {Z : D} (f : Z ⟶ M.power [] γ) :
    f ≫ (M.emptyPowerIso γ).hom = lift (toUnit Z) f ≫ M.eval [] γ := by
  change f ≫ lift (toUnit _) (𝟙 _) ≫ M.eval [] γ = _
  rw [← Category.assoc, comp_lift, comp_toUnit, Category.comp_id]

/-- Nullary metavariables, as arguments, tuple to the context product. -/
theorem tupleCtx_metaArgs : ∀ (Γ : Ctx S) {Z : D} (m : Z ⟶ M.family (nullaries Γ))
    (ρ : M.Env Z []),
    M.tupleCtx Γ (FreeBindingTerms.foldArgs (M.kripke (nullaries Γ)).toRaw
      (metaArgs (nullaries Γ))) Z m ρ = m ≫ (M.nullariesIso Γ).hom
  | [], _, _, _ => toUnit_unique _ _
  | γ :: Γ, Z, m, ρ => by
      have tail := M.tupleCtx_instIntoArgs (X := ⟨nullaries (γ :: Γ)⟩) (Y := ⟨nullaries Γ⟩)
        (tailArrow ([], γ) ⟨nullaries Γ⟩) Γ (metaArgs (nullaries Γ)) Z m ρ
      rw [tupleCtx_metaArgs Γ, M.assignHom_tailArrow] at tail
      change lift (lift (toUnit Z) (m ≫ fst _ _) ≫ M.eval [] γ)
        (M.tupleCtx Γ (FreeBindingTerms.foldArgs
          (M.kripke (⟨nullaries (γ :: Γ)⟩ : Object S).arities).toRaw
          (instIntoArgs (tailArrow ([], γ) ⟨nullaries Γ⟩) (metaArgs (nullaries Γ)))) Z m ρ) =
        m ≫ ((M.emptyPowerIso γ).hom ⊗ₘ (M.nullariesIso Γ).hom)
      rw [tail]
      apply hom_ext
      · rw [lift_fst, Category.assoc, tensorHom_fst, ← Category.assoc, comp_emptyPower]
      · simp only [lift_snd, Category.assoc, tensorHom_snd]

/-- The evaluation context, split into the context product and the function
object. -/
def evalSplit (Γ : Ctx S) (s : S.Srt) :
    M.power Γ s ⊗ M.family (nullaries Γ) ⟶ M.ctx Γ ⊗ M.power Γ s :=
  lift (snd _ _ ≫ (M.nullariesIso Γ).hom) (fst _ _)

/-- A section of the split. -/
def evalSection (Γ : Ctx S) (s : S.Srt) :
    M.ctx Γ ⊗ M.power Γ s ⟶ M.power Γ s ⊗ M.family (nullaries Γ) :=
  lift (snd _ _) (fst _ _ ≫ (M.nullariesIso Γ).inv)

@[reassoc]
theorem evalSection_evalSplit (Γ : Ctx S) (s : S.Srt) :
    M.evalSection Γ s ≫ M.evalSplit Γ s = 𝟙 _ := by
  unfold evalSection evalSplit
  apply hom_ext <;> simp

/-- **A metavariable applied to nullary metavariables is evaluation.** -/
theorem pointValue_evalTerm (Γ : Ctx S) (s : S.Srt) :
    M.pointValue (M.interp (evalObj Γ s).arities (evalTerm Γ s)) =
      M.evalSplit Γ s ≫ M.eval Γ s := by
  have tail := fun ρ : M.Env (M.family (evalObj Γ s).arities) [] =>
    M.tupleCtx_instIntoArgs (X := evalObj Γ s) (Y := ⟨nullaries Γ⟩)
      (tailArrow (Γ, s) ⟨nullaries Γ⟩) Γ (metaArgs (nullaries Γ)) _ (𝟙 _) ρ
  simp only [M.tupleCtx_metaArgs, M.assignHom_tailArrow, Category.id_comp] at tail
  change lift (M.tupleCtx Γ (FreeBindingTerms.foldArgs (M.kripke (evalObj Γ s).arities).toRaw
      (instIntoArgs (tailArrow (Γ, s) ⟨nullaries Γ⟩) (metaArgs (nullaries Γ)))) _ (𝟙 _) _)
      (𝟙 _ ≫ fst _ _) ≫ M.eval Γ s = _
  rw [tail, Category.id_comp]
  rfl

/-- The classifying functor on a slot is the projection. -/
theorem map_slot (L : List (MetaArity S)) (i : Fin L.length) :
    M.classifyingFunctor.map (slot L i) =
      M.familyProj L i ≫ (M.powerIso (L.get i).1 (L.get i).2).inv := by
  change M.assignHom (termArrow (X := ⟨L⟩) (metaVar i)) = _
  rw [assignHom_termArrow, generic_metaVar]
  change _ = M.familyProj L i ≫ lift (𝟙 _) (toUnit _)
  rw [comp_lift, Category.comp_id, comp_toUnit]

/-! ## Natural transformations of classifying functors are maps of models -/

section Natural

variable {M} {N : Model S D} (τ : M.classifyingFunctor ⟶ N.classifyingFunctor)

/-- The function-object components of a natural transformation of classifying
functors. -/
def natPower (Γ : Ctx S) (s : S.Srt) : M.power Γ s ⟶ N.power Γ s :=
  (M.powerIso Γ s).inv ≫ τ.app (oneObj Γ s) ≫ (N.powerIso Γ s).hom

/-- Its sort components. -/
def natSort (s : S.Srt) : M.sort s ⟶ N.sort s :=
  (M.sortIso s).inv ≫ τ.app (oneObj [] s) ≫ (N.sortIso s).hom

theorem natPower_emptyPower (γ : S.Srt) :
    natPower τ [] γ ≫ (N.emptyPowerIso γ).hom = (M.emptyPowerIso γ).hom ≫ natSort τ γ := by
  simp [natPower, natSort, sortIso]

/-- **A natural transformation of classifying functors is the product of its
one-metavariable components.** -/
theorem app_eq_familyMap (X : Object S) : τ.app X = familyMap (natPower τ) X.arities := by
  have agree : ∀ i : Fin X.arities.length, τ.app X ≫ N.familyProj X.arities i =
      M.familyProj X.arities i ≫ natPower τ (X.arities.get i).1 (X.arities.get i).2 := by
    intro i
    have natural := τ.naturality (slot X.arities i)
    rw [map_slot, map_slot] at natural
    have composed := congrArg
      (· ≫ (N.powerIso (X.arities.get i).1 (X.arities.get i).2).hom) natural
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at composed
    exact composed.symm
  exact (N.familyLift_unique _ _ _ agree).trans
    (N.familyLift_unique _ _ _ fun i => familyMap_proj (natPower τ) X.arities i).symm

/-- Naturality at a closed term: point values correspond. -/
theorem pointValue_natural {X : Object S} {s : S.Srt} (t : Term (withMetas S X.arities) [] s) :
    M.pointValue (M.interp X.arities t) ≫ natSort τ s =
      familyMap (natPower τ) X.arities ≫ N.pointValue (N.interp X.arities t) := by
  rw [← M.classify_sortIso t, ← N.classify_sortIso t, ← app_eq_familyMap τ X]
  unfold natSort
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (reassoc_of% (τ.naturality (termArrow t))) (N.sortIso s).hom

theorem familyMap_nullaries {N : Model S D} (g : ∀ Γ s, M.power Γ s ⟶ N.power Γ s)
    (f : ∀ s, M.sort s ⟶ N.sort s)
    (h : ∀ γ, g [] γ ≫ (N.emptyPowerIso γ).hom = (M.emptyPowerIso γ).hom ≫ f γ) :
    ∀ Γ : Ctx S, familyMap g (nullaries Γ) ≫ (N.nullariesIso Γ).hom =
      (M.nullariesIso Γ).hom ≫ ctxMap f Γ
  | [] => rfl
  | γ :: Γ => by
      change (g [] γ ⊗ₘ familyMap g (nullaries Γ)) ≫
          ((N.emptyPowerIso γ).hom ⊗ₘ (N.nullariesIso Γ).hom) =
        ((M.emptyPowerIso γ).hom ⊗ₘ (M.nullariesIso Γ).hom) ≫ (f γ ⊗ₘ ctxMap f Γ)
      rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, h γ, familyMap_nullaries g f h Γ]

/-- **The components of a natural transformation of classifying functors form
a map of models.** -/
def homOfNat : M ⟶ N where
  sort := natSort τ
  power := natPower τ
  eval_comm := fun Γ s => by
    have split := pointValue_natural τ (X := evalObj Γ s) (evalTerm Γ s)
    rw [M.pointValue_evalTerm, N.pointValue_evalTerm] at split
    have key : familyMap (natPower τ) (evalObj Γ s).arities ≫ N.evalSplit Γ s =
        M.evalSplit Γ s ≫ (ctxMap (natSort τ) Γ ⊗ₘ natPower τ Γ s) := by
      change (natPower τ Γ s ⊗ₘ familyMap (natPower τ) (nullaries Γ)) ≫
          lift (snd _ _ ≫ (N.nullariesIso Γ).hom) (fst _ _) =
        lift (snd _ _ ≫ (M.nullariesIso Γ).hom) (fst _ _) ≫
          (ctxMap (natSort τ) Γ ⊗ₘ natPower τ Γ s)
      apply hom_ext
      · simp only [Category.assoc, lift_fst, tensorHom_fst, lift_fst_assoc, tensorHom_snd_assoc,
          familyMap_nullaries (natPower τ) (natSort τ) (natPower_emptyPower τ) Γ]
      · simp only [Category.assoc, lift_snd, tensorHom_snd, lift_snd_assoc, tensorHom_fst]
    rw [← Category.assoc, key, Category.assoc] at split
    have cancelled := congrArg (M.evalSection Γ s ≫ ·) split
    simp only [Category.assoc, M.evalSection_evalSplit_assoc] at cancelled
    exact cancelled.symm
  op_comm := fun {s} o => by
    have operator := pointValue_natural τ (X := ⟨S.arity o⟩) (opTerm o)
    rw [M.pointValue_opTerm, N.pointValue_opTerm] at operator
    exact operator.symm

end Natural

theorem homOfNat_id : homOfNat (𝟙 M.classifyingFunctor) = 𝟙 M := by
  apply Hom.ext
  · funext s
    simp [homOfNat, natSort]
  · funext Γ s
    simp [homOfNat, natPower]

theorem homOfNat_comp {N P : Model S D} (τ : M.classifyingFunctor ⟶ N.classifyingFunctor)
    (τ' : N.classifyingFunctor ⟶ P.classifyingFunctor) :
    homOfNat (τ ≫ τ') = homOfNat τ ≫ homOfNat τ' := by
  apply Hom.ext
  · funext s
    simp [homOfNat, natSort]
  · funext Γ s
    simp [homOfNat, natPower]

/-! ## Isomorphisms -/

/-- The isomorphism of models carried by a natural isomorphism of classifying
functors. -/
def isoOfClassifyingIso {N : Model S D} (α : M.classifyingFunctor ≅ N.classifyingFunctor) :
    M ≅ N where
  hom := homOfNat α.hom
  inv := homOfNat α.inv
  hom_inv_id := by rw [← homOfNat_comp, α.hom_inv_id, homOfNat_id]
  inv_hom_id := by rw [← homOfNat_comp, α.inv_hom_id, homOfNat_id]

/-- The sort components of a map of models are read through evaluation at the
empty context. -/
theorem power_nil_comp_emptyPower {N : Model S D} (h : M ⟶ N) (s : S.Srt) :
    Hom.power h [] s ≫ (N.emptyPowerIso s).hom = (M.emptyPowerIso s).hom ≫ Hom.sort h s := by
  change Hom.power h [] s ≫ lift (toUnit _) (𝟙 _) ≫ N.eval [] s =
    (lift (toUnit _) (𝟙 _) ≫ M.eval [] s) ≫ Hom.sort h s
  rw [Category.assoc, ← Hom.eval_comm]
  simp only [← Category.assoc]
  congr 1
  apply hom_ext
  · exact toUnit_unique _ _
  · simp [ctxMap]

theorem classifyingIsoOfIso_hom_app {N : Model S D} (e : M ≅ N) (X : Object S) :
    (classifyingIsoOfIso e).hom.app X = familyMap (Hom.power e.hom) X.arities :=
  rfl

theorem isoOfClassifyingIso_classifyingIsoOfIso {N : Model S D} (e : M ≅ N) :
    isoOfClassifyingIso M (classifyingIsoOfIso e) = e := by
  have power : natPower (classifyingIsoOfIso e).hom = Hom.power e.hom := by
    funext Γ s
    change (M.powerIso Γ s).inv ≫ (Hom.power e.hom Γ s ⊗ₘ 𝟙 _) ≫ (N.powerIso Γ s).hom = _
    simp [powerIso]
  apply Iso.ext
  apply Hom.ext
  · funext s
    change natSort (classifyingIsoOfIso e).hom s = Hom.sort e.hom s
    rw [← cancel_epi (M.emptyPowerIso s).hom, ← natPower_emptyPower, power,
      power_nil_comp_emptyPower]
  · exact power

theorem classifyingIsoOfIso_isoOfClassifyingIso {N : Model S D}
    (α : M.classifyingFunctor ≅ N.classifyingFunctor) :
    classifyingIsoOfIso (isoOfClassifyingIso M α) = α := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact (app_eq_familyMap α.hom X).symm

/-- **The isomorphisms of two models are exactly the natural isomorphisms of
their classifying functors.** -/
noncomputable def classifyingIsoEquiv (N : Model S D) :
    (M ≅ N) ≃ (M.classifyingFunctor ≅ N.classifyingFunctor) where
  toFun := classifyingIsoOfIso
  invFun := isoOfClassifyingIso M
  left_inv := isoOfClassifyingIso_classifyingIsoOfIso M
  right_inv := classifyingIsoOfIso_isoOfClassifyingIso M

theorem classifyingIsoOfIso_refl : classifyingIsoOfIso (Iso.refl M) = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact familyMap_id M X.arities

theorem classifyingIsoOfIso_trans {N P : Model S D} (e : M ≅ N) (e' : N ≅ P) :
    classifyingIsoOfIso (e ≪≫ e') = classifyingIsoOfIso e ≪≫ classifyingIsoOfIso e' := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact familyMap_comp _ _ X.arities

/-- Satisfaction of an equation presentation is invariant under isomorphism of
models. -/
theorem satisfies_of_iso {N : Model S D} (e : M ≅ N) {schema : List (MetaArity S)}
    (P : EquationPresentation S schema) (sat : M.Satisfies P) : N.Satisfies P := by
  intro X i Θ Δ body ambient ordinary
  rw [← interp_transport e X.arities, ← interp_transport e X.arities,
    sat X i body ambient ordinary]

end Model

/-! ## The groupoid equivalence -/

/-- The classifying functors, on the groupoid of models. -/
@[simps]
noncomputable def classifyingOnCore : Core (Model S D) ⥤ (Object S ⥤ D) where
  obj M := M.of.classifyingFunctor
  map f := (Model.classifyingIsoOfIso f.iso).hom
  map_id M := by
    change (Model.classifyingIsoOfIso (Iso.refl M.of)).hom = 𝟙 _
    rw [Model.classifyingIsoOfIso_refl]
    rfl
  map_comp f g := by
    change (Model.classifyingIsoOfIso (f.iso ≪≫ g.iso)).hom = _
    rw [Model.classifyingIsoOfIso_trans]
    rfl

instance : (Core.functorToCore (classifyingOnCore (S := S) (D := D))).Faithful where
  map_injective {M N} f g equal := by
    have homs := congrArg (fun φ => φ.iso.hom) equal
    apply CoreHom.ext
    exact (M.of.classifyingIsoEquiv N.of).injective (Iso.ext homs)

instance : (Core.functorToCore (classifyingOnCore (S := S) (D := D))).Full where
  map_surjective {M N} φ := ⟨⟨Model.isoOfClassifyingIso M.of φ.iso⟩, by
    apply Core.hom_ext
    exact congrArg Iso.hom (Model.classifyingIsoOfIso_isoOfClassifyingIso M.of φ.iso)⟩

/-- Functors from second-order contexts that carry the structure. -/
def preservingFunctors : ObjectProperty (Core (Object S ⥤ D)) :=
  fun F => Nonempty (Preserving F.of)

/-- The classifying construction, from models to structure-preserving
functors. -/
noncomputable def classifying :
    Core (Model S D) ⥤ (preservingFunctors (S := S) (D := D)).FullSubcategory :=
  ObjectProperty.lift _ (Core.functorToCore classifyingOnCore)
    fun M => ⟨M.of.classifyingPreserving⟩

instance : (classifying (S := S) (D := D)).Faithful :=
  Functor.Faithful.of_comp_iso
    (ObjectProperty.liftCompιIso _ (Core.functorToCore classifyingOnCore) _)

instance : (classifying (S := S) (D := D)).Full :=
  Functor.Full.of_comp_faithful_iso
    (ObjectProperty.liftCompιIso _ (Core.functorToCore classifyingOnCore) _)

instance : (classifying (S := S) (D := D)).EssSurj where
  mem_essImage F := by
    obtain ⟨hF⟩ := F.property
    exact ⟨⟨hF.toModel⟩, ⟨ObjectProperty.isoMk _ (Core.isoMk hF.isoClassifying.symm)⟩⟩

instance : (classifying (S := S) (D := D)).IsEquivalence where

/-- **The groupoid of models is equivalent to the groupoid of
structure-preserving functors out of the second-order context category.** -/
noncomputable def modelsEquivalence :
    Core (Model S D) ≌ (preservingFunctors (S := S) (D := D)).FullSubcategory :=
  (classifying (S := S) (D := D)).asEquivalence

/-! ## Models of an equation presentation -/

section Equations

variable {schema : List (MetaArity S)} (P : EquationPresentation S schema)

/-- Models satisfying the presentation. -/
def satisfying : ObjectProperty (Core (Model S D)) :=
  fun M => M.of.Satisfies P

/-- Structure-preserving functors identifying equation-related assignments. -/
def respecting : ObjectProperty (preservingFunctors (S := S) (D := D)).FullSubcategory :=
  fun F => ∀ {X Y : Object S} {σ τ : X ⟶ Y}, P.homRel σ τ → F.obj.of.map σ = F.obj.of.map τ

theorem respecting_classifying_iff (M : Core (Model S D)) :
    respecting P (classifying.obj M) ↔ satisfying P M := by
  constructor
  · intro respects
    exact M.of.classifyingModel.satisfies_of_iso M.of.classifyingModelIso.symm P
      (M.of.classifyingPreserving.satisfies_of_respects P respects)
  · intro sat X Y σ τ related
    exact M.of.assignHom_congr P sat related

theorem respecting_of_iso {F G : (preservingFunctors (S := S) (D := D)).FullSubcategory}
    (e : F ≅ G) (respects : respecting P F) : respecting P G := by
  intro X Y σ τ related
  let α : F.obj.of ≅ G.obj.of := e.hom.hom.iso
  rw [← cancel_mono (α.inv.app Y), α.inv.naturality, α.inv.naturality, respects related]

/-- The classifying construction on models of the presentation. -/
noncomputable def classifyingSatisfying :
    (satisfying (S := S) (D := D) P).FullSubcategory ⥤
      (respecting (S := S) (D := D) P).FullSubcategory :=
  ObjectProperty.lift _ ((satisfying (S := S) (D := D) P).ι ⋙ classifying)
    fun M => (respecting_classifying_iff P M.obj).mpr M.property

instance : (classifyingSatisfying (S := S) (D := D) P).Faithful :=
  Functor.Faithful.of_comp_iso
    (ObjectProperty.liftCompιIso _ ((satisfying (S := S) (D := D) P).ι ⋙ classifying) _)

instance : (classifyingSatisfying (S := S) (D := D) P).Full :=
  Functor.Full.of_comp_faithful_iso
    (ObjectProperty.liftCompιIso _ ((satisfying (S := S) (D := D) P).ι ⋙ classifying) _)

instance : (classifyingSatisfying (S := S) (D := D) P).EssSurj where
  mem_essImage F := by
    let M := classifying.objPreimage F.obj
    have sat : satisfying P M := (respecting_classifying_iff P M).mp
      (respecting_of_iso P (classifying.objObjPreimageIso F.obj).symm F.property)
    exact ⟨⟨M, sat⟩, ⟨ObjectProperty.isoMk _ (classifying.objObjPreimageIso F.obj)⟩⟩

instance : (classifyingSatisfying (S := S) (D := D) P).IsEquivalence where

/-- **The groupoid of models of an equation presentation is equivalent to the
groupoid of structure-preserving functors identifying its equations.** Each
such functor extends uniquely along the quotient to the equation-class context
category, by `SecondOrderContext.equationUniversalEquivalence`. -/
noncomputable def satisfyingEquivalence :
    (satisfying (S := S) (D := D) P).FullSubcategory ≌
      (respecting (S := S) (D := D) P).FullSubcategory :=
  (classifyingSatisfying P).asEquivalence

end Equations

end Mettapedia.OSLF.Binding.CategoricalBindingModel

#print axioms Mettapedia.OSLF.Binding.CategoricalBindingModel.Model.classifyingIsoEquiv
#print axioms Mettapedia.OSLF.Binding.CategoricalBindingModel.modelsEquivalence
#print axioms Mettapedia.OSLF.Binding.CategoricalBindingModel.satisfyingEquivalence
