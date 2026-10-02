import Mettapedia.OSLF.Syntax.CategoricalBindingFunctor

/-!
# Products and chosen exponentials under a functor from second-order contexts

A functor from second-order contexts preserves their products when it sends
the empty context to a terminal object and each context `a :: X` to the
product of the one-metavariable context `a` and `X`, with the head and tail
assignments as projections. It carries chosen exponentials when each
one-metavariable context `Γ ⊢ s` goes to an exponential of the product of the
sort objects of `Γ` into the sort object of `s`.

The classifying functor of every model has this structure, and it sends
substitution of terms for variables to evaluation: in the context category,
evaluation is substitution into a binder context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext (Object single termsRepresented)

universe u v

variable {S : Signature}

/-! ## Arrows of the context category -/

/-- The one-metavariable context of an arity. It is `single`, unfolded. -/
abbrev oneObj (Γ : Ctx S) (s : S.Srt) : Object S := ⟨[(Γ, s)]⟩

/-- A term, as an arrow into the one-metavariable context of its arity. -/
def termArrow {X : Object S} {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S X.arities) Γ s) :
    X ⟶ oneObj Γ s :=
  (termsRepresented S X Γ s).symm t

/-- One metavariable in front of a context. -/
abbrev consObj (a : MetaArity S) (X : Object S) : Object S := ⟨a :: X.arities⟩

/-- The head metavariable. -/
def headArrow (a : MetaArity S) (X : Object S) : consObj a X ⟶ oneObj a.1 a.2 :=
  termArrow (X := consObj a X) (metaVar (M := a :: X.arities) ⟨0, Nat.succ_pos _⟩)

/-- The remaining metavariables. -/
def tailArrow (a : MetaArity S) (X : Object S) : consObj a X ⟶ X :=
  fun i => metaVar (M := a :: X.arities) i.succ

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-! ## Exponentials and their transport along isomorphisms -/

/-- `P` with an evaluation is an exponential of `C` into `T`. -/
structure Exponential (C T P : D) where
  eval : C ⊗ P ⟶ T
  curry : ∀ {Z : D}, (C ⊗ Z ⟶ T) → (Z ⟶ P)
  curry_eval : ∀ {Z : D} (f : C ⊗ Z ⟶ T), (C ◁ curry f) ≫ eval = f
  curry_unique : ∀ {Z : D} (f : C ⊗ Z ⟶ T) (g : Z ⟶ P), (C ◁ g) ≫ eval = f → curry f = g

namespace Exponential

variable {C T P C' T' P' : D}

/-- Transport an exponential along isomorphisms of its base, its target and
its object. -/
def transport (E : Exponential C T P) (iC : C' ≅ C) (iT : T ≅ T') (iP : P ≅ P') :
    Exponential C' T' P' where
  eval := (iC.hom ⊗ₘ iP.inv) ≫ E.eval ≫ iT.hom
  curry := fun f => E.curry ((iC.inv ▷ _) ≫ f ≫ iT.inv) ≫ iP.hom
  curry_eval := by
    intro Z f
    have step : (C' ◁ (E.curry ((iC.inv ▷ Z) ≫ f ≫ iT.inv) ≫ iP.hom)) ≫ (iC.hom ⊗ₘ iP.inv) =
        (iC.hom ▷ Z) ≫ (C ◁ E.curry ((iC.inv ▷ Z) ≫ f ≫ iT.inv)) := by
      apply hom_ext <;> simp
    rw [← Category.assoc, step, Category.assoc, ← Category.assoc (C ◁ _), E.curry_eval]
    simp
  curry_unique := by
    intro Z f g h
    rw [← Iso.eq_comp_inv]
    apply E.curry_unique
    rw [← h]
    have step : (C ◁ (g ≫ iP.inv)) = (iC.inv ▷ Z) ≫ (C' ◁ g) ≫ (iC.hom ⊗ₘ iP.inv) := by
      apply hom_ext <;> simp
    rw [step]
    simp

end Exponential

/-- The exponentials of a model. -/
def Model.exponential {S : Signature} (M : Model S D) (Γ : Ctx S) (s : S.Srt) :
    Exponential (M.ctx Γ) (M.sort s) (M.power Γ s) where
  eval := M.eval Γ s
  curry := M.curry
  curry_eval := M.curry_eval
  curry_unique := M.curry_unique

/-! ## Structure preservation -/

/-- The sort objects of a functor on second-order contexts. -/
abbrev sortOf (F : Object S ⥤ D) (s : S.Srt) : D := F.obj (oneObj [] s)

/-- The images of the terms of a substitution, tupled into the product of the
sort objects of its domain context. -/
def tupleF (F : Object S ⥤ D) {X : Object S} :
    ∀ {Γ : Ctx S}, Sub (withMetas S X.arities) Γ [] → (F.obj X ⟶ contextOf (sortOf F) Γ)
  | [], _ => toUnit _
  | _ :: _, ρ => lift (F.map (termArrow (ρ _ .zero))) (tupleF F fun γ v => ρ γ (.succ v))

/-- A functor preserving the products of contexts, with chosen exponentials
for the one-metavariable contexts. -/
structure CartesianArities (F : Object S ⥤ D) where
  terminal : IsTerminal (F.obj ⟨[]⟩)
  cons : ∀ (a : MetaArity S) (X : Object S),
    IsLimit (BinaryFan.mk (F.map (headArrow a X)) (F.map (tailArrow a X)))
  exponential : ∀ (Γ : Ctx S) (s : S.Srt),
    Exponential (contextOf (sortOf F) Γ) (sortOf F s) (F.obj (oneObj Γ s))

/-! ## The classifying functor preserves the structure -/

namespace Model

variable (M : Model S D)

/-- The classifying functor sends a term to its curried generic value. -/
theorem assignHom_termArrow {X : Object S} {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    M.assignHom (termArrow t) = lift (M.curry (M.generic X.arities t)) (toUnit _) :=
  rfl

theorem assignHom_headArrow (a : MetaArity S) (X : Object S) :
    M.assignHom (headArrow a X) = lift (fst _ _) (toUnit _) := by
  change lift (M.curry (M.generic (a :: X.arities)
    (metaVar (M := a :: X.arities) ⟨0, Nat.succ_pos _⟩))) (toUnit _) = _
  rw [M.generic_metaVar]
  rfl

theorem assignHom_tailArrow (a : MetaArity S) (X : Object S) :
    M.assignHom (tailArrow a X) = snd _ _ := by
  unfold assignHom
  have components : (fun i : Fin X.arities.length =>
      M.curry (M.generic (consObj a X).arities (tailArrow a X i))) =
      fun i => snd _ _ ≫ M.familyProj X.arities i := by
    funext i
    exact M.generic_metaVar (a :: X.arities) i.succ
  rw [components]
  exact M.familyLift_eta X.arities (snd _ _)

/-- A product with the terminal object in the second place. -/
def unitFanIsLimit (P Q : D) :
    IsLimit (BinaryFan.mk (lift (fst P Q) (toUnit (P ⊗ Q)) : P ⊗ Q ⟶ P ⊗ 𝟙_ D) (snd P Q)) :=
  BinaryFan.IsLimit.mk _ (fun f g => lift (f ≫ fst _ _) g)
    (fun f g => by
      apply hom_ext
      · simp
      · exact toUnit_unique _ _)
    (fun f g => by simp)
    (fun f g m hf hg => by
      apply hom_ext
      · simp only [lift_fst]
        rw [← hf]
        simp
      · simp only [lift_snd]
        exact hg)

/-- The fan of a context `a :: X` under the classifying functor is a product. -/
def consIsLimit (a : MetaArity S) (X : Object S) :
    IsLimit (BinaryFan.mk (M.classifyingFunctor.map (headArrow a X))
      (M.classifyingFunctor.map (tailArrow a X))) := by
  change IsLimit (BinaryFan.mk (M.assignHom (headArrow a X)) (M.assignHom (tailArrow a X)))
  rw [assignHom_headArrow, assignHom_tailArrow]
  exact unitFanIsLimit _ _

/-! ### The sort and context isomorphisms -/

/-- A one-metavariable family is its power. -/
def powerIso (Γ : Ctx S) (s : S.Srt) : M.family [(Γ, s)] ≅ M.power Γ s where
  hom := fst _ _
  inv := lift (𝟙 _) (toUnit _)
  hom_inv_id := by
    apply hom_ext
    · simp
    · exact toUnit_unique _ _
  inv_hom_id := lift_fst _ _

/-- The power of the empty context is the sort. -/
def emptyPowerIso (γ : S.Srt) : M.power [] γ ≅ M.sort γ where
  hom := lift (toUnit _) (𝟙 _) ≫ M.eval [] γ
  inv := M.curry (Γ := []) (snd (𝟙_ D) (M.sort γ))
  hom_inv_id := by
    apply M.hom_ext_power
    rw [M.uncurry_natural, M.uncurry_curry]
    change _ = (M.ctx [] ◁ 𝟙 _) ≫ M.eval [] γ
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
    have unitSwap : ((M.ctx [] ◁ (lift (toUnit _) (𝟙 _) ≫ M.eval [] γ)) ≫ snd _ _ :
        M.ctx [] ⊗ M.power [] γ ⟶ M.sort γ) =
        (lift (toUnit _) (snd _ _) : M.ctx [] ⊗ M.power [] γ ⟶ 𝟙_ D ⊗ M.power [] γ) ≫ M.eval [] γ := by
      rw [whiskerLeft_snd, ← Category.assoc, comp_lift, comp_toUnit, Category.comp_id]
    have unitId : (lift (toUnit _) (snd _ _) : M.ctx [] ⊗ M.power [] γ ⟶ 𝟙_ D ⊗ M.power [] γ) = 𝟙 _ := by
      apply hom_ext
      · exact toUnit_unique _ _
      · simp
    rw [unitSwap, unitId, Category.id_comp]
  inv_hom_id := by
    have : M.curry (Γ := []) (snd (𝟙_ D) (M.sort γ)) ≫ lift (toUnit _) (𝟙 _) =
        lift (toUnit _) (𝟙 _) ≫ (M.ctx [] ◁ M.curry (Γ := []) (snd (𝟙_ D) (M.sort γ))) := by
      apply hom_ext
      · exact toUnit_unique _ _
      · simp
    rw [← Category.assoc, this, Category.assoc, M.curry_eval, lift_snd]

/-- The sort object of the classifying functor is the sort. -/
def sortIso (γ : S.Srt) : M.family [([], γ)] ≅ M.sort γ :=
  (M.powerIso [] γ).trans (M.emptyPowerIso γ)

/-- The context product of the classifying functor is the context product. -/
def ctxIso : ∀ Γ : Ctx S, contextOf (sortOf M.classifyingFunctor) Γ ≅ M.ctx Γ
  | [] => Iso.refl _
  | γ :: Γ => tensorIso (M.sortIso γ) (ctxIso Γ)

/-- The exponentials of the classifying functor. -/
def classifyingExponential (Γ : Ctx S) (s : S.Srt) :
    Exponential (contextOf (sortOf M.classifyingFunctor) Γ) (sortOf M.classifyingFunctor s)
      (M.classifyingFunctor.obj (oneObj Γ s)) :=
  (M.exponential Γ s).transport (M.ctxIso Γ) (M.sortIso s).symm (M.powerIso Γ s).symm

/-! ### Substitution goes to evaluation -/

/-- The value of a closed family at the stage of its own metavariables. -/
def pointValue {N : List (MetaArity S)} {s : S.Srt} (x : M.Elem N [] s) : M.family N ⟶ M.sort s :=
  x.value (M.family N) (𝟙 _) (fun _ v => nomatch v)

theorem curry_comp_emptyPower {N : List (MetaArity S)} {s : S.Srt}
    (g : M.ctx [] ⊗ M.family N ⟶ M.sort s) :
    M.curry g ≫ (M.emptyPowerIso s).hom = lift (toUnit _) (𝟙 _) ≫ g := by
  change M.curry g ≫ lift (toUnit _) (𝟙 _) ≫ M.eval [] s = _
  have : M.curry g ≫ lift (toUnit _) (𝟙 _) = lift (toUnit _) (𝟙 _) ≫ (M.ctx [] ◁ M.curry g) := by
    apply hom_ext
    · exact toUnit_unique _ _
    · simp
  rw [← Category.assoc, this, Category.assoc, M.curry_eval]

theorem classify_sortIso {X : Object S} {s : S.Srt} (t : Term (withMetas S X.arities) [] s) :
    M.classifyingFunctor.map (termArrow t) ≫ (M.sortIso s).hom =
      M.pointValue (M.interp X.arities t) := by
  change M.assignHom (termArrow t) ≫ (fst _ _ ≫ (M.emptyPowerIso s).hom) = _
  rw [assignHom_termArrow, lift_fst_assoc, curry_comp_emptyPower]
  unfold generic pointValue
  rw [M.value_eq_generic (M.interp X.arities t) (M.family X.arities) (𝟙 _)]
  rfl

theorem tupleF_ctxIso {X : Object S} : ∀ {Γ : Ctx S} (ρ : Sub (withMetas S X.arities) Γ []),
    tupleF M.classifyingFunctor ρ ≫ (M.ctxIso Γ).hom =
      M.tupleEnv (fun γ v => M.pointValue (M.interp X.arities (ρ γ v)))
  | [], _ => toUnit_unique _ _
  | γ :: Γ, ρ => by
      change lift _ _ ≫ ((M.sortIso γ).hom ⊗ₘ (M.ctxIso Γ).hom) = lift _ _
      rw [lift_map, M.classify_sortIso, tupleF_ctxIso (fun γ v => ρ γ (.succ v))]

/-- **Substitution goes to evaluation** under the classifying functor. -/
theorem classify_subst (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) (ρ : Sub (withMetas S X.arities) Γ []) :
    M.classifyingFunctor.map (termArrow (bind ρ t)) =
      lift (tupleF M.classifyingFunctor ρ) (M.classifyingFunctor.map (termArrow t)) ≫
        (M.classifyingExponential Γ s).eval := by
  rw [← cancel_mono (M.sortIso s).hom, M.classify_sortIso, Category.assoc]
  change M.pointValue (M.interp X.arities (bind ρ t)) =
    lift (tupleF M.classifyingFunctor ρ) (M.classifyingFunctor.map (termArrow t)) ≫
      (((M.ctxIso Γ).hom ⊗ₘ fst _ _) ≫ M.eval Γ s ≫ (M.sortIso s).inv) ≫ (M.sortIso s).hom
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, lift_map_assoc,
    M.tupleF_ctxIso]
  rw [show M.classifyingFunctor.map (termArrow t) = lift (M.curry (M.generic X.arities t)) (toUnit _)
    from M.assignHom_termArrow t, lift_fst]
  have split : (lift (M.tupleEnv (fun γ v => M.pointValue (M.interp X.arities (ρ γ v))))
      (M.curry (M.generic X.arities t)) : M.family X.arities ⟶ M.ctx Γ ⊗ M.power Γ s) =
      lift (M.tupleEnv (fun γ v => M.pointValue (M.interp X.arities (ρ γ v)))) (𝟙 _) ≫
        (M.ctx Γ ◁ M.curry (M.generic X.arities t)) := by
    rw [lift_whiskerLeft, Category.id_comp]
  rw [split, Category.assoc, M.curry_eval]
  unfold pointValue generic
  rw [M.interp_bind, ← M.value_eq_generic]

/-- **The classifying functor of a model preserves products, with the chosen
exponentials.** -/
def classifyingCartesian : CartesianArities M.classifyingFunctor where
  terminal := isTerminalTensorUnit
  cons := M.consIsLimit
  exponential := M.classifyingExponential

end Model

end Mettapedia.OSLF.Binding.CategoricalBindingModel
