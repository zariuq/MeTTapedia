import Mettapedia.OSLF.Syntax.ContextualTermAbstraction

/-!
# The exponential universal property of binder-extended intrinsic terms

For any signature and two sorts, the presheaf of terms with one additional
bound variable represents the exponential hom-set of the two corresponding
term presheaves. The comparison is explicit: curry evaluates a natural
operation at the fresh variable, and uncurry uses capture-avoiding plugging.
Both round trips and naturality in the arbitrary test presheaf are proved.

This identifies the binding *context* with the categorical exponential. It
does not equate an authored application of an authored lambda constructor with
capture-avoiding body evaluation; in the Chapter 7 lambda presentation that
comparison is an operational beta step.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualTermAbstraction

open CategoryTheory

variable {S : Signature}

abbrev ContextBase (S : Signature) := (Syntactic.Ctxt S)ᵒᵖ

def extendedContext (binder : S.Srt) (X : ContextBase S) : ContextBase S :=
  Opposite.op ⟨binder :: X.unop.vars⟩

def weakenArrow (binder : S.Srt) (X : ContextBase S) :
    X ⟶ extendedContext binder X :=
  Quiver.Hom.op (fun _ v => Term.var (Var.succ v))

def extendArrow {X Y : ContextBase S} (binder : S.Srt)
    (f : X ⟶ Y) :
    extendedContext binder X ⟶ extendedContext binder Y :=
  Quiver.Hom.op (liftSub f.unop [binder])

def plugArrow {X : ContextBase S} {binder : S.Srt}
    (arg : Term S X.unop.vars binder) :
    extendedContext binder X ⟶ X :=
  Quiver.Hom.op (extend arg)

theorem extendArrow_newVar {X Y : ContextBase S} (binder : S.Srt)
    (f : X ⟶ Y) :
    (Syntactic.termPresheaf S binder).map (extendArrow binder f)
      (Term.var Var.zero) = Term.var Var.zero := by
  rfl

theorem weaken_extend (binder : S.Srt) {X Y : ContextBase S}
    (f : X ⟶ Y) :
    weakenArrow binder X ≫ extendArrow binder f =
      f ≫ weakenArrow binder Y := by
  apply Quiver.Hom.unop_inj
  funext sort v
  change bind (liftSub f.unop [binder]) (Term.var (Var.succ v)) =
    bind (fun _ w => Term.var (Var.succ w)) (f.unop sort v)
  exact (bind_var_eq_rename (fun _ w => Var.succ w) (f.unop sort v)).symm

theorem weaken_plug {X : ContextBase S} {binder : S.Srt}
    (arg : Term S X.unop.vars binder) :
    weakenArrow binder X ≫ plugArrow arg = 𝟙 X := by
  apply Quiver.Hom.unop_inj
  funext sort v
  rfl

theorem plug_newVar {X : ContextBase S} {binder : S.Srt}
    (arg : Term S X.unop.vars binder) :
    (Syntactic.termPresheaf S binder).map (plugArrow arg)
      (Term.var Var.zero) = arg := by
  rfl

/-- A natural operation on an external input and a fresh bound variable
determines a body natural in the external input. -/
def curryBody (F : ContextBase S ⥤ Type) (binder result : S.Srt)
    (operation : FunctorToTypes.prod F (Syntactic.termPresheaf S binder) ⟶
      Syntactic.termPresheaf S result) :
    F ⟶ boundTermPresheaf S binder result where
  app X := TypeCat.ofHom (fun input =>
    operation.app (extendedContext binder X)
      (F.map (weakenArrow binder X) input, Term.var Var.zero))
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    change operation.app (extendedContext binder Y)
      (F.map (weakenArrow binder Y) (F.map f input), Term.var Var.zero) =
      bind (liftSub f.unop [binder])
        (operation.app (extendedContext binder X)
          (F.map (weakenArrow binder X) input, Term.var Var.zero))
    have natural := NatTrans.naturality_apply operation
      (extendArrow binder f)
      ((F.map (weakenArrow binder X) input, Term.var Var.zero) :
        (FunctorToTypes.prod F (Syntactic.termPresheaf S binder)).obj
          (extendedContext binder X))
    have inputMap :
        F.map (extendArrow binder f) (F.map (weakenArrow binder X) input) =
          F.map (weakenArrow binder Y) (F.map f input) := by
      calc
        F.map (extendArrow binder f) (F.map (weakenArrow binder X) input) =
            F.map (weakenArrow binder X ≫ extendArrow binder f) input := by
          exact (congrArg (fun arrow => arrow input)
            (F.map_comp (weakenArrow binder X) (extendArrow binder f))).symm
        _ = F.map (f ≫ weakenArrow binder Y) input := by
          rw [weaken_extend]
        _ = F.map (weakenArrow binder Y) (F.map f input) := by
          exact congrArg (fun arrow => arrow input)
            (F.map_comp f (weakenArrow binder Y))
    change operation.app (extendedContext binder Y)
        (F.map (extendArrow binder f) (F.map (weakenArrow binder X) input),
          Term.var Var.zero) =
      bind (liftSub f.unop [binder])
        (operation.app (extendedContext binder X)
          (F.map (weakenArrow binder X) input, Term.var Var.zero)) at natural
    rw [inputMap] at natural
    exact natural

/-- Apply an abstracted body to an explicit input term. -/
def uncurryBody (F : ContextBase S ⥤ Type) (binder result : S.Srt)
    (body : F ⟶ boundTermPresheaf S binder result) :
    FunctorToTypes.prod F (Syntactic.termPresheaf S binder) ⟶
      Syntactic.termPresheaf S result where
  app X := TypeCat.ofHom (fun pair => inst (body.app X pair.1) pair.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨input, arg⟩
    have natural := NatTrans.naturality_apply body f input
    change body.app Y (F.map f input) =
      bind (liftSub f.unop [binder]) (body.app X input) at natural
    change inst (body.app Y (F.map f input)) (bind f.unop arg) =
      bind f.unop (inst (body.app X input) arg)
    rw [natural]
    exact (ContextualLinearSubstitution.bind_inst f.unop
      (body.app X input) arg).symm

theorem uncurry_curry (F : ContextBase S ⥤ Type) (binder result : S.Srt)
    (operation : FunctorToTypes.prod F (Syntactic.termPresheaf S binder) ⟶
      Syntactic.termPresheaf S result) :
    uncurryBody F binder result (curryBody F binder result operation) =
      operation := by
  ext X pair
  rcases pair with ⟨input, arg⟩
  change Term S X.unop.vars binder at arg
  change inst (operation.app (extendedContext binder X)
      (F.map (weakenArrow binder X) input, Term.var Var.zero)) arg =
    operation.app X (input, arg)
  have natural := NatTrans.naturality_apply operation (plugArrow arg)
    ((F.map (weakenArrow binder X) input, Term.var Var.zero) :
      (FunctorToTypes.prod F (Syntactic.termPresheaf S binder)).obj
        (extendedContext binder X))
  have inputBack :
      F.map (plugArrow arg) (F.map (weakenArrow binder X) input) = input := by
    calc
      F.map (plugArrow arg) (F.map (weakenArrow binder X) input) =
          F.map (weakenArrow binder X ≫ plugArrow arg) input := by
        exact (congrArg (fun arrow => arrow input)
          (F.map_comp (weakenArrow binder X) (plugArrow arg))).symm
      _ = F.map (𝟙 X) input := by rw [weaken_plug]
      _ = input := by rw [F.map_id]; rfl
  change operation.app X
      (F.map (plugArrow arg) (F.map (weakenArrow binder X) input), arg) =
    inst (operation.app (extendedContext binder X)
      (F.map (weakenArrow binder X) input, Term.var Var.zero)) arg at natural
  rw [inputBack] at natural
  exact natural.symm

/-- Weakening the ambient context and then plugging its newly available
variable leaves a body unchanged, including its original distinguished binder. -/
theorem plug_mapBody_weaken {Γ : Ctx S} (binder result : S.Srt)
    (body : Term S (binder :: Γ) result) :
    inst (mapBody binder result
        (weakenArrow binder (Opposite.op ⟨Γ⟩)).unop body)
      (Term.var (Var.zero : Var (binder :: Γ) binder)) = body := by
  simp only [mapBody, inst, bind_comp]
  have substitution :
      (fun sort v =>
        bind (extend (Term.var (Var.zero : Var (binder :: Γ) binder)))
          (liftSub (weakenArrow binder (Opposite.op ⟨Γ⟩)).unop [binder]
            sort v)) =
        (fun sort v => Term.var v) := by
    funext sort v
    cases v with
    | zero => rfl
    | succ w => rfl
  exact (congrArg (fun sigma => bind sigma body) substitution).trans
    (bind_id body)

theorem curry_uncurry (F : ContextBase S ⥤ Type) (binder result : S.Srt)
    (body : F ⟶ boundTermPresheaf S binder result) :
    curryBody F binder result (uncurryBody F binder result body) = body := by
  ext X input
  change inst (body.app (extendedContext binder X)
      (F.map (weakenArrow binder X) input))
      (Term.var Var.zero) = body.app X input
  have natural := NatTrans.naturality_apply body
    (weakenArrow binder X) input
  change body.app (extendedContext binder X)
      (F.map (weakenArrow binder X) input) =
    mapBody binder result (weakenArrow binder X).unop
      (body.app X input) at natural
  rw [natural]
  exact plug_mapBody_weaken binder result (body.app X input)

/-- The binder-extended term presheaf represents the exponential hom-set
against the two represented term presheaves. -/
def boundTermHomEquiv (F : ContextBase S ⥤ Type)
    (binder result : S.Srt) :
    (FunctorToTypes.prod F (Syntactic.termPresheaf S binder) ⟶
      Syntactic.termPresheaf S result) ≃
      (F ⟶ boundTermPresheaf S binder result) where
  toFun := curryBody F binder result
  invFun := uncurryBody F binder result
  left_inv := uncurry_curry F binder result
  right_inv := curry_uncurry F binder result

/-- Precomposition of the test presheaf, leaving the bound program
coordinate untouched. -/
def productPrecompose {F G : ContextBase S ⥤ Type}
    (binder : S.Srt) (α : G ⟶ F) :
    FunctorToTypes.prod G (Syntactic.termPresheaf S binder) ⟶
      FunctorToTypes.prod F (Syntactic.termPresheaf S binder) where
  app X := TypeCat.ofHom (fun pair => (α.app X pair.1, pair.2))
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨input, arg⟩
    change (α.app Y (G.map f input),
        (Syntactic.termPresheaf S binder).map f arg) =
      (F.map f (α.app X input),
        (Syntactic.termPresheaf S binder).map f arg)
    exact Prod.ext (NatTrans.naturality_apply α f input) rfl

/-- The exponential comparison is natural in the arbitrary test presheaf. -/
theorem curryBody_natural_test {F G : ContextBase S ⥤ Type}
    (binder result : S.Srt) (α : G ⟶ F)
    (operation : FunctorToTypes.prod F (Syntactic.termPresheaf S binder) ⟶
      Syntactic.termPresheaf S result) :
    curryBody G binder result (productPrecompose binder α ≫ operation) =
      α ≫ curryBody F binder result operation := by
  ext X input
  change operation.app (extendedContext binder X)
      (α.app (extendedContext binder X)
        (G.map (weakenArrow binder X) input), Term.var Var.zero) =
    operation.app (extendedContext binder X)
      (F.map (weakenArrow binder X) (α.app X input), Term.var Var.zero)
  exact congrArg
    (fun mapped => operation.app (extendedContext binder X)
      (mapped, Term.var Var.zero))
    (NatTrans.naturality_apply α (weakenArrow binder X) input)

/-- The inverse comparison also commutes with precomposition in the test
presheaf; no choice of a privileged context is hidden in the equivalence. -/
theorem uncurryBody_natural_test {F G : ContextBase S ⥤ Type}
    (binder result : S.Srt) (α : G ⟶ F)
    (body : F ⟶ boundTermPresheaf S binder result) :
    uncurryBody G binder result (α ≫ body) =
      productPrecompose binder α ≫ uncurryBody F binder result body := by
  ext X pair
  rfl

end Mettapedia.OSLF.Binding.ContextualTermAbstraction
