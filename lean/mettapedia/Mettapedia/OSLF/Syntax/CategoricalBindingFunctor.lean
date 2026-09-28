import Mettapedia.OSLF.Syntax.CategoricalBindingKripke
import Mettapedia.OSLF.Syntax.SecondOrderContextCategory

/-!
# The classifying functor of a model

A model of a binding signature interprets the second-order context category:
a metavariable context is sent to the product of the function objects of its
arities, and an assignment to the tuple of the curried interpretations of its
terms at the generic stage.

Functoriality is the instantiation lemma: interpreting an instantiated term
is interpreting the term at the restaged element. Both sides are constructor
preserving maps out of the raw terms of the extended signature, so they agree
by the uniqueness of the raw fold. No induction on terms is performed here.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)
open Mettapedia.OSLF.Binding.SecondOrderContext (Object)

universe u v w

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- The same arguments, read over another metavariable extension of the
signature. Only the sorts are used, and those agree. -/
def recastArgs {S : Signature} {N₁ N₂ : List (MetaArity S)} {F : Ctx S → S.Srt → Type w} :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S},
      FamilyArgs (withMetas S N₁) F arity Γ → FamilyArgs (withMetas S N₂) F arity Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head (recastArgs tail)

namespace Model

variable {S : Signature} (M : Model S D)

/-! ## Generic elements -/

/-- The generic environment of a term context beside a metavariable stage. -/
def genericEnv (Γ : Ctx S) (W : D) : M.Env (M.ctx Γ ⊗ W) Γ :=
  M.restage (fst _ _) (M.projections Γ)

/-- The value of a term at its generic stage. -/
def generic (N : List (MetaArity S)) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S N) Γ s) : M.ctx Γ ⊗ M.family N ⟶ M.sort s :=
  (M.interp N t).value (M.ctx Γ ⊗ M.family N) (snd _ _) (M.genericEnv Γ (M.family N))

/-- Every value of a natural family is read off its generic value. -/
theorem value_eq_generic (N : List (MetaArity S)) {Γ : Ctx S} {s : S.Srt}
    (x : M.Elem N Γ s) (Z : D) (m : Z ⟶ M.family N) (ρ : M.Env Z Γ) :
    x.value Z m ρ =
      lift (M.tupleEnv ρ) m ≫ x.value (M.ctx Γ ⊗ M.family N) (snd _ _) (M.genericEnv Γ (M.family N)) := by
  rw [← x.natural, lift_snd]
  congr 1
  funext γ v
  change ρ γ v = lift (M.tupleEnv ρ) m ≫ fst _ _ ≫ projectVar M.sort v
  rw [lift_fst_assoc, M.tupleEnv_projectVar]

theorem lift_fst_snd_comp {X Y Y' : D} (g : Y ⟶ Y') :
    lift (fst X Y) (snd X Y ≫ g) = X ◁ g := by
  apply hom_ext <;> simp

/-! ## Assignments -/

/-- The arrow interpreting an assignment of metavariables. -/
def assignHom {X Y : Object S} (σ : X ⟶ Y) : M.family X.arities ⟶ M.family Y.arities :=
  M.familyLift Y.arities fun j => M.curry (M.generic X.arities (σ j))

theorem assignHom_proj {X Y : Object S} (σ : X ⟶ Y) (j : Fin Y.arities.length) :
    M.assignHom σ ≫ M.familyProj Y.arities j = M.curry (M.generic X.arities (σ j)) :=
  M.familyLift_proj _ _ j

/-- A metavariable evaluated at its arguments, after a change of metavariable
stage. -/
def metaElemAlong {N N' : List (MetaArity S)} (f : M.family N ⟶ M.family N') {Γ : Ctx S}
    (j : Fin N'.length)
    (args : FamilyArgs (withMetas S N') (M.Elem N) ((N'.get j).1.map fun b => ([], b)) Γ) :
    M.Elem N Γ (N'.get j).2 where
  value := fun Z m ρ =>
    lift (M.tupleCtx (N'.get j).1 args Z m ρ) (m ≫ f ≫ M.familyProj N' j) ≫ M.eval _ _
  natural := fun h m ρ => by
    rw [M.tupleCtx_natural, Category.assoc, ← comp_lift_assoc]

/-- Restaging a natural family along a change of metavariable stage. -/
def restageElem {N N' : List (MetaArity S)} (f : M.family N ⟶ M.family N') {Γ : Ctx S}
    {s : S.Srt} (x : M.Elem N' Γ s) : M.Elem N Γ s where
  value := fun Z m ρ => x.value Z (m ≫ f) ρ
  natural := fun h m ρ => by rw [Category.assoc, x.natural]

/-! ## Tuples of arguments -/

theorem tupleArgs_recast {N N₁ N₂ : List (MetaArity S)} :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs (withMetas S N₁) (M.Elem N) arity Γ) (Z : D) (m : Z ⟶ M.family N)
      (ρ : M.Env Z Γ),
      M.tupleArgs (recastArgs (N₂ := N₂) args) Z m ρ = M.tupleArgs args Z m ρ
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons head tail, Z, m, ρ => by
      show lift _ _ = lift _ _
      rw [tupleArgs_recast tail Z m ρ]

theorem tupleCtx_recast {N N₁ N₂ : List (MetaArity S)} :
    ∀ (bs : List S.Srt) {Γ : Ctx S}
      (args : FamilyArgs (withMetas S N₁) (M.Elem N) (bs.map fun b => ([], b)) Γ) (Z : D)
      (m : Z ⟶ M.family N) (ρ : M.Env Z Γ),
      M.tupleCtx bs (recastArgs (N₂ := N₂) args) Z m ρ = M.tupleCtx bs args Z m ρ
  | [], _, .nil, _, _, _ => rfl
  | _ :: bs, _, .cons head tail, Z, m, ρ => by
      show lift _ _ = lift _ _
      rw [tupleCtx_recast bs tail Z m ρ]

theorem opElem_recast {N N₁ N₂ : List (MetaArity S)} {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : FamilyArgs (withMetas S N₁) (M.Elem N) (S.arity o) Γ) :
    M.opElem o (recastArgs (N₂ := N₂) args) = M.opElem o args := by
  apply Elem.ext
  funext Z m ρ
  change M.tupleArgs (recastArgs args) Z m ρ ≫ M.op o = M.tupleArgs args Z m ρ ≫ M.op o
  rw [M.tupleArgs_recast]

/-- The tuple of the arguments of a metavariable is the environment they name. -/
theorem tupleCtx_foldArgs (N : List (MetaArity S)) :
    ∀ (bs : List S.Srt) {Γ : Ctx S} (args : Args (withMetas S N) (bs.map fun b => ([], b)) Γ)
      (Z : D) (m : Z ⟶ M.family N) (ρ : M.Env Z Γ),
      M.tupleCtx bs (FreeBindingTerms.foldArgs (M.kripke N).toRaw args) Z m ρ =
        M.tupleEnv fun γ v => (M.interp N (argsToSub args γ v)).value Z m ρ
  | [], _, .nil, Z, _, _ => toUnit_unique _ _
  | _ :: bs, _, .cons head tail, Z, m, ρ => by
      show lift _ _ = lift _ _
      rw [tupleCtx_foldArgs N bs tail Z m ρ]
      rfl

theorem tupleArgs_restage {N N' : List (MetaArity S)} (f : M.family N ⟶ M.family N') :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs (withMetas S N') (M.Elem N') arity Γ) (Z : D) (m : Z ⟶ M.family N)
      (ρ : M.Env Z Γ),
      M.tupleArgs (FamilyArgs.map (fun x => M.restageElem f x) args) Z m ρ =
        M.tupleArgs args Z (m ≫ f) ρ
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons head tail, Z, m, ρ => by
      show lift (M.curry (head.value _ ((snd _ _ ≫ m) ≫ f) _)) _ = lift _ _
      rw [tupleArgs_restage f tail Z m ρ, Category.assoc]

theorem tupleCtx_restage {N N' : List (MetaArity S)} (f : M.family N ⟶ M.family N') :
    ∀ (bs : List S.Srt) {Γ : Ctx S}
      (args : FamilyArgs (withMetas S N') (M.Elem N') (bs.map fun b => ([], b)) Γ) (Z : D)
      (m : Z ⟶ M.family N) (ρ : M.Env Z Γ),
      M.tupleCtx bs (FamilyArgs.map (fun x => M.restageElem f x) args) Z m ρ =
        M.tupleCtx bs args Z (m ≫ f) ρ
  | [], _, .nil, _, _, _ => rfl
  | _ :: bs, _, .cons head tail, Z, m, ρ => by
      show lift _ _ = lift _ _
      rw [tupleCtx_restage f bs tail Z m ρ]
      rfl

/-- Folding instantiated syntactic arguments is mapping the interpretation of
the instantiation over the semantic arguments. -/
theorem foldArgs_instIntoArgs {N N' : List (MetaArity S)}
    (σ : (i : Fin N'.length) → Term (withMetas S N) (N'.get i).1 (N'.get i).2) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs (withMetas S N') (Term (withMetas S N')) arity Γ),
      FreeBindingTerms.foldArgs (M.kripke N).toRaw
          (instIntoArgs σ (FreeBindingTerms.terms.familyToSyntax (withMetas S N') args)) =
        recastArgs (FamilyArgs.map (fun t => M.interp N (instInto σ t)) args)
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      show FamilyArgs.cons _ _ = FamilyArgs.cons _ _
      rw [foldArgs_instIntoArgs σ tail]
      rfl

/-! ## The instantiation lemma -/

section Instantiation

variable {X Y : Object S} (σ : X ⟶ Y)

/-- The raw algebra of natural families at `X`, read as an algebra of the
signature extended by the metavariables of `Y` through the assignment. -/
def alongAlgebra : FreeBindingTerms.Algebra.{max u v} (withMetas S Y.arities) where
  Carrier := fun Γ s => M.Elem X.arities Γ s
  injectVar := fun v => ⟨fun _ _ ρ => ρ _ v, fun _ _ _ => rfl⟩
  operation := fun o args =>
    match o, args with
    | .inl o, args => M.opElem o args
    | .inr (.mk j), args => M.metaElemAlong (M.assignHom σ) j args

/-- Interpreting after instantiation. -/
def instantiateThenInterp :
    FreeBindingTerms.Hom (FreeBindingTerms.terms (withMetas S Y.arities)) (M.alongAlgebra σ) where
  map := fun t => M.interp X.arities (instInto σ t)
  map_variable := fun _ => rfl
  map_operation := by
    intro Γ s o args
    match o, args with
    | .inl o, args =>
        change M.opElem o (FreeBindingTerms.foldArgs (M.kripke X.arities).toRaw
            (instIntoArgs σ (FreeBindingTerms.terms.familyToSyntax _ args))) =
          M.opElem o (FamilyArgs.map (fun t => M.interp X.arities (instInto σ t)) args)
        have folded := M.foldArgs_instIntoArgs σ args
        rw [folded]
        exact M.opElem_recast o _
    | .inr (.mk j), args =>
        apply Elem.ext
        funext Z m ρ
        change (M.interp X.arities (bind (argsToSub (instIntoArgs σ
            (FreeBindingTerms.terms.familyToSyntax _ args))) (σ j))).value Z m ρ =
          lift (M.tupleCtx (Y.arities.get j).1 (FamilyArgs.map
            (fun t => M.interp X.arities (instInto σ t)) args) Z m ρ)
            (m ≫ M.assignHom σ ≫ M.familyProj Y.arities j) ≫ M.eval _ _
        rw [M.interp_bind, M.value_eq_generic, M.assignHom_proj, ← lift_whiskerLeft_assoc,
          M.curry_eval]
        have tupled := M.tupleCtx_foldArgs X.arities (Y.arities.get j).1
          (instIntoArgs σ (FreeBindingTerms.terms.familyToSyntax _ args)) Z m ρ
        have folded := M.foldArgs_instIntoArgs σ args
        rw [← tupled, folded, M.tupleCtx_recast]
        rfl

/-- Interpreting, then restaging along the assignment. -/
def interpThenRestage :
    FreeBindingTerms.Hom (FreeBindingTerms.terms (withMetas S Y.arities)) (M.alongAlgebra σ) where
  map := fun t => M.restageElem (M.assignHom σ) (M.interp Y.arities t)
  map_variable := fun _ => rfl
  map_operation := by
    intro Γ s o args
    match o, args with
    | .inl o, args =>
        apply Elem.ext
        funext Z m ρ
        change M.tupleArgs (FreeBindingTerms.foldArgs (M.kripke Y.arities).toRaw
            (FreeBindingTerms.terms.familyToSyntax _ args)) Z (m ≫ M.assignHom σ) ρ ≫ M.op o =
          M.tupleArgs (FamilyArgs.map (fun t => M.restageElem (M.assignHom σ)
            (M.interp Y.arities t)) args) Z m ρ ≫ M.op o
        have folded := FreeBindingTerms.foldArgs_familyToSyntax (M.kripke Y.arities).toRaw args
        rw [folded]
        have restaged := M.tupleArgs_restage (M.assignHom σ)
          (FamilyArgs.map (fun t => M.interp Y.arities t) args) Z m ρ
        have composed := FamilyArgs.map_comp (fun t => M.interp Y.arities t)
          (fun x => M.restageElem (M.assignHom σ) x) args
        exact congrArg (· ≫ M.op o)
          (restaged.symm.trans (congrArg (fun a => M.tupleArgs a Z m ρ) composed))
    | .inr (.mk j), args =>
        apply Elem.ext
        funext Z m ρ
        change lift (M.tupleCtx (Y.arities.get j).1 (FreeBindingTerms.foldArgs
            (M.kripke Y.arities).toRaw (FreeBindingTerms.terms.familyToSyntax _ args)) Z
            (m ≫ M.assignHom σ) ρ) ((m ≫ M.assignHom σ) ≫ M.familyProj Y.arities j) ≫ M.eval _ _ =
          lift (M.tupleCtx (Y.arities.get j).1 (FamilyArgs.map (fun t => M.restageElem
            (M.assignHom σ) (M.interp Y.arities t)) args) Z m ρ)
            (m ≫ M.assignHom σ ≫ M.familyProj Y.arities j) ≫ M.eval _ _
        have folded := FreeBindingTerms.foldArgs_familyToSyntax (M.kripke Y.arities).toRaw args
        rw [folded, Category.assoc]
        have restaged := M.tupleCtx_restage (M.assignHom σ) _
          (FamilyArgs.map (fun t => M.interp Y.arities t) args) Z m ρ
        have composed := FamilyArgs.map_comp (fun t => M.interp Y.arities t)
          (fun x => M.restageElem (M.assignHom σ) x) args
        exact congrArg (fun t => lift t (m ≫ M.assignHom σ ≫ M.familyProj Y.arities j) ≫ M.eval _ _)
          (restaged.symm.trans (congrArg (fun a => M.tupleCtx _ a Z m ρ) composed))

/-- **Instantiation lemma.** Interpreting an instantiated term is interpreting
the term at the element restaged along the assignment. -/
theorem interp_instInto {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S Y.arities) Γ s) :
    M.interp X.arities (instInto σ t) = M.restageElem (M.assignHom σ) (M.interp Y.arities t) := by
  have unique := FreeBindingTerms.hom_unique (M.alongAlgebra σ) (M.instantiateThenInterp σ)
  have unique' := FreeBindingTerms.hom_unique (M.alongAlgebra σ) (M.interpThenRestage σ)
  have same := unique.trans unique'.symm
  exact congrArg (fun h : FreeBindingTerms.Hom _ _ => h.map t) same

theorem interp_instInto_value {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S Y.arities) Γ s)
    (Z : D) (m : Z ⟶ M.family X.arities) (ρ : M.Env Z Γ) :
    (M.interp X.arities (instInto σ t)).value Z m ρ =
      (M.interp Y.arities t).value Z (m ≫ M.assignHom σ) ρ := by
  rw [M.interp_instInto σ t]
  rfl

end Instantiation

/-! ## The functor -/

/-- The metavariable applied to its own variables is the projection. -/
theorem generic_metaVar (N : List (MetaArity S)) (j : Fin N.length) :
    M.curry (M.generic N (metaVar j)) = M.familyProj N j := by
  apply M.curry_unique
  have e : M.generic N (metaVar j) =
      lift (fst _ _) (snd _ _ ≫ M.familyProj N j) ≫ M.eval _ _ := by
    unfold generic metaVar
    rw [M.interp_meta]
    change lift (M.tupleCtx (N.get j).1 (FreeBindingTerms.foldArgs (M.kripke N).toRaw
        (idArgs (N.get j).1)) _ (snd _ _) (M.genericEnv _ _)) (snd _ _ ≫ M.familyProj N j) ≫
        M.eval _ _ = _
    rw [M.tupleCtx_foldArgs]
    congr 2
    symm
    apply M.tupleEnv_unique
    intro γ v
    rw [argsToSub_idArgs, M.interp_var]
    rfl
  rw [e, lift_fst_snd_comp]

/-- The classifying functor of a model: from second-order contexts to the
target. -/
@[reducible] def classifyingFunctor : Object S ⥤ D where
  obj X := M.family X.arities
  map σ := M.assignHom σ
  map_id X := by
    symm
    apply M.familyLift_unique
    intro j
    rw [Category.id_comp]
    exact (M.generic_metaVar X.arities j).symm
  map_comp σ τ := by
    symm
    apply M.familyLift_unique
    intro k
    rw [Category.assoc, M.assignHom_proj, ← M.curry_natural]
    congr 1
    unfold generic
    rw [← (M.interp _ (τ k)).natural, whiskerLeft_snd, ← M.interp_instInto_value σ (τ k)]
    congr 1
    funext γ v
    change (M.ctx _ ◁ M.assignHom σ) ≫ fst _ _ ≫ projectVar M.sort v = fst _ _ ≫ projectVar M.sort v
    rw [whiskerLeft_fst_assoc]

end Model

end Mettapedia.OSLF.Binding.CategoricalBindingModel
