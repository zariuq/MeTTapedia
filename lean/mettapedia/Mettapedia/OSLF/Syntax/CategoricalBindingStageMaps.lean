import Mettapedia.OSLF.Syntax.CategoricalBindingStageOperations
import Mettapedia.OSLF.Syntax.CategoricalBindingStage
import Mettapedia.OSLF.Syntax.CategoricalBindingInterpretationMaps

/-!
# Maps of binding models act on stage clones

A map of binding models preserving every contextual assignment moves a
generalized element through the function objects. At every stage this is a
map of binding clones. Substitution and each binding operator are the
interpretation of one term at a generalized element of a metavariable family,
and the map commutes with the interpretation of every term, because the term
is an assignment. The map is natural in the stage and carries the
interpretation of equation classes at a point to the interpretation at the
moved point.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open _root_.CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps (Hom)

universe u v


variable {S : Signature}

/-! ## Substitution and operators as terms in metavariables -/

/-- A metavariable of arity `Δ ⊢ γ` for each variable of `Γ`. -/
abbrev envArities (Γ Δ : Ctx S) : List (MetaArity S) := Γ.map fun γ => (Δ, γ)

/-- Each variable of `Γ` goes to its metavariable, applied to the variables
of `Δ`. -/
def envSub (Δ : Ctx S) : ∀ Γ : Ctx S, Sub (withMetas S (envArities Γ Δ)) Γ Δ
  | [], _, v => nomatch v
  | γ :: _, _, .zero => metaVar (M := envArities (γ :: _) Δ) ⟨0, Nat.succ_pos _⟩
  | γ :: Γ, _, .succ v => instInto (tailArrow (Δ, γ) ⟨envArities Γ Δ⟩) (envSub Δ Γ _ v)

/-- The metavariables of a substitution: the substituted term, then the
environment. -/
abbrev substObj (Γ Δ : Ctx S) (s : S.Srt) : Object S := consObj (Γ, s) ⟨envArities Γ Δ⟩

/-- The substituted term's metavariable, with the environment's
metavariables for its variables. -/
def substTerm (Γ Δ : Ctx S) (s : S.Srt) : Term (withMetas S (substObj Γ Δ s).arities) Δ s :=
  bind (fun γ v => instInto (tailArrow (Γ, s) ⟨envArities Γ Δ⟩) (envSub Δ Γ γ v))
    (metaVar (M := (substObj Γ Δ s).arities) ⟨0, Nat.succ_pos _⟩)

/-- A metavariable for each argument of an arity, depending on the
argument's binders followed by the ambient variables. -/
abbrev argArities (Γ : Ctx S) (L : List (List S.Srt × S.Srt)) : List (MetaArity S) :=
  L.map fun a => (a.1 ++ Γ, a.2)

/-- Each argument is its metavariable applied to its binders and the ambient
variables. -/
def argTerms (Γ : Ctx S) : ∀ L : List (List S.Srt × S.Srt),
    Args (withMetas S (argArities Γ L)) L Γ
  | [] => .nil
  | a :: L => .cons (metaVar (M := argArities Γ (a :: L)) ⟨0, Nat.succ_pos _⟩)
      (instIntoArgs (tailArrow (a.1 ++ Γ, a.2) ⟨argArities Γ L⟩) (argTerms Γ L))

/-- An operator applied to the metavariables of its arguments. -/
def opTermIn (Γ : Ctx S) {s : S.Srt} (o : S.Op s) :
    Term (withMetas S (argArities Γ (S.arity o))) Γ s :=
  Term.op (S := withMetas S (argArities Γ (S.arity o))) (Sum.inl o) (argTerms Γ (S.arity o))

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Model

variable (M : Model S D)

/-! ## Stage elements are interpretations at points -/

/-- A weakened term read at a point is the term read at the point's tail. -/
theorem restageElem_interp_tail (a : MetaArity S) (X : Object S) {Z : D}
    (p : Z ⟶ M.family (consObj a X).arities) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    M.restageElem p (M.interp (consObj a X).arities (instInto (tailArrow a X) t)) =
      M.restageElem (p ≫ snd _ _) (M.interp X.arities t) := by
  rw [M.interp_instInto (tailArrow a X) t, M.assignHom_tailArrow, restageElem_restageElem]

/-- The point of an environment of generalized elements. -/
noncomputable def envPoint {Z : D} (Δ : Ctx S) : ∀ {Γ : Ctx S},
    (∀ γ, Var Γ γ → M.ElemOver Z Δ γ) → (Z ⟶ M.family (envArities Γ Δ))
  | [], _ => toUnit Z
  | _ :: _, env => lift (M.elemEquiv (env _ .zero)) (envPoint Δ fun γ v => env γ (.succ v))


theorem restageElem_envSub {Z : D} (Δ : Ctx S) : ∀ {Γ : Ctx S}
    (env : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ) {γ : S.Srt} (v : Var Γ γ),
    M.restageElem (M.envPoint Δ env) (M.interp (envArities Γ Δ) (envSub Δ Γ γ v)) = env γ v
  | _ :: _, env, _, .zero =>
      (M.restageElem_interp_metaVar _ _ _).trans
        ((congrArg M.elemOfPoint (lift_fst _ _)).trans (M.elemEquiv.left_inv _))
  | _ :: Γ, env, _, .succ v => by
      refine (M.restageElem_interp_tail _ ⟨envArities Γ Δ⟩ _ _).trans ?_
      refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
      exact restageElem_envSub Δ (fun γ w => env γ (.succ w)) v

/-- **Substitution at a stage is the substitution term read at a point.** -/
theorem substitute_eq_restage {Z : D} {Γ Δ : Ctx S} {s : S.Srt} (x : M.ElemOver Z Γ s)
    (env : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ) :
    (M.kripkeSubstitution Z (N' := [])).substitute env x =
      M.restageElem (lift (M.elemEquiv x) (M.envPoint Δ env))
        (M.interp (substObj Γ Δ s).arities (substTerm Γ Δ s)) := by
  have head : M.elemOfPoint (lift (M.elemEquiv x) (M.envPoint Δ env) ≫
      M.familyProj (substObj Γ Δ s).arities ⟨0, Nat.succ_pos _⟩) = x :=
    (congrArg M.elemOfPoint (lift_fst _ _)).trans (M.elemEquiv.left_inv x)
  have environment : (fun γ v => M.restageElem (lift (M.elemEquiv x) (M.envPoint Δ env))
      (M.interp (substObj Γ Δ s).arities
        (instInto (tailArrow (Γ, s) ⟨envArities Γ Δ⟩) (envSub Δ Γ γ v)))) = env := by
    funext γ v
    refine (M.restageElem_interp_tail (Γ, s) ⟨envArities Γ Δ⟩
      (lift (M.elemEquiv x) (M.envPoint Δ env)) (envSub Δ Γ γ v)).trans ?_
    refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
    exact M.restageElem_envSub Δ env v
  refine Eq.trans ?_ (M.restageElem_interp_bind (substObj Γ Δ s).arities
    (lift (M.elemEquiv x) (M.envPoint Δ env)) (Γ := Γ) (Δ := Δ) (s := s) _
    (metaVar (M := (substObj Γ Δ s).arities) ⟨0, Nat.succ_pos _⟩)).symm
  exact congrArg₂ (fun e y => (M.kripkeSubstitution Z (N' := [])).substitute e y)
    environment.symm ((M.restageElem_interp_metaVar _ _ _).trans head).symm

/-- The point of the arguments of an operator. -/
noncomputable def argsPoint {Z : D} {Γ : Ctx S} : ∀ {L : List (List S.Srt × S.Srt)},
    FamilyArgs S (M.ElemOver Z) L Γ → (Z ⟶ M.family (argArities Γ L))
  | [], .nil => toUnit Z
  | _ :: _, .cons head tail => lift (M.elemEquiv head) (argsPoint tail)

theorem tupleArgs_argTerms {Z : D} {Γ : Ctx S} : ∀ {L : List (List S.Srt × S.Srt)}
    (args : FamilyArgs S (M.ElemOver Z) L Γ) (W : D) (w : W ⟶ Z) (ρ : M.Env W Γ),
    M.tupleArgs (FreeBindingTerms.foldArgs (M.kripke (argArities Γ L)).toRaw (argTerms Γ L)) W
        (w ≫ M.argsPoint args) ρ =
      M.tupleArgs (toAmbientArgs ⟨[]⟩ args) W w ρ
  | [], .nil, _, _, _ => rfl
  | a :: L, .cons head tail, W, w, ρ => by
      show lift _ _ = lift _ _
      congr 1
      · have atHead := congrArg
          (fun e : M.ElemOver Z (a.1 ++ Γ) a.2 => e.value (M.ctx a.1 ⊗ W) (snd _ _ ≫ w)
            (M.extendEnv a.1 ρ))
          ((M.restageElem_interp_metaVar _ (M.argsPoint (.cons head tail)) ⟨0, Nat.succ_pos _⟩).trans
            ((congrArg M.elemOfPoint (lift_fst _ _)).trans (M.elemEquiv.left_inv head)))
        refine congrArg M.curry (Eq.trans ?_ atHead)
        exact congrArg (fun m => (M.interp (argArities Γ (a :: L))
          (metaVar (M := argArities Γ (a :: L)) ⟨0, Nat.succ_pos _⟩)).value (M.ctx a.1 ⊗ W) m
            (M.extendEnv a.1 ρ)) (Category.assoc _ _ _).symm
      · refine (M.tupleArgs_instIntoArgs (tailArrow (a.1 ++ Γ, a.2) ⟨argArities Γ L⟩)
          (argTerms Γ L) W _ ρ).trans ?_
        rw [M.assignHom_tailArrow, Category.assoc]
        change M.tupleArgs _ W (w ≫ lift (M.elemEquiv head) (M.argsPoint tail) ≫ snd _ _) ρ = _
        rw [lift_snd]
        exact tupleArgs_argTerms tail W w ρ

/-- **An operator at a stage is the operator term read at a point.** -/
theorem opElem_eq_restage {Z : D} {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : FamilyArgs S (M.ElemOver Z) (S.arity o) Γ) :
    M.opElem o (toAmbientArgs ⟨[]⟩ args) =
      M.restageElem (M.argsPoint args) (M.interp (argArities Γ (S.arity o)) (opTermIn Γ o)) := by
  apply ElemOver.ext
  funext W w ρ
  exact congrArg (· ≫ M.op o) (M.tupleArgs_argTerms args W w ρ).symm

end Model

/-! ## Factorwise maps of points -/

section PointMaps

variable {M N : Model S D}

/-- **A factorwise map of points**: a map of generalized elements, and maps
of points into products of function objects acting on each factor as on the
generalized element it represents. -/
structure PointMap (M N : Model S D) (Z Z' : D) where
  elem : ∀ {Γ : Ctx S} {s : S.Srt}, M.ElemOver Z Γ s → N.ElemOver Z' Γ s
  family : ∀ L : List (MetaArity S), (Z ⟶ M.family L) → (Z' ⟶ N.family L)
  family_cons : ∀ (a : MetaArity S) (L : List (MetaArity S)) (x : M.ElemOver Z a.1 a.2)
    (rest : Z ⟶ M.family L),
    family (a :: L) (lift (M.elemEquiv x) rest) = lift (N.elemEquiv (elem x)) (family L rest)

/-- The point of an environment goes to the point of the mapped environment. -/
theorem PointMap.envPoint {Z Z' : D} (m : PointMap M N Z Z') (Δ : Ctx S) : ∀ {Γ : Ctx S}
    (env : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ),
    m.family _ (M.envPoint Δ env) = N.envPoint Δ (fun γ v => m.elem (env γ v))
  | [], _ => toUnit_unique _ _
  | _ :: _, env => (m.family_cons _ _ _ _).trans
      (congrArg (lift _) (PointMap.envPoint m Δ fun γ v => env γ (.succ v)))

/-- Restaging points along a map of stages. -/
def Model.restagePoints (M : Model S D) {Z Z' : D} (k : Z' ⟶ Z) : PointMap M M Z Z' where
  elem x := M.restageElem k x
  family _ point := k ≫ point
  family_cons _ _ x rest :=
    (comp_lift _ _ _).trans (congrArg (lift · (k ≫ rest)) (M.elemEquiv_restage k x).symm)

/-- The point of an environment moves along a map of stages by restaging. -/
theorem Model.comp_envPoint (M : Model S D) {Z Z' : D} (k : Z' ⟶ Z) (Δ : Ctx S) {Γ : Ctx S}
    (env : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ) :
    k ≫ M.envPoint Δ env = M.envPoint Δ (fun γ v => M.restageElem k (env γ v)) :=
  (M.restagePoints k).envPoint Δ env

end PointMaps


/-! ## Maps of binding models on generalized elements -/

variable {M N : Model S D}

/-- Move a generalized element through the function objects. -/
noncomputable def stageElemMap (h : Hom M N) {Z : D} {Γ : Ctx S} {s : S.Srt}
    (x : M.ElemOver Z Γ s) : N.ElemOver Z Γ s :=
  N.elemOfPoint (M.elemEquiv x ≫ h.underlying.power Γ s)

theorem elemEquiv_stageElemMap (h : Hom M N) {Z : D} {Γ : Ctx S} {s : S.Srt}
    (x : M.ElemOver Z Γ s) :
    N.elemEquiv (stageElemMap h x) = M.elemEquiv x ≫ h.underlying.power Γ s :=
  N.elemEquiv.right_inv _

/-- A map of binding models commutes with the interpretation of every term,
at the generic point. -/
theorem elemEquiv_interp_comm (h : Hom M N) (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    M.elemEquiv (M.interp X.arities t) ≫ h.underlying.power Γ s =
      Model.familyMap h.underlying.power X.arities ≫ N.elemEquiv (N.interp X.arities t) := by
  have square := congrArg (· ≫ fst _ _) (h.assignment_comm (termArrow t))
  change (lift (M.curry (M.generic X.arities t)) (toUnit _) ≫
      (h.underlying.power Γ s ⊗ₘ 𝟙 _)) ≫ fst _ _ =
    (Model.familyMap h.underlying.power X.arities ≫
      lift (N.curry (N.generic X.arities t)) (toUnit _)) ≫ fst _ _ at square
  simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst] at square
  exact square

/-- **A map of binding models commutes with the interpretation of every term
at every point.** -/
theorem stageElemMap_restage_interp (h : Hom M N) (X : Object S) {Z : D}
    (p : Z ⟶ M.family X.arities) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    stageElemMap h (M.restageElem p (M.interp X.arities t)) =
      N.restageElem (p ≫ Model.familyMap h.underlying.power X.arities) (N.interp X.arities t) := by
  apply N.elemEquiv.injective
  rw [elemEquiv_stageElemMap, M.elemEquiv_restage, N.elemEquiv_restage, Category.assoc,
    elemEquiv_interp_comm, Category.assoc]

theorem envPoint_stageElemMap (h : Hom M N) {Z : D} (Δ : Ctx S) : ∀ {Γ : Ctx S}
    (env : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ),
    M.envPoint Δ env ≫ Model.familyMap h.underlying.power (envArities Γ Δ) =
      N.envPoint Δ (fun γ v => stageElemMap h (env γ v))
  | [], _ => toUnit_unique _ _
  | _ :: _, env => by
      change lift _ _ ≫ (h.underlying.power _ _ ⊗ₘ Model.familyMap h.underlying.power _) = lift _ _
      rw [lift_map, envPoint_stageElemMap h Δ (fun γ v => env γ (.succ v)),
        elemEquiv_stageElemMap]

theorem argsPoint_stageElemMap (h : Hom M N) {Z : D} {Γ : Ctx S} :
    ∀ {L : List (List S.Srt × S.Srt)} (args : FamilyArgs S (M.ElemOver Z) L Γ),
      M.argsPoint args ≫ Model.familyMap h.underlying.power (argArities Γ L) =
        N.argsPoint (FamilyArgs.map (fun x => stageElemMap h x) args)
  | [], .nil => toUnit_unique _ _
  | _ :: _, .cons head tail => by
      change lift _ _ ≫ (h.underlying.power _ _ ⊗ₘ Model.familyMap h.underlying.power _) = lift _ _
      rw [lift_map, argsPoint_stageElemMap h tail, elemEquiv_stageElemMap]

theorem substPoint_stageElemMap (h : Hom M N) {Z : D} {Γ Δ : Ctx S} {s : S.Srt}
    (x : M.ElemOver Z Γ s) (env : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ) :
    lift (M.elemEquiv x) (M.envPoint Δ env) ≫
        Model.familyMap h.underlying.power (substObj Γ Δ s).arities =
      lift (N.elemEquiv (stageElemMap h x)) (N.envPoint Δ fun γ v => stageElemMap h (env γ v)) := by
  change lift _ _ ≫ (h.underlying.power _ _ ⊗ₘ Model.familyMap h.underlying.power _) = _
  rw [lift_map, envPoint_stageElemMap, elemEquiv_stageElemMap]

/-- **A map of binding models is a map of stage clones.** -/
noncomputable def stageMap (h : Hom M N) (Z : D) :
    FreeBindingClone.Hom (M.stage Z) (N.stage Z) where
  raw :=
    { map := fun x => stageElemMap h x
      map_variable := fun v =>
        stageElemMap_restage_interp h ⟨[]⟩ (toUnit Z) (Term.var (S := withMetas S []) v)
      map_operation := fun o args =>
        (congrArg (stageElemMap h) (M.opElem_eq_restage o args)).trans
          ((stageElemMap_restage_interp h _ _ _).trans
            ((congrArg (fun q => N.restageElem q (N.interp _ (opTermIn _ o)))
              (argsPoint_stageElemMap h args)).trans
              (N.opElem_eq_restage o _).symm)) }
  map_substitute := by
    intro Γ Δ s env x
    refine (congrArg (stageElemMap h) (M.substitute_eq_restage x env)).trans ?_
    refine (stageElemMap_restage_interp h _ _ _).trans ?_
    refine Eq.trans ?_ (N.substitute_eq_restage (stageElemMap h x)
      (fun γ v => stageElemMap h (env γ v))).symm
    exact congrArg (fun q => N.restageElem q _) (substPoint_stageElemMap h x env)

theorem stageMap_map (h : Hom M N) {Z : D} {Γ : Ctx S} {s : S.Srt} (x : M.ElemOver Z Γ s) :
    (stageMap h Z).raw.map x = stageElemMap h x :=
  rfl

theorem stageMap_id (M : Model S D) (Z : D) :
    stageMap (Hom.id M) Z = FreeBindingClone.Hom.id (M.stage Z) := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ s x
  change M.elemOfPoint (M.elemEquiv x ≫ 𝟙 _) = x
  rw [Category.comp_id]
  exact M.elemEquiv.left_inv x

theorem stageMap_comp {P : Model S D} (f : Hom M N) (g : Hom N P) (Z : D) :
    stageMap (Hom.comp f g) Z = FreeBindingClone.Hom.comp (stageMap f Z) (stageMap g Z) := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ s x
  change M.ElemOver Z Γ s at x
  apply P.elemEquiv.injective
  change P.elemEquiv (stageElemMap (Hom.comp f g) x) = P.elemEquiv (stageElemMap g (stageElemMap f x))
  rw [elemEquiv_stageElemMap, elemEquiv_stageElemMap, elemEquiv_stageElemMap, Category.assoc]
  rfl

/-- Moving points along a map of binding models. -/
noncomputable def mapPoints (h : Hom M N) (Z : D) : PointMap M N Z Z where
  elem x := stageElemMap h x
  family L point := point ≫ Model.familyMap h.underlying.power L
  family_cons _ _ x _ :=
    (lift_map _ _ _ _).trans (congrArg (lift · _) (elemEquiv_stageElemMap h x).symm)

/-- The map of stage clones is natural in the stage. -/
theorem stageMap_restage (h : Hom M N) {Z Z' : D} (k : Z' ⟶ Z) :
    FreeBindingClone.Hom.comp (stageMap h Z) (N.stageRestage k) =
      FreeBindingClone.Hom.comp (M.stageRestage k) (stageMap h Z') := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ s x
  change M.ElemOver Z Γ s at x
  apply N.elemEquiv.injective
  change N.elemEquiv (N.restageElem k (stageElemMap h x)) =
    N.elemEquiv (stageElemMap h (M.restageElem k x))
  rw [N.elemEquiv_restage, elemEquiv_stageElemMap, elemEquiv_stageElemMap, M.elemEquiv_restage,
    Category.assoc]

/-- **A moved point interprets equation classes through the stage map.** -/
theorem pointProgram_stageMap {schema : List (MetaArity S)} (P : EquationPresentation S schema)
    (satM : M.Satisfies P) (satN : N.Satisfies P) (h : Hom M N) (X : Object S) {Z : D}
    (x : Z ⟶ M.family X.arities) :
    N.pointProgram P satN X (x ≫ Model.familyMap h.underlying.power X.arities) =
      FreeBindingClone.Hom.comp (M.pointProgram P satM X x) (stageMap h Z) := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ s q
  induction q using Quotient.inductionOn with
  | _ t =>
      exact (stageElemMap_restage_interp h X x t).symm

end Mettapedia.OSLF.Binding.CategoricalBindingModel
