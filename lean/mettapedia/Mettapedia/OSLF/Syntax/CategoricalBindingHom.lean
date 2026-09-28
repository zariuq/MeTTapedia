import Mettapedia.OSLF.Syntax.CategoricalBindingKripke

/-!
# Maps of models, and interpretation transported along isomorphisms

A map of models has a component for every sort and for every chosen function
object, commuting with evaluation and with every operator. Models and their
maps form a category.

An isomorphism of models transports natural families of elements, and the
transport commutes with variables, operators and metavariable application.
Hence the interpretation of every term in one model is the transport of its
interpretation in the other, by the uniqueness of the interpretation fold.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

namespace Model

variable {S : Signature}

/-- The product of sort maps over a context. -/
def ctxMap {M N : Model S D} (f : ∀ s, M.sort s ⟶ N.sort s) : ∀ Γ : Ctx S, M.ctx Γ ⟶ N.ctx Γ
  | [] => 𝟙 _
  | γ :: Γ => f γ ⊗ₘ ctxMap f Γ

/-- The product of function-object maps over a list of arities. -/
def familyMap {M N : Model S D} (g : ∀ Γ s, M.power Γ s ⟶ N.power Γ s) :
    ∀ L : List (List S.Srt × S.Srt), M.family L ⟶ N.family L
  | [] => 𝟙 _
  | a :: L => g a.1 a.2 ⊗ₘ familyMap g L

theorem ctxMap_id (M : Model S D) : ∀ Γ : Ctx S, ctxMap (M := M) (N := M) (fun _ => 𝟙 _) Γ = 𝟙 _
  | [] => rfl
  | γ :: Γ => by
      change 𝟙 _ ⊗ₘ ctxMap (M := M) (N := M) (fun _ => 𝟙 _) Γ = _
      rw [ctxMap_id M Γ, id_tensorHom_id]

theorem ctxMap_comp {M N P : Model S D} (f : ∀ s, M.sort s ⟶ N.sort s)
    (g : ∀ s, N.sort s ⟶ P.sort s) :
    ∀ Γ : Ctx S, ctxMap (fun s => f s ≫ g s) Γ = ctxMap f Γ ≫ ctxMap g Γ
  | [] => (Category.id_comp _).symm
  | γ :: Γ => by
      change (f γ ≫ g γ) ⊗ₘ ctxMap (fun s => f s ≫ g s) Γ = (f γ ⊗ₘ ctxMap f Γ) ≫ (g γ ⊗ₘ ctxMap g Γ)
      rw [ctxMap_comp f g Γ, tensorHom_comp_tensorHom]

theorem familyMap_id (M : Model S D) :
    ∀ L : List (List S.Srt × S.Srt), familyMap (M := M) (N := M) (fun _ _ => 𝟙 _) L = 𝟙 _
  | [] => rfl
  | a :: L => by
      change 𝟙 _ ⊗ₘ familyMap (M := M) (N := M) (fun _ _ => 𝟙 _) L = _
      rw [familyMap_id M L, id_tensorHom_id]

theorem familyMap_comp {M N P : Model S D} (f : ∀ Γ s, M.power Γ s ⟶ N.power Γ s)
    (g : ∀ Γ s, N.power Γ s ⟶ P.power Γ s) :
    ∀ L : List (List S.Srt × S.Srt),
      familyMap (fun Γ s => f Γ s ≫ g Γ s) L = familyMap f L ≫ familyMap g L
  | [] => (Category.id_comp _).symm
  | a :: L => by
      change (f a.1 a.2 ≫ g a.1 a.2) ⊗ₘ familyMap (fun Γ s => f Γ s ≫ g Γ s) L =
        (f a.1 a.2 ⊗ₘ familyMap f L) ≫ (g a.1 a.2 ⊗ₘ familyMap g L)
      rw [familyMap_comp f g L, tensorHom_comp_tensorHom]

@[reassoc]
theorem familyMap_proj {M N : Model S D} (g : ∀ Γ s, M.power Γ s ⟶ N.power Γ s) :
    ∀ (L : List (List S.Srt × S.Srt)) (i : Fin L.length),
      familyMap g L ≫ N.familyProj L i = M.familyProj L i ≫ g (L.get i).1 (L.get i).2
  | _ :: _, ⟨0, _⟩ => tensorHom_fst _ _
  | _ :: rest, ⟨n + 1, bound⟩ => by
      change (g _ _ ⊗ₘ familyMap g rest) ≫ snd _ _ ≫ N.familyProj rest ⟨n, _⟩ =
        (snd _ _ ≫ M.familyProj rest ⟨n, _⟩) ≫ _
      rw [tensorHom_snd_assoc, familyMap_proj g rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩,
        Category.assoc]
      rfl

/-- A map of models: components on sorts and on function objects, commuting
with evaluation and with every operator. -/
@[ext]
structure Hom (M N : Model S D) where
  sort : ∀ s, M.sort s ⟶ N.sort s
  power : ∀ Γ s, M.power Γ s ⟶ N.power Γ s
  eval_comm : ∀ Γ s, (ctxMap sort Γ ⊗ₘ power Γ s) ≫ N.eval Γ s = M.eval Γ s ≫ sort s
  op_comm : ∀ {s} (o : S.Op s), familyMap power (S.arity o) ≫ N.op o = M.op o ≫ sort s

instance category : Category (Model S D) where
  Hom := Hom
  id M := {
    sort := fun _ => 𝟙 _
    power := fun _ _ => 𝟙 _
    eval_comm := fun Γ s => by rw [ctxMap_id, id_tensorHom_id, Category.id_comp, Category.comp_id]
    op_comm := fun o => by rw [familyMap_id, Category.id_comp, Category.comp_id] }
  comp f g := {
    sort := fun s => f.sort s ≫ g.sort s
    power := fun Γ s => f.power Γ s ≫ g.power Γ s
    eval_comm := fun Γ s => by
      rw [ctxMap_comp, ← tensorHom_comp_tensorHom, Category.assoc, g.eval_comm,
        ← Category.assoc, f.eval_comm, Category.assoc]
    op_comm := fun o => by
      rw [familyMap_comp, Category.assoc, g.op_comm, ← Category.assoc, f.op_comm,
        Category.assoc] }
  id_comp _ := by apply Hom.ext <;> (funext; simp)
  comp_id _ := by apply Hom.ext <;> (funext; simp)
  assoc _ _ _ := by apply Hom.ext <;> (funext; simp)

@[simp] theorem comp_sort {M N P : Model S D} (f : M ⟶ N) (g : N ⟶ P) (s : S.Srt) :
    Hom.sort (f ≫ g) s = Hom.sort f s ≫ Hom.sort g s := rfl

@[simp] theorem comp_power {M N P : Model S D} (f : M ⟶ N) (g : N ⟶ P) (Γ : Ctx S) (s : S.Srt) :
    Hom.power (f ≫ g) Γ s = Hom.power f Γ s ≫ Hom.power g Γ s := rfl

@[simp] theorem id_sort (M : Model S D) (s : S.Srt) : Hom.sort (𝟙 M) s = 𝟙 _ := rfl

@[simp] theorem id_power (M : Model S D) (Γ : Ctx S) (s : S.Srt) : Hom.power (𝟙 M) Γ s = 𝟙 _ := rfl

section Transport

variable {M N : Model S D} (e : M ≅ N)

theorem inv_hom_sort (s : S.Srt) : Hom.sort e.inv s ≫ Hom.sort e.hom s = 𝟙 _ := by
  rw [← comp_sort, e.inv_hom_id]
  rfl

theorem inv_hom_power (Γ : Ctx S) (s : S.Srt) : Hom.power e.inv Γ s ≫ Hom.power e.hom Γ s = 𝟙 _ := by
  rw [← comp_power, e.inv_hom_id]
  rfl

@[reassoc]
theorem ctxMap_inv_hom (Γ : Ctx S) : ctxMap (Hom.sort e.inv) Γ ≫ ctxMap (Hom.sort e.hom) Γ = 𝟙 _ := by
  rw [← ctxMap_comp]
  simp only [inv_hom_sort]
  exact ctxMap_id N Γ

theorem familyMap_inv_hom (L : List (List S.Srt × S.Srt)) :
    familyMap (Hom.power e.inv) L ≫ familyMap (Hom.power e.hom) L = 𝟙 _ := by
  rw [← familyMap_comp]
  simp only [inv_hom_power]
  exact familyMap_id N L

/-- Currying commutes with an isomorphism of models. -/
theorem curry_transport {Γ : Ctx S} {s : S.Srt} {Z : D} (f : M.ctx Γ ⊗ Z ⟶ M.sort s) :
    M.curry f ≫ Hom.power e.hom Γ s =
      N.curry ((ctxMap (Hom.sort e.inv) Γ ▷ Z) ≫ f ≫ Hom.sort e.hom s) := by
  symm
  apply N.curry_unique
  have split : (N.ctx Γ ◁ (M.curry f ≫ Hom.power e.hom Γ s)) =
      (ctxMap (Hom.sort e.inv) Γ ▷ Z) ≫ (M.ctx Γ ◁ M.curry f) ≫
        (ctxMap (Hom.sort e.hom) Γ ⊗ₘ Hom.power e.hom Γ s) := by
    apply hom_ext
    · simp only [whiskerLeft_fst, Category.assoc, tensorHom_fst, whiskerLeft_fst_assoc,
        whiskerRight_fst_assoc]
      rw [ctxMap_inv_hom e Γ, Category.comp_id]
    · simp
  rw [split, Category.assoc, Category.assoc, Hom.eval_comm, ← Category.assoc (M.ctx Γ ◁ _),
    M.curry_eval]

/-- Transport a natural family of elements along an isomorphism of models. -/
def transElem {X : List (MetaArity S)} {Γ : Ctx S} {s : S.Srt} (x : M.Elem X Γ s) :
    N.Elem X Γ s where
  value := fun Z m ρ =>
    x.value Z (m ≫ familyMap (Hom.power e.inv) X) (fun γ v => ρ γ v ≫ Hom.sort e.inv γ) ≫
      Hom.sort e.hom s
  natural := fun h m ρ => by
    rw [← Category.assoc h, ← x.natural, Category.assoc h]
    congr 2
    funext γ v
    exact Category.assoc _ _ _

theorem extendEnv_transport {Γ' : Ctx S} {Z : D} (ρ : N.Env Z Γ') :
    ∀ (bs : List S.Srt) {γ : S.Srt} (v : Var (bs ++ Γ') γ),
      (ctxMap (Hom.sort e.inv) bs ▷ Z) ≫
          M.extendEnv bs (fun γ v => ρ γ v ≫ Hom.sort e.inv γ) γ v =
        N.extendEnv bs ρ γ v ≫ Hom.sort e.inv γ
  | [], γ, v => by
      change (𝟙 _ ▷ Z) ≫ snd _ _ ≫ ρ γ v ≫ Hom.sort e.inv γ = (snd _ _ ≫ ρ γ v) ≫ _
      rw [id_whiskerRight, Category.id_comp, Category.assoc]
  | b :: bs, γ, v => by
      cases v with
      | zero =>
          change ((Hom.sort e.inv b ⊗ₘ ctxMap (Hom.sort e.inv) bs) ▷ Z) ≫ fst _ _ ≫ fst _ _ =
            (fst _ _ ≫ fst _ _) ≫ Hom.sort e.inv b
          rw [whiskerRight_fst_assoc, tensorHom_fst, Category.assoc]
      | succ w =>
          change ((Hom.sort e.inv b ⊗ₘ ctxMap (Hom.sort e.inv) bs) ▷ Z) ≫
              lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ M.extendEnv bs _ γ w =
            (lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ N.extendEnv bs ρ γ w) ≫ _
          have swap : ((Hom.sort e.inv b ⊗ₘ ctxMap (Hom.sort e.inv) bs) ▷ Z) ≫
              lift (fst _ _ ≫ snd _ _) (snd _ _) =
              lift (fst _ _ ≫ snd _ _) (snd _ _) ≫ (ctxMap (Hom.sort e.inv) bs ▷ Z) := by
            apply hom_ext <;> simp
          rw [← Category.assoc, swap, Category.assoc, extendEnv_transport ρ bs w, Category.assoc]

theorem transElem_var {X : List (MetaArity S)} {Γ : Ctx S} {γ : S.Srt} (v : Var Γ γ) :
    transElem e (⟨fun _ _ ρ => ρ _ v, fun _ _ _ => rfl⟩ : M.Elem X Γ γ) =
      (⟨fun _ _ ρ => ρ _ v, fun _ _ _ => rfl⟩ : N.Elem X Γ γ) := by
  apply Elem.ext
  funext Z m ρ
  change (ρ γ v ≫ Hom.sort e.inv γ) ≫ Hom.sort e.hom γ = ρ γ v
  rw [Category.assoc, inv_hom_sort, Category.comp_id]

theorem tupleArgs_transport {X X' : List (MetaArity S)} {Z : D} :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs (withMetas S X') (M.Elem X) arity Γ) (m : Z ⟶ N.family X)
      (ρ : N.Env Z Γ),
      M.tupleArgs args Z (m ≫ familyMap (Hom.power e.inv) X)
          (fun γ v => ρ γ v ≫ Hom.sort e.inv γ) ≫ familyMap (Hom.power e.hom) arity =
        N.tupleArgs (FamilyArgs.map (fun x => transElem e x) args) Z m ρ
  | _, _, .nil, _, _ => toUnit_unique _ _
  | _, _, .cons (bs := bs) head tail, m, ρ => by
      change lift _ _ ≫ (Hom.power e.hom _ _ ⊗ₘ familyMap (Hom.power e.hom) _) = lift _ _
      rw [lift_map, tupleArgs_transport tail m ρ, curry_transport]
      congr 2
      rw [← Category.assoc, ← head.natural, whiskerRight_snd_assoc]
      change head.value (N.ctx bs ⊗ Z) (snd _ _ ≫ m ≫ familyMap (Hom.power e.inv) X)
          (fun γ v => (ctxMap (Hom.sort e.inv) bs ▷ Z) ≫
            M.extendEnv bs (fun γ v => ρ γ v ≫ Hom.sort e.inv γ) γ v) ≫ Hom.sort e.hom _ =
        head.value (N.ctx bs ⊗ Z) ((snd _ _ ≫ m) ≫ familyMap (Hom.power e.inv) X)
          (fun γ v => N.extendEnv bs ρ γ v ≫ Hom.sort e.inv γ) ≫ Hom.sort e.hom _
      rw [Category.assoc]
      congr 3
      funext γ v
      exact extendEnv_transport e ρ bs v

theorem tupleCtx_transport {X X' : List (MetaArity S)} {Z : D} :
    ∀ (bs : List S.Srt) {Γ : Ctx S}
      (args : FamilyArgs (withMetas S X') (M.Elem X) (bs.map fun b => ([], b)) Γ)
      (m : Z ⟶ N.family X) (ρ : N.Env Z Γ),
      M.tupleCtx bs args Z (m ≫ familyMap (Hom.power e.inv) X)
          (fun γ v => ρ γ v ≫ Hom.sort e.inv γ) ≫ ctxMap (Hom.sort e.hom) bs =
        N.tupleCtx bs (FamilyArgs.map (fun x => transElem e x) args) Z m ρ
  | [], _, .nil, _, _ => toUnit_unique _ _
  | _ :: bs, _, .cons head tail, m, ρ => by
      change lift _ _ ≫ (Hom.sort e.hom _ ⊗ₘ ctxMap (Hom.sort e.hom) bs) = lift _ _
      rw [lift_map, tupleCtx_transport bs tail m ρ]
      rfl

theorem transElem_op {X X' : List (MetaArity S)} {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : FamilyArgs (withMetas S X') (M.Elem X) (S.arity o) Γ) :
    transElem e (M.opElem o args) = N.opElem o (FamilyArgs.map (fun x => transElem e x) args) := by
  apply Elem.ext
  funext Z m ρ
  change (M.tupleArgs args Z _ _ ≫ M.op o) ≫ Hom.sort e.hom s =
    N.tupleArgs (FamilyArgs.map (fun x => transElem e x) args) Z m ρ ≫ N.op o
  rw [Category.assoc, ← Hom.op_comm, ← Category.assoc, tupleArgs_transport]

theorem transElem_meta {X : List (MetaArity S)} {Γ : Ctx S} (j : Fin X.length)
    (args : FamilyArgs (withMetas S X) (M.Elem X) ((X.get j).1.map fun b => ([], b)) Γ) :
    transElem e (M.metaElem j args) = N.metaElem j (FamilyArgs.map (fun x => transElem e x) args) := by
  apply Elem.ext
  funext Z m ρ
  change (lift (M.tupleCtx (X.get j).1 args Z _ _) ((m ≫ familyMap (Hom.power e.inv) X) ≫
      M.familyProj X j) ≫ M.eval _ _) ≫ Hom.sort e.hom _ =
    lift (N.tupleCtx (X.get j).1 (FamilyArgs.map (fun x => transElem e x) args) Z m ρ)
      (m ≫ N.familyProj X j) ≫ N.eval _ _
  rw [Category.assoc, ← Hom.eval_comm, ← Category.assoc, lift_map, tupleCtx_transport,
    Category.assoc, Category.assoc, familyMap_proj_assoc, inv_hom_power, Category.comp_id]

/-- Interpretation in `M`, transported to `N`, as a map of raw algebras. -/
def transportHom (X : List (MetaArity S)) :
    FreeBindingTerms.Hom (FreeBindingTerms.terms (withMetas S X)) (N.kripke X).toRaw where
  map := fun t => transElem e (M.interp X t)
  map_variable := fun v => transElem_var e v
  map_operation := by
    intro Γ s o args
    match o, args with
    | .inl o, args =>
        change transElem e (M.opElem o (FreeBindingTerms.foldArgs (M.kripke X).toRaw
            (FreeBindingTerms.terms.familyToSyntax _ args))) = N.opElem o _
        have folded := FreeBindingTerms.foldArgs_familyToSyntax (M.kripke X).toRaw args
        rw [folded]
        exact (transElem_op e o _).trans (congrArg (N.opElem o)
          (FamilyArgs.map_comp (fun t => FreeBindingTerms.fold (M.kripke X).toRaw t)
            (fun x => transElem e x) args))
    | .inr (.mk j), args =>
        change transElem e (M.metaElem j (FreeBindingTerms.foldArgs (M.kripke X).toRaw
            (FreeBindingTerms.terms.familyToSyntax _ args))) = N.metaElem j _
        have folded := FreeBindingTerms.foldArgs_familyToSyntax (M.kripke X).toRaw args
        rw [folded]
        exact (transElem_meta e j _).trans (congrArg (N.metaElem j)
          (FamilyArgs.map_comp (fun t => FreeBindingTerms.fold (M.kripke X).toRaw t)
            (fun x => transElem e x) args))

/-- **Isomorphic models interpret alike.** -/
theorem interp_transport (X : List (MetaArity S)) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X) Γ s) : transElem e (M.interp X t) = N.interp X t := by
  have unique := FreeBindingTerms.hom_unique (N.kripke X).toRaw (transportHom e X)
  exact congrArg (fun h : FreeBindingTerms.Hom _ _ => h.map t) unique

end Transport

end Model

end Mettapedia.OSLF.Binding.CategoricalBindingModel
