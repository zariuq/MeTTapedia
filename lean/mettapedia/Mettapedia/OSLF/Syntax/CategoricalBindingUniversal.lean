import Mettapedia.OSLF.Syntax.CategoricalBindingPreservation
import Mettapedia.OSLF.Syntax.CategoricalBindingHom

/-!
# The universal property of the second-order context category

A functor out of the second-order context category preserves its structure
when it preserves the products of contexts, carries chosen exponentials for
the one-metavariable contexts, carries an arrow for each operator, and
commutes with the three term constructors: a variable goes to a projection,
an operator to its arrow applied to the curried arguments, and a metavariable
applied to arguments to evaluation. The meaning of a term under such a functor
is read through the chosen evaluation.

The data of a preserving functor form a model, and the functor is naturally
isomorphic to the classifying functor of that model. Conversely the classifying
functor of every model preserves the structure, and its model is isomorphic
to the original one. Uniqueness is the uniqueness of the interpretation fold:
a meaning that commutes with the constructors is the interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.FreeBindingTerms (FamilyArgs)
open Mettapedia.OSLF.Binding.SecondOrderContext (Object)

universe u v

variable {S : Signature}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-! ## Syntax -/

/-- The metavariable at a position, as an arrow to its one-metavariable
context. -/
def slot (L : List (MetaArity S)) (i : Fin L.length) :
    (⟨L⟩ : Object S) ⟶ oneObj (L.get i).1 (L.get i).2 :=
  termArrow (X := ⟨L⟩) (metaVar i)

theorem oneObj_hom_ext {X : Object S} {Γ : Ctx S} {s : S.Srt} {f g : X ⟶ oneObj Γ s}
    (h : f ⟨0, Nat.zero_lt_one⟩ = g ⟨0, Nat.zero_lt_one⟩) : f = g := by
  funext i
  rcases i with ⟨n, bound⟩
  change n < 1 at bound
  obtain rfl : n = 0 := by omega
  exact h

/-- Composing with a slot reads off the assigned term. -/
theorem comp_slot {X : Object S} (L : List (MetaArity S)) (σ : X ⟶ (⟨L⟩ : Object S))
    (i : Fin L.length) : σ ≫ slot L i = termArrow (σ i) := by
  apply oneObj_hom_ext
  exact instInto_metaVar σ i

theorem tail_comp_slot (a : MetaArity S) (L : List (MetaArity S)) (k : Fin L.length) :
    tailArrow a ⟨L⟩ ≫ slot L k = slot (a :: L) k.succ := by
  rw [comp_slot]
  rfl

theorem syntaxToFamily_familyToSyntax {T : Signature} :
    ∀ {arity : List (List T.Srt × T.Srt)} {Γ : Ctx T}
      (args : FamilyArgs T (Term T) arity Γ),
      FreeBindingTerms.syntaxToFamily (FreeBindingTerms.terms.familyToSyntax T args) = args
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg (FamilyArgs.cons head) (syntaxToFamily_familyToSyntax tail)

/-- Products of maps over families of function objects. -/
def familyOfMap {P Q : Ctx S → S.Srt → D} (g : ∀ Γ s, P Γ s ⟶ Q Γ s) :
    ∀ L : List (List S.Srt × S.Srt), familyOf P L ⟶ familyOf Q L
  | [] => 𝟙 _
  | a :: L => g a.1 a.2 ⊗ₘ familyOfMap g L

theorem familyMap_eq {M N : Model S D} (g : ∀ Γ s, M.power Γ s ⟶ N.power Γ s) :
    ∀ L : List (List S.Srt × S.Srt), Model.familyMap g L = familyOfMap g L
  | [] => rfl
  | a :: L => by
      change g a.1 a.2 ⊗ₘ Model.familyMap g L = g a.1 a.2 ⊗ₘ familyOfMap g L
      rw [familyMap_eq g L]

/-! ## Preserving functors and their models -/

namespace CartesianArities

variable {F : Object S ⥤ D} (hF : CartesianArities F)

/-- The image of `a :: X` is the product of the images of `a` and `X`. -/
noncomputable def consIso (a : MetaArity S) (X : Object S) :
    F.obj (consObj a X) ≅ F.obj (oneObj a.1 a.2) ⊗ F.obj X where
  hom := lift (F.map (headArrow a X)) (F.map (tailArrow a X))
  inv := (hF.cons a X).lift (BinaryFan.mk (fst _ _) (snd _ _))
  hom_inv_id := by
    apply (hF.cons a X).hom_ext
    rintro ⟨_ | _⟩
    · simp only [Category.assoc, IsLimit.fac, Category.id_comp]
      exact lift_fst _ _
    · simp only [Category.assoc, IsLimit.fac, Category.id_comp]
      exact lift_snd _ _
  inv_hom_id := by
    apply hom_ext
    · rw [Category.assoc, lift_fst, Category.id_comp]
      exact (hF.cons a X).fac _ ⟨WalkingPair.left⟩
    · rw [Category.assoc, lift_snd, Category.id_comp]
      exact (hF.cons a X).fac _ ⟨WalkingPair.right⟩

/-- The image of a context is the product of the images of its arities. -/
noncomputable def famIso :
    ∀ L : List (MetaArity S), F.obj ⟨L⟩ ≅ familyOf (fun Γ s => F.obj (oneObj Γ s)) L
  | [] => hF.terminal.uniqueUpToIso isTerminalTensorUnit
  | a :: L => hF.consIso a ⟨L⟩ ≪≫ whiskerLeftIso (F.obj (oneObj a.1 a.2)) (famIso L)

@[reassoc]
theorem famIso_cons_hom_fst (a : MetaArity S) (L : List (MetaArity S)) :
    (hF.famIso (a :: L)).hom ≫ fst (F.obj (oneObj a.1 a.2)) _ = F.map (headArrow a ⟨L⟩) := by
  change (lift (F.map (headArrow a ⟨L⟩)) (F.map (tailArrow a ⟨L⟩)) ≫
    (F.obj (oneObj a.1 a.2) ◁ (hF.famIso L).hom)) ≫ fst _ _ = _
  rw [Category.assoc, whiskerLeft_fst, lift_fst]

@[reassoc]
theorem famIso_cons_hom_snd (a : MetaArity S) (L : List (MetaArity S)) :
    (hF.famIso (a :: L)).hom ≫ snd (F.obj (oneObj a.1 a.2)) _ =
      F.map (tailArrow a ⟨L⟩) ≫ (hF.famIso L).hom := by
  change (lift (F.map (headArrow a ⟨L⟩)) (F.map (tailArrow a ⟨L⟩)) ≫
    (F.obj (oneObj a.1 a.2) ◁ (hF.famIso L).hom)) ≫ snd _ _ = _
  rw [Category.assoc, whiskerLeft_snd, lift_snd_assoc]

end CartesianArities

/-- A functor with products, chosen exponentials and operator arrows. -/
structure PreservingData (F : Object S ⥤ D) extends CartesianArities F where
  op : ∀ {s : S.Srt} (o : S.Op s), familyOf (fun Γ s => F.obj (oneObj Γ s)) (S.arity o) ⟶ sortOf F s

namespace PreservingData

variable {F : Object S ⥤ D} (hF : PreservingData F)

/-- The model formed by the data of a functor. -/
abbrev toModel : Model S D where
  sort := sortOf F
  power := fun Γ s => F.obj (oneObj Γ s)
  eval := fun Γ s => (hF.exponential Γ s).eval
  curry := fun f => (hF.exponential _ _).curry f
  curry_eval := fun f => (hF.exponential _ _).curry_eval f
  curry_unique := fun f g h => (hF.exponential _ _).curry_unique f g h
  op := fun o => hF.op o

theorem famIso_proj : ∀ (L : List (MetaArity S)) (i : Fin L.length),
    (hF.famIso L).hom ≫ hF.toModel.familyProj L i = F.map (slot L i)
  | _ :: _, ⟨0, _⟩ => hF.famIso_cons_hom_fst _ _
  | a :: L, ⟨n + 1, bound⟩ => by
      change (hF.famIso (a :: L)).hom ≫ snd _ _ ≫ hF.toModel.familyProj L ⟨n, _⟩ = _
      rw [hF.famIso_cons_hom_snd_assoc, famIso_proj L ⟨n, Nat.lt_of_succ_lt_succ bound⟩,
        ← F.map_comp, tail_comp_slot]
      rfl

/-- The meaning of a term under the functor, read through the chosen
evaluation. -/
noncomputable def meaning {X : Object S} {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) : hF.toModel.Elem X.arities Γ s where
  value := fun Z m ρ =>
    lift (hF.toModel.tupleEnv ρ) (m ≫ (hF.famIso X.arities).inv ≫ F.map (termArrow t)) ≫
      hF.toModel.eval Γ s
  natural := fun h m ρ => by
    rw [hF.toModel.tupleEnv_restage]
    simp only [comp_lift_assoc, Category.assoc]

end PreservingData

/-- **A structure-preserving functor**: products, chosen exponentials and
operator arrows, with the meaning of terms commuting with the constructors. -/
structure Preserving (F : Object S ⥤ D) extends PreservingData F where
  meaning_var : ∀ (X : Object S) {Γ : Ctx S} {γ : S.Srt} (v : Var Γ γ),
    toPreservingData.meaning (X := X) (Term.var v) = ⟨fun _ _ ρ => ρ _ v, fun _ _ _ => rfl⟩
  meaning_op : ∀ (X : Object S) {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : Args (withMetas S X.arities) (S.arity o) Γ),
    toPreservingData.meaning (X := X) (Term.op (Sum.inl o) args) =
      toPreservingData.toModel.opElem o
        (FamilyArgs.map (fun t => toPreservingData.meaning t) (FreeBindingTerms.syntaxToFamily args))
  meaning_meta : ∀ (X : Object S) {Γ : Ctx S} (j : Fin X.arities.length)
    (args : Args (withMetas S X.arities) ((X.arities.get j).1.map fun b => ([], b)) Γ),
    toPreservingData.meaning (X := X) (Term.op (Sum.inr (MetaOp.mk j)) args) =
      toPreservingData.toModel.metaElem j
        (FamilyArgs.map (fun t => toPreservingData.meaning t) (FreeBindingTerms.syntaxToFamily args))

namespace Preserving

variable {F : Object S ⥤ D} (hF : Preserving F)

/-- The meaning, as a map of raw algebras. -/
noncomputable def meaningHom (X : Object S) :
    FreeBindingTerms.Hom (FreeBindingTerms.terms (withMetas S X.arities))
      (hF.toModel.kripke X.arities).toRaw where
  map := fun t => hF.meaning t
  map_variable := fun v => hF.meaning_var X v
  map_operation := by
    intro Γ s o args
    match o, args with
    | .inl o, args =>
        have law := hF.meaning_op X o (FreeBindingTerms.terms.familyToSyntax _ args)
        rw [syntaxToFamily_familyToSyntax (T := withMetas S X.arities) args] at law
        exact law
    | .inr (.mk j), args =>
        have law := hF.meaning_meta X j (FreeBindingTerms.terms.familyToSyntax _ args)
        rw [syntaxToFamily_familyToSyntax (T := withMetas S X.arities) args] at law
        exact law

/-- **Uniqueness.** The meaning of every term is its interpretation in the
model of the functor. -/
theorem meaning_eq_interp (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    hF.meaning t = hF.toModel.interp X.arities t := by
  have unique := FreeBindingTerms.hom_unique (hF.toModel.kripke X.arities).toRaw (hF.meaningHom X)
  exact congrArg (fun h : FreeBindingTerms.Hom _ _ => h.map t) unique

/-- The functor's value on a term is determined by the interpretation. -/
theorem map_termArrow (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S X.arities) Γ s) :
    F.map (termArrow t) =
      (hF.famIso X.arities).hom ≫ hF.toModel.curry (hF.toModel.generic X.arities t) := by
  rw [← Iso.inv_comp_eq]
  symm
  apply hF.toModel.curry_unique
  unfold Model.generic
  rw [← hF.meaning_eq_interp X t]
  change _ = lift (hF.toModel.tupleEnv (hF.toModel.genericEnv Γ _)) (snd _ _ ≫ _) ≫ _
  unfold Model.genericEnv
  rw [hF.toModel.tupleEnv_restage, hF.toModel.tupleEnv_projections, Category.comp_id]
  congr 1
  apply hom_ext <;> simp

/-- **A structure-preserving functor is the classifying functor of its model.** -/
noncomputable def isoClassifying : F ≅ hF.toModel.classifyingFunctor :=
  NatIso.ofComponents (fun X => hF.famIso X.arities) (fun {X Y} σ => by
    change F.map σ ≫ (hF.famIso Y.arities).hom = (hF.famIso X.arities).hom ≫ hF.toModel.assignHom σ
    unfold Model.assignHom
    rw [hF.toModel.familyLift_comp]
    apply hF.toModel.familyLift_unique
    intro j
    rw [Category.assoc, hF.famIso_proj, ← F.map_comp, comp_slot, hF.map_termArrow])

end Preserving

end Mettapedia.OSLF.Binding.CategoricalBindingModel
