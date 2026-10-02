import Mettapedia.OSLF.Syntax.SemanticAccountSignature
import Mettapedia.GSLT.LanguageDef.Cost.BindingValuationAction

/-!
# Full valuation semantics for an additional account operator

Every operator of the actual declaration-derived binding signature retains
its supplied interpretation. The additional semantic Mark operator acts only
at its declared result sort. Functions, multiple binders and the complete
mixed substitution environment are interpreted by the existing native model.

This extension does not assert that arbitrary supplied source operators
satisfy their equations or commute with the account action.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.SemanticAccountValuation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open _root_.CategoryTheory
open BindingSyntax.Valuation

universe u

variable {language : LanguageDef} {base : String → Type u}
  (constructors : Constructors language base) (signatureSort wrappedSort : TypeExpr)

abbrev signature := SemanticAccountSignature.signature (BindingSyntax.signatureOf language)
  signatureSort wrappedSort

abbrev Context (Γ : List TypeExpr) :=
  contextOf (S := signature (language := language) signatureSort wrappedSort) (Value base) Γ

abbrev Power (Γ : List TypeExpr) (sort : TypeExpr) :=
  Context (language := language) (base := base) signatureSort wrappedSort Γ → Value base sort

abbrev Family (arity : List (List TypeExpr × TypeExpr)) :=
  familyOf (S := signature (language := language) signatureSort wrappedSort)
    (Power (language := language) (base := base) signatureSort wrappedSort) arity

theorem context_eq (Γ : List TypeExpr) :
    Context (language := language) (base := base) signatureSort wrappedSort Γ =
      BindingSyntax.Valuation.Context language base Γ := by
  induction Γ with
  | nil => rfl
  | cons sort rest ih =>
      change (Value base sort × Context (language := language) (base := base) signatureSort wrappedSort rest) = _
      rw [ih]
      rfl

theorem family_eq (arity : List (List TypeExpr × TypeExpr)) :
    Family (language := language) (base := base) signatureSort wrappedSort arity =
      BindingSyntax.Valuation.Family language base arity := by
  induction arity with
  | nil => rfl
  | cons head rest ih =>
      change ((Context (language := language) (base := base) signatureSort wrappedSort head.1 → Value base head.2) ×
        Family (language := language) (base := base) signatureSort wrappedSort rest) = _
      rw [context_eq, ih]
      rfl

/-- Repackage the same complete argument functions. Each binding context is
transported in full; neither its values nor their account annotations are
projected to an erased environment. -/
def toOriginalFamily : (arity : List (List TypeExpr × TypeExpr)) →
    Family (language := language) (base := base) signatureSort wrappedSort arity →
      BindingSyntax.Valuation.Family language base arity
  | [], _ => PUnit.unit
  | head :: rest, values =>
      (fun context => values.1 (cast (context_eq signatureSort wrappedSort head.1).symm context),
        toOriginalFamily rest values.2)

/-- An independently specified native operation; no source law is encoded
in this interpretation data. -/
def operator (mark : Value base signatureSort → Value base wrappedSort →
    Value base wrappedSort) : {sort : TypeExpr} → (op : (signature (language := language) signatureSort wrappedSort).Op sort) →
    Family (language := language) (base := base) signatureSort wrappedSort
      ((signature (language := language) signatureSort wrappedSort).arity op) → Value base sort
  | _, .inl original, args => BindingSyntax.Valuation.operator constructors original
      (toOriginalFamily signatureSort wrappedSort _ args)
  | _, .inr (.mk position), args => by
      obtain ⟨index, bounded⟩ := position
      have zero : index = 0 := by simpa only [SemanticAccountSignature.declarations,
        List.length_singleton, Nat.lt_one_iff] using bounded
      subst index
      exact mark (args.1 PUnit.unit) (args.2.1 PUnit.unit)

/-- Existing powers and their independent universal curry laws give the
whole mixed-sort model, including all original binding arities. -/
abbrev model (mark : Value base signatureSort → Value base wrappedSort →
    Value base wrappedSort) : Model (signature (language := language) signatureSort wrappedSort) (Type u) where
  sort := Value base
  power := Power (language := language) (base := base) signatureSort wrappedSort
  eval := fun _ _ => TypeCat.ofHom (fun input => input.2 input.1)
  curry := fun f => TypeCat.ofHom (fun stage assignment => f (assignment, stage))
  curry_eval := by intros; rfl
  curry_unique := by
    intro Γ sort Z f g same
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext stage assignment
    exact (congrArg (fun h => h (assignment, stage)) same).symm
  op := fun op => TypeCat.ofHom (operator constructors signatureSort wrappedSort mark op)

abbrev algebra (mark : Value base signatureSort → Value base wrappedSort →
    Value base wrappedSort) : BindingCloneAlgebra.Algebra.{u + 1}
      (signature (language := language) signatureSort wrappedSort) :=
  (model constructors signatureSort wrappedSort mark).stage PUnit.{u + 1}

def homogeneousArguments
    (mark : Value base signatureSort → Value base wrappedSort → Value base wrappedSort)
    {Γ : List TypeExpr} {sort : TypeExpr} :
    (values : List ((algebra constructors signatureSort wrappedSort mark).substitution.Carrier Γ sort)) →
      FreeBindingTerms.FamilyArgs (signature (language := language) signatureSort wrappedSort)
        (algebra constructors signatureSort wrappedSort mark).substitution.Carrier
        (List.replicate values.length ([], sort)) Γ
  | [] => .nil
  | head :: tail => .cons head (homogeneousArguments mark tail)

/-- Every finite collection reads all complete semantic inputs. Its empty
binding prefixes are eliminated by naturality, not by source erasure. -/
theorem listArguments_tuple
    (mark : Value base signatureSort → Value base wrappedSort → Value base wrappedSort)
    {Γ : List TypeExpr} {sort : TypeExpr}
    (values : List ((algebra constructors signatureSort wrappedSort mark).substitution.Carrier Γ sort))
    (stage : Type u) (above : stage ⟶ PUnit)
    (environment : (model constructors signatureSort wrappedSort mark).Env stage Γ) (point : stage) :
    BindingSyntax.Valuation.listArguments language base sort values.length
      (toOriginalFamily signatureSort wrappedSort _
        ((model constructors signatureSort wrappedSort mark).tupleArgs
          (SecondOrderContext.toAmbientArgs ⟨[]⟩
            (homogeneousArguments constructors signatureSort wrappedSort mark values))
          stage above environment point)) =
      values.map (fun value => value.value stage above environment point) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change _ :: _ = _ :: _
      apply congrArg₂ List.cons
      · exact congrArg (fun f => f (PUnit.unit, point))
          (head.natural (TypeCat.ofHom (Prod.snd : PUnit × stage → stage)) above environment)
      · exact ih

/-- A complete semantic value is read at the supplied ordinary valuation. -/
def read (mark : Value base signatureSort → Value base wrappedSort → Value base wrappedSort)
    {Γ : List TypeExpr} {sort : TypeExpr}
    (value : (algebra constructors signatureSort wrappedSort mark).substitution.Carrier Γ sort)
    (assignment : (type : TypeExpr) → Var Γ type → Value base type) : Value base sort :=
  value.value PUnit (𝟙 _) (fun type position => TypeCat.ofHom
    (fun _ => assignment type position)) PUnit.unit

/-- The actual additional operator is the pointwise action on full natural
values. Naturality removes the empty binding prefix without erasing inputs. -/
theorem mark_value
    (mark : Value base signatureSort → Value base wrappedSort → Value base wrappedSort)
    {Γ : List TypeExpr}
    (account : (algebra constructors signatureSort wrappedSort mark).substitution.Carrier Γ signatureSort)
    (value : (algebra constructors signatureSort wrappedSort mark).substitution.Carrier Γ wrappedSort)
    (stage : Type u) (above : stage ⟶ PUnit)
    (environment : (model constructors signatureSort wrappedSort mark).Env stage Γ) (point : stage) :
    ((algebra constructors signatureSort wrappedSort mark).operation
      (.inr (.mk ⟨0, by simp [SemanticAccountSignature.declarations]⟩))
      (.cons account (.cons value .nil))).value stage above environment point =
        mark (account.value stage above environment point) (value.value stage above environment point) := by
  exact congrArg₂ mark
    (congrArg (fun f => f (PUnit.unit, point))
      (account.natural (TypeCat.ofHom (Prod.snd : PUnit × stage → stage)) above environment))
    (congrArg (fun f => f (PUnit.unit, point))
      (value.natural (TypeCat.ofHom (Prod.snd : PUnit × stage → stage)) above environment))

theorem read_substitute
    (mark : Value base signatureSort → Value base wrappedSort → Value base wrappedSort)
    {Γ Δ : List TypeExpr} {sort : TypeExpr}
    (environment : BindingSubstitutionAlgebra.Environment (signature (language := language) signatureSort wrappedSort)
      (algebra constructors signatureSort wrappedSort mark).substitution.Carrier Γ Δ)
    (value : (algebra constructors signatureSort wrappedSort mark).substitution.Carrier Γ sort)
    (assignment : (type : TypeExpr) → Var Δ type → Value base type) :
    read constructors signatureSort wrappedSort mark
      ((algebra constructors signatureSort wrappedSort mark).substitution.substitute environment value)
      assignment =
    read constructors signatureSort wrappedSort mark value (fun type position =>
      read constructors signatureSort wrappedSort mark (environment type position) assignment) := by
  unfold read
  change value.value PUnit (𝟙 _) _ PUnit.unit = value.value PUnit (𝟙 _) _ PUnit.unit
  congr 2

theorem read_mark
    (mark : Value base signatureSort → Value base wrappedSort → Value base wrappedSort)
    {Γ : List TypeExpr}
    (account : Term (signature (language := language) signatureSort wrappedSort) Γ signatureSort)
    (value : Term (signature (language := language) signatureSort wrappedSort) Γ wrappedSort)
    (assignment : (type : TypeExpr) → Var Γ type → Value base type) :
    read constructors signatureSort wrappedSort mark
      (BindingCloneFoldSubstitution.interpret (algebra constructors signatureSort wrappedSort mark)
        (SemanticAccountSignature.mark account value)) assignment =
      mark (read constructors signatureSort wrappedSort mark
          (BindingCloneFoldSubstitution.interpret (algebra constructors signatureSort wrappedSort mark)
            account) assignment)
        (read constructors signatureSort wrappedSort mark
          (BindingCloneFoldSubstitution.interpret (algebra constructors signatureSort wrappedSort mark)
            value) assignment) := by
  let environment : (model constructors signatureSort wrappedSort mark).Env PUnit Γ :=
    fun type position => TypeCat.ofHom (fun _ => assignment type position)
  have first := (BindingCloneFoldSubstitution.interpret
    (algebra constructors signatureSort wrappedSort mark) account).natural
      (TypeCat.ofHom (Prod.snd : PUnit × PUnit → PUnit)) (𝟙 PUnit) environment
  have second := (BindingCloneFoldSubstitution.interpret
    (algebra constructors signatureSort wrappedSort mark) value).natural
      (TypeCat.ofHom (Prod.snd : PUnit × PUnit → PUnit)) (𝟙 PUnit) environment
  exact congrArg₂ mark
    (congrArg (fun f => f (PUnit.unit, PUnit.unit)) first)
    (congrArg (fun f => f (PUnit.unit, PUnit.unit)) second)

end Mettapedia.GSLT.LanguageDef.Cost.SemanticAccountValuation
