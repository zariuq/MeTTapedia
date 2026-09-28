import Mettapedia.OSLF.Syntax.TermCloneCategoryComparison
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Variables and Cartesian closure in a projection-only theory

The one-sort signature with no operators is a genuine instance of the general
binding-signature construction. Its terms are positional variables; its
context category has finite products by the existing clone comparison. Thus
the blanket claim that Lawvere-style context theories have no variables is
incorrect.

This category has no exponential of the one-variable context by itself. The
proof first excludes even a family of pointwise hom-set equivalences for the
explicit concatenation product, then transports that product to Mathlib's
chosen cartesian monoidal structure. The thin GSLT signature definition alone
therefore cannot imply a cartesian-closed classifying category. This does not
challenge cartesian closure for a theory separately equipped with genuine
function types, abstraction, application, and the required equations.
-/

namespace Mettapedia.OSLF.Binding.ProjectionOnly

open CategoryTheory

set_option autoImplicit false

/-- A single sort and no operators, retaining the intrinsic variables. -/
def signature : Signature where
  Srt := Unit
  Op := fun _ => Empty
  arity := fun o => nomatch o

/-- Contexts and simultaneous substitutions for the projection-only theory. -/
abbrev Context := Syntactic.Ctxt signature
def empty : Context := ⟨[]⟩
def one : Context := ⟨[()]⟩
def two : Context := ⟨[(), ()]⟩

/-- An empty context provides no variable, and there are no operators. -/
theorem noClosedTerm : ¬ Nonempty (Term signature [] ()) := by
  rintro ⟨term⟩
  cases term with
  | var v => cases v
  | op o _ => cases o

/-- The one-variable context contains exactly its projection term. -/
theorem oneTermUnique (term : Term signature [()] ()) :
    term = .var .zero := by
  cases term with
  | var v =>
      cases v with
      | zero => rfl
      | succ v => cases v
  | op o _ => cases o

theorem emptyHomForcesEmpty (E : Context) (arrow : empty ⟶ E) :
    E.vars = [] := by
  cases E with
  | mk vars =>
      cases vars with
      | nil => rfl
      | cons sort rest =>
          cases sort
          exact False.elim (noClosedTerm ⟨arrow () .zero⟩)

theorem homToEmptyUnique (f g : one ⟶ empty) : f = g := by
  funext sort v
  cases v

/-- Select the first variable from a two-variable context. -/
def left : two ⟶ one := fun _ v =>
  match v with
  | .zero => .var .zero
  | .succ w => nomatch w

/-- Select the second variable from a two-variable context. -/
def right : two ⟶ one := fun _ v =>
  match v with
  | .zero => .var (.succ .zero)
  | .succ w => nomatch w

/-- The two positional variables really are distinct arrows. -/
theorem left_ne_right : left ≠ right := by
  intro equal
  have atZero := congrFun (congrFun equal ()) (Var.zero : Var [()] ())
  cases atZero

/-- No context represents the hom-sets obtained by appending one variable on
the right, even if naturality of the proposed equivalences is omitted. -/
theorem noRepresentingExponential :
    ¬ ∃ E : Context,
      ∀ Γ : Context,
        Nonempty ((Γ ⟶ E) ≃ ((⟨List.append Γ.vars [()]⟩ : Context) ⟶ one)) := by
  rintro ⟨E, equivalence⟩
  have fromEmpty : empty ⟶ E :=
    (Classical.choice (equivalence empty)).symm (𝟙 one)
  have hE := emptyHomForcesEmpty E fromEmpty
  cases E with
  | mk vars =>
      cases vars with
      | nil =>
          let e := Classical.choice (equivalence one)
          have equal : e.symm left = e.symm right :=
            homToEmptyUnique _ _
          exact left_ne_right (e.symm.injective equal)
      | cons sort rest =>
          cases hE

/-- The analogous left-append obstruction, matching the chosen left tensor
convention for closed categories. -/
theorem noRepresentingLeftExponential :
    ¬ ∃ E : Context,
      ∀ Γ : Context,
        Nonempty ((Γ ⟶ E) ≃ ((⟨List.append [()] Γ.vars⟩ : Context) ⟶ one)) := by
  rintro ⟨E, equivalence⟩
  have fromEmpty : empty ⟶ E :=
    (Classical.choice (equivalence empty)).symm (𝟙 one)
  have hE := emptyHomForcesEmpty E fromEmpty
  cases E with
  | mk vars =>
      cases vars with
      | nil =>
          let e := Classical.choice (equivalence one)
          have equal : e.symm left = e.symm right :=
            homToEmptyUnique _ _
          exact left_ne_right (e.symm.injective equal)
      | cons sort rest =>
          cases hE

/-- Regard a typed substitution context as its equivalent clone context. -/
def cloneContext (Γ : Context) :
    Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject (termClone signature) :=
  Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
    (termClone signature) Γ.vars

/-- Concatenation is the actual categorical binary product, transported
through the proved clone/context-category equivalence. -/
noncomputable def appendedContextsIsProduct (Γ Δ : Context) :
    CategoryTheory.Limits.IsLimit
      (CategoryTheory.Limits.BinaryFan.mk
        ((cloneContextToSyntactic signature).map
          (Mettapedia.GSLT.LanguageDef.MultiSortedClone.fstProjection
            (termClone signature) (cloneContext Γ) (cloneContext Δ)))
        ((cloneContextToSyntactic signature).map
          (Mettapedia.GSLT.LanguageDef.MultiSortedClone.sndProjection
            (termClone signature) (cloneContext Γ) (cloneContext Δ)))) := by
  exact (CategoryTheory.Limits.BinaryFan.isLimitMapConeEquiv
    (F := cloneContextToSyntactic signature)).toFun
    (CategoryTheory.Limits.isLimitOfPreserves
      (cloneContextToSyntactic signature)
      (Mettapedia.GSLT.LanguageDef.MultiSortedClone.concatIsLimit
        (termClone signature) (cloneContext Γ) (cloneContext Δ)))

local instance : CategoryTheory.Limits.HasFiniteProducts Context :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

noncomputable local instance : CategoryTheory.CartesianMonoidalCategory Context :=
  CategoryTheory.CartesianMonoidalCategory.ofHasFiniteProducts

-- The closed-category contradiction uses local instances to construct its adjunction.
set_option linter.style.haveILetI false

/-- The explicit left-appended product agrees with Mathlib's chosen product. -/
noncomputable def leftAppendIsoTensor (Γ : Context) :
    (⟨List.append [()] Γ.vars⟩ : Context) ≅
      CategoryTheory.MonoidalCategoryStruct.tensorObj one Γ := by
  exact (appendedContextsIsProduct one Γ).conePointUniqueUpToIso
    (CategoryTheory.Limits.limit.isLimit (CategoryTheory.Limits.pair one Γ))

/-- The one-variable context is not exponentiable in this chosen cartesian
monoidal category. -/
theorem notClosedOne : ¬ Nonempty (CategoryTheory.Closed one) := by
  rintro ⟨closed⟩
  letI : CategoryTheory.Closed one := closed
  apply noRepresentingLeftExponential
  refine ⟨(CategoryTheory.ihom one).obj one, ?_⟩
  intro Γ
  let comparison := leftAppendIsoTensor Γ
  let precompose :
      (CategoryTheory.MonoidalCategoryStruct.tensorObj one Γ ⟶ one) ≃
      ((⟨List.append [()] Γ.vars⟩ : Context) ⟶ one) :=
    { toFun := fun arrow => comparison.hom ≫ arrow
      invFun := fun arrow => comparison.inv ≫ arrow
      left_inv := by
        intro arrow
        simp
      right_inv := by
        intro arrow
        simp }
  exact ⟨((CategoryTheory.ihom.adjunction one).homEquiv Γ one).symm.trans
    precompose⟩

/-- The projection-only context category is not cartesian closed. -/
theorem notCartesianClosed :
    ¬ Nonempty (CategoryTheory.MonoidalClosed Context) := by
  rintro ⟨closed⟩
  letI : CategoryTheory.MonoidalClosed Context := closed
  exact notClosedOne ⟨inferInstance⟩

end Mettapedia.OSLF.Binding.ProjectionOnly
