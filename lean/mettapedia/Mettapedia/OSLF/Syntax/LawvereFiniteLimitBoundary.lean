import Mettapedia.OSLF.Syntax.TermCloneCategoryComparison
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Finite products do not give the finite limits of a classifying theory

A one-sorted signature with one unary constructor has the finite products
provided by every binding-clone context category. Its context category lacks
the equalizer of identity and that constructor: an equalizing arrow would be
a finite term equal to its own unary successor, contrary to syntactic size.

The presheaf category has this equalizer, but every one of its fibres is
empty, so it cannot be represented by an existing raw context. This identifies
a concrete object that a finite-limit completion must add. It does not claim
that the whole presheaf category is the free finite-limit or cartesian-closed
completion of the authored theory.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.UnaryContextBoundary

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

inductive UnaryOp : Unit → Type where
  | next : UnaryOp ()

/-- The single unary operation binds nothing and has no constant. -/
def signature : Signature where
  Srt := Unit
  Op := UnaryOp
  arity := fun {_} op => match op with
    | .next => [([], ())]

def one : Syntactic.Ctxt signature := ⟨[()]⟩

def nextTerm {Γ : Ctx signature} (term : Term signature Γ ()) :
    Term signature Γ () :=
  .op UnaryOp.next (.cons term .nil)

/-- Applying the unary constructor strictly increases syntactic size. -/
theorem nextTerm_ne_self {Γ : Ctx signature}
    (term : Term signature Γ ()) : nextTerm term ≠ term := by
  intro equal
  have sizes := congrArg termSize equal
  simp only [nextTerm, termSize, argsSize] at sizes
  omega

def nextArrow : one ⟶ one :=
  fun _ v => match v with
    | .zero => nextTerm (.var .zero)
    | .succ impossible => nomatch impossible

/-- No environment can equalize identity and the unary operation. -/
theorem no_equalizing_arrow (Γ : Syntactic.Ctxt signature)
    (arrow : Γ ⟶ one) :
    arrow ≫ (𝟙 one) ≠ arrow ≫ nextArrow := by
  intro equal
  have atVariable := congrFun (congrFun equal ())
    (Var.zero : Var [()] ())
  change arrow () Var.zero = nextTerm (arrow () Var.zero) at atVariable
  exact (nextTerm_ne_self (arrow () Var.zero)) atVariable.symm

/-- The finite-product context category of this valid unary signature lacks
the equalizer of identity and its unary operation. -/
theorem no_equalizer : ¬ HasEqualizer (𝟙 one) nextArrow := by
  intro available
  obtain ⟨limitCone⟩ := available.exists_limit
  let fork := Fork.ofCone limitCone.cone
  exact no_equalizing_arrow fork.pt fork.ι (Fork.condition fork)

/-- The same context category does have finite products, by the general
clone/context-category construction. -/
theorem has_finite_products : HasFiniteProducts (Syntactic.Ctxt signature) :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

/-- The two natural endomorphisms of the singleton representable encode the
identity and the authored unary operation. -/
def yonedaIdentity : yoneda.obj one ⟶ yoneda.obj one :=
  yoneda.map (𝟙 one)

def yonedaNext : yoneda.obj one ⟶ yoneda.obj one :=
  yoneda.map nextArrow

/-- The presheaf category contains the equalizer that raw contexts lack. -/
noncomputable def fixedPointPresheaf :
    (Syntactic.Ctxt signature)ᵒᵖ ⥤ Type :=
  equalizer yonedaIdentity yonedaNext

/-- The newly supplied equalizer has no section at any raw context: a section
would be a fixed term for the unary constructor. -/
theorem fixedPointPresheaf_empty_at
    (X : (Syntactic.Ctxt signature)ᵒᵖ) :
    IsEmpty (fixedPointPresheaf.obj X) := by
  refine ⟨fun point => ?_⟩
  let termArrow : X.unop ⟶ one :=
    (equalizer.ι yonedaIdentity yonedaNext).app X point
  have condition := equalizer.condition yonedaIdentity yonedaNext
  have atX := congrArg
    (fun transformation : fixedPointPresheaf ⟶ yoneda.obj one =>
      transformation.app X point) condition
  have fixed : termArrow ≫ 𝟙 one = termArrow ≫ nextArrow := by
    exact atX
  exact no_equalizing_arrow X.unop termArrow fixed

/-- The new equalizer object cannot be represented by any raw context: its
fibre at that context would contain the representing identity arrow. -/
theorem fixedPointPresheaf_not_representable :
    ¬ ∃ Γ : Syntactic.Ctxt signature,
      Nonempty (fixedPointPresheaf ≅ yoneda.obj Γ) := by
  rintro ⟨Γ, ⟨representation⟩⟩
  let point : fixedPointPresheaf.obj (Opposite.op Γ) :=
    representation.inv.app (Opposite.op Γ) (𝟙 Γ)
  exact (fixedPointPresheaf_empty_at (Opposite.op Γ)).false point

/-- The missing equalizer is an initial object of the ambient presheaf
category: every pointwise source fibre is empty, so each outgoing natural
transformation exists uniquely. -/
noncomputable def fixedPointPresheaf_isInitial :
    IsInitial fixedPointPresheaf := by
  refine IsInitial.ofUniqueHom
    (fun target => {
      app := fun X => TypeCat.ofHom
        (fun point => ((fixedPointPresheaf_empty_at X).false point).elim)
      naturality := by
        intro X Y f
        apply ConcreteCategory.hom_ext
        intro point
        exact ((fixedPointPresheaf_empty_at X).false point).elim }) ?_
  intro target arrow
  ext X point
  exact ((fixedPointPresheaf_empty_at X).false point).elim

end Mettapedia.OSLF.Binding.UnaryContextBoundary
