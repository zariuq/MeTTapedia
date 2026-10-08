import Mettapedia.GSLT.Topos.PredicateFibration
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Order.BooleanAlgebra.Defs

/-!
# Presheaf theory restriction need not preserve implication

The two-object category `false ⟶ true` and the terminal category are cartesian
closed. The functor selecting `true` preserves products, the terminal object,
and exponentials. Nevertheless, its actual presheaf precomposition does not
preserve implication between subfunctors of the terminal presheaf.

The predicate supported at `false` has empty negation: the restriction from
`true` sees its support at `false`. After selecting only `true`, the predicate
is empty, so its negation is top. Thus a law requiring exact preservation of
fiber implication is stronger than arbitrary cartesian-closed theory change.

The implication below is the existing frame implication on actual subfunctors;
neither the presheaf action nor its truth values are replaced by lattice data.
-/

namespace Mettapedia.OSLF.PresheafNativeType.TheoryTranslationCounterexample

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory Opposite

noncomputable section

private abbrev heytingCartesian (C : Type) [HeytingAlgebra C] :
    CartesianMonoidalCategory C :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    { cone := asEmptyCone (⊤ : C), isLimit := isTerminalTop }
    (fun X Y =>
      { cone := BinaryFan.mk (P := X ⊓ Y) (homOfLE inf_le_left) (homOfLE inf_le_right)
        isLimit := Preorder.isLimitBinaryFan X Y })

private def implicationFunctor (C : Type) [HeytingAlgebra C] (A : C) : C ⥤ C where
  obj B := A ⇨ B
  map f := homOfLE (himp_le_himp_left f.le)

private abbrev heytingClosed (C : Type) [HeytingAlgebra C] :
    @MonoidalClosed C _ (heytingCartesian C).toMonoidalCategory := by
  letI : CartesianMonoidalCategory C := heytingCartesian C
  exact { closed := fun A =>
    { rightAdj := implicationFunctor C A
      adj := Adjunction.mkOfHomEquiv
        { homEquiv := fun X Y =>
            { toFun := fun f => homOfLE (le_himp_iff'.mpr f.le)
              invFun := fun f => homOfLE (le_himp_iff'.mp f.le)
              left_inv := fun _ => Subsingleton.elim _ _
              right_inv := fun _ => Subsingleton.elim _ _ }
          homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
          homEquiv_naturality_right := by intros; apply Subsingleton.elim } } }

local instance : CartesianMonoidalCategory Bool := heytingCartesian Bool
local instance : MonoidalClosed Bool := heytingClosed Bool
local instance : CartesianMonoidalCategory PUnit.{1} := heytingCartesian PUnit
local instance : MonoidalClosed PUnit.{1} := heytingClosed PUnit

/-- The actual base functor from the terminal category to the arrow category. -/
def selectTerminal : PUnit.{1} ⥤ Bool := (Functor.const PUnit).obj true

instance selectTerminal_preservesLimits : PreservesLimits selectTerminal where
  preservesLimitsOfShape :=
    { preservesLimit :=
        { preserves := fun _ =>
            ⟨{ lift := fun _ => homOfLE le_top
               fac := by intros; apply Subsingleton.elim
               uniq := by intros; apply Subsingleton.elim }⟩ } }

instance selectTerminal_monoidalClosed : MonoidalClosedFunctor selectTerminal where
  comparison_iso A := by
    have (B : PUnit.{1}) : IsIso ((expComparison selectTerminal A).natTrans.app B) :=
      ⟨⟨homOfLE le_rfl, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    exact NatIso.isIso_of_isIso_app _

/-- A singleton-valued presheaf with its ordinary identity restrictions. -/
def terminalPresheaf : Boolᵒᵖ ⥤ Type := (Functor.const Boolᵒᵖ).obj PUnit.{1}

/-- Terminality is established in the actual presheaf category. -/
def terminalPresheaf_isTerminal : IsTerminal terminalPresheaf :=
  IsTerminal.ofUniqueHom
    (fun X => { app := fun i => ↾(fun _ : X.obj i => PUnit.unit) })
    (by intro X f; ext i x; exact @Subsingleton.elim PUnit.{1} _ (f.app i x) PUnit.unit)

/-- The downward-closed predicate true only at the source of the arrow. -/
def supportedAtSource : Subfunctor terminalPresheaf where
  obj X := fun _ => X.unop = false
  map := by
    intro U V f x hx
    change V.unop = false
    have hle := le_of_op_hom f
    rw [hx] at hle
    exact le_antisymm hle bot_le

/-- Actual presheaf precomposition along the opposite of the base functor. -/
def precomposition : (Boolᵒᵖ ⥤ Type) ⥤ (PUnit.{1}ᵒᵖ ⥤ Type) :=
  (Functor.whiskeringLeft PUnit.{1}ᵒᵖ Boolᵒᵖ (Type)).obj selectTerminal.op

/-- Restrict a predicate on the same precomposed presheaf, including its maps. -/
def restrictPredicate (U : Subfunctor terminalPresheaf) :
    Subfunctor (precomposition.obj terminalPresheaf) where
  obj X := U.obj (selectTerminal.op.obj X)
  map f := U.map (selectTerminal.op.map f)

theorem supportedAtSource_truth_distinction :
    PUnit.unit ∈ supportedAtSource.obj (op false) ∧
      PUnit.unit ∉ supportedAtSource.obj (op true) := by
  constructor
  · change false = false
    rfl
  · change ¬ true = false
    decide

/-- Restriction preserves truth; the counterexample is specific to implication. -/
theorem restrict_top :
    restrictPredicate ⊤ = (⊤ : Subfunctor (precomposition.obj terminalPresheaf)) := rfl

theorem restrict_bot :
    restrictPredicate ⊥ = (⊥ : Subfunctor (precomposition.obj terminalPresheaf)) := rfl

theorem restrict_supportedAtSource :
    restrictPredicate supportedAtSource = ⊥ := by
  ext X x
  change (true = false) ↔ False
  simp

/-- At `true`, negation must also survive restriction along `false ⟶ true`. -/
theorem supportedAtSource_imp_bot :
    supportedAtSource ⇨ (⊥ : Subfunctor terminalPresheaf) = ⊥ := by
  apply le_antisymm
  · intro X x hx
    have hfalse : PUnit.unit ∉
        (supportedAtSource ⇨ (⊥ : Subfunctor terminalPresheaf)).obj (op false) := by
      intro h
      exact (himp_inf_le :
        (supportedAtSource ⇨ (⊥ : Subfunctor terminalPresheaf)) ⊓ supportedAtSource ≤ ⊥)
        (op false) ⟨h, supportedAtSource_truth_distinction.1⟩
    have hrestrict :=
      (supportedAtSource ⇨ (⊥ : Subfunctor terminalPresheaf)).map
        (homOfLE (show false ≤ X.unop by simp)).op hx
    exact hfalse hrestrict
  · exact bot_le

/-- Two different truth values remain observable in the restricted presheaf. -/
theorem restricted_truth_distinction :
    PUnit.unit ∈ (⊤ : Subfunctor (precomposition.obj terminalPresheaf)).obj
        (op (PUnit.unit : PUnit.{1})) ∧
      PUnit.unit ∉ (⊥ : Subfunctor (precomposition.obj terminalPresheaf)).obj
        (op (PUnit.unit : PUnit.{1})) := by
  exact ⟨Set.mem_univ _, Set.notMem_empty _⟩

theorem actual_precomposition_does_not_preserve_implication :
    restrictPredicate (supportedAtSource ⇨ (⊥ : Subfunctor terminalPresheaf)) ≠
      restrictPredicate supportedAtSource ⇨
        (⊥ : Subfunctor (precomposition.obj terminalPresheaf)) := by
  rw [supportedAtSource_imp_bot, restrict_supportedAtSource, bot_himp]
  intro h
  have hx := restricted_truth_distinction.1
  rw [← h] at hx
  exact hx

#print axioms selectTerminal_preservesLimits
#print axioms selectTerminal_monoidalClosed
#print axioms terminalPresheaf_isTerminal
#print axioms supportedAtSource_truth_distinction
#print axioms restrict_top
#print axioms restrict_bot
#print axioms supportedAtSource_imp_bot
#print axioms restricted_truth_distinction
#print axioms actual_precomposition_does_not_preserve_implication

end

end Mettapedia.OSLF.PresheafNativeType.TheoryTranslationCounterexample
