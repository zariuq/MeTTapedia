import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyCones
import Mettapedia.TypeTheory.ContextualSmallFamilyIdentity

/-!
# Substitution between independently constructed contextual receipt graphs

The graph retained through a parameter substitution and the graph newly
constructed for the substituted family have inverse natural receipt
comparisons. Their native decoders commute on complete sections. No
equality of the two authored graph diagrams is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilySubstitution

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse
open ContextualGraphFamilyRepresentation

universe u
variable {D : Type u} [Category.{u} D] {base other : D ⥤ Type u}
variable (native : base.Elements ⥤ Type u) (change : NaturalHom other base)

abbrev nativeUnder := restrict (elementMap change) native
abbrev retained := ContextualGraphReceiptFamilies.along (change.comp (parent native))

def forward : NaturalHom (retained native change) (literal (nativeUnder native change)) where
  app point receipt := encode (nativeUnder native change) point
    (decode native ((elementMap change).obj point) receipt)
  naturality {_first second} step receipt :=
    (encode_naturality (nativeUnder native change) step _).trans
      (congrArg (encode (nativeUnder native change) second)
        (decode_naturality native ((elementMap change).map step) receipt).symm)

def backward : NaturalHom (literal (nativeUnder native change)) (retained native change) where
  app point receipt := encode native ((elementMap change).obj point)
    (decode (nativeUnder native change) point receipt)
  naturality {_first second} step receipt :=
    (encode_naturality native ((elementMap change).map step) _).trans
      (congrArg (encode native ((elementMap change).obj second))
        (decode_naturality (nativeUnder native change) step receipt).symm)

theorem forward_backward : (forward native change).comp (backward native change) =
    ContextualSmallMapConstructions.identity (retained native change) := by
  apply NaturalHom.ext
  intro point receipt
  exact encode_decode native ((elementMap change).obj point) receipt

theorem backward_forward : (backward native change).comp (forward native change) =
    ContextualSmallMapConstructions.identity (literal (nativeUnder native change)) := by
  apply NaturalHom.ext
  intro point receipt
  exact encode_decode (nativeUnder native change) point receipt

def sectionComparison : (retained native change).sections ≃ (literal (nativeUnder native change)).sections where
  toFun := (forward native change).mapSection
  invFun := (backward native change).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact encode_decode native ((elementMap change).obj point) (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact encode_decode (nativeUnder native change) point (term.val point)

def pullSection (term : (literal native).sections) : (retained native change).sections :=
  ⟨fun point => term.val ((elementMap change).obj point),
    fun {_ _} step => term.property ((elementMap change).map step)⟩

def substituteSection (term : (literal native).sections) : (literal (nativeUnder native change)).sections :=
  sectionComparison native change (pullSection native change term)

theorem decoder_substitution (term : (literal native).sections) :
    sectionDecoder (nativeUnder native change) (substituteSection native change term) =
      ContextualSmallFamilyIdentity.reindexSection change native (sectionDecoder native term) := by
  apply Subtype.ext
  funext point
  rfl

theorem substitution_identity (term : (literal native).sections) :
    substituteSection native (ContextualSmallMapConstructions.identity base) term = term := by
  apply Subtype.ext
  funext point
  exact encode_decode native point (term.val point)

theorem substitution_composition {third : D ⥤ Type u} (later : NaturalHom third other)
    (term : (literal native).sections) :
    substituteSection (nativeUnder native change) later (substituteSection native change term) =
      substituteSection native (later.comp change) term := by
  apply Subtype.ext
  funext point
  rfl

section Cone
variable (point : D) (parameter : base.obj point)

def parameterMap : NaturalHom (ContextualGraphFamilyCones.arrivals point) base where
  app _target path := base.map path parameter
  naturality tail path := (base.map_comp_apply path tail parameter).symm

theorem native_under_parameter : nativeUnder native (parameterMap point parameter) =
    ContextualGraphFamilyCones.nativeCone (familyCode native point parameter) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

/-- The retained global graph and its separately constructed whole-cone
representation decode the same actual native family after parameter pullback. -/
def globalConeSections :
    (retained native (parameterMap point parameter)).sections ≃
      (ContextualGraphFamilyCones.literal (familyCode native point parameter)).sections :=
  sectionComparison native (parameterMap point parameter)

end Cone

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilySubstitution
