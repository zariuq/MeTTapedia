import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyEnclosure
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyProducts
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyW
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedFamilies

/-!
# Generated dependent families in the varying untyped graph model

Every actual decoded native family has a constructed graph for its entire
future cone. Small parameters admit one strict global graph; parameters
at the next level admit one after the explicitly raised site bound.
The original generated sum, product, identity and hereditary W recipes
are retained. Whole section and elimination comparisons use the actual
receipt decoder, not the older family's material term dictionaries.

The universal successor enclosure contains the complete future-family
classifier codes, including codes that appear only later. Its decoder
retains literal receipt values. Material equality can identify those
values, so this does not assert faithful extensional encoding of every
native type or closure under all upper-level families.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedFamilies

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualAuthoredMaterialFamilies
open ContextualGraphDiagrams ContextualRealizedGraphs

universe u v
variable {D : Type u} [Category.{u} D]
variable {worlds : ArgumentCoding D} {arrows : (first second : D) → ArgumentCoding (first ⟶ second)}
variable {seeds : (base : D ⥤ Type (max u v)) → Type (max (u+1) v)}
variable {seedModel : (base : D ⥤ Type (max u v)) → seeds base → Family base}
variable {base : D ⥤ Type (max u v)}
variable (code : ContextualAuthoredGeneratedFamilies.Code worlds arrows seeds seedModel base)

def coneValue (point : D) (parameter : base.obj point) : Value D point :=
  ContextualGraphFamilyCones.familyValue code.decode.native parameter

def currentDecoder (point : D) (parameter : base.obj point) :
    Child D (coneValue code point parameter) ≃ code.decode.native.obj ⟨point, parameter⟩ :=
  ContextualGraphFamilyCones.currentDecoder code.decode.native parameter

def wholeConeSections (point : D) (parameter : base.obj point) :
    (ContextualGraphFamilyCones.literal (familyCode code.decode.native point parameter)).sections ≃
      (restrict (futureElement point parameter) code.decode.native).sections :=
  ContextualGraphFamilyCones.wholeFamilySections code.decode.native parameter

/-- A generated code's whole future family is an actual member of the
constructed successor graph at every future arrival. -/
def codeMembership (initial : ContextualGraphFamilyEnclosure.UpperSite (D := D))
    {target : ContextualGraphFamilyEnclosure.UpperSite (D := D)} (path : initial ⟶ target)
    (parameter : base.obj target.down) :
    Member (ContextualGraphFamilyEnclosure.representedCode target
      (familyCode code.decode.native target.down parameter))
      (move _ path (ContextualGraphFamilyEnclosure.enclosure initial)) :=
  ContextualGraphFamilyEnclosure.codeMember initial path _

def enclosedDecoder (point : D) (parameter : base.obj point) :
    Child (ContextualGraphFamilyEnclosure.UpperSite (D := D))
      (ContextualGraphFamilyEnclosure.representedCode (PresheafSiteLift.Site.upFunctor.obj point)
        (familyCode code.decode.native point parameter)) ≃ code.decode.native.obj ⟨point, parameter⟩ :=
  (ContextualGraphFamilyEnclosure.codeDecoder _ _).trans (evaluationEquiv code.decode.native point parameter)

section Small
variable {smallSeeds : (base : D ⥤ Type u) → Type (u+1)}
variable {smallModels : (base : D ⥤ Type u) → smallSeeds base → Family.{u,u} base}
variable {smallBase : D ⥤ Type u}
variable (domain : ContextualAuthoredGeneratedFamilies.Code worlds arrows smallSeeds smallModels smallBase)
variable (body : ContextualAuthoredGeneratedFamilies.Code worlds arrows smallSeeds smallModels domain.decode.extension)

abbrev receipts := ContextualGraphFamilyRepresentation.literal domain.decode.native

def parent : NaturalHom smallBase (values D) := ContextualGraphFamilyRepresentation.parent domain.decode.native

def sections : (receipts domain).sections ≃ domain.decode.native.sections :=
  ContextualGraphFamilyRepresentation.sectionDecoder domain.decode.native

def selections : domain.decode.native.sections ≃ ContextualGraphReceiptFamilies.Selection (parent domain) :=
  ContextualGraphFamilyRepresentation.selectionDecoder domain.decode.native

def lambda : (receipts body).sections ≃ (receipts (domain.pi body)).sections :=
  ContextualGraphFamilyProducts.lambdaEquiv domain.decode.native body.decode.native

theorem abstraction_future (term : (receipts body).sections) (point : smallBase.Elements)
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain domain.decode.native point).Elements) :
    (ContextualGraphFamilyRepresentation.decode (domain.pi body).decode.native point
      ((lambda domain body term).val point)).val argument =
      ContextualGraphFamilyRepresentation.decode body.decode.native
        ((ContextualSmallFamilyComprehension.flatten domain.decode.native).obj
          ((ContextualSmallFamilyTypeFormers.futureArguments domain.decode.native point).obj argument))
        (term.val ((ContextualSmallFamilyComprehension.flatten domain.decode.native).obj
          ((ContextualSmallFamilyTypeFormers.futureArguments domain.decode.native point).obj argument))) :=
  ContextualGraphFamilyProducts.lambda_future_value domain.decode.native body.decode.native term point argument

variable (motive : ContextualAuthoredGeneratedFamilies.Code worlds arrows smallSeeds smallModels
  (ContextualSmallFamilyIdentity.identityContext domain.decode.native))

/-- Independently decoded generated motives use the actual receipt
identity context, and their complete sections commute with native J. -/
theorem generated_J_square
    (method : (ContextualGraphFamilyRepresentation.literal
      (ContextualSmallFamilyIdentity.reindex motive.decode.native
        (ContextualSmallFamilyIdentity.diagonal domain.decode.native))).sections) :
    ContextualGraphFamilyRepresentation.sectionDecoder
      (ContextualGraphFamilyIdentity.pulledMotive domain.decode.native motive.decode.native)
      (ContextualGraphFamilyIdentity.nativeReceiptJ domain.decode.native motive.decode.native method) =
      ContextualSmallFamilyIdentity.reindexSection (ContextualGraphFamilyIdentity.toNativeIdentity domain.decode.native)
        motive.decode.native (ContextualSmallFamilyIdentity.J domain.decode.native motive.decode.native
          (ContextualGraphFamilyRepresentation.sectionDecoder _ method)) :=
  ContextualGraphFamilyIdentity.nativeReceiptJ_square domain.decode.native motive.decode.native method

end Small

section Wider
variable {wideSeeds : (base : D ⥤ Type (u+1)) → Type (u+1)}
variable {wideModels : (base : D ⥤ Type (u+1)) → wideSeeds base → Family.{u,u+1} base}
variable {wideBase : D ⥤ Type (u+1)}
variable (wide : ContextualAuthoredGeneratedFamilies.Code.{u,u+1} worlds arrows wideSeeds wideModels wideBase)

def upperSections : (ContextualGraphFamilyEnclosure.literal wide.decode.native).sections ≃
    wide.decode.native.sections := ContextualGraphFamilyEnclosure.sectionDecoder wide.decode.native

def upperSelections : wide.decode.native.sections ≃
    ContextualGraphReceiptFamilies.Selection (ContextualGraphFamilyEnclosure.parent wide.decode.native) :=
  ContextualGraphFamilyEnclosure.selectionDecoder wide.decode.native

end Wider

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGeneratedFamilies
