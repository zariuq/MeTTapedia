import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilySubstitution
import Mettapedia.TypeTheory.ContextualFutureSiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphGenerators

/-!
# Constructed global family representation at the explicit successor bound

A parameter carrier one universe above the original fibre bound admits
a strict global graph representation after the site and graph bound are
raised once. Its literal receipts decode whole original sections through
the proved site equivalence. This includes the actual untyped lower graph
universe and the complete future-family code universe.

All lower small family codes occur in a constructed upper graph enclosure.
This external successor enclosure does not internalize every upper family,
assert a same-level universal set, or assume a transfinite closure operator.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyEnclosure

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualSmallFamilyUniverse

universe u
variable {D : Type u} [Category.{u} D]
variable {base : D ⥤ Type (u+1)} (native : base.Elements ⥤ Type u)

abbrev UpperSite := ContextualFutureSiteLift.Raised (D := D)
abbrev upperBase := ContextualFutureSiteLift.base base
abbrev upperNative := ContextualFutureSiteLift.family base native

def parent : NaturalHom (upperBase (base := base)) (values (UpperSite (D := D))) :=
  ContextualGraphFamilyRepresentation.parent (upperNative native)

def literal : (upperBase (base := base)).Elements ⥤ Type (u+1) :=
  ContextualGraphFamilyRepresentation.literal (upperNative native)

def value (point : UpperSite (D := D)) (parameter : base.obj point.down) :
    Value (UpperSite (D := D)) point :=
  ContextualGraphFamilyRepresentation.value (upperNative native) point parameter

def decoder (point : UpperSite (D := D)) (parameter : base.obj point.down) :
    Child (UpperSite (D := D)) (value native point parameter) ≃ native.obj ⟨point.down, parameter⟩ :=
  (ContextualGraphFamilyRepresentation.decoder (upperNative native) ⟨point, parameter⟩).trans Equiv.ulift

def sectionDecoder : (literal native).sections ≃ native.sections :=
  (ContextualGraphFamilyRepresentation.sectionDecoder (upperNative native)).trans
    (ContextualFutureSiteLift.sections base native).symm

def selectionDecoder : native.sections ≃ ContextualGraphReceiptFamilies.Selection (parent native) :=
  (ContextualFutureSiteLift.sections base native).trans
    (ContextualGraphFamilyRepresentation.selectionDecoder (upperNative native))

theorem sectionDecoder_value (term : (literal native).sections) (point : base.Elements) :
    (sectionDecoder native term).val point =
      decoder native (PresheafSiteLift.Site.upFunctor.obj point.1) point.2
        (term.val ⟨PresheafSiteLift.Site.upFunctor.obj point.1, point.2⟩) := rfl

def globalConeSections (point : UpperSite (D := D)) (parameter : base.obj point.down) :
    (ContextualGraphFamilySubstitution.retained (upperNative native)
      (ContextualGraphFamilySubstitution.parameterMap point parameter)).sections ≃
      (ContextualGraphFamilyCones.literal (familyCode (upperNative native) point parameter)).sections :=
  ContextualGraphFamilySubstitution.globalConeSections (upperNative native) point parameter

section Universal

abbrev LowerCodes : D ⥤ Type (u+1) := universeFamily
abbrev LowerDecoder : (LowerCodes (D := D)).Elements ⥤ Type u := ContextualSmallFamilyUniverse.decoder

def representedCode (point : UpperSite (D := D)) (code : Code point.down) :
    Value (UpperSite (D := D)) point := value (LowerDecoder (D := D)) point code

def codeDecoder (point : UpperSite (D := D)) (code : Code point.down) :
    Child (UpperSite (D := D)) (representedCode point code) ≃ decode code :=
  decoder (LowerDecoder (D := D)) point code

variable (initial : UpperSite (D := D))

abbrev Origin : Type (u+1) := Σ target : UpperSite (D := D), Σ _arrival : initial ⟶ target, Code target.down

def source (origin : Origin initial) : UpperSite (D := D) := origin.1
def arrival (origin : Origin initial) : initial ⟶ source initial origin := origin.2.1
def witness (origin : Origin initial) : Value (UpperSite (D := D)) (source initial origin) :=
  representedCode origin.1 origin.2.2

def enclosure : Value (UpperSite (D := D)) initial :=
  ContextualGraphGenerators.root (source initial) (arrival initial) (witness initial) (𝟙 initial)

def enclosureRoot {target : UpperSite (D := D)} (path : initial ⟶ target) :
    Value (UpperSite (D := D)) target :=
  ContextualGraphGenerators.root (source initial) (arrival initial) (witness initial) path

theorem enclosure_move {target : UpperSite (D := D)} (path : initial ⟶ target) :
    move (UpperSite (D := D)) path (enclosure initial) = enclosureRoot initial path :=
  congrArg (ContextualGraphGenerators.root (source initial) (arrival initial) (witness initial))
    (Category.id_comp path)

/-- Every code newly available at an actual future is included. The
enclosure is not merely an enumeration of the codes visible initially. -/
def codeMember {target : UpperSite (D := D)} (path : initial ⟶ target) (code : Code target.down) :
    Member (representedCode target code) (move (UpperSite (D := D)) path (enclosure initial)) :=
  Member.transportParent (Equal.ofEq (enclosure_move initial path).symm)
    (Member.transportChild (Equal.ofEq (move_identity (UpperSite (D := D)) target (representedCode target code)))
      (ContextualGraphGenerators.rootIntro (source initial) (arrival initial) (witness initial)
        path ⟨target, path, code⟩ (𝟙 target) (Category.comp_id path)))

end Universal

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyEnclosure
