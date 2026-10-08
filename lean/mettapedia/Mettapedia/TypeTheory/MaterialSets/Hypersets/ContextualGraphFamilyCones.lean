import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyRepresentation

/-!
# Whole future family cones as original-small contextual graphs

A family over a possibly wider parameter universe is localized at an
actual parameter. Its full future cone is small and is represented by
one actual contextual diagram retaining that origin and every arrival.
Literal receipt transport decodes to the native family action, and whole
sections decode bijectively. Recentring an origin is an explicit natural
comparison of receipt families; it is not an equality of authored diagrams.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyCones

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualGraphDiagrams ContextualSmallFamilyUniverse
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D]

def arrivals (point : D) : D ⥤ Type u where
  obj target := point ⟶ target
  map tail := TypeCat.ofHom (fun path => path ≫ tail)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    exact Category.comp_id
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro path
    exact (Category.assoc path first second).symm

def coneTarget (point : D) : (arrivals point).Elements ⥤ Future.Objects point where
  obj future := ⟨future.1, future.2⟩
  map step := ⟨step.1, step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def coneElements (point : D) : Future.Objects point ⥤ (arrivals point).Elements where
  obj future := ⟨future.1, future.2⟩
  map step := ⟨step.1, step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable {point : D} (code : Code point)

def nativeCone : (arrivals point).Elements ⥤ Type u := restrict (coneTarget point) code

def parent : NaturalHom (arrivals point) (values D) :=
  ContextualGraphFamilyRepresentation.parent (nativeCone code)

def literal : (arrivals point).Elements ⥤ Type u :=
  ContextualGraphFamilyRepresentation.literal (nativeCone code)

def value {target : D} (path : point ⟶ target) : Value D target :=
  ContextualGraphFamilyRepresentation.value (nativeCone code) target path

theorem value_move {first second : D} (tail : first ⟶ second) (path : point ⟶ first) :
    move D tail (value code path) = value code (path ≫ tail) := rfl

def decoder (target : D) (path : point ⟶ target) :
    Child D (value code path) ≃ code.obj ⟨target, path⟩ :=
  ContextualGraphFamilyRepresentation.decoder (nativeCone code) ⟨target, path⟩

theorem decoder_naturality {first second : (arrivals point).Elements} (step : first ⟶ second)
    (receipt : (literal code).obj first) :
    decoder code second.1 second.2 ((literal code).map step receipt) =
      code.map ((coneTarget point).map step) (decoder code first.1 first.2 receipt) :=
  ContextualGraphFamilyRepresentation.decode_naturality (nativeCone code) step receipt

def nativeSectionEquiv : (nativeCone code).sections ≃ code.sections where
  toFun term := ⟨fun future => term.val ⟨future.1, future.2⟩,
    fun {_ _} arrow => term.property ((coneElements point).map arrow)⟩
  invFun term := ⟨fun future => term.val ⟨future.1, future.2⟩,
    fun {_ _} arrow => term.property ((coneTarget point).map arrow)⟩
  left_inv term := by
    apply Subtype.ext
    funext future
    rfl
  right_inv term := by
    apply Subtype.ext
    funext future
    rfl

def sectionDecoder : (literal code).sections ≃ code.sections :=
  (ContextualGraphFamilyRepresentation.sectionDecoder (nativeCone code)).trans (nativeSectionEquiv code)

def selectionDecoder : code.sections ≃ ContextualGraphReceiptFamilies.Selection (parent code) :=
  (nativeSectionEquiv code).symm.trans (ContextualGraphFamilyRepresentation.selectionDecoder (nativeCone code))

section ArbitraryBase
variable {base : D ⥤ Type v} (family : base.Elements ⥤ Type u)
variable (parameter : base.obj point)

/-- An actual value in the same untyped universe; the represented family
may have a larger parameter carrier, but this whole future cone is small. -/
def familyValue : Value D point := value (familyCode family point parameter) (𝟙 point)

def currentDecoder : Child D (familyValue family parameter) ≃ family.obj ⟨point, parameter⟩ :=
  (decoder (familyCode family point parameter) point (𝟙 point)).trans (evaluationEquiv family point parameter)

def futureDecoder (target : D) (path : point ⟶ target) :
    Child D (value (familyCode family point parameter) path) ≃
      family.obj ⟨target, base.map path parameter⟩ :=
  decoder (familyCode family point parameter) target path

def wholeFamilySections :
    (literal (familyCode family point parameter)).sections ≃
      (restrict (futureElement point parameter) family).sections :=
  sectionDecoder (familyCode family point parameter)

end ArbitraryBase

def originPrefix {target : D} (path : point ⟶ target) : NaturalHom (arrivals target) (arrivals point) where
  app _ tail := path ≫ tail
  naturality tail arrival := Category.assoc path arrival tail

theorem nativeCone_prefix {target : D} (path : point ⟶ target) :
    restrict (elementMap (originPrefix path)) (nativeCone code) = nativeCone (codeMap path code) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def retained {target : D} (path : point ⟶ target) : (arrivals target).Elements ⥤ Type u :=
  ContextualGraphReceiptFamilies.along ((originPrefix path).comp (parent code))

def recenter {target : D} (path : point ⟶ target) :
    NaturalHom (retained code path) (literal (codeMap path code)) where
  app future receipt := ContextualGraphFamilyRepresentation.encode (nativeCone (codeMap path code)) future
    (decoder code future.1 (path ≫ future.2) receipt)
  naturality {first second} step receipt := by
    have encoded := ContextualGraphFamilyRepresentation.encode_naturality
      (nativeCone (codeMap path code)) step (decoder code first.1 (path ≫ first.2) receipt)
    have decoded := decoder_naturality code ((elementMap (originPrefix path)).map step) receipt
    exact encoded.trans (congrArg
      (ContextualGraphFamilyRepresentation.encode (nativeCone (codeMap path code)) second) decoded.symm)

def retainOrigin {target : D} (path : point ⟶ target) :
    NaturalHom (literal (codeMap path code)) (retained code path) where
  app future receipt := ContextualGraphFamilyRepresentation.encode (nativeCone code)
    ⟨future.1, path ≫ future.2⟩ (decoder (codeMap path code) future.1 future.2 receipt)
  naturality {first second} step receipt := by
    have encoded := ContextualGraphFamilyRepresentation.encode_naturality
      (nativeCone code) ((elementMap (originPrefix path)).map step)
      (decoder (codeMap path code) first.1 first.2 receipt)
    have decoded := decoder_naturality (codeMap path code) step receipt
    exact encoded.trans (congrArg
      (ContextualGraphFamilyRepresentation.encode (nativeCone code) ⟨second.1, path ≫ second.2⟩) decoded.symm)

def recenteringSections {target : D} (path : point ⟶ target) :
    (retained code path).sections ≃ (literal (codeMap path code)).sections where
  toFun := (recenter code path).mapSection
  invFun := (retainOrigin code path).mapSection
  left_inv term := by
    apply Subtype.ext
    funext future
    exact (decoder code future.1 (path ≫ future.2)).symm_apply_apply (term.val future)
  right_inv term := by
    apply Subtype.ext
    funext future
    exact (decoder (codeMap path code) future.1 future.2).symm_apply_apply (term.val future)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyCones
