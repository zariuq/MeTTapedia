import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMap

/-!
# Composition of declaration-local maps

Composition combines the independently supplied base functors and primitive
name maps. Complete object and arrow renaming earns all six local header and
equation comparisons. The resulting map transports the actual generated
judgments, rather than only listing a composite family of names.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.SignatureMap

open _root_.CategoryTheory

universe u v a w z b r h c

variable {C : Type u} [Category.{v} C] {firstSymbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D] {secondSymbols : Symbols.{b}}
variable {E : Type r} [Category.{h} E] {thirdSymbols : Symbols.{c}}
variable {first : Signature (C := C) (symbols := firstSymbols)}
variable {second : Signature (C := D) (symbols := secondSymbols)}
variable {third : Signature (C := E) (symbols := thirdSymbols)}
variable (before : SignatureMap first second) (after : SignatureMap second third)

def identity (signature : Signature (C := C) (symbols := firstSymbols)) : SignatureMap signature signature where
  base := Functor.id C
  objects := id
  arrows := id
  equations := id
  source origin := (ObjectCode.map_identity (signature.source origin)).symm
  target origin := (ObjectCode.map_identity (signature.target origin)).symm
  equationSource origin := (ObjectCode.map_identity (signature.equationSource origin)).symm
  equationTarget origin := (ObjectCode.map_identity (signature.equationTarget origin)).symm
  left origin := (ArrowCode.map_identity (signature.left origin)).symm
  right origin := (ArrowCode.map_identity (signature.right origin)).symm

def compose : SignatureMap first third where
  base := before.base ⋙ after.base
  objects := after.objects ∘ before.objects
  arrows := after.arrows ∘ before.arrows
  equations := after.equations ∘ before.equations
  source origin := (after.source (before.arrows origin)).trans
    ((congrArg (fun code => code.map after.base after.objects after.arrows) (before.source origin)).trans
      (ObjectCode.map_compose before.base after.base before.objects after.objects before.arrows after.arrows _))
  target origin := (after.target (before.arrows origin)).trans
    ((congrArg (fun code => code.map after.base after.objects after.arrows) (before.target origin)).trans
      (ObjectCode.map_compose before.base after.base before.objects after.objects before.arrows after.arrows _))
  equationSource origin := (after.equationSource (before.equations origin)).trans
    ((congrArg (fun code => code.map after.base after.objects after.arrows) (before.equationSource origin)).trans
      (ObjectCode.map_compose before.base after.base before.objects after.objects before.arrows after.arrows _))
  equationTarget origin := (after.equationTarget (before.equations origin)).trans
    ((congrArg (fun code => code.map after.base after.objects after.arrows) (before.equationTarget origin)).trans
      (ObjectCode.map_compose before.base after.base before.objects after.objects before.arrows after.arrows _))
  left origin := (after.left (before.equations origin)).trans
    ((congrArg (fun code => code.map after.base after.objects after.arrows) (before.left origin)).trans
      (ArrowCode.map_compose before.base after.base before.objects after.objects before.arrows after.arrows _))
  right origin := (after.right (before.equations origin)).trans
    ((congrArg (fun code => code.map after.base after.objects after.arrows) (before.right origin)).trans
      (ArrowCode.map_compose before.base after.base before.objects after.objects before.arrows after.arrows _))

theorem object_code_compose (object : GeneratedCategory.Object first) :
    (after.object (before.object object)).code = ((before.compose after).object object).code :=
  ObjectCode.map_compose before.base after.base before.objects after.objects before.arrows after.arrows object.code

theorem object_compose (object : GeneratedCategory.Object first) :
    after.object (before.object object) = (before.compose after).object object :=
  GeneratedCategory.Object.ext (object_code_compose before after object)

theorem arrow_code_compose {source target : GeneratedCategory.Object first}
    (arrow : GeneratedCategory.RawHom source target) :
    (after.rawArrow (before.rawArrow arrow)).code = ((before.compose after).rawArrow arrow).code :=
  ArrowCode.map_compose before.base after.base before.objects after.objects before.arrows after.arrows arrow.code

end Mettapedia.CategoryTheory.RelativeClosedSyntax.SignatureMap
