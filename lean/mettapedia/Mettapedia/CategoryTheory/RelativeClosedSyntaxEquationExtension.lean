import Mettapedia.CategoryTheory.RelativeClosedSyntaxDeclarationBounds
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapClosed
import Mettapedia.GSLT.Core.LambdaTheory

/-!
# Adjoining actual typed equation declarations

An equation declaration supplies two independently admitted parallel raw
arrows. Their complete expressions determine the new declaration rank.
Original objects, operators and equations retain their origins. The actual
syntax inclusion transports all generated judgments and preserves finite
limits and function objects.

The new equation is derived from its authored declaration in the generated
calculus. It is not assumed to hold in a target interpretation; that requires
a separate local satisfaction proof.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.EquationExtension

open _root_.CategoryTheory
open GeneratedCategory

universe k

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (signature : Signature (C := C) (symbols := symbols))

structure Declaration where
  source : Object signature
  target : Object signature
  left : RawHom source target
  right : RawHom source target

variable {Index : Type k}

def extendedSymbols (symbols : Symbols.{k}) (Index : Type k) : Symbols.{k} where
  ObjectName := symbols.ObjectName
  ArrowName := symbols.ArrowName
  EquationName := symbols.EquationName ⊕ Index

def originalObject (code : ObjectCode C symbols) : ObjectCode C (extendedSymbols symbols Index) :=
  ObjectCode.map (symbols := symbols) (targetSymbols := extendedSymbols symbols Index)
    (Functor.id C) id id code

def originalArrow (code : ArrowCode C symbols) : ArrowCode C (extendedSymbols symbols Index) :=
  ArrowCode.map (symbols := symbols) (targetSymbols := extendedSymbols symbols Index)
    (Functor.id C) id id code

variable (declarations : Index → Declaration signature)

def addedRank (origin : Index) : Nat :=
  max (DeclarationBounds.objectRequirement signature.objectRank signature.arrowRank (declarations origin).source.code)
    (max (DeclarationBounds.objectRequirement signature.objectRank signature.arrowRank (declarations origin).target.code)
      (max (DeclarationBounds.arrowRequirement signature.objectRank signature.arrowRank (declarations origin).left.code)
        (DeclarationBounds.arrowRequirement signature.objectRank signature.arrowRank (declarations origin).right.code)))

private theorem original_object_before (bound : Nat) (code : ObjectCode C symbols) :
    ObjectCode.before (symbols := extendedSymbols symbols Index)
      signature.objectRank signature.arrowRank bound (originalObject code) ↔
      code.before signature.objectRank signature.arrowRank bound :=
  DeclarationBounds.object_before_map (symbols := symbols) (nextSymbols := extendedSymbols symbols Index)
    signature.objectRank signature.arrowRank (Functor.id C) id id
    signature.objectRank signature.arrowRank (fun _ => rfl) (fun _ => rfl) bound code

private theorem original_arrow_before (bound : Nat) (code : ArrowCode C symbols) :
    ArrowCode.before (symbols := extendedSymbols symbols Index)
      signature.objectRank signature.arrowRank bound (originalArrow code) ↔
      code.before signature.objectRank signature.arrowRank bound :=
  DeclarationBounds.arrow_before_map (symbols := symbols) (nextSymbols := extendedSymbols symbols Index)
    signature.objectRank signature.arrowRank (Functor.id C) id id
    signature.objectRank signature.arrowRank (fun _ => rfl) (fun _ => rfl) bound code

def extend : Signature (C := C) (symbols := extendedSymbols symbols Index) where
  objectRank := signature.objectRank
  arrowRank := signature.arrowRank
  source origin := originalObject (signature.source origin)
  target origin := originalObject (signature.target origin)
  source_before origin := (original_object_before signature _ _).mpr (signature.source_before origin)
  target_before origin := (original_object_before signature _ _).mpr (signature.target_before origin)
  equationRank
    | .inl origin => signature.equationRank origin
    | .inr origin => addedRank signature declarations origin
  equationSource
    | .inl origin => originalObject (signature.equationSource origin)
    | .inr origin => originalObject (declarations origin).source.code
  equationTarget
    | .inl origin => originalObject (signature.equationTarget origin)
    | .inr origin => originalObject (declarations origin).target.code
  left
    | .inl origin => originalArrow (signature.left origin)
    | .inr origin => originalArrow (declarations origin).left.code
  right
    | .inl origin => originalArrow (signature.right origin)
    | .inr origin => originalArrow (declarations origin).right.code
  equation_before origin := by
    cases origin with
    | inl origin =>
        obtain ⟨source, target, first, second⟩ := signature.equation_before origin
        exact ⟨(original_object_before signature _ _).mpr source,
          (original_object_before signature _ _).mpr target,
          (original_arrow_before signature _ _).mpr first,
          (original_arrow_before signature _ _).mpr second⟩
    | inr origin =>
        refine ⟨(original_object_before signature _ _).mpr ?_,
          (original_object_before signature _ _).mpr ?_,
          (original_arrow_before signature _ _).mpr ?_,
          (original_arrow_before signature _ _).mpr ?_⟩
        · apply (DeclarationBounds.object_before_iff signature.objectRank signature.arrowRank _ _).mpr
          exact le_max_left _ _
        · apply (DeclarationBounds.object_before_iff signature.objectRank signature.arrowRank _ _).mpr
          exact (le_max_left _ _).trans (le_max_right _ _)
        · apply (DeclarationBounds.arrow_before_iff signature.objectRank signature.arrowRank _ _).mpr
          exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
        · apply (DeclarationBounds.arrow_before_iff signature.objectRank signature.arrowRank _ _).mpr
          exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

def inclusion : SignatureMap signature (extend signature declarations) where
  base := Functor.id C
  objects := id
  arrows := id
  equations := Sum.inl
  source _ := rfl
  target _ := rfl
  equationSource _ := rfl
  equationTarget _ := rfl
  left _ := rfl
  right _ := rfl

def headers (original : HeaderFormation signature) : HeaderFormation (extend signature declarations) where
  source origin := (inclusion signature declarations).derivation (original.source origin)
  target origin := (inclusion signature declarations).derivation (original.target origin)
  left
    | .inl origin => (inclusion signature declarations).derivation (original.left origin)
    | .inr origin => (inclusion signature declarations).derivation (declarations origin).left.admitted.some
  right
    | .inl origin => (inclusion signature declarations).derivation (original.right origin)
    | .inr origin => (inclusion signature declarations).derivation (declarations origin).right.admitted.some

def equation (origin : Index) : Derivation (extend signature declarations)
    (.equation (originalObject (declarations origin).source.code)
      (originalObject (declarations origin).target.code)
      (originalArrow (declarations origin).left.code) (originalArrow (declarations origin).right.code)) :=
  .declaredEquation (signature := extend signature declarations) (Sum.inr origin)
    ((inclusion signature declarations).derivation (declarations origin).left.admitted.some)
    ((inclusion signature declarations).derivation (declarations origin).right.admitted.some)

theorem equation_class (origin : Index) :
    (inclusion signature declarations).functor.map (classOf (declarations origin).left) =
      (inclusion signature declarations).functor.map (classOf (declarations origin).right) :=
  Quotient.sound ⟨equation signature declarations origin⟩

def theory : Mettapedia.GSLT.Core.LambdaTheory.{k, k} :=
  Mettapedia.GSLT.Core.LambdaTheory.ofCategory (Object (extend signature declarations))

def theoryMap : Mettapedia.GSLT.Core.LambdaTheoryMap
    (Mettapedia.GSLT.Core.LambdaTheory.ofCategory (Object signature)) (theory signature declarations) where
  functor := (inclusion signature declarations).functor
  preservesFiniteLimits := SignatureMap.functor_preservesFiniteLimits (inclusion signature declarations)
  preservesExponentials := SignatureMap.functor_closed (inclusion signature declarations)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.EquationExtension
