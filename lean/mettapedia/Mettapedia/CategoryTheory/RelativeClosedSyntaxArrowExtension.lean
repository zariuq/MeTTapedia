import Mettapedia.CategoryTheory.RelativeClosedSyntaxDeclarationBounds
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapClosed
import Mettapedia.GSLT.Core.LambdaTheory

/-!
# Adjoining independently typed primitive arrows

A declaration retains its complete generated domain and codomain. Their
computed name requirements determine the new arrow rank. All original
objects, operators and equations retain their origins and rank admission.
The actual generated inclusion preserves finite limits and function objects.
New operators are genuine primitive arrows between the mapped authored
objects; no equation or target satisfaction is assumed for them.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.ArrowExtension

open _root_.CategoryTheory
open GeneratedCategory

universe k

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (signature : Signature (C := C) (symbols := symbols))

structure Declaration where
  source : Object signature
  target : Object signature

variable {Index : Type k}

def extendedSymbols (symbols : Symbols.{k}) (Index : Type k) : Symbols.{k} where
  ObjectName := symbols.ObjectName
  ArrowName := symbols.ArrowName ⊕ Index
  EquationName := symbols.EquationName

def originalObject (code : ObjectCode C symbols) : ObjectCode C (extendedSymbols symbols Index) :=
  ObjectCode.map (symbols := symbols) (targetSymbols := extendedSymbols symbols Index)
    (Functor.id C) id Sum.inl code

def originalArrow (code : ArrowCode C symbols) : ArrowCode C (extendedSymbols symbols Index) :=
  ArrowCode.map (symbols := symbols) (targetSymbols := extendedSymbols symbols Index)
    (Functor.id C) id Sum.inl code

variable (declarations : Index → Declaration signature)

def addedRank (origin : Index) : Nat :=
  max (DeclarationBounds.objectRequirement signature.objectRank signature.arrowRank (declarations origin).source.code)
    (DeclarationBounds.objectRequirement signature.objectRank signature.arrowRank (declarations origin).target.code)

def arrowRanks : (extendedSymbols symbols Index).ArrowName → Nat
  | .inl origin => signature.arrowRank origin
  | .inr origin => addedRank signature declarations origin

private theorem original_object_before (bound : Nat) (code : ObjectCode C symbols) :
    ObjectCode.before (symbols := extendedSymbols symbols Index) signature.objectRank
      (arrowRanks signature declarations) bound (originalObject code) ↔
        code.before signature.objectRank signature.arrowRank bound :=
  DeclarationBounds.object_before_map (symbols := symbols) (nextSymbols := extendedSymbols symbols Index)
    signature.objectRank signature.arrowRank (Functor.id C) id Sum.inl
    signature.objectRank (arrowRanks signature declarations) (fun _ => rfl) (fun _ => rfl) bound code

private theorem original_arrow_before (bound : Nat) (code : ArrowCode C symbols) :
    ArrowCode.before (symbols := extendedSymbols symbols Index) signature.objectRank
      (arrowRanks signature declarations) bound (originalArrow code) ↔
        code.before signature.objectRank signature.arrowRank bound :=
  DeclarationBounds.arrow_before_map (symbols := symbols) (nextSymbols := extendedSymbols symbols Index)
    signature.objectRank signature.arrowRank (Functor.id C) id Sum.inl
    signature.objectRank (arrowRanks signature declarations) (fun _ => rfl) (fun _ => rfl) bound code

def extend : Signature (C := C) (symbols := extendedSymbols symbols Index) where
  objectRank := signature.objectRank
  arrowRank := arrowRanks signature declarations
  source
    | .inl origin => originalObject (signature.source origin)
    | .inr origin => originalObject (declarations origin).source.code
  target
    | .inl origin => originalObject (signature.target origin)
    | .inr origin => originalObject (declarations origin).target.code
  source_before origin := by
    cases origin with
    | inl origin => exact (original_object_before signature declarations _ _).mpr (signature.source_before origin)
    | inr origin =>
        apply (original_object_before signature declarations _ _).mpr
        exact (DeclarationBounds.object_before_iff signature.objectRank signature.arrowRank _ _).mpr (le_max_left _ _)
  target_before origin := by
    cases origin with
    | inl origin => exact (original_object_before signature declarations _ _).mpr (signature.target_before origin)
    | inr origin =>
        apply (original_object_before signature declarations _ _).mpr
        exact (DeclarationBounds.object_before_iff signature.objectRank signature.arrowRank _ _).mpr (le_max_right _ _)
  equationRank := signature.equationRank
  equationSource origin := originalObject (signature.equationSource origin)
  equationTarget origin := originalObject (signature.equationTarget origin)
  left origin := originalArrow (signature.left origin)
  right origin := originalArrow (signature.right origin)
  equation_before origin := by
    obtain ⟨source, target, first, second⟩ := signature.equation_before origin
    exact ⟨(original_object_before signature declarations _ _).mpr source,
      (original_object_before signature declarations _ _).mpr target,
      (original_arrow_before signature declarations _ _).mpr first,
      (original_arrow_before signature declarations _ _).mpr second⟩

def inclusion : SignatureMap signature (extend signature declarations) where
  base := Functor.id C
  objects := id
  arrows := Sum.inl
  equations := id
  source _ := rfl
  target _ := rfl
  equationSource _ := rfl
  equationTarget _ := rfl
  left _ := rfl
  right _ := rfl

def headers (original : HeaderFormation signature) : HeaderFormation (extend signature declarations) where
  source
    | .inl origin => (inclusion signature declarations).derivation (original.source origin)
    | .inr origin => (inclusion signature declarations).derivation (declarations origin).source.formed.some
  target
    | .inl origin => (inclusion signature declarations).derivation (original.target origin)
    | .inr origin => (inclusion signature declarations).derivation (declarations origin).target.formed.some
  left origin := (inclusion signature declarations).derivation (original.left origin)
  right origin := (inclusion signature declarations).derivation (original.right origin)

def generator (origin : Index) : RawHom ((inclusion signature declarations).object (declarations origin).source)
    ((inclusion signature declarations).object (declarations origin).target) where
  code := .name (Sum.inr origin)
  admitted := ⟨.arrowName (signature := extend signature declarations) (Sum.inr origin)
    ((inclusion signature declarations).derivation (declarations origin).source.formed.some)
    ((inclusion signature declarations).derivation (declarations origin).target.formed.some)⟩

def theory : Mettapedia.GSLT.Core.LambdaTheory.{k, k} :=
  Mettapedia.GSLT.Core.LambdaTheory.ofCategory (Object (extend signature declarations))

def theoryMap : Mettapedia.GSLT.Core.LambdaTheoryMap
    (Mettapedia.GSLT.Core.LambdaTheory.ofCategory (Object signature)) (theory signature declarations) where
  functor := (inclusion signature declarations).functor
  preservesFiniteLimits := SignatureMap.functor_preservesFiniteLimits (inclusion signature declarations)
  preservesExponentials := SignatureMap.functor_closed (inclusion signature declarations)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.ArrowExtension
