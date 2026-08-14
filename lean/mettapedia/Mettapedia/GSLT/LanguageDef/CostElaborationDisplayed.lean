import Mettapedia.GSLT.LanguageDef.CostElaborationDecorationReindex
import Mettapedia.GSLT.LanguageDef.CostSemanticErasure

/-!
# The displayed total category of proof-relevant Cost elaborations

An object is a continued authority together with one fully checked
elaborated term in its indexed fibre.  An arrow is a continued morphism whose
structural action carries the complete computational decoration of the
source term to that of the target term.

This is deliberately only a displayed-category-style total construction.
No Cost₁ normalizer laws and no cartesian or cocartesian lifting property are
asserted here.  Lawful Cost₁ objects form a later restriction of this base;
requiring those laws here would make the structural total category depend on
the still-separate normalization theorem.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- The total space of checked Cost elaborations over continued authorities.
The dependent fibre retains the term, its typing indices, and
the complete checked region tree. -/
structure CostElaborationTotal where
  base : CIGSLT
  fiber : CostElaborationFiber base

namespace CostElaborationTotal

/-- The proof-erased but computationally complete decoration of a total
object. -/
def decoration (object : CostElaborationTotal) :
    CostTreeDecoration object.base :=
  object.fiber.2.decoration

/-- Every checked compact term gives an actual object of the total category
through the independently defined proof-relevant region-tree compiler. -/
def ofOpenTerm (source : CIGSLT)
    {targetFree : WellSorted.FreeTypeContext}
    {targetBound : List TypeExpr}
    {targetSort : LangSort source.costWholeLanguage}
    (term : ReflectiveWellSorted.OpenTerm
      source.costWholeReflectionProfile source.costWholeLanguage
      targetFree targetBound targetSort) : CostElaborationTotal where
  base := source
  fiber :=
    ⟨⟨targetFree, targetBound, targetSort⟩,
      CostOpenElaboration.compileTerm source term⟩

/-- The total region-tree object embeds into the retained semantic Cost
carrier whenever the source supplies the local unary normalization laws.
This is the bridge from executable decomposition evidence to normalization
in place; it does not erase and recompile the semantic tree. -/
def toSemantic (object : CostElaborationTotal)
    (laws : CostTypedUnaryNormalizationLaws object.base) :
    CostSemanticElabTerm object.base
      object.fiber.1.targetFree object.fiber.1.targetBound
        object.fiber.1.targetSort :=
  ⟨object.fiber.2.1,
    object.fiber.2.2.tree.toSemantic laws.canonicalPathSafe⟩

/-- The semantic image of an executable Cost elaboration reaches its exact
normal form through one retained semantic edge. -/
theorem toSemantic_normalizes (object : CostElaborationTotal)
    (laws : CostTypedUnaryNormalizationLaws object.base) :
    (CostSemanticOpenElaboration.equationSetoid object.base
      object.fiber.1.targetFree object.fiber.1.targetBound
        object.fiber.1.targetSort).r
      (CostSemanticOpenElaboration.normalizeTerm (object.toSemantic laws))
      (object.toSemantic laws) :=
  CostSemanticOpenElaboration.normalizeTerm_related (object.toSemantic laws)

/-- Normalization in the semantic image is the exact canonical section
already proved for stable Cost frames. -/
theorem toSemantic_normalize_eq_iff (object : CostElaborationTotal)
    (laws : CostTypedUnaryNormalizationLaws object.base)
    (other : CostSemanticElabTerm object.base
      object.fiber.1.targetFree object.fiber.1.targetBound
        object.fiber.1.targetSort) :
    (CostSemanticOpenElaboration.equationSetoid object.base
      object.fiber.1.targetFree object.fiber.1.targetBound
        object.fiber.1.targetSort).r (object.toSemantic laws) other ↔
      CostSemanticOpenElaboration.normalizeTerm (object.toSemantic laws) =
        CostSemanticOpenElaboration.normalizeTerm other :=
  CostSemanticOpenElaboration.equivalent_iff_normalizeTerm_eq object.base
    (object.toSemantic laws) other

/-- A displayed arrow consists of a conservative base arrow and the exact
statement that it transports the retained computational decoration. -/
structure Morphism (source target : CostElaborationTotal) where
  base : source.base ⟶ target.base
  decoration_natural :
    source.decoration.map base = target.decoration

namespace Morphism

/-- Displayed arrows are determined by their base arrow; decoration
naturality is a proposition. -/
@[ext]
theorem ext {source target : CostElaborationTotal}
    {first second : Morphism source target}
    (base : first.base = second.base) : first = second := by
  cases first
  cases second
  cases base
  rfl

/-- Every total object has the displayed identity over its base identity. -/
def id (source : CostElaborationTotal) : Morphism source source where
  base := CIGSLT.Morphism.id source.base
  decoration_natural := CostTreeDecoration.map_id _ _

/-- Displayed composition is inherited from strict decoration transport. -/
def comp {first second third : CostElaborationTotal}
    (left : Morphism first second) (right : Morphism second third) :
    Morphism first third where
  base := CIGSLT.Morphism.comp left.base right.base
  decoration_natural := by
    calc
      first.decoration.map
          (CIGSLT.Morphism.comp left.base right.base) =
          (first.decoration.map left.base).map right.base :=
        CostTreeDecoration.map_comp left.base right.base first.decoration
      _ = second.decoration.map right.base :=
        congrArg (CostTreeDecoration.map right.base)
          left.decoration_natural
      _ = third.decoration := right.decoration_natural

end Morphism

/-- The total category associated to the decoration-preserving displayed
family. -/
instance : CategoryTheory.Category CostElaborationTotal where
  Hom := Morphism
  id := Morphism.id
  comp := Morphism.comp
  id_comp morphism := by
    apply Morphism.ext
    exact CategoryTheory.Category.id_comp morphism.base
  comp_id morphism := by
    apply Morphism.ext
    exact CategoryTheory.Category.comp_id morphism.base
  assoc first second third := by
    apply Morphism.ext
    exact CategoryTheory.Category.assoc first.base second.base third.base

/-- Forget the checked elaboration and its decoration, retaining the selected
continued authority and its arrow. -/
def projection :
    CategoryTheory.Functor CostElaborationTotal CIGSLT where
  obj object := object.base
  map morphism := morphism.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A positive displayed-arrow witness over identity: equal computational
decorations admit a lift even when the retained proof terms differ. -/
def identityLiftOfDecorationEq
    {base : CIGSLT}
    (sourceFiber targetFiber :
      CostElaborationFiber base)
    (equalDecoration : sourceFiber.2.decoration =
      targetFiber.2.decoration) :
    Morphism
      ⟨base, sourceFiber⟩
      ⟨base, targetFiber⟩ where
  base := CIGSLT.Morphism.id base
  decoration_natural := by
    change sourceFiber.2.decoration.map
        (CIGSLT.Morphism.id base) =
      targetFiber.2.decoration
    exact (CostTreeDecoration.map_id _ _).trans equalDecoration

/-- Negative canary: identity cannot transport one computational decoration
to a distinct decoration.  Thus the total category does not collapse all
elaborations over the same compact authority. -/
theorem noIdentityLiftOfDecorationNe
    {base : CIGSLT}
    (sourceFiber targetFiber :
      CostElaborationFiber base)
    (differentDecoration : sourceFiber.2.decoration ≠
      targetFiber.2.decoration) :
    ¬ ∃ morphism : Morphism
        ⟨base, sourceFiber⟩
        ⟨base, targetFiber⟩,
      morphism.base = CIGSLT.Morphism.id base := by
  rintro ⟨morphism, baseIdentity⟩
  have natural := morphism.decoration_natural
  rw [baseIdentity] at natural
  change sourceFiber.2.decoration.map
      (CIGSLT.Morphism.id base) =
    targetFiber.2.decoration at natural
  rw [CostTreeDecoration.map_id] at natural
  exact differentDecoration natural

end CostElaborationTotal

end Mettapedia.GSLT.LanguageDef
