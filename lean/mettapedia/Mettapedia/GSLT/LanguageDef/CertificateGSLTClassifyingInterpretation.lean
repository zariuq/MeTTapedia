import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory
import Mettapedia.GSLT.LanguageDef.CertificateGSLTInterpretation

/-!
# Interpretations act on ordered certificate contexts

A derivation-valued interpretation of checked calculus languages translates
each primitive rule application to a possibly composite open derivation. Its
already-proved substitution law makes that translation functorial on the
classifying context categories. It also preserves ordered proof-vector
pairing exactly. No preservation of implication or a full internal logic is
inferred from this finite-product fragment.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory

/-- Interpret every ordered open-derivation vector while leaving its ordered
judgment context unchanged. -/
def Interpretation.contextFunctor {source target : Object}
    (interpretation : Interpretation source target) :
    ClassifyingContext source.definition ⥤
      ClassifyingContext target.definition where
  obj context := ⟨context.judgments⟩
  map morphism := interpretation.mapOpenList morphism
  map_id context :=
    interpretation.mapOpenList_assumptionEnvironment context.judgments
  map_comp earlier later :=
    interpretation.mapOpenList_bind later earlier

/-- Interpretation distributes over concatenation of proof vectors, without
identifying distinct occurrences or dropping either side. -/
theorem Interpretation.mapOpenList_append {source target : Object}
    (interpretation : Interpretation source target)
    {context firstGoals secondGoals : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (left : OpenDerivationList source.definition context firstGoals)
    (right : OpenDerivationList source.definition context secondGoals) :
    interpretation.mapOpenList (left.append right) =
      (interpretation.mapOpenList left).append
        (interpretation.mapOpenList right) := by
  cases left with
  | nil => rfl
  | cons head tail =>
      exact congrArg (OpenDerivationList.cons (interpretation.mapOpen head))
        (Interpretation.mapOpenList_append interpretation tail right)

theorem Interpretation.mapOpen_castGoal {source target : Object}
    (interpretation : Interpretation source target)
    {context : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {firstGoal secondGoal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (equal : firstGoal = secondGoal)
    (derivation : OpenDerivation source.definition context firstGoal) :
    interpretation.mapOpen (equal ▸ derivation) =
      equal ▸ interpretation.mapOpen derivation := by
  cases equal
  rfl

/-- Translating an assumption projection leaves the chosen ordered premise
occurrence unchanged. -/
theorem Interpretation.mapOpenList_leftProjection {source target : Object}
    (interpretation : Interpretation source target)
    (first second : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    interpretation.mapOpenList
        (OpenDerivationList.leftProjection first second) =
      (OpenDerivationList.leftProjection first second :
        OpenDerivationList target.definition (first ++ second) first) := by
  unfold OpenDerivationList.leftProjection
  rw [interpretation.mapOpenList_ofFn]
  congr 1
  funext index
  rw [interpretation.mapOpen_castGoal]
  rfl

theorem Interpretation.mapOpenList_rightProjection {source target : Object}
    (interpretation : Interpretation source target)
    (first second : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    interpretation.mapOpenList
        (OpenDerivationList.rightProjection first second) =
      (OpenDerivationList.rightProjection first second :
        OpenDerivationList target.definition (first ++ second) second) := by
  unfold OpenDerivationList.rightProjection
  rw [interpretation.mapOpenList_ofFn]
  congr 1
  funext index
  rw [interpretation.mapOpen_castGoal]
  rfl

/-- The functor preserves pairing of ordered proof environments exactly.
This is a positive theory-translation law for the finite-product fragment. -/
theorem Interpretation.contextFunctor_pair {source target : Object}
    (interpretation : Interpretation source target)
    {context first second : ClassifyingContext source.definition}
    (left : context ⟶ first) (right : context ⟶ second) :
    interpretation.contextFunctor.map
        (ClassifyingContext.pair left right) =
      ClassifyingContext.pair
        (interpretation.contextFunctor.map left)
        (interpretation.contextFunctor.map right) :=
  interpretation.mapOpenList_append left right

theorem Interpretation.contextFunctor_fstProjection {source target : Object}
    (interpretation : Interpretation source target)
    (first second : ClassifyingContext source.definition) :
    interpretation.contextFunctor.map
        (ClassifyingContext.fstProjection first second) =
      ClassifyingContext.fstProjection
        (interpretation.contextFunctor.obj first)
        (interpretation.contextFunctor.obj second) :=
  interpretation.mapOpenList_leftProjection first.judgments second.judgments

theorem Interpretation.contextFunctor_sndProjection {source target : Object}
    (interpretation : Interpretation source target)
    (first second : ClassifyingContext source.definition) :
    interpretation.contextFunctor.map
        (ClassifyingContext.sndProjection first second) =
      ClassifyingContext.sndProjection
        (interpretation.contextFunctor.obj first)
        (interpretation.contextFunctor.obj second) :=
  interpretation.mapOpenList_rightProjection first.judgments second.judgments

/-- The actual named terminal object is preserved on objects. -/
theorem Interpretation.contextFunctor_empty {source target : Object}
    (interpretation : Interpretation source target) :
    interpretation.contextFunctor.obj
        (ClassifyingContext.emptyContext source.definition) =
      ClassifyingContext.emptyContext target.definition := rfl

/-- Derivation-valued theory translation sends the named finite-product
projections to a limiting binary fan. It needs no preservation of implication. -/
def Interpretation.contextFunctor_concatIsLimit {source target : Object}
    (interpretation : Interpretation source target)
    (first second : ClassifyingContext source.definition) :
    CategoryTheory.Limits.IsLimit
      (CategoryTheory.Limits.BinaryFan.mk
        (interpretation.contextFunctor.map
          (ClassifyingContext.fstProjection first second))
        (interpretation.contextFunctor.map
          (ClassifyingContext.sndProjection first second))) := by
  rw [interpretation.contextFunctor_fstProjection,
    interpretation.contextFunctor_sndProjection]
  exact ClassifyingContext.concatIsLimit
    (interpretation.contextFunctor.obj first)
    (interpretation.contextFunctor.obj second)

/-- Identity rule interpretation acts identically on every proof-vector
morphism of the context category. -/
theorem Interpretation.id_contextFunctor_map (object : Object)
    {first second : ClassifyingContext object.definition}
    (morphism : first ⟶ second) :
    (Interpretation.id object).contextFunctor.map morphism = morphism :=
  Interpretation.id_mapOpenList morphism

/-- Composed rule interpretations act on context arrows by composed
functorial maps. This is the theory-change coherence actually used below. -/
theorem Interpretation.comp_contextFunctor_map {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last)
    {source target : ClassifyingContext first.definition}
    (morphism : source ⟶ target) :
    (Interpretation.comp earlier later).contextFunctor.map morphism =
      later.contextFunctor.map (earlier.contextFunctor.map morphism) :=
  Interpretation.comp_mapOpenList earlier later morphism

#print axioms Interpretation.contextFunctor
#print axioms Interpretation.contextFunctor_pair
#print axioms Interpretation.contextFunctor_fstProjection
#print axioms Interpretation.contextFunctor_sndProjection
#print axioms Interpretation.contextFunctor_concatIsLimit
#print axioms Interpretation.comp_contextFunctor_map

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
