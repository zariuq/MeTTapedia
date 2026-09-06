import Mettapedia.GSLT.Core.SemanticImplementation
import Mettapedia.GSLT.Core.OperationalRealization
import Mettapedia.GSLT.Logic.HennessyMilnerTransport
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilationCanary
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Passes between language-definition-presented GSLTs

An intermediate representation of a compiler is not a host-language
inductive with an erasure map.  It is a language definition, and its meaning
is the GSLT modulo equations that definition generates under the relation
environment its premises consult.  A compiler pass between two such
representations is a morphism of those GSLTs: a term map that respects the
equations, maps steps, and lifts every step leaving a translated term back to
the source up to the target equations.  Passes compose, the composite pass has
the composite cover, and the category of representations forgets to the
semantic covered operational category.

Consequences that hold for every pass, before any particular representation
is authored: bisimilarity is preserved; with observations carried exactly,
every Hennessy–Milner formula is preserved and reflected, so native types of
the generated OSLF transport exactly along the pass; and a term map with one
escaping target step permits no pass at all.  The lax variant, a forward pass,
keeps only step preservation and is what a stage map that adds behaviour can
still be.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IRPass

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis

universe uAtom uAtom' uIndex vIndex

/-! ## Representations -/

/-- A representation: a validated language definition together with the
relation environment its premises consult.  Nothing else. -/
structure IRLanguage where
  definition : ValidatedLanguageDef
  relations : RelationEnv

namespace IRLanguage

/-- The meaning of a representation is the GSLT modulo equations its
definition generates.  There is no second semantics. -/
def semantics (ir : IRLanguage) : GSLT :=
  langGSLTUsing ir.relations ir.definition.language

/-- A representation whose premises consult no external relation. -/
def ofValidated (definition : ValidatedLanguageDef) : IRLanguage :=
  ⟨definition, RelationEnv.empty⟩

@[simp]
theorem semantics_ofValidated (definition : ValidatedLanguageDef) :
    (ofValidated definition).semantics = langGSLT definition.language :=
  rfl

end IRLanguage

/-! ## Passes -/

/-- An exact pass: an equation-class-covered translation between the semantics
of two representations. -/
abbrev Pass (source target : IRLanguage) :=
  SemanticCoveredTranslation source.semantics target.semantics

/-- A forward pass: step preservation only.  A stage map that adds behaviour
at translated terms is a forward pass and not a pass. -/
abbrev ForwardPass (source target : IRLanguage) :=
  OperationalTranslation source.semantics target.semantics

namespace Pass

variable {source middle target : IRLanguage}

/-- The identity pass. -/
def id (ir : IRLanguage) : Pass ir ir :=
  SemanticCoveredTranslation.id ir.semantics

/-- Passes compose in execution order. -/
def comp (earlier : Pass source middle) (later : Pass middle target) : Pass source target :=
  SemanticCoveredTranslation.comp earlier later

@[simp]
theorem comp_mapTerm (earlier : Pass source middle) (later : Pass middle target) :
    (earlier.comp later).mapTerm = later.mapTerm ∘ earlier.mapTerm :=
  rfl

/-- Every pass is a forward pass. -/
def toForward (pass : Pass source target) : ForwardPass source target :=
  pass.toOperational

/-- Every pass is a path-valued realization with singleton target paths. -/
def toRealization (pass : Pass source target) :
    OperationalRealization source.semantics target.semantics :=
  OperationalRealization.ofTranslation pass.toOperational

@[simp]
theorem toRealization_mapTerm (pass : Pass source target) :
    pass.toRealization.mapTerm = pass.mapTerm :=
  rfl

/-- Passes preserve bisimilarity. -/
theorem preservesBisimilar (pass : Pass source target) {left right : source.semantics.Term}
    (bisimilar : source.semantics.Bisimilar left right) :
    target.semantics.Bisimilar (pass.mapTerm left) (pass.mapTerm right) :=
  SemanticCoveredTranslation.preservesBisimilar pass bisimilar

/-! ### Observations carried along a pass -/

/-- A pass whose atomic observations are carried exactly is a cover of the
observed step systems. -/
def systemCover (pass : Pass source target)
    (sourceObserved : ObservedGSLT.{uAtom} source.semantics)
    (targetObserved : ObservedGSLT.{uAtom'} target.semantics)
    (sourceResp : ∀ (atom : sourceObserved.Atom) {left right : source.semantics.Term},
      source.semantics.Equiv left right →
        (sourceObserved.observes atom left ↔ sourceObserved.observes atom right))
    (targetResp : ∀ (atom : targetObserved.Atom) {left right : target.semantics.Term},
      target.semantics.Equiv left right →
        (targetObserved.observes atom left ↔ targetObserved.observes atom right))
    (mapAtom : sourceObserved.Atom → targetObserved.Atom)
    (observes_iff : ∀ atom term, sourceObserved.observes atom term ↔
      targetObserved.observes (mapAtom atom) (pass.mapTerm term)) :
    SystemCover (System.ofObserved sourceObserved sourceResp)
      (System.ofObserved targetObserved targetResp) :=
  SemanticCoveredTranslation.systemCover pass sourceObserved targetObserved
    sourceResp targetResp mapAtom observes_iff

/-- Every Hennessy–Milner formula is preserved and reflected along a pass
with exactly carried observations. -/
theorem sat_map (pass : Pass source target)
    (sourceObserved : ObservedGSLT.{uAtom} source.semantics)
    (targetObserved : ObservedGSLT.{uAtom'} target.semantics)
    (sourceResp : ∀ (atom : sourceObserved.Atom) {left right : source.semantics.Term},
      source.semantics.Equiv left right →
        (sourceObserved.observes atom left ↔ sourceObserved.observes atom right))
    (targetResp : ∀ (atom : targetObserved.Atom) {left right : target.semantics.Term},
      target.semantics.Equiv left right →
        (targetObserved.observes atom left ↔ targetObserved.observes atom right))
    (mapAtom : sourceObserved.Atom → targetObserved.Atom)
    (observes_iff : ∀ atom term, sourceObserved.observes atom term ↔
      targetObserved.observes (mapAtom atom) (pass.mapTerm term))
    (formula : Formula sourceObserved.Atom Unit) (term : source.semantics.Term) :
    (System.ofObserved targetObserved targetResp).sat (formula.map mapAtom _root_.id)
        (pass.mapTerm term) ↔
      (System.ofObserved sourceObserved sourceResp).sat formula term :=
  (pass.systemCover sourceObserved targetObserved sourceResp targetResp mapAtom observes_iff).sat_map
    formula term

/-- With every target observation reached, observed bisimilarity is exact
along a pass. -/
theorem bisimilar_map_iff (pass : Pass source target)
    (sourceObserved : ObservedGSLT.{uAtom} source.semantics)
    (targetObserved : ObservedGSLT.{uAtom'} target.semantics)
    (sourceResp : ∀ (atom : sourceObserved.Atom) {left right : source.semantics.Term},
      source.semantics.Equiv left right →
        (sourceObserved.observes atom left ↔ sourceObserved.observes atom right))
    (targetResp : ∀ (atom : targetObserved.Atom) {left right : target.semantics.Term},
      target.semantics.Equiv left right →
        (targetObserved.observes atom left ↔ targetObserved.observes atom right))
    (mapAtom : sourceObserved.Atom → targetObserved.Atom)
    (observes_iff : ∀ atom term, sourceObserved.observes atom term ↔
      targetObserved.observes (mapAtom atom) (pass.mapTerm term))
    (atomSurjective : Function.Surjective mapAtom) (left right : source.semantics.Term) :
    (System.ofObserved targetObserved targetResp).Bisimilar (pass.mapTerm left)
        (pass.mapTerm right) ↔
      (System.ofObserved sourceObserved sourceResp).Bisimilar left right :=
  (pass.systemCover sourceObserved targetObserved sourceResp targetResp mapAtom
    observes_iff).bisimilar_map_iff atomSurjective (fun label => ⟨label, rfl⟩) left right

end Pass

/-! ## The category of representations -/

instance : CategoryTheory.Category IRLanguage where
  Hom := Pass
  id := Pass.id
  comp := Pass.comp
  id_comp _ := by
    apply SemanticCoveredTranslation.ext
    rfl
  comp_id _ := by
    apply SemanticCoveredTranslation.ext
    rfl
  assoc _ _ _ := by
    apply SemanticCoveredTranslation.ext
    rfl

/-- Representations first forget to the category whose arrows cover target
steps up to target equations.  No representative equality is assumed here. -/
def toSemanticCoveredTheory :
    CategoryTheory.Functor IRLanguage SemanticCoveredTheory where
  obj ir := ⟨ir.semantics⟩
  map pass := pass
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Quotienting each represented language by its equations turns an IR pass
into a literal covered translation.  This is the canonical interface to the
existing indexed GSLT machinery. -/
def toCoveredTheory : CategoryTheory.Functor IRLanguage CoveredTheory :=
  CategoryTheory.Functor.comp toSemanticCoveredTheory quotientCoverage

/-- A categorical pipeline of language representations induces an existing
`CoveredDiagram` after quotient completion.  Host compiler data may realize
the arrows, but it is not another public semantic node. -/
def quotientCoveredDiagram
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (pipeline : CategoryTheory.Functor Index IRLanguage) :
    CoveredDiagram Index :=
  CategoryTheory.Functor.comp pipeline toCoveredTheory

/-! ## The obstruction -/

/-- A term map under which one target step leaves the image of the source
is not the term map of any pass. -/
theorem no_pass_of_escape {source target : IRLanguage} (translation : ForwardPass source target)
    (escape : EquationClassEscapingStep source.semantics target.semantics translation.mapTerm) :
    ¬ ∃ pass : Pass source target, pass.mapTerm = translation.mapTerm := by
  exact escape.not_semanticCoveredTranslation

/-! ## Canaries on an authored representation -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.MeTTaILPatternMatrixCompilationCanary

/-- The two-row rewrite language of the matrix canary, as a representation. -/
def rows : IRLanguage := IRLanguage.ofValidated validatedLanguage

/-- Its reordered presentation. -/
def reorderedRows : IRLanguage := IRLanguage.ofValidated validatedReorderedLanguage

/-- The identity pass exists on every representation. -/
example : Pass rows rows := Pass.id rows

/-- Identity passes are identities of the category. -/
example : (CategoryTheory.CategoryStruct.id rows : Pass rows rows).mapTerm = _root_.id := rfl

/-- Composition in the category is composition of passes. -/
example :
    (CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.id rows)
      (CategoryTheory.CategoryStruct.id rows) : Pass rows rows).mapTerm = _root_.id :=
  rfl

end Canary

#print axioms Pass.preservesBisimilar
#print axioms Pass.sat_map
#print axioms Pass.bisimilar_map_iff
#print axioms no_pass_of_escape
#print axioms toCoveredTheory
#print axioms quotientCoveredDiagram

end Mettapedia.GSLT.LanguageDef.IRPass
