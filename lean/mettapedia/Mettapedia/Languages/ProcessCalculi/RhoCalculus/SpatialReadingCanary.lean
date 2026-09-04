import Mettapedia.OSLF.StructuralModal.EquationInvariance
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness

/-!
# Rho canaries for the spatial reading

The raw spatial former of the structural-modal language reads the outermost
constructor of the representative it is given.  Rho supplies two closed
processes that the equations identify and that the raw reading separates: the
singleton parallel wrapper and the quote/drop respelling of a name.  The same
observations read modulo the equations are invariant, as is the behavioural
observation "can step".
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.SpatialReadingCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.StructuralModal
open Mettapedia.OSLF.StructuralModal.EquationInvariance
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness

/-! ## Rho canaries: the spatial former is not invariant -/


/-- The drop of the quoted nil. -/
def dropOfNil : Pattern := .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]

/-- The same process inside a singleton parallel wrapper. -/
def wrappedDropOfNil : Pattern := .collection .hashBag [dropOfNil] none

/-- The same process with its name written as the quote of a drop. -/
def dropOfQuotedDrop : Pattern := .apply "PDrop" [.apply "NQuote" [dropOfNil]]

theorem dropOfNil_hasSort :
    HasSort rhoCalc FreeTypeContext.empty [] dropOfNil "Proc" :=
  rho_drop_hasSort (rho_quote_hasSort (rho_zero_hasSort _ _))

/-- The singleton wrapper is a derived equation. -/
theorem wrapped_equiv : (langGSLT rhoCalc).Equiv wrappedDropOfNil dropOfNil := by
  show CoreEquiv defaultBasePremises wrappedDropOfNil dropOfNil
  exact coreEquiv_singleton (free := FreeTypeContext.empty) (bound := [])
    (.cons dropOfNil_hasSort (.nil [] TypeExpr.proc))

/-- Rewriting the name by the authored quote/drop law is an equation. -/
theorem quoteShape_equiv : (langGSLT rhoCalc).Equiv dropOfQuotedDrop dropOfNil := by
  show CoreEquiv defaultBasePremises dropOfQuotedDrop dropOfNil
  have inner : CoreEquiv defaultBasePremises
      (.apply "NQuote" [.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]])
      (.apply "NQuote" [.apply "PZero" []]) :=
    coreEquiv_quoteDrop _
  have filled := equationEquiv_fill (.apply "PDrop" [] .hole []) inner
  simp only [OneHoleContext.fill, List.nil_append] at filled
  exact filled

/-- The spatial observation "headed by a drop" separates the singleton
wrapper from its content, so it is not a predicate of the OSLF frame. -/
theorem headed_drop_not_equationInvariant :
    ¬ EquationInvariant (langGSLT rhoCalc)
      (satisfiesOver (langSpan rhoCalc) (.headed "PDrop" [.top])) := by
  intro invariant
  have holds : satisfiesOver (langSpan rhoCalc) (.headed "PDrop" [.top]) dropOfNil :=
    ⟨[.apply "NQuote" [.apply "PZero" []]], rfl, ⟨trivial, trivial⟩⟩
  obtain ⟨children, shape, _⟩ := (invariant wrapped_equiv).mpr holds
  exact Pattern.noConfusion shape

/-- The quote-shape observation separates two spellings of one process. -/
theorem headed_quoteShape_not_equationInvariant :
    ¬ EquationInvariant (langGSLT rhoCalc)
      (satisfiesOver (langSpan rhoCalc)
        (.headed "PDrop" [.headed "NQuote" [.headed "PDrop" [.top]]])) := by
  intro invariant
  have holds : satisfiesOver (langSpan rhoCalc)
      (.headed "PDrop" [.headed "NQuote" [.headed "PDrop" [.top]]]) dropOfQuotedDrop :=
    ⟨[.apply "NQuote" [dropOfNil]], rfl,
      ⟨⟨[dropOfNil], rfl,
        ⟨⟨[.apply "NQuote" [.apply "PZero" []]], rfl, ⟨trivial, trivial⟩⟩, trivial⟩⟩,
        trivial⟩⟩
  obtain ⟨children, shape, inner⟩ := (invariant quoteShape_equiv).mp holds
  simp only [dropOfNil, Pattern.apply.injEq, true_and] at shape
  subst shape
  obtain ⟨⟨grandchildren, nameShape, deeper⟩, _⟩ := inner
  simp only [Pattern.apply.injEq, true_and] at nameShape
  subst nameShape
  obtain ⟨⟨_, zeroShape, _⟩, _⟩ := deeper
  simp at zeroShape

/-- Positive control: the behavioural observation "can step" is invariant. -/
theorem diamond_top_equationInvariant :
    EquationInvariant (langGSLT rhoCalc) (satisfies rhoCalc (.diamond .top)) :=
  satisfies_equationInvariant rhoCalc (.diamond .top)

/-- Positive control: the same quote-shape observation read modulo the
equations is invariant. -/
theorem quoteShape_modulo_equationInvariant :
    EquationInvariant (langGSLT rhoCalc)
      (satisfiesModulo rhoCalc
        (.headed "PDrop" [.headed "NQuote" [.headed "PDrop" [.top]]])) :=
  satisfiesModulo_equationInvariant rhoCalc _



end Mettapedia.Languages.ProcessCalculi.RhoCalculus.SpatialReadingCanary
