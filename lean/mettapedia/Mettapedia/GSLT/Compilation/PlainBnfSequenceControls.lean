import Mettapedia.GSLT.Compilation.DeclaredSequence
import Mettapedia.GSLT.Parsing.PlainBnfInputCarrier

/-!
# A declared scalar sequence in the authored BNF data language

This is the carrier of the source scalar fields, before Unicode or order
admission. It does not make arbitrary constructor applications into lists.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.PlainBnfSequenceControls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.GSLT.Parsing.PlainBnfInputCarrier
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted

def scalarView : DeclaredSequence.View language where
  sort := "BnfScalarList"
  elementSort := "Integer"
  nil := "bnf-v1:scalars-nil"
  cons := "bnf-v1:scalars-cons"
  nilDeclared := by
    refine ⟨⟨"bnf-v1:scalars-nil", "BnfScalarList", [], [], none, none, .bare⟩,
      ?_, rfl, rfl, rfl⟩
    simp [language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]
  consDeclared := by
    refine ⟨⟨"bnf-v1:scalars-cons", "BnfScalarList",
      [.simple "head" (.base "Integer"), .simple "tail" (.base "BnfScalarList")],
      [], none, none, .bare⟩, ?_, "head", "tail", rfl, rfl, rfl⟩
    simp [language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]

theorem put_scalar_sort_iff (items : List Pattern) :
    Checked (scalarView.put items) "BnfScalarList" ↔
      ∀ item ∈ items, Checked item "Integer" := by
  induction items with
  | nil =>
      change Checked (.apply "bnf-v1:scalars-nil" []) "BnfScalarList" ↔
        ∀ item ∈ ([] : List Pattern), Checked item "Integer"
      simp [Checked, checkHasType, checkBuiltinAtomHasType, checkArgumentsHaveTypes,
        LanguageDef.WellSorted.usesBareCollection?,
        language, decodeLanguage?, wireSyntax, rows?, type?, name?, rule?, parameter?]
  | cons item rest ih =>
      change Checked (.apply "bnf-v1:scalars-cons" [item, scalarView.put rest]) "BnfScalarList" ↔
        ∀ value ∈ item :: rest, Checked value "Integer"
      rw [scalar_cons_iff, ih, List.forall_mem_cons]

theorem decoded_scalar_types {value : Pattern} {items : List Pattern}
    (decoded : scalarView.get? value = some items) :
    Checked value "BnfScalarList" ↔ ∀ item ∈ items, Checked item "Integer" := by
  rw [← scalarView.put_get decoded, put_scalar_sort_iff]

theorem scalar_view_rejects_text_tail :
    scalarView.get? (.apply "bnf-v1:scalars-cons"
      [.apply "65" [], .apply "bnf-v1:text-nil" []]) = none := by
  simp [DeclaredSequence.View.get?, scalarView]

#print axioms put_scalar_sort_iff
#print axioms decoded_scalar_types
#print axioms scalar_view_rejects_text_tail

end Mettapedia.GSLT.Compilation.PlainBnfSequenceControls
