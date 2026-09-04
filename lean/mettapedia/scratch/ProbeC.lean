import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryLeafDichotomyProbe

namespace ProbeC

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

#check @rhoQuoteConstructor
#check @rhoCIGSLT

example : rhoCIGSLT.IsDeclaredCostConstructor (.base rhoQuoteConstructor) := True.intro

theorem quoteWrapped_mem :
    rhoQuoteConstructor ∈ rhoCIGSLT.continuationRetyping.wrappedConstructors :=
  (rhoCIGSLT.continuationRetyping.mem_wrappedConstructors_iff
    rhoQuoteConstructor).2 (by
      constructor
      · exact fun equality => absurd (congrArg Subtype.val equality) (by decide)
      · exact fun equality => absurd (congrArg Subtype.val equality) (by decide))

def quoteDeclared : CostStaticColor → rhoCIGSLT.DeclaredCostConstructor
  | .base => ⟨.base rhoQuoteConstructor, True.intro⟩
  | .wrapped => ⟨.wrapped rhoQuoteConstructor, quoteWrapped_mem⟩

theorem quoteDeclared_role (color : CostStaticColor) :
    rhoCIGSLT.declaredCostConstructorRole (quoteDeclared color) =
      .static color := by
  cases color <;> rfl

theorem quoteDeclared_render (color : CostStaticColor) :
    rhoCIGSLT.renderDeclaredCostConstructor (quoteDeclared color) =
      (costStaticReflectivePresentationDecl rhoCIGSLT color
        rhoReflectivePresentation.toReflectivePresentationDecl
        ).quoteConstructor := by
  cases color <;> rfl

end ProbeC
