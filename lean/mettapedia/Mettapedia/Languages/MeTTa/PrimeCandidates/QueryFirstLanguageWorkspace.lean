import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT
import Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef

/-!
# Query-first candidate as a first-class language workspace

This instance associates the query-first validated presentation with one
admitted authored route.  It preserves the presentation under quotation and
retains the route's compilation license.  As with `LanguageWorkspace` itself,
the association is data: these results do not assert semantic adequacy between
the query-first dynamics and the route program.
-/


open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.QueryFirstLanguageWorkspace

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FirstClassGSLT

/-- The query-first presentation accompanied by the admitted singleton route. -/
def queryFirstWorkspace : LanguageWorkspace where
  presentation := LanguageDef.queryFirstCandidatePresentation
  routes := [unitRouteValue]

theorem queryFirstWorkspace_roundtrip :
    (queryFirstWorkspace.quoted 0).quotedLanguage? =
      some LanguageDef.queryFirstCandidatePresentation :=
  rfl

theorem queryFirstWorkspace_has_admitted_route :
    ∃ route ∈ queryFirstWorkspace.routes, Nonempty route.License :=
  ⟨unitRouteValue, by simp [queryFirstWorkspace], ⟨unitRouteLicense⟩⟩

#print axioms queryFirstWorkspace_roundtrip
#print axioms queryFirstWorkspace_has_admitted_route

end Mettapedia.Languages.MeTTa.PrimeCandidates.QueryFirstLanguageWorkspace
