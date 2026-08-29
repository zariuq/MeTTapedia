import Mettapedia.Languages.MeTTa.HE.HELanguageDef
import Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef
import Mettapedia.Languages.MeTTa.Pure.Core
import Mettapedia.Languages.MeTTa.MeTTaZero
import Mettapedia.Languages.MeTTa.Prime.LanguageDef
import Mettapedia.OSLF.Framework.ConstructorCategory

/-!
# Rewrite-head census of the serialized MeTTa-family presentations

**Scope of what is proved here.**  Every theorem in this module is a decidable
fact about the *serialized presentations* currently in the tree: which sort
name each presentation's rewrite heads carry, and whether any unary sort
crossing has that name as its domain.  Those are facts about authored
LanguageDef data.  They are **not** theorems about the running MeTTa
engines, and they must not be read as any of the following:

* that MeTTa atoms do not evaluate — real HE, PeTTa, and Prime evaluate
  atoms; the presentations below model evaluation by rewriting explicit
  request/state terms, which is a modelling choice, not a semantic claim;
* that a presentation's `State`/`Process`/`Control` sort is the surface
  semantic carrier — the OSLF wrapper takes the reduction sort as an external
  string and uses `Pattern` at every sort, so a sort *name* is not a witnessed
  carrier;
* that these presentations are adequate to HE, PeTTa, or Prime — adequacy is
  a separate theorem each presentation must earn (see the authority ledger);
* that a glued or mediated synthesis of the dialects cannot identify their
  surface carriers — only that a *flat coproduct of these serializations*
  keeps their reduction-sort names distinct.

Read as a diagnostic, the census says: under the current classifier, only
the reflective presentation `rhoCalc` yields a quoting modality, and the
machine-style serializations yield none, because in each of them nothing has
the reduction sort as a domain.  Whether that reflects the surface semantics
is exactly the question the observed-realization structure is built to
answer.  The PeTTa mainline call guard is an abstract typed operational GSLT,
rather than a serialized `LanguageDef`, so it is intentionally outside this
census.
-/

namespace Mettapedia.Languages.MeTTa.DialectReductionCarrierCensus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory

/-- The constructor category of a rewrite's head symbol, `?` when the
left-hand side is not a constructor application. -/
def headCategory (language : LanguageDef) (rule : RewriteRule) : String :=
  match rule.left with
  | .apply head _ =>
      ((language.terms.find? (·.label = head)).map (·.category)).getD "?"
  | _ => "?"

/-- The distinct reduction sorts of a presentation: the categories of its
rewrite heads. -/
def reductionSorts (language : LanguageDef) : List String :=
  (language.rewrites.map (headCategory language)).eraseDups

/-- Whether some unary crossing has the given sort as its domain, i.e. whether
the derivation would produce a quoting arrow for that reduction sort. -/
def hasQuotingCrossing (language : LanguageDef) (reductionSort : String) : Bool :=
  (unaryCrossings language).any (fun crossing => crossing.2.1 == reductionSort)

/-! ## Reduction sorts, per presentation -/

theorem he_reduces_state :
    reductionSorts Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE = ["State"] := by
  decide +kernel

theorem fullLegacy_reduces_state :
    reductionSorts Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef.mettaFullLegacy =
      ["State"] := by
  decide +kernel

theorem pure_reduces_tm :
    reductionSorts Mettapedia.Languages.MeTTa.Pure.Core.mettaPure = ["Tm"] := by
  decide +kernel

theorem zero_reduces_process :
    reductionSorts Mettapedia.Languages.MeTTa.MeTTaZero.language = ["Process"] := by
  decide +kernel

theorem probe_reduces_process :
    reductionSorts Mettapedia.Languages.MeTTa.Prime.LanguageDef.language = ["Process"] := by
  decide +kernel

/-- Rho's rewrites are on parallel-composition collections, so its reduction
sort is read from its process constructors. -/
theorem rho_process_constructors :
    (rhoCalc.terms.filter (·.category == "Proc")).map (·.label) =
      ["PZero", "PDrop", "PPar", "POutput", "PInput"] := by
  decide

/-! ## Quoting modalities: present only in rho -/

theorem rho_has_quoting_crossing : hasQuotingCrossing rhoCalc "Proc" = true := by
  decide

theorem he_no_quoting_crossing :
    hasQuotingCrossing Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE "State" = false := by
  decide +kernel

theorem fullLegacy_no_quoting_crossing :
    hasQuotingCrossing
      Mettapedia.Languages.MeTTa.OSLFCore.FullLanguageDef.mettaFullLegacy "State" = false := by
  decide +kernel

theorem pure_no_quoting_crossing :
    hasQuotingCrossing Mettapedia.Languages.MeTTa.Pure.Core.mettaPure "Tm" = false := by
  decide +kernel

theorem zero_no_quoting_crossing :
    hasQuotingCrossing Mettapedia.Languages.MeTTa.MeTTaZero.language "Process" = false := by
  decide +kernel

theorem probe_no_quoting_crossing :
    hasQuotingCrossing Mettapedia.Languages.MeTTa.Prime.LanguageDef.language "Process" = false := by
  decide +kernel

/-! ## No shared carrier across the family -/

/-- The reduction sorts of the MeTTa-family presentations, in one list. -/
def familyReductionSorts : List String :=
  reductionSorts Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE ++
    reductionSorts Mettapedia.Languages.MeTTa.Pure.Core.mettaPure ++
    reductionSorts Mettapedia.Languages.MeTTa.MeTTaZero.language

/-- Three serialized presentations, three distinct reduction-sort *names*.  A
flat coproduct of these serializations therefore keeps three reduction sorts;
whether a mediated synthesis identifies their surface carriers is not decided
here. -/
theorem family_reduction_sort_names_distinct :
    familyReductionSorts.eraseDups.length = 3 := by
  decide +kernel

#print axioms he_reduces_state
#print axioms rho_has_quoting_crossing
#print axioms he_no_quoting_crossing
#print axioms family_reduction_sort_names_distinct

end Mettapedia.Languages.MeTTa.DialectReductionCarrierCensus
