import Mettapedia.Languages.ProcessCalculi.CCS.Surface
import Mettapedia.GSLT.LanguageDef.BagNormalFormSection

/-!
# The canonical section of CCS

CCS authors no equation, and its one collection-carrying constructor is
parallel composition, a bag over processes with the flattening algebra and
unit `CNil`.  It is therefore a bag theory, and the normal form for one bag is
a computable section of its static equivalence: nested compositions are
spliced, inactions dropped, components sorted, and an empty or singleton
composition is replaced by inaction or by its component.

The section is computed on the handshake.  Its two orders, and the same two
processes with a nested composition and an inaction added, all have the
action-first handshake as normal form.  The two components of the handshake,
which are not equivalent, have different normal forms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode

/-- CCS is a bag theory: no authored equation, and parallel composition is its
only collection, with the flattening algebra and unit `CNil`. -/
theorem ccs_bagTheory : BagTheory ccsCalc ccsParallelConstructor.1 (some "CNil") :=
  bagTheory_of_check (by decide +kernel)

/-- **The canonical section of CCS.** -/
def ccsCanonicalSection : ComputableCanonicalSection ccsIGSLT :=
  bagCanonicalSection ccsIGSLT ccs_bagTheory

/-- The section computes the bag normal form of the underlying pattern. -/
theorem ccsCanonicalSection_normalize_val (term : ccsIGSLT.toGSLT.Term) :
    (ccsCanonicalSection.normalize term).1 = normalForm (some "CNil") term.1 :=
  rfl

/-! ## The handshake -/

/-- The two components of the handshake are in code order, action first. -/
theorem handshake_components_sorted :
    sortPatterns
        [Pattern.apply "CAct" [.apply "NBase" [], .apply "CNil" []],
          .apply "CCoAct"
            [.apply "NBase" [], .apply "CAct" [.apply "NBase" [], .apply "CNil" []]]] =
      [.apply "CAct" [.apply "NBase" [], .apply "CNil" []],
        .apply "CCoAct"
          [.apply "NBase" [], .apply "CAct" [.apply "NBase" [], .apply "CNil" []]]] :=
  sortPatterns_of_sorted (by decide +kernel)

/-- The handshake is its own normal form. -/
theorem handshake_normalForm : normalForm (some "CNil") handshake = handshake := by
  simp [handshake, nameA, nil, normalForm, normalizeBag, bagContents, splice, collapse,
    handshake_components_sorted]

/-- The exchanged handshake has the handshake as normal form. -/
theorem handshakeSwapped_normalForm :
    normalForm (some "CNil") handshakeSwapped = handshake := by
  have exchanged :
      sortPatterns
          [Pattern.apply "CCoAct"
              [.apply "NBase" [], .apply "CAct" [.apply "NBase" [], .apply "CNil" []]],
            .apply "CAct" [.apply "NBase" [], .apply "CNil" []]] =
        [.apply "CAct" [.apply "NBase" [], .apply "CNil" []],
          .apply "CCoAct"
            [.apply "NBase" [], .apply "CAct" [.apply "NBase" [], .apply "CNil" []]]] :=
    (sortPatterns_eq_of_perm (List.Perm.swap _ _ _)).trans handshake_components_sorted
  simp [handshakeSwapped, handshake, nameA, nil, normalForm, normalizeBag, bagContents,
    splice, collapse, exchanged]

/-- **The two orders of the handshake have one representative.** -/
theorem handshake_orders_normalize_alike :
    ccsCanonicalSection.normalize handshakeTerm =
      ccsCanonicalSection.normalize handshakeSwappedTerm :=
  ccsCanonicalSection.complete handshake_swaps

/-- That representative is the action-first handshake. -/
theorem handshake_representative :
    (ccsCanonicalSection.normalize handshakeTerm).1 = handshake ∧
      (ccsCanonicalSection.normalize handshakeSwappedTerm).1 = handshake :=
  ⟨handshake_normalForm, handshakeSwapped_normalForm⟩

/-- The handshake with its action nested in a composition beside an
inaction: `{ {a.0 | 0} | ~a.(a.0) }`. -/
def handshakeNested : Pattern :=
  .collection .hashBag [
    .collection .hashBag [.apply "CAct" [nameA, nil], nil] none,
    .apply "CCoAct" [nameA, .apply "CAct" [nameA, nil]]] none

/-- The nested handshake as a closed process. -/
def handshakeNestedTerm : ccsInteractivePresentation.Term :=
  ClosedTerm.ofCheck handshakeNested (by decide +kernel)

/-- Splicing the nested composition and dropping the inaction leaves the
handshake. -/
theorem handshakeNested_normalForm :
    normalForm (some "CNil") handshakeNested = handshake := by
  simp [handshakeNested, handshake, nameA, nil, normalForm, normalizeBag, bagContents,
    splice, collapse, handshake_components_sorted]

/-- The nested handshake is equivalent to the handshake: the section decides
the static equivalence. -/
theorem handshakeNested_equivalent :
    ccsIGSLT.toGSLT.equations.r handshakeNestedTerm handshakeTerm := by
  apply (ccsCanonicalSection.equivalent_iff_normalize_eq _ _).mpr
  apply Subtype.ext
  show normalForm (some "CNil") handshakeNested = normalForm (some "CNil") handshake
  exact handshakeNested_normalForm.trans handshake_normalForm.symm

/-! ## Inequivalent processes are told apart -/

/-- `a.0` as a closed process. -/
def actionTerm : ccsInteractivePresentation.Term :=
  ClosedTerm.ofCheck (.apply "CAct" [nameA, nil]) (by decide +kernel)

/-- `~a.(a.0)` as a closed process. -/
def coActionTerm : ccsInteractivePresentation.Term :=
  ClosedTerm.ofCheck (.apply "CCoAct" [nameA, .apply "CAct" [nameA, nil]])
    (by decide +kernel)

/-- **The two components of the handshake have different representatives.**
They are not equivalent, and a section sends inequivalent terms to different
normal forms. -/
theorem components_normalize_apart :
    ccsCanonicalSection.normalize actionTerm ≠ ccsCanonicalSection.normalize coActionTerm := by
  intro same
  have equivalent : ccsIGSLT.toGSLT.equations.r actionTerm coActionTerm :=
    (ccsCanonicalSection.equivalent_iff_normalize_eq _ _).mpr same
  exact handshake_components_differ (equationEquiv_of_presentedEquationSetoid equivalent)

end Mettapedia.Languages.ProcessCalculi.CCS
