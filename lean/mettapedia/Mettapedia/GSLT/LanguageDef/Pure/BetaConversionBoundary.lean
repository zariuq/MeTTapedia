/-
# Localization of beta conversion in the Pure atomic elaborator

These certificates expose where the beta-aware root may ask a conversion
question.  Selecting a Pi-typed head starts its dependent spine without a
conversion query.  Conversion is consulted only when an empty spine or a
newly completed argument spine is matched against its local expected type.
-/

import Mettapedia.GSLT.LanguageDef.Pure.BetaAtomicRefinement

namespace Mettapedia.GSLT.LanguageDef.PureBetaConversionBoundary

open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureRefinement
open Mettapedia.GSLT.LanguageDef.PureAtomicRefinement
open Mettapedia.GSLT.LanguageDef.PureBeta
open Mettapedia.GSLT.LanguageDef.PureBetaAtomicRefinement

/--
A certificate for deterministic frame delivery.  Its only conversion premises
occur in the three `spine*` constructors, after the argument has been inserted
and its dependent result type computed.
-/
inductive DeliverLocalized : Nf → List Frame → CheckResult Core → Prop where
  | done {term} : DeliverLocalized term [] (.ok (.done term))
  | lambda {term domain rest result} :
      DeliverLocalized (.lam domain term) rest result →
      DeliverLocalized term (.lambda domain :: rest) result
  | spineConvertible {term context head arguments body expected rest result} :
      conversionVerdict normalizationFuel
          (Expr.subst0 term.erase body) expected = .convertible →
      DeliverLocalized (.head head (arguments ++ [term])) rest result →
      DeliverLocalized term
        (.spine context head arguments body expected :: rest) result
  | spineFuelExhausted {term context head arguments body expected rest} :
      conversionVerdict normalizationFuel
          (Expr.subst0 term.erase body) expected = .conversionFuelExhausted →
      DeliverLocalized term
        (.spine context head arguments body expected :: rest)
        .conversionFuelExhausted
  | spineContinues {term context head arguments body expected rest domain nextBody} :
      conversionVerdict normalizationFuel
          (Expr.subst0 term.erase body) expected = .normalFormsDiffer →
      Expr.subst0 term.erase body = .pi domain nextBody →
      DeliverLocalized term
        (.spine context head arguments body expected :: rest)
        (.ok (prepare 0 context domain
          (.spine context head (arguments ++ [term]) nextBody expected :: rest)))
  | spineRejected {term context head arguments body expected rest} :
      conversionVerdict normalizationFuel
          (Expr.subst0 term.erase body) expected = .normalFormsDiffer →
      (∀ domain nextBody, Expr.subst0 term.erase body ≠ .pi domain nextBody) →
      DeliverLocalized term
        (.spine context head arguments body expected :: rest) .rejected

/-- Every delivery result has a certificate with conversion confined to match boundaries. -/
theorem deliver_localized (term : Nf) (frames : List Frame) :
    DeliverLocalized term frames (deliver term frames) := by
  induction frames generalizing term with
  | nil => exact .done
  | cons frame rest ih =>
      cases frame with
      | lambda domain => exact .lambda (ih (.lam domain term))
      | spine context head arguments body expected =>
          cases hconversion : conversionVerdict normalizationFuel
              (Expr.subst0 term.erase body) expected with
          | convertible =>
              simpa [PureBetaAtomicRefinement.deliver, hconversion] using
                (DeliverLocalized.spineConvertible
                  (context := context) (head := head) (arguments := arguments)
                  (body := body) (expected := expected) (rest := rest) hconversion
                  (ih (.head head (arguments ++ [term]))))
          | conversionFuelExhausted =>
              simpa [PureBetaAtomicRefinement.deliver, hconversion] using
                (DeliverLocalized.spineFuelExhausted
                  (context := context) (head := head) (arguments := arguments)
                  (body := body) (expected := expected) (rest := rest) hconversion)
          | normalFormsDiffer =>
              cases hnext : Expr.subst0 term.erase body with
              | pi domain nextBody =>
                  have hconversion' :
                      conversionVerdict normalizationFuel (.pi domain nextBody) expected =
                        .normalFormsDiffer := by
                    simpa [hnext] using hconversion
                  simpa [PureBetaAtomicRefinement.deliver, hnext, hconversion'] using
                    (DeliverLocalized.spineContinues
                      (context := context) (head := head) (arguments := arguments)
                      (body := body) (expected := expected) (rest := rest)
                      hconversion hnext)
              | sort =>
                  have hconversion' :
                      conversionVerdict normalizationFuel .sort expected =
                        .normalFormsDiffer := by
                    simpa [hnext] using hconversion
                  simpa [PureBetaAtomicRefinement.deliver, hnext, hconversion'] using
                    (DeliverLocalized.spineRejected
                      (context := context) (head := head) (arguments := arguments)
                      (body := body) (expected := expected) (rest := rest) hconversion
                      (by intro; simp [hnext]))
              | bvar index =>
                  have hconversion' :
                      conversionVerdict normalizationFuel (.bvar index) expected =
                        .normalFormsDiffer := by
                    simpa [hnext] using hconversion
                  simpa [PureBetaAtomicRefinement.deliver, hnext, hconversion'] using
                    (DeliverLocalized.spineRejected
                      (context := context) (head := head) (arguments := arguments)
                      (body := body) (expected := expected) (rest := rest) hconversion
                      (by intro; simp [hnext]))
              | lam domain nextBody =>
                  have hconversion' :
                      conversionVerdict normalizationFuel (.lam domain nextBody) expected =
                        .normalFormsDiffer := by
                    simpa [hnext] using hconversion
                  simpa [PureBetaAtomicRefinement.deliver, hnext, hconversion'] using
                    (DeliverLocalized.spineRejected
                      (context := context) (head := head) (arguments := arguments)
                      (body := body) (expected := expected) (rest := rest) hconversion
                      (by intro; simp [hnext]))
              | app fn argument =>
                  have hconversion' :
                      conversionVerdict normalizationFuel (.app fn argument) expected =
                        .normalFormsDiffer := by
                    simpa [hnext] using hconversion
                  simpa [PureBetaAtomicRefinement.deliver, hnext, hconversion'] using
                    (DeliverLocalized.spineRejected
                      (context := context) (head := head) (arguments := arguments)
                      (body := body) (expected := expected) (rest := rest) hconversion
                      (by intro; simp [hnext]))

/-- Certificate for starting a selected head's deterministic spine. -/
inductive StartSpineLocalized (context : Ctx) (expected : Expr)
    (frames : List Frame) (head : Nat) (arguments : List Nf) :
    Expr → CheckResult Core → Prop where
  | pi {domain body} :
      StartSpineLocalized context expected frames head arguments (.pi domain body)
        (.ok (prepare 0 context domain
          (.spine context head arguments body expected :: frames)))
  | matched {headType result} :
      (∀ domain body, headType ≠ .pi domain body) →
      conversionVerdict normalizationFuel headType expected = .convertible →
      DeliverLocalized (.head head arguments) frames result →
      StartSpineLocalized context expected frames head arguments headType result
  | mismatched {headType} :
      (∀ domain body, headType ≠ .pi domain body) →
      conversionVerdict normalizationFuel headType expected = .normalFormsDiffer →
      StartSpineLocalized context expected frames head arguments headType .rejected
  | fuelExhausted {headType} :
      (∀ domain body, headType ≠ .pi domain body) →
      conversionVerdict normalizationFuel headType expected = .conversionFuelExhausted →
      StartSpineLocalized context expected frames head arguments headType
        .conversionFuelExhausted

/-- Every start-spine result is localized; the Pi case has no conversion premise. -/
theorem startSpine_localized (context : Ctx) (expected : Expr)
    (frames : List Frame) (head : Nat) (arguments : List Nf) (headType : Expr) :
    StartSpineLocalized context expected frames head arguments headType
      (startSpine context expected frames head arguments headType) := by
  cases headType with
  | pi domain body => exact .pi
  | sort =>
      cases hconversion : conversionVerdict normalizationFuel .sort expected with
      | convertible =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.matched (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion
              (deliver_localized (.head head arguments) frames))
      | normalFormsDiffer =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.mismatched (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion)
      | conversionFuelExhausted =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.fuelExhausted (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion)
  | bvar index =>
      cases hconversion : conversionVerdict normalizationFuel (.bvar index) expected with
      | convertible =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.matched (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion
              (deliver_localized (.head head arguments) frames))
      | normalFormsDiffer =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.mismatched (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion)
      | conversionFuelExhausted =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.fuelExhausted (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion)
  | lam domain body =>
      cases hconversion : conversionVerdict normalizationFuel (.lam domain body) expected with
      | convertible =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.matched (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion
              (deliver_localized (.head head arguments) frames))
      | normalFormsDiffer =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.mismatched (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion)
      | conversionFuelExhausted =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.fuelExhausted (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion)
  | app fn argument =>
      cases hconversion : conversionVerdict normalizationFuel (.app fn argument) expected with
      | convertible =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.matched (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion
              (deliver_localized (.head head arguments) frames))
      | normalFormsDiffer =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.mismatched (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion)
      | conversionFuelExhausted =>
          simpa [PureBetaAtomicRefinement.startSpine, hconversion] using
            (StartSpineLocalized.fuelExhausted (context := context) (expected := expected)
              (frames := frames) (head := head) (arguments := arguments)
              (by intro; simp) hconversion)

/-- A valid atomic selection delegates exactly once to the localized spine starter. -/
theorem rawRefine_selected_eq_startSpine {hole head : Nat} {context : Ctx}
    {expected headType : Expr} {frames : List Frame}
    (hlookup : ctxLookup context head = some headType) :
    rawRefineResult (.needHole hole context expected frames) ⟨hole, head⟩ =
      startSpine context expected frames head [] headType := by
  simp [rawRefineResult, hlookup]

/-- In particular, a Pi-typed head starts construction independently of conversion. -/
theorem pi_head_starts_spine_without_conversion {hole head : Nat} {context : Ctx}
    {expected domain body : Expr} {frames : List Frame}
    (hlookup : ctxLookup context head = some (.pi domain body)) :
    rawRefineResult (.needHole hole context expected frames) ⟨hole, head⟩ =
      .ok (prepare 0 context domain
        (.spine context head [] body expected :: frames)) := by
  rw [rawRefine_selected_eq_startSpine hlookup]
  rfl

#print axioms deliver_localized
#print axioms startSpine_localized
#print axioms rawRefine_selected_eq_startSpine
#print axioms pi_head_starts_spine_without_conversion

end Mettapedia.GSLT.LanguageDef.PureBetaConversionBoundary
