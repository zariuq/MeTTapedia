import Mettapedia.Languages.MeTTa.Prime.NativeCostOneReceiptPolicyNIKAdmission
import Mettapedia.Languages.MeTTa.Prime.CostTwoDisplayedKeyTransport

/-!
# Prime's language-independent Cost interface

This import gate exposes the Prime-facing Cost boundary without selecting a
concrete language:

* proof-relevant Cost₁ operational schedules and chronological receipts;
* `WorkSpan` as a valuation of retained execution evidence;
* policy-relative cache and replay keys;
* the Cost² information order and NIK admission boundary; and
* displayed transport of compact policy keys.

A consumer of this module may state scheduling, metering, receipt, cache, and
replay obligations for any `CostOneDomainObject`.  Concrete inhabitants and
language-specific counterexamples belong in separate annexes.
-/
