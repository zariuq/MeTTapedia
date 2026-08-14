/-
# Certificate necessity: the undecidability half of the doctrine pair

`DecisionKernel.authority` (KernelAuthority.lean) is the ELIMINATION half of
the certificate doctrine: wherever a kernel decides the judgment directly,
the trivial-certificate checker already has full replay authority —
certificates add nothing on decidable ground.

This file proves the NECESSITY half: there is a semantic claim family with a
computable, sound, certificate-complete checker whose meaning is NOT
computably decidable.  Certificates strictly exceed direct computation
exactly at undecidability — they are the undecidability tax, chargeable only
at genuine search or trust boundaries, never on a decidable typing path.

The witness is the canonical one: claims are partial-recursive codes, the
meaning is halting (at input 0), a certificate is a step budget, and the
checker is bounded evaluation.  The certificate carries a CHOICE (how long
to run — what an unbounded search discovered) while the checker computes the
consequence, which is exactly the compact-certificate discipline.

Statement discipline (load-bearing): the bare claim "no `DecisionKernel`
exists for this meaning" is CLASSICALLY FALSE — `Classical.choice` conjures
a noncomputable `decide` for any meaning.  The honest separation must be
stated with `ComputablePred`/`Computable₂`, and that is what is proved.
-/
import Mathlib.Computability.Halting
import Mettapedia.GSLT.LanguageDef.KernelAuthority

namespace Mettapedia.GSLT.LanguageDef.CertificateNecessity

open Mettapedia.GSLT.LanguageDef.KernelAuthority (Checker)
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- The undecidable meaning: the coded partial function halts on input 0. -/
def HaltsAtZero (c : Code) : Prop := (eval c 0).Dom

/-- The certificate checker: a certificate is a step budget, checking is
bounded evaluation.  Choices in the certificate, consequences computed. -/
def budgetCheck (c : Code) (k : ℕ) : Bool := (evaln k c 0).isSome

/-- The checker is primitive recursive — comfortably computable. -/
theorem budgetCheck_primrec : Primrec₂ budgetCheck := by
  have hpack : Primrec fun p : Code × ℕ => ((p.2, p.1), 0) :=
    (Primrec.snd.pair Primrec.fst).pair (Primrec.const 0)
  exact Primrec.option_isSome.comp (primrec_evaln.comp hpack)

/-- Soundness: an accepted budget certificate establishes halting. -/
theorem budgetCheck_sound (c : Code) (k : ℕ)
    (accepted : budgetCheck c k = true) : HaltsAtZero c := by
  rcases Option.isSome_iff_exists.1 accepted with ⟨v, hv⟩
  exact Part.dom_iff_mem.2 ⟨v, evaln_sound (Option.mem_def.2 hv)⟩

/-- Certificate completeness: every halting code has an accepted budget. -/
theorem budgetCheck_complete (c : Code) (halts : HaltsAtZero c) :
    ∃ k, budgetCheck c k = true := by
  rcases Part.dom_iff_mem.1 halts with ⟨v, hv⟩
  rcases evaln_complete.1 hv with ⟨k, hk⟩
  exact ⟨k, Option.isSome_iff_exists.2 ⟨v, Option.mem_def.1 hk⟩⟩

/-- The meaning itself is not computably decidable: the halting problem. -/
theorem haltsAtZero_not_computable : ¬ComputablePred HaltsAtZero :=
  ComputablePred.halting_problem 0

/-- The budget checker packaged in the NIK `Checker` interface. -/
def budgetChecker : Checker Code ℕ where
  check := budgetCheck

/-- Exact replay authority: acceptance-by-some-certificate coincides with
halting. -/
theorem budgetChecker_authority : budgetChecker.Authority HaltsAtZero where
  sound := fun c k accepted => budgetCheck_sound c k accepted
  complete := fun c halts => budgetCheck_complete c halts

/-- The zero code halts on input 0. -/
theorem zero_code_halts : HaltsAtZero Code.zero := trivial

/-- Positive witness: some budget certificate accepts the zero code — the
checker is not vacuously rejecting. -/
theorem zero_code_accepted : ∃ k, budgetCheck Code.zero k = true :=
  budgetCheck_complete Code.zero zero_code_halts

/-- Negative witness: budget 0 rejects every claim — the checker is not
vacuously accepting, and certificates carry real content. -/
theorem zero_budget_rejects (c : Code) : budgetCheck c 0 = false := by
  rw [Bool.eq_false_iff]
  intro accepted
  rcases Option.isSome_iff_exists.1 accepted with ⟨v, hv⟩
  exact absurd (evaln_bound (Option.mem_def.2 hv)) (Nat.lt_irrefl 0)

/-- **Certificate necessity.**  A claim family and meaning exist with a
computable (indeed primitive recursive), sound, certificate-complete
checker — full replay authority — while NO computable decision procedure
for the meaning exists.  Together with the elimination theorem
(`DecisionKernel.authority`: certificate-free kernels lose nothing on
decidable ground), this pins the doctrine as mathematics: certificates are
exactly the compensation for undecidability. -/
theorem certificates_strictly_beyond_computation :
    ∃ (Meaning : Code → Prop) (checker : Checker Code ℕ),
      Computable₂ checker.check ∧
        checker.Authority Meaning ∧
          ¬ComputablePred Meaning :=
  ⟨HaltsAtZero, budgetChecker, budgetCheck_primrec.to_comp,
    budgetChecker_authority, haltsAtZero_not_computable⟩

end Mettapedia.GSLT.LanguageDef.CertificateNecessity
