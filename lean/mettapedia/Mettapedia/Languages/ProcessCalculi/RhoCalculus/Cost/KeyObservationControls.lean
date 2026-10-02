import Mettapedia.GSLT.LanguageDef.Cost.KeyObservation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-!
# Canonical-class keys versus literal rho commitments

Parallel zero and zero are different source presentations of one admitted
equation class.  A free Drop of the quotation of zero is a different class,
and is inert in the selected pure-rho profile.  These controls separate
literal syntax, canonical classes, and optional digest collisions.  Executable
Drop belongs to a separate operational profile.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.KeyObservationControls

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Cost.Elaboration
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open LanguageDefGSLT LanguageDefRewriteSystem LanguageDefSemanticAgreement
open LanguageDefContinuedInteraction

/-- Use the existing closed-carrier comparison, retaining its quote-safety
evidence when reading the empty open fibre. -/
def asKeyCarrier (process : RhoProcess) : rhoCIGSLT.CanonicalCarrier := by
  let term := presentedRhoProcessEquiv.symm process
  exact ⟨term.1,
    (closedTermToOpen (theory := rhoCIGSLT.theory)
      (ReflectiveWellSorted.ClosedTerm.toCore term)).2, term.2.2⟩

/-- A closed parallel unit in the actual rho syntax. -/
def zero : RhoProcess :=
  ⟨.apply "PZero" [],
    (rhoClosedTermWellSorted_process_iff _).mpr ⟨.unit, by decide⟩⟩

/-- Two explicit parallel units retain a different literal presentation. -/
def parallelZero : RhoProcess :=
  ⟨.collection .hashBag [.apply "PZero" [], .apply "PZero" []] none,
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.parallel (.cons .unit (.cons .unit .nil)), by decide⟩⟩

theorem parallelZero_literal_ne_zero :
    (asKeyCarrier parallelZero).val ≠ (asKeyCarrier zero).val := by
  decide

/-- The concrete parallel-unit equation has one canonical key. -/
theorem parallelZero_key_eq_zero :
    rhoCIGSLT.canonicalKey (asKeyCarrier parallelZero) =
      rhoCIGSLT.canonicalKey (asKeyCarrier zero) := by
  apply Subtype.ext
  apply Subtype.ext
  exact Canonical.canonicalize_parallel_nil_left (.apply "PZero" [])

/-- This is an equation of the admitted reflective fibre, not merely a
coincidence of raw normalization outputs. -/
theorem parallelZero_equivalent_zero :
    rhoCIGSLT.canonicalEquationSetoid.r (asKeyCarrier parallelZero)
      (asKeyCarrier zero) :=
  (rhoCIGSLT.canonicalKey_eq_iff _ _).mp parallelZero_key_eq_zero

/-- No choice of digest of canonical keys can distinguish this equation. -/
theorem parallelZero_digest_eq_zero {Digest : Type*}
    (digest : rhoCIGSLT.CanonicalKey → Digest) :
    digest (rhoCIGSLT.canonicalKey (asKeyCarrier parallelZero)) =
      digest (rhoCIGSLT.canonicalKey (asKeyCarrier zero)) :=
  rhoCIGSLT.canonicalDigest_eq_of_equivalent digest parallelZero_equivalent_zero

/-- Literal source inspection does not descend to the canonical quotient. -/
theorem literal_has_no_canonical_realization :
    ¬ ReplayKey.HasRealization rhoCIGSLT.canonicalKey
      (Subtype.val : rhoCIGSLT.CanonicalCarrier → Pattern) :=
  rhoCIGSLT.canonicalSetoidSection.no_realization_of_distinguished_equivalents
    Subtype.val parallelZero_equivalent_zero parallelZero_literal_ne_zero

/-- Canonicalization does not identify free Drop with its quoted body. -/
theorem freeDrop_key_ne_zero :
    rhoCIGSLT.canonicalKey (asKeyCarrier closedFreeDrop) ≠
      rhoCIGSLT.canonicalKey (asKeyCarrier zero) := by
  intro same
  have patterns := congrArg (fun key : rhoCIGSLT.CanonicalKey => key.1.1) same
  change Pattern.apply "PDrop" [Pattern.apply "NQuote" [Pattern.apply "PZero" []]] =
    Pattern.apply "PZero" [] at patterns
  exact (by decide : ("PDrop" : String) ≠ "PZero") (Pattern.apply.inj patterns).1

/-- The selected pure-rho GSLT has no outgoing step from this same term. -/
theorem freeDrop_irreducible (target : RhoProcess) :
    ¬ rhoLanguageDefGSLT.Step closedFreeDrop target :=
  closedFreeDrop_irreducible_in_gslt target

/-- A deliberately colliding digest is accepted only for the same class. -/
theorem colliding_digest_accepts_equivalent :
    rhoCIGSLT.canonicalSetoidSection.checkKey (fun _ => (0 : Nat))
      (rhoCIGSLT.canonicalKey (asKeyCarrier parallelZero))
      (rhoCIGSLT.canonicalKey (asKeyCarrier zero)) = true :=
  (rhoCIGSLT.canonicalSetoidSection.checkKey_eq_true_iff _ _ _).mpr
    parallelZero_key_eq_zero

/-- The same digest cannot identify the inert Drop with zero. -/
theorem colliding_digest_rejects_distinct :
    rhoCIGSLT.canonicalSetoidSection.checkKey (fun _ => (0 : Nat))
      (rhoCIGSLT.canonicalKey (asKeyCarrier closedFreeDrop))
      (rhoCIGSLT.canonicalKey (asKeyCarrier zero)) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact freeDrop_key_ne_zero
    ((rhoCIGSLT.canonicalSetoidSection.checkKey_eq_true_iff _ _ _).mp accepted)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.KeyObservationControls
