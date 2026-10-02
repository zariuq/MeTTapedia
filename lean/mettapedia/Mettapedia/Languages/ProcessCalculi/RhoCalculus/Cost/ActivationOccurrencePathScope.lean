import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrenceReadout
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSerializationPaths
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimePathRefinement

/-!
# Pure-erasure scope of admitted occurrence paths

Whole runtime scope includes located purses, whereas the existing pure-erasure
scope forgets their bookkeeping fields. The constructive comparison below
retains quotation's reset to depth zero. Actual serialized admission therefore
supplies the scope premise of the established runtime-to-pure path theorem.
The signature-name encoding license is independent of exact purse matching.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

mutual
  theorem RawCostName.binderSafeAt_of_runtimeBinderSafeAt (depth : Nat) :
      ∀ name : RawCostName, name.runtimeBinderSafeAt depth = true → name.binderSafeAt depth = true
    | .bvar _index, safe => safe
    | .signature _signature, _ => rfl
    | .quote term, safe => RawCostTerm.binderSafeAt_of_runtimeBinderSafeAt 0 term safe

  theorem RawCostProc.binderSafeAt_of_runtimeBinderSafeAt (depth : Nat) :
      ∀ process : RawCostProc, process.runtimeBinderSafeAt depth = true → process.binderSafeAt depth = true
    | .nil, _ => rfl
    | .par first second, safe => by
        simp only [RawCostProc.runtimeBinderSafeAt, RawCostProc.binderSafeAt, Bool.and_eq_true] at safe ⊢
        exact ⟨RawCostProc.binderSafeAt_of_runtimeBinderSafeAt depth first safe.1,
          RawCostProc.binderSafeAt_of_runtimeBinderSafeAt depth second safe.2⟩
    | .send name payload, safe => by
        simp only [RawCostProc.runtimeBinderSafeAt, RawCostProc.binderSafeAt, Bool.and_eq_true] at safe ⊢
        exact ⟨RawCostName.binderSafeAt_of_runtimeBinderSafeAt depth name safe.1,
          RawCostTerm.binderSafeAt_of_runtimeBinderSafeAt depth payload safe.2⟩
    | .recv name body, safe => by
        simp only [RawCostProc.runtimeBinderSafeAt, RawCostProc.binderSafeAt, Bool.and_eq_true] at safe ⊢
        exact ⟨RawCostName.binderSafeAt_of_runtimeBinderSafeAt depth name safe.1,
          RawCostTerm.binderSafeAt_of_runtimeBinderSafeAt (depth + 1) body safe.2⟩

  theorem RawCostTerm.binderSafeAt_of_runtimeBinderSafeAt (depth : Nat) :
      ∀ term : RawCostTerm, term.runtimeBinderSafeAt depth = true → term.binderSafeAt depth = true
    | .nil, _ => rfl
    | .signed process _signature, safe => RawCostProc.binderSafeAt_of_runtimeBinderSafeAt depth process safe
    | .par first second, safe => by
        simp only [RawCostTerm.runtimeBinderSafeAt, RawCostTerm.binderSafeAt, Bool.and_eq_true] at safe ⊢
        exact ⟨RawCostTerm.binderSafeAt_of_runtimeBinderSafeAt depth first safe.1,
          RawCostTerm.binderSafeAt_of_runtimeBinderSafeAt depth second safe.2⟩
    | .drop name, safe => RawCostName.binderSafeAt_of_runtimeBinderSafeAt depth name safe
    | .purse _location _stack, _ => rfl
end

namespace ActivationGenerated.SerializationAdmission

theorem CodeAdmitted.binderSafeAt {depth : Nat} {term : RawCostTerm}
    (image : CodeAdmitted depth term) : term.binderSafeAt depth = true :=
  term.binderSafeAt_of_runtimeBinderSafeAt depth image.runtimeBinderSafeAt

theorem ConfigAdmitted.binderSafe {location : RawCostName} {term : RawCostTerm}
    (image : ConfigAdmitted location term) : term.binderSafe = true := by
  induction image with
  | code code => exact code.binderSafeAt
  | purse stack => rfl
  | par first second firstSafe secondSafe =>
      change (_ && _) = true
      unfold RawCostTerm.binderSafe at firstSafe secondSafe
      rw [firstSafe, secondSafe]
      rfl

theorem configAdmitted_decoded_binderSafe {location : RawCostName} {config : RawCostConfig}
    (images : config.Forall (ConfigAdmitted location)) : (decodeRawConfig config).BinderSafe := by
  apply (RawCostConfig.binderSafe_iff_decode config).mp
  rw [List.forall_iff_forall_mem]
  intro term member
  exact (List.forall_iff_forall_mem.mp images term member).binderSafe

end ActivationGenerated.SerializationAdmission

namespace ActivationGenerated

theorem ConfigImage.initial_decoded_binderSafe {location : CostName LiteralAuthority}
    {source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern} {term : CostTerm LiteralAuthority}
    (image : ConfigImage location source term) :
    (decodeRawConfig ((initialTraceComponents (literalEncodeTerm term)).map RawTraceComponent.term)).BinderSafe :=
  SerializationAdmission.configAdmitted_decoded_binderSafe image.initial_serialized_admission

/-- Every actual finite admitted execution contributes exactly one base COMM
step per firing. The independently licensed name encoding observes erasure;
it does not replace the literal keys used by funding. -/
theorem ConfigImage.finite_path_base_erasure {location : CostName LiteralAuthority}
    {source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern} {term : CostTerm LiteralAuthority}
    (image : ConfigImage location source term)
    {nextId : Nat} {finalComponents : List RawTraceComponent}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) nextId finalComponents)
    {signatureName : SignatureNameEncoding String}
    (signatureClosed : signatureName.MapsToClosedRhoNames) :
    ∃ finalSafe : (decodeRawConfig (finalComponents.map RawTraceComponent.term)).BinderSafe,
      ∃ purePath : Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT.rhoLanguageDefGSLT.RewritePath
        ((decodeRawConfig ((initialTraceComponents (literalEncodeTerm term)).map RawTraceComponent.term))
          |>.eraseCanonicalProcess signatureClosed image.initial_decoded_binderSafe)
        ((decodeRawConfig (finalComponents.map RawTraceComponent.term))
          |>.eraseCanonicalProcess signatureClosed finalSafe), purePath.length = path.depth :=
  path.exists_eraseCanonical_rhoLanguageDefRewritePath signatureClosed
    (initialTraceComponents_canonical _) image.initial_decoded_binderSafe

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
