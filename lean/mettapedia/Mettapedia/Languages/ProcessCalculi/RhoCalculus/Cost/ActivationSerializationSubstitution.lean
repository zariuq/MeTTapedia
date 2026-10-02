import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSerializationReadback

/-!
# Actual communication preserves serialized code admission

These laws use the existing raw lifting and binder-eliminating substitution.
Closed communicated code retains its checked literal signatures. Quotations
remain opaque and carry closed admitted code; eliminating a receiver binder
therefore never opens a quoted scope or manufactures a purse.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission

mutual
  theorem NameAdmitted.liftAbove_identity :
      ∀ {scope cutoff : Nat} {name : RawCostName}, NameAdmitted scope name →
        scope ≤ cutoff → ∀ amount, name.lift amount cutoff = name := by
    intro scope cutoff name image larger amount
    cases image with
    | @bvar _ index bound => simp [RawCostName.lift, show ¬cutoff ≤ index from by omega]
    | quote code => rfl

  theorem CodeAdmitted.liftAbove_identity :
      ∀ {scope cutoff : Nat} {term : RawCostTerm}, CodeAdmitted scope term →
        scope ≤ cutoff → ∀ amount, term.lift amount cutoff = term := by
    intro scope cutoff term image larger amount
    cases image with
    | zero => rfl
    | drop name => simp only [RawCostTerm.lift, name.liftAbove_identity larger amount]
    | signed process signature => simp only [RawCostTerm.lift, process.liftAbove_identity larger amount]
    | par first second =>
        simp only [RawCostTerm.lift, first.liftAbove_identity larger amount,
          second.liftAbove_identity larger amount]

  theorem ProcAdmitted.liftAbove_identity :
      ∀ {scope cutoff : Nat} {process : RawCostProc}, ProcAdmitted scope process →
        scope ≤ cutoff → ∀ amount, process.lift amount cutoff = process := by
    intro scope cutoff process image larger amount
    cases image with
    | zero => rfl
    | send name code =>
        simp only [RawCostProc.lift, name.liftAbove_identity larger amount,
          code.liftAbove_identity larger amount]
    | recv name code =>
        simp only [RawCostProc.lift, name.liftAbove_identity larger amount,
          code.liftAbove_identity (Nat.add_le_add_right larger 1) amount]
    | par first second =>
        simp only [RawCostProc.lift, first.liftAbove_identity larger amount,
          second.liftAbove_identity larger amount]
end

mutual
  theorem NameAdmitted.substitute :
      ∀ {depth : Nat} {name : RawCostName} {payload : RawCostTerm},
        NameAdmitted (depth + 1) name → CodeAdmitted 0 payload →
        NameAdmitted depth (name.substitute payload depth) := by
    intro depth name payload image payloadImage
    cases image with
    | @bvar _ index bound =>
        by_cases matched : index = depth
        · subst index
          rw [RawCostName.substitute, if_pos rfl,
            payloadImage.liftAbove_identity (le_refl 0) depth]
          exact .quote payloadImage
        · simp only [RawCostName.substitute, matched, if_false,
            show ¬depth < index from by omega]
          exact .bvar (by omega)
    | quote code => exact .quote code

  theorem CodeAdmitted.substitute :
      ∀ {depth : Nat} {term payload : RawCostTerm},
        CodeAdmitted (depth + 1) term → CodeAdmitted 0 payload →
        CodeAdmitted depth (RawCostTerm.substitute payload depth term) := by
    intro depth term payload image payloadImage
    cases image with
    | zero => exact .zero
    | drop name =>
        cases name with
        | @bvar _ index bound =>
            by_cases matched : index = depth
            · subst index
              rw [RawCostTerm.substitute, if_pos rfl,
                payloadImage.liftAbove_identity (le_refl 0) depth]
              exact payloadImage.weaken (Nat.zero_le depth)
            · simp only [RawCostTerm.substitute, matched, if_false,
                show ¬depth < index from by omega]
              exact .drop (.bvar (by omega))
        | quote code => exact .drop (.quote code)
    | signed process signature => exact .signed (process.substitute payloadImage) signature
    | par first second => exact .par (first.substitute payloadImage) (second.substitute payloadImage)

  theorem ProcAdmitted.substitute :
      ∀ {depth : Nat} {process : RawCostProc} {payload : RawCostTerm},
        ProcAdmitted (depth + 1) process → CodeAdmitted 0 payload →
        ProcAdmitted depth (process.substitute payload depth) := by
    intro depth process payload image payloadImage
    cases image with
    | zero => exact .zero
    | send name code => exact .send (name.substitute payloadImage) (code.substitute payloadImage)
    | recv name code => exact .recv (name.substitute payloadImage) (code.substitute payloadImage)
    | par first second => exact .par (first.substitute payloadImage) (second.substitute payloadImage)
end

/-- The existing COMM operation consumes one binder and preserves admission. -/
theorem CodeAdmitted.commSubst {body payload : RawCostTerm}
    (receiver : CodeAdmitted 1 body) (message : CodeAdmitted 0 payload) :
    CodeAdmitted 0 (body.commSubst payload) := receiver.substitute message

theorem CodeAdmitted.commSubst_normalize {body payload : RawCostTerm}
    (receiver : CodeAdmitted 1 body) (message : CodeAdmitted 0 payload) :
    CodeAdmitted 0 (body.commSubst payload).normalize := (receiver.commSubst message).normalize

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission
