import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLiteralEncoding

/-!
# Existing raw encoding commutes with communication substitution

These laws concern the actual encoder and actual raw substitution. Neither
normalization nor a new operational rule is inserted into communication.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

mutual
  theorem encodeCostName_lift (name : CostName String) (amount cutoff : Nat) :
      encodeCostName (name.lift amount cutoff) = (encodeCostName name).lift amount cutoff := by
    cases name with
    | bvar index => by_cases above : cutoff ≤ index <;> simp [CostName.lift, RawCostName.lift, encodeCostName, above]
    | quote term => rfl
    | signature signature => rfl

  theorem encodeCostProc_lift (process : CostProc String) (amount cutoff : Nat) :
      encodeCostProc (process.lift amount cutoff) = (encodeCostProc process).lift amount cutoff := by
    cases process <;> simp [CostProc.lift, RawCostProc.lift, encodeCostProc,
      encodeCostName_lift, encodeCostTerm_lift, encodeCostProc_lift]

  theorem encodeCostTerm_lift (term : CostTerm String) (amount cutoff : Nat) :
      encodeCostTerm (term.lift amount cutoff) = (encodeCostTerm term).lift amount cutoff := by
    cases term <;> simp [CostTerm.lift, RawCostTerm.lift, encodeCostTerm,
      encodeCostName_lift, encodeCostProc_lift, encodeCostTerm_lift]
end

mutual
  theorem encodeCostName_substitute (name : CostName String) (replacement : CostTerm String) (depth : Nat) :
      encodeCostName (name.substitute replacement depth) =
        (encodeCostName name).substitute (encodeCostTerm replacement) depth := by
    cases name with
    | bvar index =>
      by_cases same : index = depth
      · simp [CostName.substitute, RawCostName.substitute, encodeCostName, same, encodeCostTerm_lift]
      · by_cases above : depth < index <;>
          simp [CostName.substitute, RawCostName.substitute, encodeCostName, same, above]
    | quote term => rfl
    | signature signature => rfl

  theorem encodeCostProc_substitute (process : CostProc String) (replacement : CostTerm String) (depth : Nat) :
      encodeCostProc (process.substitute replacement depth) =
        (encodeCostProc process).substitute (encodeCostTerm replacement) depth := by
    cases process <;> simp [CostProc.substitute, RawCostProc.substitute, encodeCostProc,
      encodeCostName_substitute, encodeCostTerm_substitute, encodeCostProc_substitute]

  theorem encodeCostTerm_substitute (term : CostTerm String) (replacement : CostTerm String) (depth : Nat) :
      encodeCostTerm (CostTerm.substitute replacement depth term) =
        RawCostTerm.substitute (encodeCostTerm replacement) depth (encodeCostTerm term) := by
    cases term with
    | nil => rfl
    | signed process signature =>
      simp [CostTerm.substitute, RawCostTerm.substitute, encodeCostTerm, encodeCostProc_substitute]
    | par left right =>
      simp [CostTerm.substitute, RawCostTerm.substitute, encodeCostTerm, encodeCostTerm_substitute]
    | drop name =>
      cases name with
      | bvar index =>
        by_cases same : index = depth
        · simp [CostTerm.substitute, RawCostTerm.substitute, encodeCostTerm, encodeCostName, same,
            encodeCostTerm_lift]
        · by_cases above : depth < index <;>
            simp [CostTerm.substitute, RawCostTerm.substitute, encodeCostTerm, encodeCostName, same, above]
      | quote term => rfl
      | signature signature => rfl
    | purse location stack =>
      simp [CostTerm.substitute, RawCostTerm.substitute, encodeCostTerm, encodeCostName_substitute]
end

theorem encodeCostTerm_commSubst (body payload : CostTerm String) :
    encodeCostTerm (body.commSubst payload) =
      (encodeCostTerm body).commSubst (encodeCostTerm payload) :=
  encodeCostTerm_substitute body payload 0

namespace ActivationGenerated

theorem literalEncodeName_lift (name : CostName LiteralAuthority) (amount cutoff : Nat) :
    literalEncodeName (name.lift amount cutoff) = (literalEncodeName name).lift amount cutoff := by
  unfold literalEncodeName
  rw [CostName.relabel_lift, encodeCostName_lift]

theorem literalEncodeTerm_lift (term : CostTerm LiteralAuthority) (amount cutoff : Nat) :
    literalEncodeTerm (term.lift amount cutoff) = (literalEncodeTerm term).lift amount cutoff := by
  unfold literalEncodeTerm
  rw [CostTerm.relabel_lift, encodeCostTerm_lift]

theorem literalEncodeName_substitute (name : CostName LiteralAuthority)
    (payload : CostTerm LiteralAuthority) (depth : Nat) :
    literalEncodeName (name.substitute payload depth) =
      (literalEncodeName name).substitute (literalEncodeTerm payload) depth := by
  unfold literalEncodeName literalEncodeTerm
  rw [CostName.relabel_substitute, encodeCostName_substitute]

theorem literalEncodeTerm_substitute (term payload : CostTerm LiteralAuthority) (depth : Nat) :
    literalEncodeTerm (CostTerm.substitute payload depth term) =
      RawCostTerm.substitute (literalEncodeTerm payload) depth (literalEncodeTerm term) := by
  unfold literalEncodeTerm
  rw [CostTerm.relabel_substitute, encodeCostTerm_substitute]

theorem literalEncodeTerm_commSubst (body payload : CostTerm LiteralAuthority) :
    literalEncodeTerm (body.commSubst payload) =
      (literalEncodeTerm body).commSubst (literalEncodeTerm payload) :=
  literalEncodeTerm_substitute body payload 0

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
