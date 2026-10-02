import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedConfigClosure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Encoding
import Mettapedia.OSLF.MeTTaIL.DecimalNames
import Mettapedia.OSLF.MeTTaIL.PatternCode

/-!
# Injective literal authority transport to the existing raw runtime

The complete generated signature pattern is encoded as one ground string.
Relabelling preserves cost constructors, quotation boundaries and ordered
stacks. It does not interpret a signature product as a sum of two keys.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u v w

mutual
  def CostName.relabel {Ground : Type u} {Target : Type v} (label : Ground → Target) :
      CostName Ground → CostName Target
    | .bvar index => .bvar index
    | .quote term => .quote (term.relabel label)
    | .signature signature => .signature (signature.map label)

  def CostProc.relabel {Ground : Type u} {Target : Type v} (label : Ground → Target) :
      CostProc Ground → CostProc Target
    | .nil => .nil
    | .par left right => .par (left.relabel label) (right.relabel label)
    | .send channel payload => .send (channel.relabel label) (payload.relabel label)
    | .recv channel body => .recv (channel.relabel label) (body.relabel label)

  def CostTerm.relabel {Ground : Type u} {Target : Type v} (label : Ground → Target) :
      CostTerm Ground → CostTerm Target
    | .nil => .nil
    | .signed process signature => .signed (process.relabel label) (signature.map label)
    | .par left right => .par (left.relabel label) (right.relabel label)
    | .drop name => .drop (name.relabel label)
    | .purse location stack => .purse (location.relabel label) (stack.relabel label)

  def CostStack.relabel {Ground : Type u} {Target : Type v} (label : Ground → Target) :
      CostStack Ground → CostStack Target
    | .empty => .empty
    | .cons signature rest => .cons (signature.map label) (rest.relabel label)
end

mutual
  theorem CostName.relabel_id {Ground : Type u} (name : CostName Ground) : name.relabel id = name := by
    cases name <;> simp [CostName.relabel, CostTerm.relabel_id]

  theorem CostProc.relabel_id {Ground : Type u} (process : CostProc Ground) :
      process.relabel id = process := by
    cases process <;> simp [CostProc.relabel, CostName.relabel_id, CostTerm.relabel_id,
      CostProc.relabel_id]

  theorem CostTerm.relabel_id {Ground : Type u} (term : CostTerm Ground) : term.relabel id = term := by
    cases term <;> simp [CostTerm.relabel, CostName.relabel_id, CostProc.relabel_id,
      CostTerm.relabel_id, CostStack.relabel_id]

  theorem CostStack.relabel_id {Ground : Type u} (stack : CostStack Ground) : stack.relabel id = stack := by
    cases stack <;> simp [CostStack.relabel, CostStack.relabel_id]
end

mutual
  theorem CostName.relabel_comp {Ground : Type u} {Middle : Type v} {Target : Type w}
      (first : Ground → Middle) (second : Middle → Target) (name : CostName Ground) :
      (name.relabel first).relabel second = name.relabel (second ∘ first) := by
    cases name <;> simp [CostName.relabel, CostTerm.relabel_comp, Multiset.map_map]

  theorem CostProc.relabel_comp {Ground : Type u} {Middle : Type v} {Target : Type w}
      (first : Ground → Middle) (second : Middle → Target) (process : CostProc Ground) :
      (process.relabel first).relabel second = process.relabel (second ∘ first) := by
    cases process <;> simp [CostProc.relabel, CostName.relabel_comp, CostTerm.relabel_comp,
      CostProc.relabel_comp]

  theorem CostTerm.relabel_comp {Ground : Type u} {Middle : Type v} {Target : Type w}
      (first : Ground → Middle) (second : Middle → Target) (term : CostTerm Ground) :
      (term.relabel first).relabel second = term.relabel (second ∘ first) := by
    cases term <;> simp [CostTerm.relabel, CostName.relabel_comp, CostProc.relabel_comp,
      CostTerm.relabel_comp, CostStack.relabel_comp, Multiset.map_map]

  theorem CostStack.relabel_comp {Ground : Type u} {Middle : Type v} {Target : Type w}
      (first : Ground → Middle) (second : Middle → Target) (stack : CostStack Ground) :
      (stack.relabel first).relabel second = stack.relabel (second ∘ first) := by
    cases stack <;> simp [CostStack.relabel, CostStack.relabel_comp, Multiset.map_map]
end

mutual
  theorem CostName.relabel_lift {Ground : Type u} {Target : Type v}
      (label : Ground → Target) (amount cutoff : Nat) (name : CostName Ground) :
      (name.lift amount cutoff).relabel label = (name.relabel label).lift amount cutoff := by
    cases name with
    | bvar index => by_cases inScope : cutoff ≤ index <;> simp [CostName.lift, CostName.relabel, inScope]
    | quote term => rfl
    | signature signature => rfl

  theorem CostProc.relabel_lift {Ground : Type u} {Target : Type v}
      (label : Ground → Target) (amount cutoff : Nat) (process : CostProc Ground) :
      (process.lift amount cutoff).relabel label = (process.relabel label).lift amount cutoff := by
    cases process <;> simp [CostProc.lift, CostProc.relabel, CostName.relabel_lift,
      CostTerm.relabel_lift, CostProc.relabel_lift]

  theorem CostTerm.relabel_lift {Ground : Type u} {Target : Type v}
      (label : Ground → Target) (amount cutoff : Nat) (term : CostTerm Ground) :
      (term.lift amount cutoff).relabel label = (term.relabel label).lift amount cutoff := by
    cases term <;> simp [CostTerm.lift, CostTerm.relabel, CostName.relabel_lift,
      CostProc.relabel_lift, CostTerm.relabel_lift]
end

mutual
  theorem CostName.relabel_substitute {Ground : Type u} {Target : Type v}
      (label : Ground → Target) (replacement : CostTerm Ground) (depth : Nat) (name : CostName Ground) :
      (name.substitute replacement depth).relabel label =
        (name.relabel label).substitute (replacement.relabel label) depth := by
    cases name with
    | bvar index =>
      by_cases same : index = depth
      · simp [CostName.substitute, CostName.relabel, same, CostTerm.relabel_lift]
      · by_cases above : depth < index <;> simp [CostName.substitute, CostName.relabel, same, above]
    | quote term => rfl
    | signature signature => rfl

  theorem CostProc.relabel_substitute {Ground : Type u} {Target : Type v}
      (label : Ground → Target) (replacement : CostTerm Ground) (depth : Nat) (process : CostProc Ground) :
      (process.substitute replacement depth).relabel label =
        (process.relabel label).substitute (replacement.relabel label) depth := by
    cases process <;> simp [CostProc.substitute, CostProc.relabel, CostName.relabel_substitute,
      CostTerm.relabel_substitute, CostProc.relabel_substitute]

  theorem CostTerm.relabel_substitute {Ground : Type u} {Target : Type v}
      (label : Ground → Target) (replacement : CostTerm Ground) (depth : Nat) (term : CostTerm Ground) :
      (CostTerm.substitute replacement depth term).relabel label =
        CostTerm.substitute (replacement.relabel label) depth (term.relabel label) := by
    cases term with
    | nil => rfl
    | signed process signature =>
      simp [CostTerm.substitute, CostTerm.relabel, CostProc.relabel_substitute]
    | par left right => simp [CostTerm.substitute, CostTerm.relabel, CostTerm.relabel_substitute]
    | drop name =>
      cases name with
      | bvar index =>
        by_cases same : index = depth
        · simp [CostTerm.substitute, CostTerm.relabel, CostName.relabel, same, CostTerm.relabel_lift]
        · by_cases above : depth < index <;>
            simp [CostTerm.substitute, CostTerm.relabel, CostName.relabel, same, above]
      | quote term => rfl
      | signature signature => rfl
    | purse location stack =>
      simp [CostTerm.substitute, CostTerm.relabel, CostName.relabel_substitute]
end

theorem CostTerm.relabel_commSubst {Ground : Type u} {Target : Type v} (label : Ground → Target)
    (body payload : CostTerm Ground) :
    (body.commSubst payload).relabel label = (body.relabel label).commSubst (payload.relabel label) :=
  CostTerm.relabel_substitute label payload 0 body

namespace ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode

local instance : Nonempty Pattern := ⟨.bvar 0⟩

/-- One complete literal pattern becomes one exact runtime atom. -/
def literalAuthorityKey (source : Pattern) : String := Nat.repr (patternCode source)

theorem literalAuthorityKey_injective : Function.Injective literalAuthorityKey := by
  intro left right same
  exact patternCode_injective (Mettapedia.OSLF.MeTTaIL.DecimalNames.repr_injective same)

theorem literal_signature_transport_injective :
    Function.Injective (fun signature : CostSig LiteralAuthority => signature.map literalAuthorityKey) :=
  Multiset.map_injective literalAuthorityKey_injective

theorem literal_signature_singleton (source : Pattern) :
    ({source} : CostSig LiteralAuthority).map literalAuthorityKey = {literalAuthorityKey source} := by
  simp

private theorem literalKey_leftInverse : Function.LeftInverse (Function.invFun literalAuthorityKey)
    literalAuthorityKey := by
  exact Function.leftInverse_invFun literalAuthorityKey_injective

theorem literal_name_transport_injective :
    Function.Injective (CostName.relabel literalAuthorityKey) := by
  intro left right same
  have back := congrArg (CostName.relabel (Function.invFun literalAuthorityKey)) same
  rw [CostName.relabel_comp, CostName.relabel_comp,
    show Function.invFun literalAuthorityKey ∘ literalAuthorityKey = id from funext literalKey_leftInverse,
    CostName.relabel_id, CostName.relabel_id] at back
  exact back

theorem literal_term_transport_injective :
    Function.Injective (CostTerm.relabel literalAuthorityKey) := by
  intro left right same
  have back := congrArg (CostTerm.relabel (Function.invFun literalAuthorityKey)) same
  rw [CostTerm.relabel_comp, CostTerm.relabel_comp,
    show Function.invFun literalAuthorityKey ∘ literalAuthorityKey = id from funext literalKey_leftInverse,
    CostTerm.relabel_id, CostTerm.relabel_id] at back
  exact back

def literalEncodeName (name : CostName LiteralAuthority) : RawCostName :=
  encodeCostName (name.relabel literalAuthorityKey)

def literalEncodeProc (process : CostProc LiteralAuthority) : RawCostProc :=
  encodeCostProc (process.relabel literalAuthorityKey)

def literalEncodeTerm (term : CostTerm LiteralAuthority) : RawCostTerm :=
  encodeCostTerm (term.relabel literalAuthorityKey)

def literalEncodeStack (stack : CostStack LiteralAuthority) : RawCostStack :=
  encodeCostStack (stack.relabel literalAuthorityKey)

theorem literalEncodeTerm_injective : Function.Injective literalEncodeTerm := by
  intro left right same
  apply literal_term_transport_injective
  simpa only [literalEncodeTerm, decodeCostTerm_encodeCostTerm] using congrArg decodeCostTerm same

theorem literalEncodeName_injective : Function.Injective literalEncodeName := by
  intro left right same
  apply literal_name_transport_injective
  simpa only [literalEncodeName, decodeCostName_encodeCostName] using congrArg decodeCostName same

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
