import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.UnitPolicy
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ScopedSyntax
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Wrapping

/-!
# Substitution does not copy purses from admitted code-only payloads

The unrestricted runtime syntax permits purses inside communicated payloads.
Consequently code duplication is authority-preserving only on a code-only
payload domain.  The inventory below counts every literal purse constructor,
including quoted data and suspended continuations.  It is deliberately finer
than the currently executable purse occurrences of a configuration.

For a payload with empty inventory, capture-avoiding substitution preserves
the entire inventory of the receiving term.  Existing quotation is opaque;
opening a matched bound Drop copies the payload with its original seals and
cannot introduce a purse.  Every ensuing actual firing still requires the
positive located funding law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

mutual
  /-- Literal purse stacks in a name, including its quoted syntax. -/
  def CostName.purseInventory {Ground : Type u} :
      CostName Ground → Multiset (CostStack Ground)
    | .bvar _ => 0
    | .quote term => term.purseInventory
    | .signature _ => 0

  /-- Literal purse stacks in introductions and their suspended code. -/
  def CostProc.purseInventory {Ground : Type u} :
      CostProc Ground → Multiset (CostStack Ground)
    | .nil => 0
    | .par left right => left.purseInventory + right.purseInventory
    | .send channel payload => channel.purseInventory + payload.purseInventory
    | .recv channel body => channel.purseInventory + body.purseInventory

  /-- Exact multiset of all literal purse stacks, including latent data. -/
  def CostTerm.purseInventory {Ground : Type u} :
      CostTerm Ground → Multiset (CostStack Ground)
    | .nil => 0
    | .signed process _ => process.purseInventory
    | .par left right => left.purseInventory + right.purseInventory
    | .drop name => name.purseInventory
    | .purse location stack => {stack} + location.purseInventory
end

/-- A code-only payload contains no purse even in quoted or suspended syntax. -/
def CostTerm.PurseFree {Ground : Type u} (term : CostTerm Ground) : Prop :=
  term.purseInventory = 0

mutual
  theorem CostName.purseInventory_lift {Ground : Type u}
      (amount cutoff : Nat) : ∀ name : CostName Ground,
      (name.lift amount cutoff).purseInventory = name.purseInventory
    | .bvar index => by
        simp only [CostName.lift]
        split <;> rfl
    | .quote term => rfl
    | .signature signature => rfl

  theorem CostProc.purseInventory_lift {Ground : Type u}
      (amount cutoff : Nat) : ∀ process : CostProc Ground,
      (process.lift amount cutoff).purseInventory = process.purseInventory
    | .nil => rfl
    | .par left right => by
        simp only [CostProc.lift, CostProc.purseInventory,
          CostProc.purseInventory_lift amount cutoff left,
          CostProc.purseInventory_lift amount cutoff right]
    | .send channel payload => by
        simp only [CostProc.lift, CostProc.purseInventory,
          CostName.purseInventory_lift amount cutoff channel,
          CostTerm.purseInventory_lift amount cutoff payload]
    | .recv channel body => by
        simp only [CostProc.lift, CostProc.purseInventory,
          CostName.purseInventory_lift amount cutoff channel,
          CostTerm.purseInventory_lift amount (cutoff + 1) body]

  theorem CostTerm.purseInventory_lift {Ground : Type u}
      (amount cutoff : Nat) : ∀ term : CostTerm Ground,
      (term.lift amount cutoff).purseInventory = term.purseInventory
    | .nil => rfl
    | .signed process signature =>
        CostProc.purseInventory_lift amount cutoff process
    | .par left right => by
        simp only [CostTerm.lift, CostTerm.purseInventory,
          CostTerm.purseInventory_lift amount cutoff left,
          CostTerm.purseInventory_lift amount cutoff right]
    | .drop name => CostName.purseInventory_lift amount cutoff name
    | .purse location stack => by
        simp only [CostTerm.lift, CostTerm.purseInventory,
          CostName.purseInventory_lift amount cutoff location]
end

mutual
  theorem CostName.purseInventory_substitute {Ground : Type u}
      (payload : CostTerm Ground) (payloadFree : payload.PurseFree)
      (depth : Nat) : ∀ name : CostName Ground,
      (name.substitute payload depth).purseInventory = name.purseInventory
    | .bvar index => by
        simp only [CostName.substitute]
        split
        · simpa only [CostTerm.PurseFree, CostName.purseInventory,
            CostTerm.purseInventory_lift]
            using payloadFree
        · split <;> rfl
    | .quote term => rfl
    | .signature signature => rfl

  theorem CostProc.purseInventory_substitute {Ground : Type u}
      (payload : CostTerm Ground) (payloadFree : payload.PurseFree)
      (depth : Nat) : ∀ process : CostProc Ground,
      (process.substitute payload depth).purseInventory = process.purseInventory
    | .nil => rfl
    | .par left right => by
        simp only [CostProc.substitute, CostProc.purseInventory,
          CostProc.purseInventory_substitute payload payloadFree depth left,
          CostProc.purseInventory_substitute payload payloadFree depth right]
    | .send channel body => by
        simp only [CostProc.substitute, CostProc.purseInventory,
          CostName.purseInventory_substitute payload payloadFree depth channel,
          CostTerm.purseInventory_substitute payload payloadFree depth body]
    | .recv channel body => by
        simp only [CostProc.substitute, CostProc.purseInventory,
          CostName.purseInventory_substitute payload payloadFree depth channel,
          CostTerm.purseInventory_substitute payload payloadFree (depth + 1) body]

  theorem CostTerm.purseInventory_substitute {Ground : Type u}
      (payload : CostTerm Ground) (payloadFree : payload.PurseFree)
      (depth : Nat) : ∀ term : CostTerm Ground,
      (CostTerm.substitute payload depth term).purseInventory = term.purseInventory
    | .nil => rfl
    | .signed process signature =>
        CostProc.purseInventory_substitute payload payloadFree depth process
    | .par left right => by
        simp only [CostTerm.substitute, CostTerm.purseInventory,
          CostTerm.purseInventory_substitute payload payloadFree depth left,
          CostTerm.purseInventory_substitute payload payloadFree depth right]
    | .drop (.bvar index) => by
        simp only [CostTerm.substitute]
        split
        · simpa only [CostTerm.PurseFree, CostTerm.purseInventory, CostName.purseInventory,
            CostTerm.purseInventory_lift] using payloadFree
        · split <;> rfl
    | .drop (.quote term) => rfl
    | .drop (.signature signature) => rfl
    | .purse location stack => by
        simp only [CostTerm.substitute, CostTerm.purseInventory,
          CostName.purseInventory_substitute payload payloadFree depth location]
end

/-- Opening any receiving body with code-only payload preserves every stack. -/
theorem CostTerm.purseInventory_commSubst {Ground : Type u}
    (body payload : CostTerm Ground) (payloadFree : payload.PurseFree) :
    (body.commSubst payload).purseInventory = body.purseInventory :=
  CostTerm.purseInventory_substitute payload payloadFree 0 body

/-- The code-only payload discipline is stable under arbitrary binder depth. -/
theorem CostTerm.PurseFree.substitute {Ground : Type u}
    {body payload : CostTerm Ground} (bodyFree : body.PurseFree)
    (payloadFree : payload.PurseFree) (depth : Nat) :
    (CostTerm.substitute payload depth body).PurseFree := by
  change _ = 0
  rw [CostTerm.purseInventory_substitute payload payloadFree depth body]
  exact bodyFree

/-- An admitted code payload remains supported, binder-safe and purse-free. -/
theorem CostTerm.code_admission_commSubst {Ground : Type u}
    {body payload : CostTerm Ground}
    (bodySupported : body.RuntimeSupported)
    (payloadSupported : payload.RuntimeSupported)
    (bodySafe : body.BinderSafeAt 1) (payloadSafe : payload.BinderSafe)
    (bodyFree : body.PurseFree) (payloadFree : payload.PurseFree) :
    (body.commSubst payload).RuntimeSupported ∧
      (body.commSubst payload).BinderSafe ∧
      (body.commSubst payload).PurseFree :=
  ⟨CostTerm.runtimeSupported_commSubst bodySupported payloadSupported,
    bodySafe.commSubst payloadSafe, bodyFree.substitute payloadFree 0⟩

/-- A purse-free term has no active purse among its top-level components. -/
theorem CostTerm.PurseFree.no_component_purse {Ground : Type u}
    {term : CostTerm Ground} (free : term.PurseFree)
    (location : CostName Ground) (stack : CostStack Ground) :
    CostTerm.purse location stack ∉ term.components := by
  cases term with
  | nil => simp [CostTerm.components]
  | signed process signature => simp [CostTerm.components]
  | par left right =>
      have both : left.purseInventory = 0 ∧ right.purseInventory = 0 := by
        have zeroCard := congrArg Multiset.card free
        simp only [CostTerm.purseInventory, Multiset.card_add,
          Multiset.card_zero] at zeroCard
        exact ⟨Multiset.card_eq_zero.mp (by omega),
          Multiset.card_eq_zero.mp (by omega)⟩
      simpa only [CostTerm.components, Multiset.mem_add, not_or] using
        ⟨CostTerm.PurseFree.no_component_purse both.1 location stack,
          CostTerm.PurseFree.no_component_purse both.2 location stack⟩
  | drop name => simp [CostTerm.components]
  | purse purseLocation purseStack =>
      have zeroCard := congrArg Multiset.card free
      simp only [CostTerm.purseInventory, Multiset.card_add,
        Multiset.card_singleton, Multiset.card_zero] at zeroCard
      omega

/-- Redexes exposed by substitution still cannot fire without added funding. -/
theorem CostTerm.code_substitution_unfunded_blocked {Ground : Type u}
    {body payload : CostTerm Ground} (bodyFree : body.PurseFree)
    (payloadFree : payload.PurseFree)
    (location : CostName Ground) (spend : CostSig Ground)
    (target : CostConfig Ground) :
    ¬ CostStep (body.commSubst payload).components location spend target := by
  apply CostStep.blocked_of_no_funding_at
  intro head tail
  exact (bodyFree.substitute payloadFree 0).no_component_purse location (.cons head tail)

/-- COMM substitution copies a signed payload's seal without recomputing it. -/
theorem CostTerm.open_signed_payload {Ground : Type u}
    (process : CostProc Ground) (signature : CostSig Ground) :
    (CostTerm.drop (.bvar 0)).commSubst (.signed process signature) =
      .signed process signature := by
  simp [CostTerm.commSubst, CostTerm.substitute]

/-- A receiving body with two uses copies code, but does not invent a new seal. -/
theorem CostTerm.duplicate_signed_payload {Ground : Type u}
    (process : CostProc Ground) (signature : CostSig Ground) :
    (CostTerm.par (.drop (.bvar 0)) (.drop (.bvar 0))).commSubst
        (.signed process signature) =
      .par (.signed process signature) (.signed process signature) := by
  simp [CostTerm.commSubst, CostTerm.substitute]

/-- A receiving body that ignores its payload discards even nonempty latent
code.  This actual funded COMM spends only its outer seal and leaves the
context and exact purse tail intact. -/
theorem CostStep.discarded_payload_fires_only_outer {Ground : Type u}
    (context : CostConfig Ground) (channel : CostName Ground)
    (payload : CostTerm Ground) (signature : CostSig Ground)
    (valid : signature.RuntimeValid) (tail : CostStack Ground) :
    CostStep
      (context +
        {CostTerm.signed (.par (.recv channel .nil) (.send channel payload)) signature} +
        {CostTerm.purse channel (.cons signature tail)})
      channel signature (context + {CostTerm.purse channel tail}) := by
  simpa [CostTerm.commSubst, CostTerm.substitute, CostTerm.components] using
    CostStep.wholeRecvSend_single_head context channel .nil payload signature valid tail

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
