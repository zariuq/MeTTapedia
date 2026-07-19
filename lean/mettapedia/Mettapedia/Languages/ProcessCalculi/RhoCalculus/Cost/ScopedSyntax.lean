import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Erasure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RawConfig
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Step
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy

/-!
# Binder-safe cost syntax

The raw cost syntax uses natural-number binders and therefore contains values
that are not rho terms.  The judgments below isolate the genuine locally
nameless fragment.  Quotations seal surrounding binders, matching the
paper-facing COMM substitution: a quoted term must be closed with respect to
the surrounding process, although it may contain its own input binders.

This is a representation invariant over the existing cost syntax.  Erasure
derives the established `ProcWellSorted` judgment from the authored rho
presentation; no second rho carrier or reduction is introduced.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy

universe u

mutual
  /-- A cost name has no dangling de Bruijn index at `depth`.  A quotation
  seals the surrounding binders, so its process starts again at depth zero. -/
  inductive CostName.BinderSafeAt {Ground : Type u} :
      Nat → CostName Ground → Prop where
    | bvar {depth index} (inScope : index < depth) :
        CostName.BinderSafeAt depth (.bvar index)
    | quote {depth term} (termSafe : CostTerm.BinderSafeAt 0 term) :
        CostName.BinderSafeAt depth (.quote term)
    | signature {depth signature} :
        CostName.BinderSafeAt depth (.signature signature)

  /-- Binder safety through the process constructors. -/
  inductive CostProc.BinderSafeAt {Ground : Type u} :
      Nat → CostProc Ground → Prop where
    | nil {depth} : CostProc.BinderSafeAt depth .nil
    | par {depth left right} :
        CostProc.BinderSafeAt depth left →
        CostProc.BinderSafeAt depth right →
        CostProc.BinderSafeAt depth (.par left right)
    | send {depth channel payload} :
        CostName.BinderSafeAt depth channel →
        CostTerm.BinderSafeAt depth payload →
        CostProc.BinderSafeAt depth (.send channel payload)
    | recv {depth channel body} :
        CostName.BinderSafeAt depth channel →
        CostTerm.BinderSafeAt (depth + 1) body →
        CostProc.BinderSafeAt depth (.recv channel body)

  /-- Binder safety through cost wrappers.  Purses erase completely, so their
  funding locations do not participate in the pure process scope invariant. -/
  inductive CostTerm.BinderSafeAt {Ground : Type u} :
      Nat → CostTerm Ground → Prop where
    | nil {depth} : CostTerm.BinderSafeAt depth .nil
    | signed {depth process signature} :
        CostProc.BinderSafeAt depth process →
        CostTerm.BinderSafeAt depth (.signed process signature)
    | par {depth left right} :
        CostTerm.BinderSafeAt depth left →
        CostTerm.BinderSafeAt depth right →
        CostTerm.BinderSafeAt depth (.par left right)
    | drop {depth name} :
        CostName.BinderSafeAt depth name →
        CostTerm.BinderSafeAt depth (.drop name)
    | purse {depth surface stack} :
        CostTerm.BinderSafeAt depth (.purse surface stack)
end

mutual
  /-- A lift whose cutoff is outside the available scope cannot create a
  dangling name. -/
  theorem CostName.BinderSafeAt.liftAbove {Ground : Type u}
      {scope cutoff amount : Nat} {name : CostName Ground}
      (safe : name.BinderSafeAt scope) (scopeLe : scope ≤ cutoff) :
      (name.lift amount cutoff).BinderSafeAt scope := by
    cases safe with
    | bvar inScope =>
        have belowCutoff : ¬ cutoff ≤ _ :=
          Nat.not_le.mpr (Nat.lt_of_lt_of_le inScope scopeLe)
        simpa [CostName.lift, belowCutoff] using CostName.BinderSafeAt.bvar inScope
    | quote termSafe => exact .quote termSafe
    | signature => exact .signature

  /-- Process form of lifting above the available scope. -/
  theorem CostProc.BinderSafeAt.liftAbove {Ground : Type u}
      {scope cutoff amount : Nat} {process : CostProc Ground}
      (safe : process.BinderSafeAt scope) (scopeLe : scope ≤ cutoff) :
      (process.lift amount cutoff).BinderSafeAt scope := by
    cases safe with
    | nil => exact .nil
    | par leftSafe rightSafe =>
        exact .par (leftSafe.liftAbove scopeLe) (rightSafe.liftAbove scopeLe)
    | send channelSafe payloadSafe =>
        exact .send (channelSafe.liftAbove scopeLe)
          (payloadSafe.liftAbove scopeLe)
    | recv channelSafe bodySafe =>
        exact .recv (channelSafe.liftAbove scopeLe)
          (bodySafe.liftAbove (Nat.add_le_add_right scopeLe 1))

  /-- Term form of lifting above the available scope. -/
  theorem CostTerm.BinderSafeAt.liftAbove {Ground : Type u}
      {scope cutoff amount : Nat} {term : CostTerm Ground}
      (safe : term.BinderSafeAt scope) (scopeLe : scope ≤ cutoff) :
      (term.lift amount cutoff).BinderSafeAt scope := by
    cases safe with
    | nil => exact .nil
    | signed processSafe => exact .signed (processSafe.liftAbove scopeLe)
    | par leftSafe rightSafe =>
        exact .par (leftSafe.liftAbove scopeLe) (rightSafe.liftAbove scopeLe)
    | drop nameSafe => exact .drop (nameSafe.liftAbove scopeLe)
    | purse => exact .purse
end

/-- Top-level binder safety. -/
abbrev CostTerm.BinderSafe {Ground : Type u} (term : CostTerm Ground) : Prop :=
  term.BinderSafeAt 0

/-- Every top-level component of a normalized configuration is binder-safe. -/
def CostConfig.BinderSafe {Ground : Type u} (config : CostConfig Ground) : Prop :=
  ∀ term ∈ config, term.BinderSafe

mutual
  /-- The executable name checker recognizes exactly the decoded binder-safe
  names. -/
  theorem RawCostName.binderSafeAt_iff_decode (depth : Nat) :
      ∀ name : RawCostName,
        name.binderSafeAt depth = true ↔
          (decodeCostName name).BinderSafeAt depth
    | .bvar index => by
        constructor
        · intro checked
          exact .bvar (by simpa [RawCostName.binderSafeAt] using checked)
        · intro safe
          cases safe with
          | bvar inScope => simpa [RawCostName.binderSafeAt] using inScope
    | .quote term => by
        constructor
        · intro checked
          exact .quote
            ((RawCostTerm.binderSafeAt_iff_decode 0 term).mp checked)
        · intro safe
          cases safe with
          | quote termSafe =>
              exact (RawCostTerm.binderSafeAt_iff_decode 0 term).mpr termSafe
    | .signature signature => by
        constructor
        · intro _; exact .signature
        · intro _; rfl

  /-- The executable process checker recognizes exactly the decoded
  binder-safe processes. -/
  theorem RawCostProc.binderSafeAt_iff_decode (depth : Nat) :
      ∀ process : RawCostProc,
        process.binderSafeAt depth = true ↔
          (decodeCostProc process).BinderSafeAt depth
    | .nil => by
        constructor
        · intro _; exact .nil
        · intro _; rfl
    | .par left right => by
        rw [RawCostProc.binderSafeAt, Bool.and_eq_true,
          RawCostProc.binderSafeAt_iff_decode depth left,
          RawCostProc.binderSafeAt_iff_decode depth right]
        constructor
        · rintro ⟨leftSafe, rightSafe⟩
          exact .par leftSafe rightSafe
        · intro safe
          cases safe with
          | par leftSafe rightSafe => exact ⟨leftSafe, rightSafe⟩
    | .send channel payload => by
        rw [RawCostProc.binderSafeAt, Bool.and_eq_true,
          RawCostName.binderSafeAt_iff_decode depth channel,
          RawCostTerm.binderSafeAt_iff_decode depth payload]
        constructor
        · rintro ⟨channelSafe, payloadSafe⟩
          exact .send channelSafe payloadSafe
        · intro safe
          cases safe with
          | send channelSafe payloadSafe => exact ⟨channelSafe, payloadSafe⟩
    | .recv channel body => by
        rw [RawCostProc.binderSafeAt, Bool.and_eq_true,
          RawCostName.binderSafeAt_iff_decode depth channel,
          RawCostTerm.binderSafeAt_iff_decode (depth + 1) body]
        constructor
        · rintro ⟨channelSafe, bodySafe⟩
          exact .recv channelSafe bodySafe
        · intro safe
          cases safe with
          | recv channelSafe bodySafe => exact ⟨channelSafe, bodySafe⟩

  /-- The executable term checker recognizes exactly the decoded binder-safe
  cost terms. -/
  theorem RawCostTerm.binderSafeAt_iff_decode (depth : Nat) :
      ∀ term : RawCostTerm,
        term.binderSafeAt depth = true ↔
          (decodeCostTerm term).BinderSafeAt depth
    | .nil => by
        constructor
        · intro _; exact .nil
        · intro _; rfl
    | .signed process signature => by
        rw [RawCostTerm.binderSafeAt,
          RawCostProc.binderSafeAt_iff_decode depth process]
        constructor
        · intro processSafe; exact .signed processSafe
        · intro safe
          cases safe with
          | signed processSafe => exact processSafe
    | .par left right => by
        rw [RawCostTerm.binderSafeAt, Bool.and_eq_true,
          RawCostTerm.binderSafeAt_iff_decode depth left,
          RawCostTerm.binderSafeAt_iff_decode depth right]
        constructor
        · rintro ⟨leftSafe, rightSafe⟩
          exact .par leftSafe rightSafe
        · intro safe
          cases safe with
          | par leftSafe rightSafe => exact ⟨leftSafe, rightSafe⟩
    | .drop name => by
        rw [RawCostTerm.binderSafeAt,
          RawCostName.binderSafeAt_iff_decode depth name]
        constructor
        · intro nameSafe; exact .drop nameSafe
        · intro safe
          cases safe with
          | drop nameSafe => exact nameSafe
    | .purse surface stack => by
        constructor
        · intro _; exact .purse
        · intro _; rfl
end

/-- Top-level raw scope checking is exact after decoding. -/
theorem RawCostTerm.binderSafe_iff_decode (term : RawCostTerm) :
    term.binderSafe = true ↔ (decodeCostTerm term).BinderSafe := by
  exact RawCostTerm.binderSafeAt_iff_decode 0 term

mutual
  /-- Whole-object runtime scope implies the pure-erasure scope check for
  names. -/
  theorem RawCostName.runtimeBinderSafeAt_implies_binderSafeAt
      (depth : Nat) : ∀ name : RawCostName,
      name.runtimeBinderSafeAt depth = true →
        name.binderSafeAt depth = true
    | .bvar index => by
        simp [RawCostName.runtimeBinderSafeAt,
          RawCostName.binderSafeAt]
    | .quote term => by
        intro checked
        exact RawCostTerm.runtimeBinderSafeAt_implies_binderSafeAt 0 term
          checked
    | .signature signature => by
        intro _
        rfl

  /-- Whole-object runtime scope implies the pure-erasure scope check for
  processes. -/
  theorem RawCostProc.runtimeBinderSafeAt_implies_binderSafeAt
      (depth : Nat) : ∀ process : RawCostProc,
      process.runtimeBinderSafeAt depth = true →
        process.binderSafeAt depth = true
    | .nil => by intro _; rfl
    | .par left right => by
        intro checked
        simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true]
          at checked
        have leftChecked := checked.1
        have rightChecked := checked.2
        rw [RawCostProc.binderSafeAt, Bool.and_eq_true]
        exact ⟨RawCostProc.runtimeBinderSafeAt_implies_binderSafeAt depth left
              leftChecked,
            RawCostProc.runtimeBinderSafeAt_implies_binderSafeAt depth right
              rightChecked⟩
    | .send channel payload => by
        intro checked
        simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true]
          at checked
        have channelChecked := checked.1
        have payloadChecked := checked.2
        rw [RawCostProc.binderSafeAt, Bool.and_eq_true]
        exact ⟨RawCostName.runtimeBinderSafeAt_implies_binderSafeAt depth channel
              channelChecked,
            RawCostTerm.runtimeBinderSafeAt_implies_binderSafeAt depth payload
              payloadChecked⟩
    | .recv channel body => by
        intro checked
        simp only [RawCostProc.runtimeBinderSafeAt, Bool.and_eq_true]
          at checked
        have channelChecked := checked.1
        have bodyChecked := checked.2
        rw [RawCostProc.binderSafeAt, Bool.and_eq_true]
        exact ⟨RawCostName.runtimeBinderSafeAt_implies_binderSafeAt depth channel
              channelChecked,
            RawCostTerm.runtimeBinderSafeAt_implies_binderSafeAt (depth + 1)
              body bodyChecked⟩

  /-- Whole-object runtime scope implies the pure-erasure scope check for
  cost terms.  The purse case is the deliberate strictness difference. -/
  theorem RawCostTerm.runtimeBinderSafeAt_implies_binderSafeAt
      (depth : Nat) : ∀ term : RawCostTerm,
      term.runtimeBinderSafeAt depth = true →
        term.binderSafeAt depth = true
    | .nil => by intro _; rfl
    | .signed process signature => by
        intro checked
        exact RawCostProc.runtimeBinderSafeAt_implies_binderSafeAt depth
          process checked
    | .par left right => by
        intro checked
        simp only [RawCostTerm.runtimeBinderSafeAt, Bool.and_eq_true]
          at checked
        have leftChecked := checked.1
        have rightChecked := checked.2
        rw [RawCostTerm.binderSafeAt, Bool.and_eq_true]
        exact ⟨RawCostTerm.runtimeBinderSafeAt_implies_binderSafeAt depth left
              leftChecked,
            RawCostTerm.runtimeBinderSafeAt_implies_binderSafeAt depth right
              rightChecked⟩
    | .drop name => by
        intro checked
        exact RawCostName.runtimeBinderSafeAt_implies_binderSafeAt depth name
          checked
    | .purse surface stack => by
        intro _
        rfl
end

/-- Whole-object top-level scope implies the pure-erasure scope check. -/
theorem RawCostTerm.runtimeBinderSafe_implies_binderSafe
    {term : RawCostTerm} (checked : term.runtimeBinderSafe = true) :
    term.binderSafe = true :=
  RawCostTerm.runtimeBinderSafeAt_implies_binderSafeAt 0 term checked

/-- Public raw-input admission is grammar validity plus whole-object runtime
scope, including purse locations. -/
theorem RawCostTerm.supported_iff (term : RawCostTerm) :
    term.supported = true ↔
      term.wellFormed = true ∧ term.runtimeBinderSafe = true := by
  rw [RawCostTerm.supported, Bool.and_eq_true]

/-- Public admission discharges the pure-erasure binder-safety premise. -/
theorem RawCostTerm.supported_decode_binderSafe {term : RawCostTerm}
    (supported : term.supported = true) :
    (decodeCostTerm term).BinderSafe := by
  apply (RawCostTerm.binderSafe_iff_decode term).mp
  exact RawCostTerm.runtimeBinderSafe_implies_binderSafe
    ((RawCostTerm.supported_iff term).mp supported).2

/-- A raw component list is scope-safe exactly when its decoded cost
configuration is binder-safe. -/
theorem RawCostConfig.binderSafe_iff_decode (config : RawCostConfig) :
    config.Forall (fun term => term.binderSafe = true) ↔
      (decodeRawConfig config).BinderSafe := by
  constructor
  · intro checked term membership
    change term ∈ (config.map decodeCostTerm : Multiset (CostTerm String))
      at membership
    rw [Multiset.mem_coe] at membership
    obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp membership
    exact (RawCostTerm.binderSafe_iff_decode raw).mp
      (List.forall_iff_forall_mem.mp checked raw rawMember)
  · intro decodedSafe
    rw [List.forall_iff_forall_mem]
    intro raw rawMember
    apply (RawCostTerm.binderSafe_iff_decode raw).mpr
    apply decodedSafe (decodeCostTerm raw)
    change decodeCostTerm raw ∈
      (config.map decodeCostTerm : Multiset (CostTerm String))
    rw [Multiset.mem_coe]
    exact List.mem_map.mpr ⟨raw, rawMember, rfl⟩

mutual
  /-- Adding available surrounding binders preserves name safety. -/
  theorem CostName.BinderSafeAt.mono {Ground : Type u}
      {small large : Nat} {name : CostName Ground}
      (safe : name.BinderSafeAt small) (le : small ≤ large) :
      name.BinderSafeAt large := by
    cases safe with
    | bvar inScope => exact .bvar (Nat.lt_of_lt_of_le inScope le)
    | quote termSafe => exact .quote termSafe
    | signature => exact .signature

  /-- Adding available surrounding binders preserves process safety. -/
  theorem CostProc.BinderSafeAt.mono {Ground : Type u}
      {small large : Nat} {process : CostProc Ground}
      (safe : process.BinderSafeAt small) (le : small ≤ large) :
      process.BinderSafeAt large := by
    cases safe with
    | nil => exact .nil
    | par leftSafe rightSafe =>
        exact .par (leftSafe.mono le) (rightSafe.mono le)
    | send channelSafe payloadSafe =>
        exact .send (channelSafe.mono le) (payloadSafe.mono le)
    | recv channelSafe bodySafe =>
        exact .recv (channelSafe.mono le)
          (bodySafe.mono (Nat.add_le_add_right le 1))

  /-- Adding available surrounding binders preserves term safety. -/
  theorem CostTerm.BinderSafeAt.mono {Ground : Type u}
      {small large : Nat} {term : CostTerm Ground}
      (safe : term.BinderSafeAt small) (le : small ≤ large) :
      term.BinderSafeAt large := by
    cases safe with
    | nil => exact .nil
    | signed processSafe => exact .signed (processSafe.mono le)
    | par leftSafe rightSafe =>
        exact .par (leftSafe.mono le) (rightSafe.mono le)
    | drop nameSafe => exact .drop (nameSafe.mono le)
    | purse => exact .purse
end

mutual
  /-- Eliminating the distinguished binder preserves name safety. -/
  theorem CostName.BinderSafeAt.substitute {Ground : Type u}
      {depth : Nat} {name : CostName Ground} {replacement : CostTerm Ground}
      (safe : name.BinderSafeAt (depth + 1))
      (replacementSafe : replacement.BinderSafe) :
      (CostName.substitute replacement depth name).BinderSafeAt depth := by
    cases safe with
    | bvar inScope =>
        simp only [CostName.substitute]
        split
        next matched =>
          exact .quote (replacementSafe.liftAbove
            (scope := 0) (cutoff := 0) (amount := depth) (le_refl 0))
        next notMatched =>
          split
          next higher => omega
          next lower => exact .bvar (by omega)
    | quote termSafe => exact .quote termSafe
    | signature => exact .signature

  /-- Eliminating the distinguished binder preserves process safety. -/
  theorem CostProc.BinderSafeAt.substitute {Ground : Type u}
      {depth : Nat} {process : CostProc Ground} {replacement : CostTerm Ground}
      (safe : process.BinderSafeAt (depth + 1))
      (replacementSafe : replacement.BinderSafe) :
      (CostProc.substitute replacement depth process).BinderSafeAt depth := by
    cases safe with
    | nil => exact .nil
    | par leftSafe rightSafe =>
        exact .par (leftSafe.substitute replacementSafe)
          (rightSafe.substitute replacementSafe)
    | send channelSafe payloadSafe =>
        exact .send (channelSafe.substitute replacementSafe)
          (payloadSafe.substitute replacementSafe)
    | recv channelSafe bodySafe =>
        exact .recv (channelSafe.substitute replacementSafe) (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            bodySafe.substitute replacementSafe)

  /-- Eliminating the distinguished binder preserves term safety. -/
  theorem CostTerm.BinderSafeAt.substitute {Ground : Type u}
      {depth : Nat} {term replacement : CostTerm Ground}
      (safe : term.BinderSafeAt (depth + 1))
      (replacementSafe : replacement.BinderSafe) :
      (CostTerm.substitute replacement depth term).BinderSafeAt depth := by
    cases safe with
    | nil => exact .nil
    | signed processSafe =>
        exact .signed (processSafe.substitute replacementSafe)
    | par leftSafe rightSafe =>
        exact .par (leftSafe.substitute replacementSafe)
          (rightSafe.substitute replacementSafe)
    | drop nameSafe =>
        cases nameSafe with
        | bvar inScope =>
            simp only [CostTerm.substitute]
            split
            next matched =>
              exact (replacementSafe.liftAbove
                (scope := 0) (cutoff := 0) (amount := depth) (le_refl 0)).mono
                  (Nat.zero_le depth)
            next notMatched =>
              split
              next higher => omega
              next lower => exact .drop (.bvar (by omega))
        | quote termSafe => exact .drop (.quote termSafe)
        | signature => exact .drop .signature
    | purse => exact .purse
end

/-- COMM opens one binder and therefore maps a safe body and closed payload to
a closed contractum. -/
theorem CostTerm.BinderSafeAt.commSubst {Ground : Type u}
    {body payload : CostTerm Ground}
    (bodySafe : body.BinderSafeAt 1) (payloadSafe : payload.BinderSafe) :
    (body.commSubst payload).BinderSafe := by
  exact bodySafe.substitute payloadSafe

/-! ## Configuration preservation -/

/-- The empty configuration is binder-safe. -/
theorem CostConfig.BinderSafe.zero {Ground : Type u} :
    (0 : CostConfig Ground).BinderSafe := by
  intro term membership
  simp at membership

/-- Binder safety is closed under multiset addition. -/
theorem CostConfig.BinderSafe.add {Ground : Type u}
    {left right : CostConfig Ground}
    (leftSafe : left.BinderSafe) (rightSafe : right.BinderSafe) :
    (left + right).BinderSafe := by
  intro term membership
  rw [Multiset.mem_add] at membership
  exact membership.elim (leftSafe term) (rightSafe term)

/-- A binder-safe term yields a binder-safe singleton configuration. -/
theorem CostTerm.BinderSafe.singleton {Ground : Type u}
    {term : CostTerm Ground} (safe : term.BinderSafe) :
    CostConfig.BinderSafe (term ::ₘ 0) := by
  intro candidate membership
  have equality : candidate = term := by simpa using membership
  subst equality
  exact safe

/-- Flattening a safe top-level parallel term preserves binder safety of every
resulting component. -/
theorem CostTerm.BinderSafe.components {Ground : Type u} :
    ∀ {term : CostTerm Ground}, term.BinderSafe → term.components.BinderSafe
  | .nil, _ => CostConfig.BinderSafe.zero
  | .par left right, safe => by
      cases safe with
      | par leftSafe rightSafe =>
          exact (CostTerm.BinderSafe.components leftSafe).add
            (CostTerm.BinderSafe.components rightSafe)
  | .signed process signature, safe => safe.singleton
  | .drop name, safe => safe.singleton
  | .purse surface stack, safe => safe.singleton

/-- Located purse configurations erase computationally and are binder-safe
regardless of their bookkeeping locations. -/
theorem LocatedPurse.configComponents_binderSafe {Ground : Type u}
    (purses : Multiset (LocatedPurse Ground)) :
    (LocatedPurse.configComponents purses).BinderSafe := by
  intro term membership
  rw [LocatedPurse.configComponents, Multiset.mem_map] at membership
  rcases membership with ⟨purse, _, rfl⟩
  exact .purse

/-- A safe subconfiguration remains safe when viewed inside a larger sum. -/
theorem CostConfig.BinderSafe.of_left_add {Ground : Type u}
    {left right : CostConfig Ground} (safe : (left + right).BinderSafe) :
    left.BinderSafe := by
  intro term membership
  exact safe term (Multiset.mem_add.mpr (Or.inl membership))

/-- Every declarative funded step preserves the genuine scoped fragment. -/
theorem CostStep.preserves_binderSafe {Ground : Type u}
    {source target : CostConfig Ground} {channel : CostName Ground}
    {demand : CostSig Ground}
    (step : CostStep source channel demand target)
    (sourceSafe : source.BinderSafe) :
    target.BinderSafe := by
  cases step with
  | @wholeRecvSend context available residual stepChannel body payload outerSig
      signatureValid cover =>
      have redexSafe :
          (CostTerm.signed
            (.par (.recv channel body) (.send channel payload)) demand).BinderSafe :=
        sourceSafe _ (by simp)
      have contextSafe : context.BinderSafe := by
        intro term membership
        exact sourceSafe term (by simp [membership])
      cases redexSafe with
      | signed processSafe =>
          cases processSafe with
          | par receiveSafe sendSafe =>
              cases receiveSafe with
              | recv channelSafe bodySafe =>
                  cases sendSafe with
                  | send sendChannelSafe payloadSafe =>
                      exact (contextSafe.add
                        (bodySafe.commSubst payloadSafe).components).add
                          (LocatedPurse.configComponents_binderSafe residual)
  | @wholeSendRecv context available residual stepChannel body payload outerSig
      signatureValid cover =>
      have redexSafe :
          (CostTerm.signed
            (.par (.send channel payload) (.recv channel body)) demand).BinderSafe :=
        sourceSafe _ (by simp)
      have contextSafe : context.BinderSafe := by
        intro term membership
        exact sourceSafe term (by simp [membership])
      cases redexSafe with
      | signed processSafe =>
          cases processSafe with
          | par sendSafe receiveSafe =>
              cases sendSafe with
              | send sendChannelSafe payloadSafe =>
                  cases receiveSafe with
                  | recv channelSafe bodySafe =>
                      exact (contextSafe.add
                        (bodySafe.commSubst payloadSafe).components).add
                          (LocatedPurse.configComponents_binderSafe residual)
  | @split context available residual stepChannel body payload recvSeal sendSeal
      recvValid sendValid cover =>
      have receiveSafe :
          (CostTerm.signed (.recv channel body) recvSeal).BinderSafe :=
        sourceSafe _ (by simp)
      have sendSafe :
          (CostTerm.signed (.send channel payload) sendSeal).BinderSafe :=
        sourceSafe _ (by simp)
      have contextSafe : context.BinderSafe := by
        intro term membership
        exact sourceSafe term (by simp [membership])
      cases receiveSafe with
      | signed receiveProcessSafe =>
          cases receiveProcessSafe with
          | recv receiveChannelSafe bodySafe =>
              cases sendSafe with
              | signed sendProcessSafe =>
                  cases sendProcessSafe with
                  | send sendChannelSafe payloadSafe =>
                      exact (contextSafe.add
                        (bodySafe.commSubst payloadSafe).components).add
                          (LocatedPurse.configComponents_binderSafe residual)


/-! ## Derived rho shape and opacity facts -/

mutual
  /-- A derived name cannot contain an index at or above its context length. -/
  theorem nameWellSorted_noBVarAtOrAbove
      {free : FreeSortContext} {bound : List String} {name : Pattern}
      (typed : NameWellSorted rhoReflectivePresentation free bound name)
      {index : Nat} (outside : bound.length ≤ index) :
      noBVar index name = true := by
    cases typed with
    | bvar lookup =>
        have inScope := (List.getElem?_eq_some_iff.mp lookup).1
        simp only [noBVar, bne_iff_ne]
        omega
    | fvar => simp [noBVar]
    | quote processTyped =>
        simpa [noBVar, noBVarList] using
          procWellSorted_noBVarAtOrAbove processTyped outside

  /-- Process form of the out-of-scope-index exclusion. -/
  theorem procWellSorted_noBVarAtOrAbove
      {free : FreeSortContext} {bound : List String} {process : Pattern}
      (typed : ProcWellSorted rhoReflectivePresentation free bound process)
      {index : Nat} (outside : bound.length ≤ index) :
      noBVar index process = true := by
    cases typed with
    | bvar lookup =>
        have inScope := (List.getElem?_eq_some_iff.mp lookup).1
        simp only [noBVar, bne_iff_ne]
        omega
    | fvar => simp [noBVar]
    | unit => simp [noBVar, noBVarList]
    | drop nameTyped =>
        simpa [noBVar, noBVarList] using
          nameWellSorted_noBVarAtOrAbove nameTyped outside
    | output channelTyped payloadTyped =>
        simp [noBVar, noBVarList,
          nameWellSorted_noBVarAtOrAbove channelTyped outside,
          procWellSorted_noBVarAtOrAbove payloadTyped outside]
    | input channelTyped bodyTyped =>
        have bodyOutside :
            (rhoReflectivePresentation.nameSort :: bound).length ≤ index + 1 := by
          simp
          omega
        simp [noBVar, noBVarList,
          nameWellSorted_noBVarAtOrAbove channelTyped outside,
          procWellSorted_noBVarAtOrAbove bodyTyped bodyOutside]
    | parallel processesTyped =>
        simpa [noBVar] using
          procListWellSorted_noBVarListAtOrAbove processesTyped outside

  /-- List form of the out-of-scope-index exclusion. -/
  theorem procListWellSorted_noBVarListAtOrAbove
      {free : FreeSortContext} {bound : List String} {processes : List Pattern}
      (typed : ProcListWellSorted rhoReflectivePresentation free bound processes)
      {index : Nat} (outside : bound.length ≤ index) :
      noBVarList index processes = true := by
    cases typed with
    | nil => simp [noBVarList]
    | cons processTyped processesTyped =>
        simp [noBVarList,
          procWellSorted_noBVarAtOrAbove processTyped outside,
          procListWellSorted_noBVarListAtOrAbove processesTyped outside]
end

mutual
  /-- Derived names have exactly the authored rho name shape. -/
  theorem nameWellSorted_rhoCoreShape
      {free : FreeSortContext} {bound : List String} {name : Pattern}
      (typed : NameWellSorted rhoReflectivePresentation free bound name) :
      rhoNameCoreShape name = true := by
    cases typed with
    | bvar => rfl
    | fvar => rfl
    | quote processTyped =>
        simpa [rhoNameCoreShape, rhoReflectivePresentation] using
          procWellSorted_rhoCoreShape processTyped

  /-- Derived processes have exactly the authored rho process shape. -/
  theorem procWellSorted_rhoCoreShape
      {free : FreeSortContext} {bound : List String} {process : Pattern}
      (typed : ProcWellSorted rhoReflectivePresentation free bound process) :
      rhoProcCoreShape process = true := by
    cases typed with
    | bvar => rfl
    | fvar => rfl
    | unit => rfl
    | drop nameTyped =>
        simpa [rhoProcCoreShape, rhoReflectivePresentation] using
          nameWellSorted_rhoCoreShape nameTyped
    | output channelTyped payloadTyped =>
        simp [rhoProcCoreShape, rhoReflectivePresentation,
          nameWellSorted_rhoCoreShape channelTyped,
          procWellSorted_rhoCoreShape payloadTyped]
    | input channelTyped bodyTyped =>
        simp [rhoProcCoreShape, rhoReflectivePresentation,
          nameWellSorted_rhoCoreShape channelTyped,
          procWellSorted_rhoCoreShape bodyTyped]
    | parallel processesTyped =>
        simpa [rhoProcCoreShape, rhoReflectivePresentation] using
          procListWellSorted_rhoCoreShapeList processesTyped

  /-- List form of authored rho shape. -/
  theorem procListWellSorted_rhoCoreShapeList
      {free : FreeSortContext} {bound : List String} {processes : List Pattern}
      (typed : ProcListWellSorted rhoReflectivePresentation free bound processes) :
      rhoProcCoreShapeList processes = true := by
    cases typed with
    | nil => simp [rhoProcCoreShapeList]
    | cons processTyped processesTyped =>
        simp [rhoProcCoreShapeList, procWellSorted_rhoCoreShape processTyped,
          procListWellSorted_rhoCoreShapeList processesTyped]
end

mutual
  /-- An index outside the derived name context is absent beneath quotations. -/
  theorem nameWellSorted_noBoundUnderQuoteAtOrAbove
      {free : FreeSortContext} {bound : List String} {name : Pattern}
      (typed : NameWellSorted rhoReflectivePresentation free bound name)
      {index : Nat} (outside : bound.length ≤ index) :
      noBoundUnderQuote index name = true := by
    cases typed with
    | bvar => rfl
    | fvar => simp [noBoundUnderQuote]
    | quote processTyped =>
        simpa [noBoundUnderQuote, rhoReflectivePresentation] using
          procWellSorted_noBVarAtOrAbove processTyped outside

  /-- Process form of quote-opacity outside the derived context. -/
  theorem procWellSorted_noBoundUnderQuoteAtOrAbove
      {free : FreeSortContext} {bound : List String} {process : Pattern}
      (typed : ProcWellSorted rhoReflectivePresentation free bound process)
      {index : Nat} (outside : bound.length ≤ index) :
      noBoundUnderQuote index process = true := by
    cases typed with
    | bvar => rfl
    | fvar => simp [noBoundUnderQuote]
    | unit => simp [noBoundUnderQuote, noBoundUnderQuoteList]
    | drop nameTyped =>
        simpa [noBoundUnderQuote, noBoundUnderQuoteList,
          rhoReflectivePresentation] using
          nameWellSorted_noBoundUnderQuoteAtOrAbove nameTyped outside
    | output channelTyped payloadTyped =>
        simp [noBoundUnderQuote, noBoundUnderQuoteList,
          rhoReflectivePresentation,
          nameWellSorted_noBoundUnderQuoteAtOrAbove channelTyped outside,
          procWellSorted_noBoundUnderQuoteAtOrAbove payloadTyped outside]
    | input channelTyped bodyTyped =>
        have bodyOutside :
            (rhoReflectivePresentation.nameSort :: bound).length ≤ index + 1 := by
          simp
          omega
        simp [noBoundUnderQuote, noBoundUnderQuoteList,
          rhoReflectivePresentation,
          nameWellSorted_noBoundUnderQuoteAtOrAbove channelTyped outside,
          procWellSorted_noBoundUnderQuoteAtOrAbove bodyTyped bodyOutside]
    | parallel processesTyped =>
        simpa [noBoundUnderQuote, rhoReflectivePresentation] using
          procListWellSorted_noBoundUnderQuoteListAtOrAbove processesTyped outside

  /-- List form of quote-opacity outside the derived context. -/
  theorem procListWellSorted_noBoundUnderQuoteListAtOrAbove
      {free : FreeSortContext} {bound : List String} {processes : List Pattern}
      (typed : ProcListWellSorted rhoReflectivePresentation free bound processes)
      {index : Nat} (outside : bound.length ≤ index) :
      noBoundUnderQuoteList index processes = true := by
    cases typed with
    | nil => simp [noBoundUnderQuoteList]
    | cons processTyped processesTyped =>
        simp [noBoundUnderQuoteList,
          procWellSorted_noBoundUnderQuoteAtOrAbove processTyped outside,
          procListWellSorted_noBoundUnderQuoteListAtOrAbove processesTyped outside]
end

/-- A signature interpretation is well sorted when every signature denotes a
closed name derived from the authored rho presentation. -/
def SignatureNameEncoding.WellSorted {Ground : Type u}
    (signatureName : SignatureNameEncoding Ground) (free : FreeSortContext) : Prop :=
  ∀ signature,
    NameWellSorted rhoReflectivePresentation free [] (signatureName signature)

mutual
  /-- Binder-safe names erase to the existing derived name judgment. -/
  theorem CostName.BinderSafeAt.erase_wellSorted {Ground : Type u}
      {signatureName : SignatureNameEncoding Ground} {free : FreeSortContext}
      (signatureTyped : signatureName.WellSorted free)
      {depth : Nat} {name : CostName Ground} (safe : name.BinderSafeAt depth) :
      NameWellSorted rhoReflectivePresentation free
        (List.replicate depth rhoReflectivePresentation.nameSort)
        (name.erase signatureName) := by
    cases safe with
    | bvar inScope =>
        apply NameWellSorted.bvar
        simp [inScope]
    | quote termSafe =>
        apply NameWellSorted.quote
        have typed := termSafe.erase_wellSorted signatureTyped
        simpa using typed.weakenBoundRight
          (List.replicate depth rhoReflectivePresentation.nameSort)
    | signature =>
        simpa [CostName.erase] using (signatureTyped _).weakenBoundRight
          (List.replicate depth rhoReflectivePresentation.nameSort)

  /-- Binder-safe processes erase to the existing derived process judgment. -/
  theorem CostProc.BinderSafeAt.erase_wellSorted {Ground : Type u}
      {signatureName : SignatureNameEncoding Ground} {free : FreeSortContext}
      (signatureTyped : signatureName.WellSorted free)
      {depth : Nat} {process : CostProc Ground} (safe : process.BinderSafeAt depth) :
      ProcWellSorted rhoReflectivePresentation free
        (List.replicate depth rhoReflectivePresentation.nameSort)
        (process.erase signatureName) := by
    cases safe with
    | nil => exact .parallel .nil
    | par leftSafe rightSafe =>
        exact .parallel (.cons (leftSafe.erase_wellSorted signatureTyped)
          (.cons (rightSafe.erase_wellSorted signatureTyped) .nil))
    | send channelSafe payloadSafe =>
        exact .output (channelSafe.erase_wellSorted signatureTyped)
          (payloadSafe.erase_wellSorted signatureTyped)
    | recv channelSafe bodySafe =>
        exact .input (channelSafe.erase_wellSorted signatureTyped) (by
          simpa [List.replicate_succ] using
            bodySafe.erase_wellSorted signatureTyped)

  /-- Binder-safe cost terms erase to the existing derived process judgment. -/
  theorem CostTerm.BinderSafeAt.erase_wellSorted {Ground : Type u}
      {signatureName : SignatureNameEncoding Ground} {free : FreeSortContext}
      (signatureTyped : signatureName.WellSorted free)
      {depth : Nat} {term : CostTerm Ground} (safe : term.BinderSafeAt depth) :
      ProcWellSorted rhoReflectivePresentation free
        (List.replicate depth rhoReflectivePresentation.nameSort)
        (term.erase signatureName) := by
    cases safe with
    | nil => exact .parallel .nil
    | signed processSafe => exact processSafe.erase_wellSorted signatureTyped
    | par leftSafe rightSafe =>
        exact .parallel (.cons (leftSafe.erase_wellSorted signatureTyped)
          (.cons (rightSafe.erase_wellSorted signatureTyped) .nil))
    | drop nameSafe => exact .drop (nameSafe.erase_wellSorted signatureTyped)
    | purse => exact .parallel .nil
end

/-! ## Controls -/

/-- Positive: the defining substituted drop is binder-safe. -/
example {Ground : Type u} :
    (CostTerm.drop (.bvar 0) : CostTerm Ground).BinderSafeAt 1 :=
  .drop (.bvar (by omega))

/-- Positive: opening the defining drop with nil produces a closed term. -/
example {Ground : Type u} :
    ((CostTerm.drop (.bvar 0) : CostTerm Ground).commSubst .nil).BinderSafe :=
  CostTerm.BinderSafeAt.commSubst (.drop (.bvar (by omega))) .nil

/-- Negative: a quotation cannot capture the surrounding COMM binder. -/
theorem quoted_surrounding_binder_not_safe {Ground : Type u} :
    ¬(CostTerm.drop (.quote (.drop (.bvar 0))) : CostTerm Ground).BinderSafeAt 1 := by
  intro safe
  cases safe with
  | drop nameSafe =>
      cases nameSafe with
      | quote termSafe =>
          cases termSafe with
          | drop indexSafe =>
              cases indexSafe with
              | bvar inScope => omega

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
