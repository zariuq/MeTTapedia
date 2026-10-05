import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSourceInventory
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBinaryResidual
import Mettapedia.Languages.LambdaCalculus.NamePassingReturningLambda

/-!
# Private call ownership recovers the actual source beta site

Each application owns the private channel named by its constructor address.
Matching a binary call against the independently computed source inventory
forces the listener to be its function's returning lambda. Definitions and
one-shot declarations on that path are retained, while nested applications
own different private channels. The resulting certificate identifies both
source origins and computes the source successor before target execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBinaryOwnership

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingActiveOrigins
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSourceInventory
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarkedNames
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda

universe u

/-- The listening lambda's constructor address through active environments. -/
def returningOrigin : {Γ : Ctx sig} → {function : Expr Srt.nm Γ} →
    Environment.ReturningLambda function → List Edge → Origin
  | _, _, .lam _, address => ⟨.lambda, address⟩
  | _, _, .defn _ returning, address => returningOrigin returning (.definitionBody :: address)
  | _, _, .carrier _ _ returning, address => returningOrigin returning (.carrierBody :: address)

/-- A binary listener either listens on the current result or belongs to an
application at this address or deeper. No stored value is inspected. -/
theorem input_channel {Key : Type u} (binderKey : Origin → Key) {Γ : Ctx sig}
    (source : Expr Srt.nm Γ) (address : List Edge) (references : ReferenceKeys Key Γ)
    (result channel : Key) (origin : Origin)
    (member : (⟨.input2, origin, channel, []⟩ : Observation Origin Key) ∈
      inventory binderKey source address references result) :
    channel = result ∨ ∃ owner : List Edge,
      address.length ≤ owner.length ∧ channel = binderKey ⟨.privateCall, owner⟩ := by
  induction source generalizing address result with
  | var => simp [inventory, Observation.mk.injEq] at member
  | lam =>
      simp only [inventory, Set.mem_singleton_iff, Observation.mk.injEq] at member
      exact Or.inl member.2.2.1
  | app function argument ih =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at member
      rcases member with inner | impossible
      · rcases ih (.function :: address) references _ inner with same | ⟨owner, deeper, same⟩
        · exact Or.inr ⟨address, Nat.le_refl _, same⟩
        · exact Or.inr ⟨owner, by simpa only [List.length_cons] using Nat.le_of_succ_le deeper, same⟩
      · cases impossible.1
  | defn value body valueIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at member
      rcases member with inner | impossible
      · rcases bodyIH (.definitionBody :: address) _ result inner with same | ⟨owner, deeper, same⟩
        · exact Or.inl same
        · exact Or.inr ⟨owner, by simpa only [List.length_cons] using Nat.le_of_succ_le deeper, same⟩
      · cases impossible.1
  | carrier name value body valueIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at member
      rcases member with inner | impossible
      · rcases bodyIH (.carrierBody :: address) references result inner with same | ⟨owner, deeper, same⟩
        · exact Or.inl same
        · exact Or.inr ⟨owner, by simpa only [List.length_cons] using Nat.le_of_succ_le deeper, same⟩
      · cases impossible.1

/-- A binary input on an external result channel is the returning lambda,
unless that result aliases a locally authored private application channel. -/
theorem returning_listener {Key : Type u} (binderKey : Origin → Key) {Γ : Ctx sig}
    (source : Expr Srt.nm Γ) (address : List Edge) (references : ReferenceKeys Key Γ)
    (result : Key) (origin : Origin)
    (fresh : ∀ owner : List Edge, address.length ≤ owner.length →
      binderKey ⟨.privateCall, owner⟩ ≠ result)
    (member : (⟨.input2, origin, result, []⟩ : Observation Origin Key) ∈
      inventory binderKey source address references result) :
    ∃ returning : Environment.ReturningLambda source, origin = returningOrigin returning address := by
  induction source generalizing address result with
  | var => simp [inventory, Observation.mk.injEq] at member
  | lam body =>
      simp only [inventory, Set.mem_singleton_iff, Observation.mk.injEq] at member
      exact ⟨.lam body, member.2.1⟩
  | app function argument ih =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at member
      rcases member with inner | impossible
      · rcases input_channel binderKey function (.function :: address) references _ result origin inner with same | ⟨owner, deeper, same⟩
        · exact False.elim (fresh address (Nat.le_refl _) same.symm)
        · exact False.elim (fresh owner (by simpa only [List.length_cons] using Nat.le_of_succ_le deeper) same.symm)
      · cases impossible.1
  | defn value body valueIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at member
      rcases member with inner | impossible
      · rcases bodyIH (.definitionBody :: address) _ result
          (fun owner deeper => fresh owner (by simpa only [List.length_cons] using Nat.le_of_succ_le deeper)) inner with
          ⟨returning, same⟩
        exact ⟨.defn value returning, same⟩
      · cases impossible.1
  | carrier name value body valueIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at member
      rcases member with inner | impossible
      · rcases bodyIH (.carrierBody :: address) references result
          (fun owner deeper => fresh owner (by simpa only [List.length_cons] using Nat.le_of_succ_le deeper)) inner with
          ⟨returning, same⟩
        exact ⟨.carrier name value returning, same⟩
      · cases impossible.1

/-- Both actual source constructor origins of a beta event, including all
active environments and pending application contexts. -/
inductive BetaSite : {Γ : Ctx sig} → Expr Srt.nm Γ → List Edge → Origin → Origin → Type where
  | root {Γ} {function : Expr Srt.nm Γ} (returning : Environment.ReturningLambda function)
      (argument : Var Γ Srt.nm) (address : List Edge) :
      BetaSite (.app function argument) address
        (returningOrigin returning (.function :: address)) ⟨.application, address⟩
  | app {Γ} {function : Expr Srt.nm Γ} {address : List Edge} {input output : Origin}
      (argument : Var Γ Srt.nm) : BetaSite function (.function :: address) input output →
      BetaSite (.app function argument) address input output
  | defn {Γ} (value : Expr Srt.nm Γ) {body : Expr Srt.nm (Srt.nm :: Γ)}
      {address : List Edge} {input output : Origin} :
      BetaSite body (.definitionBody :: address) input output →
      BetaSite (.defn value body) address input output
  | carrier {Γ} (name : Var Γ Srt.nm) (value : Expr Srt.nm Γ) {body : Expr Srt.nm Γ}
      {address : List Edge} {input output : Origin} :
      BetaSite body (.carrierBody :: address) input output →
      BetaSite (.carrier name value body) address input output

def BetaSite.successor : {Γ : Ctx sig} → {source : Expr Srt.nm Γ} → {address : List Edge} →
    {input output : Origin} → BetaSite source address input output → Expr Srt.nm Γ
  | _, _, _, _, _, .root returning argument _ => returning.result argument
  | _, _, _, _, _, .app argument inner => .app inner.successor argument
  | _, _, _, _, _, .defn value inner => .defn value inner.successor
  | _, _, _, _, _, .carrier name value inner => .carrier name value inner.successor

theorem BetaSite.sound {Γ : Ctx sig} {source : Expr Srt.nm Γ} {address : List Edge}
    {input output : Origin} (site : BetaSite source address input output) :
    Environment.StepModulo .beta source site.successor := by
  induction site with
  | root returning argument => exact returning.call argument
  | app argument inner ih => exact ih.app argument
  | defn value inner ih => exact ih.defn value
  | carrier name value inner ih => exact ih.carrier name value

/-- Same-channel source inventory actors force a real beta site. The
injectivity premise is about authored application keys, not a simulation. -/
theorem matching_binary_site {Key : Type u} (binderKey : Origin → Key)
    (calls : Function.Injective (fun address : List Edge => binderKey ⟨.privateCall, address⟩))
    {Γ : Ctx sig} (source : Expr Srt.nm Γ) (address : List Edge)
    (references : ReferenceKeys Key Γ) (result channel : Key) (fields : List Key)
    (input output : Origin)
    (listener : (⟨.input2, input, channel, []⟩ : Observation Origin Key) ∈
      inventory binderKey source address references result)
    (sender : (⟨.output2, output, channel, fields⟩ : Observation Origin Key) ∈
      inventory binderKey source address references result) :
    Nonempty (BetaSite source address input output) := by
  induction source generalizing address result with
  | var => simp [inventory, Observation.mk.injEq] at listener
  | lam => simp [inventory, Observation.mk.injEq] at sender
  | app function argument ih =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at listener sender
      rcases listener with listener | impossible
      · rcases sender with sender | root
        · rcases ih (.function :: address) references _ listener sender with ⟨site⟩
          exact ⟨.app argument site⟩
        · have channelEq := root.2.2.1
          have outputEq := root.2.1
          have onResult : (⟨.input2, input, binderKey ⟨.privateCall, address⟩, []⟩ : Observation Origin Key) ∈
              inventory binderKey function (.function :: address) references (binderKey ⟨.privateCall, address⟩) := by
            simpa only [channelEq] using listener
          rcases returning_listener binderKey function (.function :: address) references _ input
            (fun owner deeper same => by
              have equal := calls same
              have sizes := congrArg List.length equal
              simp only [List.length_cons] at deeper
              omega) onResult with ⟨returning, inputEq⟩
          subst input output
          exact ⟨.root returning argument address⟩
      · cases impossible.1
  | defn value body valueIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at listener sender
      rcases listener with listener | impossible
      · rcases sender with sender | impossible
        · rcases bodyIH (.definitionBody :: address) _ result listener sender with ⟨site⟩
          exact ⟨.defn value site⟩
        · cases impossible.1
      · cases impossible.1
  | carrier name value body valueIH bodyIH =>
      simp only [inventory, Set.mem_union, Set.mem_singleton_iff, Observation.mk.injEq] at listener sender
      rcases listener with listener | impossible
      · rcases sender with sender | impossible
        · rcases bodyIH (.carrierBody :: address) references result listener sender with ⟨site⟩
          exact ⟨.carrier name value site⟩
        · cases impossible.1
      · cases impossible.1

/-- Private constructor keys and actual ambient names inhabit disjoint
summands. This supplies an injective call allocation without an assumption. -/
abbrev Keys (Γ : Ctx sig) := Sum (Var Γ Srt.nm) Origin

def binderKey {Γ : Ctx sig} (origin : Origin) : Keys Γ := .inr origin

def ambientKeys {Γ : Ctx sig} (name : Var Γ Srt.nm) : Keys Γ := .inl name

theorem call_keys_injective {Γ : Ctx sig} :
    Function.Injective (fun address : List Edge => (binderKey ⟨.privateCall, address⟩ : Keys Γ)) := by
  intro first second same
  cases same
  rfl

/-- Every supplied binary target exposure is owned by a real source beta
site with these exact selected constructor origins. -/
theorem traced_binary_site {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) {target : Proc Δ}
    (exposure : Exposure (compile source environment result) target)
    (traced : TracedExposure (mark source []) exposure)
    (binary : inputHeader exposure.selected = .input2) :
    Nonempty (BetaSite source [] traced.continuation.inputOrigin traced.continuation.outputOrigin) := by
  have listener := traced_input_observed (binderKey : Origin → Keys Δ) traced ambientKeys
  have sender := traced_output_observed (binderKey : Origin → Keys Δ) traced ambientKeys
  rw [compile_inventory] at listener sender
  rcases exposure with ⟨world, scope, redex, reduct, selected, frame, before, after⟩
  rcases traced with ⟨binders, redexMarks, frameMarks, communication, frameFits,
    transportedFits, tracked, originalInput, originalOutput⟩
  cases selected with
  | unary => simp only [inputHeader] at binary; cases binary
  | binary channel first second body =>
      cases communication with
      | binary _ _ _ _ outputOrigin inputOrigin continuation bodyFits =>
          exact matching_binary_site binderKey call_keys_injective source [] _ _
            (nameKey (scopeEnvironment binderKey binders ambientKeys) channel)
            [nameKey (scopeEnvironment binderKey binders ambientKeys) first,
              nameKey (scopeEnvironment binderKey binders ambientKeys) second]
            inputOrigin outputOrigin listener sender

/-- Binary execution cannot invent a source beta event. Its selected source
site computes a successor and also retains the exact target frame theorem.
Identification of the entire supplied endpoint additionally needs the
selected guarded-body opening comparison. -/
theorem actual_binary_authorized {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) {target : Proc Δ}
    (exposure : Exposure (compile source environment result) target)
    (traced : TracedExposure (mark source []) exposure)
    (binary : inputHeader exposure.selected = .input2) :
    ∃ site : BetaSite source [] traced.continuation.inputOrigin traced.continuation.outputOrigin,
      Environment.StepModulo .beta source site.successor ∧
      StructuralEq
        (ActivePrefixResidual.remove .output2 traced.continuation.outputOrigin
          (ActivePrefixResidual.cutTree .input2 traced.continuation.inputOrigin (mark source []))
          (ActivePrefixResidual.remove .input2 traced.continuation.inputOrigin (mark source [])
            (compile source environment result)))
        (exposure.scope.close exposure.frame) := by
  rcases traced_binary_site source environment result exposure traced binary with ⟨site⟩
  exact ⟨site, site.sound, NamePassingBinaryResidual.actual_binary_frame source environment result exposure traced binary⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBinaryOwnership
