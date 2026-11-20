import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.CanonicalHistories
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNativeRounds

/-!
# Named canonical histories use the hosted-to-native execution adapter

The source name is retained with its actual rule lookup. Equal equation
schemas may share a rule body; their list indices are not identified. The
native projection below preserves an actual sequential execution and its
endpoint up to dead names. It makes no multiplicity claim for native paths
after the rigid source names have been forgotten.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedCanonicalHistories

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open RuleSyntax.StepWeb.HostedNative
open RuleSyntax.StepWeb.HostedNative.Rounds

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}
  (N : Nodes S Γ star)

def NamedMembers {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (word : List RuleName)
    (members : List (Member Γ star κ (translate N P))) : Prop :=
  List.Forall₂ (fun name member => ruleNamed N P name = some member.rule) word members

theorem namedMembers_length {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}
    {word : List RuleName} {members : List (Member Γ star κ (translate N P))}
    (named : NamedMembers N P word members) : word.length = members.length := named.length_eq

theorem namedMembers_snoc {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}
    {word : List RuleName} {members : List (Member Γ star κ (translate N P))}
    (named : NamedMembers N P word members) {name : RuleName}
    {member : Member Γ star κ (translate N P)} (last : ruleNamed N P name = some member.rule) :
    NamedMembers N P (word ++ [name]) (members ++ [member]) := by
  unfold NamedMembers at named ⊢
  induction named with
  | nil => exact .cons last .nil
  | cons same rest ih => exact .cons same ih

theorem hosted_append {P : CProgram S} {first middle last : HostState S}
    {p : Presented Γ star first} {q : Presented Γ star middle} {r : Presented Γ star last}
    {initial interim final : Finset ℕ} {before after : List (Member Γ star κ P)}
    (left : HostedRun first p initial before middle q interim)
    (right : HostedRun middle q interim after last r final) :
    HostedRun first p initial (before ++ after) last r final := by
  induction left with
  | nil => exact right
  | cons member rest admitted later ih =>
      exact .cons member (rest ++ after) admitted (ih right)

theorem canonical_step_hosted {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}
    {name : RuleName} {first last : HostState S} {old fresh : ℕ}
    (p : Presented Γ star first) (occupied : Finset ℕ) (fuel : RuleName → ℕ)
    (fired : FiresNamedCanonical N P name first old last fresh) :
    ∃ (member : Member Γ star κ (translate N P)) (q : Presented Γ star last),
      ruleNamed N P name = some member.rule ∧
      member.selection = (⟨[old],[],[fresh]⟩ : Selection ℕ) ∧ member.fuel = fuel name ∧
      HostedRun first p occupied [member] last q (nextLedger occupied member.selection) := by
  obtain ⟨rule,inside,named,admitted,rfl⟩ := fired
  let member : Member Γ star κ (translate N P) :=
    ⟨rule,inside,placedNamed N P name rule named,⟨[old],[],[fresh]⟩,fuel name⟩
  let q := resultPresented first p inside member.placed member.selection
  refine ⟨member,q,named,rfl,rfl,?_⟩
  exact .cons member [] admitted (.nil _ _ _)

theorem canonical_chain_hosted {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}
    {first last : HostState S} {old fresh : ℕ} {word : List RuleName}
    (chain : Chain (FiresNamedCanonical N P) first old word last fresh)
    (p : Presented Γ star first) (occupied : Finset ℕ) (fuel : RuleName → ℕ) :
    ∃ (members : List (Member Γ star κ (translate N P))) (q : Presented Γ star last) (final : Finset ℕ),
      NamedMembers N P word members ∧ HostedRun first p occupied members last q final := by
  induction chain with
  | nil => exact ⟨[],p,occupied,.nil,.nil _ _ _⟩
  | snoc before fired ih =>
      obtain ⟨members,q,interim,named,run⟩ := ih
      obtain ⟨member,r,namedLast,_,_,single⟩ := canonical_step_hosted N q interim fuel fired
      refine ⟨members ++ [member],r,_,?_,hosted_append run single⟩
      exact namedMembers_snoc N named namedLast

section Native

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

theorem canonical_chain_native {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}
    {first last : HostState S} {old fresh : ℕ} {word : List RuleName}
    (chain : Chain (FiresNamedCanonical N P) first old word last fresh)
    (p : Presented Γ star first) (occupied : Finset ℕ) (fuel : RuleName → ℕ) :
    ∃ (members : List (Member Γ star κ (translate N P))) (q : Presented Γ star last)
      (final : Finset ℕ) (nativeLast : NativeState S ℕ Γ star),
      NamedMembers N P word members ∧ members.length = word.length ∧
      HostedRun first p occupied members last q final ∧
      NativeIterated.Sequential (state κ first p occupied) (members.map (Member.live N first p occupied)) nativeLast ∧
      NativeDead.DeadEquiv (state κ last q final) nativeLast := by
  obtain ⟨members,q,final,named,hosted⟩ := canonical_chain_hosted N chain p occupied fuel
  obtain ⟨nativeLast,nativeRun,same⟩ := (sequential_iff N members first p occupied).2 hosted
  exact ⟨members,q,final,nativeLast,named,(namedMembers_length N named).symm,hosted,nativeRun,same⟩

end Native

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.HostedCanonicalHistories
