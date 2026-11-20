import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalRootMatching

/-!
# Normality decomposes into the actual root probe and native children

The statement covers every native constructor. Dependent codomains and
lambda bodies retain their incremented scope; scalar constant, variable and
universe fields are not recursive terms. The root test is connected to the
actual source probe's fresh constraint admission. Completed scanner execution
is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalStructure

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

variable {dev : Definitions.Development} (built : Compiled dev)

abbrev Normal {n : Nat} (term : Tower.Tm n) : Prop :=
  ContextualDependentExecutableJoin.Normal (Definitions.devPackage dev built.nativeRows) term

def ChildrenNormal : {n : Nat} → Tower.Tm n → Prop
  | _, .var _ | _, .const _ | _, .head _ => True
  | _, .pi domain body | _, .sigma domain body => Normal built domain ∧ Normal built body
  | _, .id carrier left right => Normal built carrier ∧ Normal built left ∧ Normal built right
  | _, .lam body => Normal built body
  | _, .app first second | _, .pair first second => Normal built first ∧ Normal built second
  | _, .fst subject | _, .snd subject | _, .refl subject => Normal built subject

theorem normal_children {n : Nat} (term : Tower.Tm n) (normal : Normal built term) :
    ChildrenNormal built term := by
  cases term with
  | var _ | const _ | head _ => trivial
  | pi domain body =>
      exact ⟨fun output edge => normal _ (.congPiDom edge),
        fun output edge => normal _ (.congPiCod edge)⟩
  | sigma domain body =>
      exact ⟨fun output edge => normal _ (.congSigmaDom edge),
        fun output edge => normal _ (.congSigmaCod edge)⟩
  | id carrier left right =>
      exact ⟨fun output edge => normal _ (.congIdTy edge),
        fun output edge => normal _ (.congIdLeft edge),
        fun output edge => normal _ (.congIdRight edge)⟩
  | lam body => exact fun output edge => normal _ (.congLam edge)
  | app function argument =>
      exact ⟨fun output edge => normal _ (.congAppFun edge),
        fun output edge => normal _ (.congAppArg edge)⟩
  | pair first second =>
      exact ⟨fun output edge => normal _ (.congPairFst edge),
        fun output edge => normal _ (.congPairSnd edge)⟩
  | fst subject => exact fun output edge => normal _ (.congFst edge)
  | snd subject => exact fun output edge => normal _ (.congSnd edge)
  | refl subject => exact fun output edge => normal _ (.congRefl edge)

theorem normal_no_root {n : Nat} (term : Tower.Tm n) (normal : Normal built term) :
    ¬ NormalRootMatching.Redex built term := by
  rintro ⟨action, allowed, starts⟩
  have reduced := DirectedSyntax.action_reduces action allowed
  rw [starts] at reduced
  exact normal _ reduced

theorem normal_of_parts {n : Nat} (term : Tower.Tm n)
    (root : ¬ NormalRootMatching.Redex built term) (children : ChildrenNormal built term) :
    Normal built term := by
  intro output edge
  cases edge with
  | betaPi body argument => exact root ⟨.beta body argument, rfl, rfl⟩
  | betaSigmaFst => exact root ⟨.first _ _, rfl, rfl⟩
  | betaSigmaSnd => exact root ⟨.second _ _, rfl, rfl⟩
  | head impossible => cases impossible
  | root computation =>
      obtain ⟨arity, left, right, substitution, selected, starts, _⟩ :=
        (RootRewrites.presentation built).cover computation
      exact root ⟨.declared left right selected substitution, rfl, starts⟩
  | congPiDom reduced => exact children.1 _ reduced
  | congPiCod reduced => exact children.2 _ reduced
  | congSigmaDom reduced => exact children.1 _ reduced
  | congSigmaCod reduced => exact children.2 _ reduced
  | congIdTy reduced => exact children.1 _ reduced
  | congIdLeft reduced => exact children.2.1 _ reduced
  | congIdRight reduced => exact children.2.2 _ reduced
  | congLam reduced => exact children _ reduced
  | congAppFun reduced => exact children.1 _ reduced
  | congAppArg reduced => exact children.2 _ reduced
  | congPairFst reduced => exact children.1 _ reduced
  | congPairSnd reduced => exact children.2 _ reduced
  | congFst reduced => exact children _ reduced
  | congSnd reduced => exact children _ reduced
  | congRefl reduced => exact children _ reduced

theorem normal_iff_parts {n : Nat} (term : Tower.Tm n) :
    Normal built term ↔ ¬ NormalRootMatching.Redex built term ∧ ChildrenNormal built term :=
  ⟨fun normal => ⟨normal_no_root built term normal, normal_children built term normal⟩,
    fun parts => normal_of_parts built term parts.1 parts.2⟩

theorem normal_iff_probe_blocked (D : Discipline MSig [] ()) (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ()) {n : Nat} (term : Tower.Tm n)
    (continuation : MClosed)
    (fresh : BinderCore.Fresh built.rules scope K datum)
    (determined : Determines K datum (rootC (encodeTm term) continuation)) :
    Normal built term ↔
      ¬ NormalRootMatching.Enabled built D scope K datum ∧ ChildrenNormal built term := by
  rw [NormalRootMatching.probe_iff_redex built D scope K datum term continuation fresh determined]
  exact normal_iff_parts built term

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalStructure

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalStructure.normal_iff_probe_blocked
