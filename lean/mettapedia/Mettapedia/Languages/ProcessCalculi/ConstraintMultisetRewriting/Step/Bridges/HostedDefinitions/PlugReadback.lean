import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.SearchReadback

/-! # Readback of actual context reconstruction steps -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PlugReadback

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage.Elaboration
open ContextStack

@[simp] theorem plug_eq (a b c d k l : MClosed) :
    plugC a c k = plugC b d l ↔ a = b ∧ c = d ∧ k = l := by
  simp [plugC, activeC, DataEmbedding.nodeC_eq_iff]

def Plugging {outer : Nat} (whole : Tower.Tm outer) (continuation current : MClosed) : Prop :=
  ∃ inner, ∃ focus : Tower.Tm inner, ∃ stack : Stack outer inner,
    current = plugC (encodeTm focus) (code stack) continuation ∧ plug stack focus = whole

def Returned {outer : Nat} (whole : Tower.Tm outer) (continuation current : MClosed) : Prop :=
  current = resumeC (encodeTm whole) continuation

theorem cases_preserve {outer : Nat} {whole : Tower.Tm outer} {continuation current next : MClosed}
    (represented : Plugging whole continuation current) (step : TraversalCases.Case current next) :
    Plugging whole continuation next ∨ Returned whole continuation next := by
  obtain ⟨inner, focus, stack, same, restored⟩ := represented
  cases step with
  | empty term k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      have sameTerm : focus = whole := by
        simpa only [ContextStack.plug, ContextStack.context, ComputationSyntax.Context.plug] using restored
      exact .inr (congrArg (fun term => resumeC (encodeTm term) k) sameTerm)
  | piPlugLeft term other context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i codomain tail
      obtain ⟨rfl, rfl⟩ := stackEq
      refine .inl ⟨_, .pi focus codomain, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | piPlugRight term other context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i domain tail
      obtain ⟨rfl, rfl⟩ := stackEq
      refine .inl ⟨_, .pi domain focus, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | sigmaPlugLeft term other context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i codomain tail
      obtain ⟨rfl, rfl⟩ := stackEq
      refine .inl ⟨_, .sigma focus codomain, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | sigmaPlugRight term other context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i domain tail
      obtain ⟨rfl, rfl⟩ := stackEq
      refine .inl ⟨_, .sigma domain focus, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | appPlugLeft term other context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i argument tail
      obtain ⟨rfl, rfl⟩ := stackEq
      refine .inl ⟨_, .app focus argument, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | appPlugRight term other context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i function tail
      obtain ⟨rfl, rfl⟩ := stackEq
      refine .inl ⟨_, .app function focus, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | pairPlugLeft term other context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i second tail
      obtain ⟨rfl, rfl⟩ := stackEq
      refine .inl ⟨_, .pair focus second, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | pairPlugRight term other context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i first tail
      obtain ⟨rfl, rfl⟩ := stackEq
      refine .inl ⟨_, .pair first focus, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | lamPlug term context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i tail
      subst context
      refine .inl ⟨_, .lam focus, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | fstPlug term context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i tail
      subst context
      refine .inl ⟨_, .fst focus, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | sndPlug term context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i tail
      subst context
      refine .inl ⟨_, .snd focus, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | reflPlug term context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i tail
      subst context
      refine .inl ⟨_, .refl focus, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | idPlugType term a b context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i left right tail
      obtain ⟨rfl, rfl, rfl⟩ := stackEq
      refine .inl ⟨_, .id focus left right, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | idPlugLeft term a b context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i carrier right tail
      obtain ⟨rfl, rfl, rfl⟩ := stackEq
      refine .inl ⟨_, .id carrier focus right, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | idPlugRight term a b context k =>
      obtain ⟨rfl, stackEq, rfl⟩ := (plug_eq _ _ _ _ _ _).mp same
      cases stack <;> simp [code, emptyContext, DataEmbedding.nodeC_eq_iff] at stackEq
      rename_i carrier left tail
      obtain ⟨rfl, rfl, rfl⟩ := stackEq
      refine .inl ⟨_, .id carrier left focus, tail, by simp, ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | _ => simp [plugC, seekC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PlugReadback
