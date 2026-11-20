import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.TraversalCases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContextStack
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.TermViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PatternReadback

/-!
# Readback of context search at the actual native scope

These predicates interpret literal seek/root states by the existing native
term and a typed view of its context stack. A search step keeps the same whole
native term; choosing the root moves to a request without claiming a reduction
has already happened.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.SearchReadback

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage.Elaboration
open ContextStack

@[simp] theorem seek_eq (a b c d k l : MClosed) :
    seekC a c k = seekC b d l ↔ a = b ∧ c = d ∧ k = l := by
  simp [seekC, activeC, DataEmbedding.nodeC_eq_iff]

def Seeking {outer : Nat} (whole : Tower.Tm outer) (continuation current : MClosed) : Prop :=
  ∃ inner, ∃ focus : Tower.Tm inner, ∃ stack : Stack outer inner,
    current = seekC (encodeTm focus) (code stack) continuation ∧ plug stack focus = whole

def Rooted {outer : Nat} (whole : Tower.Tm outer) (continuation current : MClosed) : Prop :=
  ∃ inner, ∃ focus : Tower.Tm inner, ∃ stack : Stack outer inner,
    current = rootC (encodeTm focus) (nodeC "hd-main-plug" [code stack, continuation]) ∧ plug stack focus = whole

theorem initial {n : Nat} (term : Tower.Tm n) (continuation : MClosed) :
    Seeking term continuation (seekC (encodeTm term) emptyContext continuation) :=
  ⟨n, term, .nil, by simp only [ContextStack.code],
    by simp only [ContextStack.plug, ContextStack.context, ComputationSyntax.Context.plug]⟩

theorem cases_preserve {outer : Nat} {whole : Tower.Tm outer} {continuation current next : MClosed}
    (represented : Seeking whole continuation current) (step : TraversalCases.Case current next) :
    Seeking whole continuation next ∨ Rooted whole continuation next := by
  obtain ⟨inner, focus, stack, same, restored⟩ := represented
  cases step with
  | routeRoot term context k =>
      obtain ⟨rfl, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      exact .inr ⟨inner, focus, stack, rfl, restored⟩
  | piSeekLeft a b context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨left, right, rfl, rfl, rfl⟩ := TermViews.pi_of_code encoded
      refine .inl ⟨_, left, .piDom right stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | piSeekRight a b context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨left, right, rfl, rfl, rfl⟩ := TermViews.pi_of_code encoded
      refine .inl ⟨_, right, .piCod left stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | sigmaSeekLeft a b context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨left, right, rfl, rfl, rfl⟩ := TermViews.sigma_of_code encoded
      refine .inl ⟨_, left, .sigmaDom right stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | sigmaSeekRight a b context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨left, right, rfl, rfl, rfl⟩ := TermViews.sigma_of_code encoded
      refine .inl ⟨_, right, .sigmaCod left stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | appSeekLeft a b context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨left, right, rfl, rfl, rfl⟩ := PatternReadback.encoded_app encoded
      refine .inl ⟨_, left, .appFun right stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | appSeekRight a b context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨left, right, rfl, rfl, rfl⟩ := PatternReadback.encoded_app encoded
      refine .inl ⟨_, right, .appArg left stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | pairSeekLeft a b context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨left, right, rfl, rfl, rfl⟩ := TermViews.pair_of_code encoded
      refine .inl ⟨_, left, .pairFst right stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | pairSeekRight a b context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨left, right, rfl, rfl, rfl⟩ := TermViews.pair_of_code encoded
      refine .inl ⟨_, right, .pairSnd left stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | lamSeek term context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨subject, rfl, rfl⟩ := TermViews.lam_of_code encoded
      refine .inl ⟨_, subject, .lam stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | fstSeek term context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨subject, rfl, rfl⟩ := TermViews.fst_of_code encoded
      refine .inl ⟨_, subject, .fst stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | sndSeek term context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨subject, rfl, rfl⟩ := TermViews.snd_of_code encoded
      refine .inl ⟨_, subject, .snd stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | reflSeek term context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨subject, rfl, rfl⟩ := PatternReadback.encoded_refl encoded
      refine .inl ⟨_, subject, .refl stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | idSeekType a b c context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨carrier, left, right, rfl, rfl, rfl, rfl⟩ := TermViews.id_of_code encoded
      refine .inl ⟨_, carrier, .idType left right stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | idSeekLeft a b c context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨carrier, left, right, rfl, rfl, rfl, rfl⟩ := TermViews.id_of_code encoded
      refine .inl ⟨_, left, .idLeft carrier right stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | idSeekRight a b c context k =>
      obtain ⟨encoded, rfl, rfl⟩ := (seek_eq _ _ _ _ _ _).mp same
      obtain ⟨carrier, left, right, rfl, rfl, rfl, rfl⟩ := TermViews.id_of_code encoded
      refine .inl ⟨_, right, .idRight carrier left stack, by simp only [ContextStack.code], ?_⟩
      simpa only [ContextStack.plug, ContextStack.context, ContextOperations.plug_append, ComputationSyntax.Context.plug] using restored
  | _ => simp [seekC, plugC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.SearchReadback
