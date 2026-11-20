import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContextRewrites

/-!
# Traversing every existing directed computation context by actual source rules

The proof follows the original intrinsically scoped Context. Encoded bodies
under binders retain their changed ambient arity. Only forward availability
is asserted under added rules; reflection needs the fixed-program phase laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContextTraversal

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage.Elaboration
open RuleInstances

variable {all : List (ProgramBinders.Equation MSig [] ())}
  (included : ∀ rule ∈ ContextRules.traversal, rule ∈ all)

include included

theorem seek {outer inner : Nat} (context : ComputationSyntax.Context Tower.Head outer inner)
    (term : Tower.Tm inner) (rest continuation : MClosed) :
    Steps all (seekC (encodeTm (context.plug term)) rest continuation)
      (seekC (encodeTm term) (contextCode context rest) continuation) := by
  induction context generalizing rest with
  | hole => exact .refl
  | piDom inner codomain ih =>
      have move := ContextRewrites.binary_seek_left "prime-tm-pi" "hd-context-pi-domain" "hd-context-pi-codomain"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) (encodeTm codomain) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_pi, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-pi-domain" [encodeTm codomain, rest]))
  | piCod domain inner ih =>
      have move := ContextRewrites.binary_seek_right "prime-tm-pi" "hd-context-pi-domain" "hd-context-pi-codomain"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm domain) (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_pi, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-pi-codomain" [encodeTm domain, rest]))
  | sigmaDom inner codomain ih =>
      have move := ContextRewrites.binary_seek_left "prime-tm-sigma" "hd-context-sigma-domain" "hd-context-sigma-codomain"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) (encodeTm codomain) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_sigma, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-sigma-domain" [encodeTm codomain, rest]))
  | sigmaCod domain inner ih =>
      have move := ContextRewrites.binary_seek_right "prime-tm-sigma" "hd-context-sigma-domain" "hd-context-sigma-codomain"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm domain) (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_sigma, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-sigma-codomain" [encodeTm domain, rest]))
  | appFun inner argument ih =>
      have move := ContextRewrites.binary_seek_left "prime-tm-app" "hd-context-app-function" "hd-context-app-argument"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) (encodeTm argument) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_app, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-app-function" [encodeTm argument, rest]))
  | appArg function inner ih =>
      have move := ContextRewrites.binary_seek_right "prime-tm-app" "hd-context-app-function" "hd-context-app-argument"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm function) (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_app, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-app-argument" [encodeTm function, rest]))
  | pairFst inner second ih =>
      have move := ContextRewrites.binary_seek_left "prime-tm-pair" "hd-context-pair-first" "hd-context-pair-second"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) (encodeTm second) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_pair, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-pair-first" [encodeTm second, rest]))
  | pairSnd first inner ih =>
      have move := ContextRewrites.binary_seek_right "prime-tm-pair" "hd-context-pair-first" "hd-context-pair-second"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm first) (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_pair, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-pair-second" [encodeTm first, rest]))
  | lam inner ih =>
      have move := ContextRewrites.unary_seek "prime-tm-lam" "hd-context-lam"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_lam, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-lam" [rest]))
  | fst inner ih =>
      have move := ContextRewrites.unary_seek "prime-tm-fst" "hd-context-first"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_fst, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-first" [rest]))
  | snd inner ih =>
      have move := ContextRewrites.unary_seek "prime-tm-snd" "hd-context-second"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_snd, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-second" [rest]))
  | refl inner ih =>
      have move := ContextRewrites.unary_seek "prime-tm-refl" "hd-context-refl"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_refl, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-refl" [rest]))
  | idType inner left right ih =>
      have move := ContextRewrites.identity_seek_type
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) (encodeTm left) (encodeTm right) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_id, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-id-type" [encodeTm left, encodeTm right, rest]))
  | idLeft carrier inner right ih =>
      have move := ContextRewrites.identity_seek_left
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm carrier) (encodeTm (inner.plug term)) (encodeTm right) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_id, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-id-left" [encodeTm carrier, encodeTm right, rest]))
  | idRight carrier left inner ih =>
      have move := ContextRewrites.identity_seek_right
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm carrier) (encodeTm left) (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_id, contextCode] using
        (Relation.ReflTransGen.single move).trans (ih term (nodeC "hd-context-id-right" [encodeTm carrier, encodeTm left, rest]))

theorem plug {outer inner : Nat} (context : ComputationSyntax.Context Tower.Head outer inner)
    (term : Tower.Tm inner) (rest continuation : MClosed) :
    Steps all (plugC (encodeTm term) (contextCode context rest) continuation)
      (plugC (encodeTm (context.plug term)) rest continuation) := by
  induction context generalizing rest with
  | hole => exact .refl
  | piDom inner codomain ih =>
      have last := ContextRewrites.binary_plug_left "prime-tm-pi" "hd-context-pi-domain" "hd-context-pi-codomain"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) (encodeTm codomain) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_pi, contextCode] using
        (ih term (nodeC "hd-context-pi-domain" [encodeTm codomain, rest])).trans (Relation.ReflTransGen.single last)
  | piCod domain inner ih =>
      have last := ContextRewrites.binary_plug_right "prime-tm-pi" "hd-context-pi-domain" "hd-context-pi-codomain"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm domain) (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_pi, contextCode] using
        (ih term (nodeC "hd-context-pi-codomain" [encodeTm domain, rest])).trans (Relation.ReflTransGen.single last)
  | sigmaDom inner codomain ih =>
      have last := ContextRewrites.binary_plug_left "prime-tm-sigma" "hd-context-sigma-domain" "hd-context-sigma-codomain"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) (encodeTm codomain) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_sigma, contextCode] using
        (ih term (nodeC "hd-context-sigma-domain" [encodeTm codomain, rest])).trans (Relation.ReflTransGen.single last)
  | sigmaCod domain inner ih =>
      have last := ContextRewrites.binary_plug_right "prime-tm-sigma" "hd-context-sigma-domain" "hd-context-sigma-codomain"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm domain) (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_sigma, contextCode] using
        (ih term (nodeC "hd-context-sigma-codomain" [encodeTm domain, rest])).trans (Relation.ReflTransGen.single last)
  | appFun inner argument ih =>
      have last := ContextRewrites.binary_plug_left "prime-tm-app" "hd-context-app-function" "hd-context-app-argument"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) (encodeTm argument) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_app, contextCode] using
        (ih term (nodeC "hd-context-app-function" [encodeTm argument, rest])).trans (Relation.ReflTransGen.single last)
  | appArg function inner ih =>
      have last := ContextRewrites.binary_plug_right "prime-tm-app" "hd-context-app-function" "hd-context-app-argument"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm function) (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_app, contextCode] using
        (ih term (nodeC "hd-context-app-argument" [encodeTm function, rest])).trans (Relation.ReflTransGen.single last)
  | pairFst inner second ih =>
      have last := ContextRewrites.binary_plug_left "prime-tm-pair" "hd-context-pair-first" "hd-context-pair-second"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) (encodeTm second) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_pair, contextCode] using
        (ih term (nodeC "hd-context-pair-first" [encodeTm second, rest])).trans (Relation.ReflTransGen.single last)
  | pairSnd first inner ih =>
      have last := ContextRewrites.binary_plug_right "prime-tm-pair" "hd-context-pair-first" "hd-context-pair-second"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm first) (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_pair, contextCode] using
        (ih term (nodeC "hd-context-pair-second" [encodeTm first, rest])).trans (Relation.ReflTransGen.single last)
  | lam inner ih =>
      have last := ContextRewrites.unary_plug "prime-tm-lam" "hd-context-lam"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_lam, contextCode] using
        (ih term (nodeC "hd-context-lam" [rest])).trans (Relation.ReflTransGen.single last)
  | fst inner ih =>
      have last := ContextRewrites.unary_plug "prime-tm-fst" "hd-context-first"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_fst, contextCode] using
        (ih term (nodeC "hd-context-first" [rest])).trans (Relation.ReflTransGen.single last)
  | snd inner ih =>
      have last := ContextRewrites.unary_plug "prime-tm-snd" "hd-context-second"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_snd, contextCode] using
        (ih term (nodeC "hd-context-second" [rest])).trans (Relation.ReflTransGen.single last)
  | refl inner ih =>
      have last := ContextRewrites.unary_plug "prime-tm-refl" "hd-context-refl"
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_refl, contextCode] using
        (ih term (nodeC "hd-context-refl" [rest])).trans (Relation.ReflTransGen.single last)
  | idType inner left right ih =>
      have last := ContextRewrites.identity_plug_type
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm (inner.plug term)) (encodeTm left) (encodeTm right) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_id, contextCode] using
        (ih term (nodeC "hd-context-id-type" [encodeTm left, encodeTm right, rest])).trans (Relation.ReflTransGen.single last)
  | idLeft carrier inner right ih =>
      have last := ContextRewrites.identity_plug_left
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm carrier) (encodeTm (inner.plug term)) (encodeTm right) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_id, contextCode] using
        (ih term (nodeC "hd-context-id-left" [encodeTm carrier, encodeTm right, rest])).trans (Relation.ReflTransGen.single last)
  | idRight carrier left inner ih =>
      have last := ContextRewrites.identity_plug_right
        (fun rule member => included rule (by simp [ContextRules.traversal, member]))
        (encodeTm carrier) (encodeTm left) (encodeTm (inner.plug term)) rest continuation
      simpa only [ComputationSyntax.Context.plug, encodeTm_id, contextCode] using
        (ih term (nodeC "hd-context-id-right" [encodeTm carrier, encodeTm left, rest])).trans (Relation.ReflTransGen.single last)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContextTraversal
