import Mettapedia.GSLT.LanguageDef.LF.BetaEtaConversion
import Mathlib.Logic.Relation

/-!
# Contextual beta-delta-eta certificates for LF

The inductive LF reduction relation closes beta, delta, and eta steps under
every term constructor and under transitivity.  This file gives an equivalent
certificate representation whose atomic evidence is more explicit:

* a `RootStep` records one beta, delta, or eta contraction;
* a one-hole `Context` records the exact position of that contraction;
* a finite reflexive-transitive path records composition.

The representation is semantic: it does not yet prescribe a serialized proof
format or a checker implementation.  Its purpose is to identify the complete
certificate language that such a checker must represent.  In particular, it
supports arbitrary nesting under products, abstractions, and applications,
unlike a fixed family of binder-wrapped congruence schemas.
-/

namespace Mettapedia.GSLT.LanguageDef.LFContextualBetaEta

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping
open Mettapedia.GSLT.LanguageDef.LFBetaEta

/-- A one-hole context for LF terms.  Constructors distinguish every argument
position, so a certificate exposes the exact location of its root step. -/
inductive Context where
  | hole
  | piDomain (rest : Context) (body : Term)
  | piBody (domain : Term) (rest : Context)
  | lamDomain (rest : Context) (body : Term)
  | lamBody (domain : Term) (rest : Context)
  | appFunction (rest : Context) (argument : Term)
  | appArgument (function : Term) (rest : Context)
deriving DecidableEq, Repr

namespace Context

/-- Fill the distinguished hole of a context. -/
def plug : Context → Term → Term
  | .hole, term => term
  | .piDomain rest body, term => .pi (rest.plug term) body
  | .piBody domain rest, term => .pi domain (rest.plug term)
  | .lamDomain rest body, term => .lam (rest.plug term) body
  | .lamBody domain rest, term => .lam domain (rest.plug term)
  | .appFunction rest argument, term => .app (rest.plug term) argument
  | .appArgument function rest, term => .app function (rest.plug term)

/-- Context composition: `outer.comp inner` first fills `inner`, then places
the result in `outer`. -/
def comp : Context → Context → Context
  | .hole, inner => inner
  | .piDomain rest body, inner => .piDomain (rest.comp inner) body
  | .piBody domain rest, inner => .piBody domain (rest.comp inner)
  | .lamDomain rest body, inner => .lamDomain (rest.comp inner) body
  | .lamBody domain rest, inner => .lamBody domain (rest.comp inner)
  | .appFunction rest argument, inner =>
      .appFunction (rest.comp inner) argument
  | .appArgument function rest, inner =>
      .appArgument function (rest.comp inner)

theorem plug_comp (outer inner : Context) (term : Term) :
    (outer.comp inner).plug term = outer.plug (inner.plug term) := by
  induction outer <;> simp [comp, plug, *]

end Context

/-- A single contraction at the root, before any contextual closure. -/
inductive RootStep (signature : LFTyping.Sig) : Term → Term → Prop where
  | beta {domain body argument} :
      RootStep signature (.app (.lam domain body) argument)
        (subst0 argument body)
  | delta {name body} :
      lookupBody signature name = some body →
      RootStep signature (.con name) body
  | eta {domain function reduced} :
      unbind 0 function = some reduced →
      RootStep signature
        (.lam domain (.app function (.var 0))) reduced

/-- One root contraction placed at one explicit position. -/
inductive ContextualStep (signature : LFTyping.Sig) : Term → Term → Prop where
  | inContext {source target : Term}
      (context : Context)
      (step : RootStep signature source target) :
      ContextualStep signature
        (context.plug source) (context.plug target)

theorem RootStep.sound {signature : LFTyping.Sig} {source target : Term}
    (step : RootStep signature source target) :
    LFBetaEta.Reduces signature source target := by
  cases step with
  | beta => exact .beta
  | delta hbody => exact .delta hbody
  | eta hunbind => exact .eta hunbind

/-- Semantic reduction is closed under an arbitrary one-hole context. -/
theorem Context.plug_reduces {signature : LFTyping.Sig}
    (context : Context) {source target : Term}
    (reduction : LFBetaEta.Reduces signature source target) :
    LFBetaEta.Reduces signature
      (context.plug source) (context.plug target) := by
  induction context with
  | hole => exact reduction
  | piDomain rest body ih => exact .pi ih .refl
  | piBody domain rest ih => exact .pi .refl ih
  | lamDomain rest body ih => exact .lam ih .refl
  | lamBody domain rest ih => exact .lam .refl ih
  | appFunction rest argument ih => exact .app ih .refl
  | appArgument function rest ih => exact .app .refl ih

theorem ContextualStep.sound {signature : LFTyping.Sig}
    {source target : Term}
    (step : ContextualStep signature source target) :
    LFBetaEta.Reduces signature source target := by
  cases step with
  | inContext context root =>
      exact context.plug_reduces root.sound

/-- Add an outer context to a contextual step without changing its root
evidence. -/
theorem ContextualStep.mapContext {signature : LFTyping.Sig}
    (outer : Context) {source target : Term}
    (step : ContextualStep signature source target) :
    ContextualStep signature
      (outer.plug source) (outer.plug target) := by
  cases step with
  | @inContext rootSource rootTarget inner root =>
      rw [← Context.plug_comp, ← Context.plug_comp]
      exact .inContext (outer.comp inner) root

/-- Map every edge of a finite contextual path through an outer context. -/
theorem path_mapContext {signature : LFTyping.Sig}
    (context : Context) {source target : Term}
    (path : Relation.ReflTransGen (ContextualStep signature) source target) :
    Relation.ReflTransGen (ContextualStep signature)
      (context.plug source) (context.plug target) := by
  induction path with
  | refl => exact .refl
  | tail pathPrefix edge ih =>
      exact Relation.ReflTransGen.tail ih
        (ContextualStep.mapContext context edge)

/-- Every semantic beta-delta-eta reduction has a finite certificate path
made only of explicit root contractions and explicit one-hole contexts. -/
theorem reduces_to_path {signature : LFTyping.Sig} {source target : Term}
    (reduction : LFBetaEta.Reduces signature source target) :
    Relation.ReflTransGen (ContextualStep signature) source target := by
  induction reduction with
  | refl => exact .refl
  | beta => exact .single (.inContext .hole .beta)
  | delta hbody => exact .single (.inContext .hole (.delta hbody))
  | eta hunbind => exact .single (.inContext .hole (.eta hunbind))
  | @pi domain domain' body body' domainReduction bodyReduction
      domainPath bodyPath =>
      exact
        (path_mapContext (.piDomain .hole body) domainPath).trans
          (path_mapContext (.piBody domain' .hole) bodyPath)
  | @lam domain domain' body body' domainReduction bodyReduction
      domainPath bodyPath =>
      exact
        (path_mapContext (.lamDomain .hole body) domainPath).trans
          (path_mapContext (.lamBody domain' .hole) bodyPath)
  | @app function function' argument argument'
      functionReduction argumentReduction functionPath argumentPath =>
      exact
        (path_mapContext (.appFunction .hole argument) functionPath).trans
          (path_mapContext (.appArgument function' .hole) argumentPath)
  | trans firstReduction secondReduction firstPath secondPath =>
      exact firstPath.trans secondPath

/-- Every finite contextual certificate path is sound for semantic
beta-delta-eta reduction. -/
theorem path_to_reduces {signature : LFTyping.Sig} {source target : Term}
    (path : Relation.ReflTransGen (ContextualStep signature) source target) :
    LFBetaEta.Reduces signature source target := by
  induction path with
  | refl => exact .refl
  | tail pathPrefix edge ih => exact .trans ih edge.sound

/-- Crown theorem: semantic LF reduction is exactly finite composition of
root beta/delta/eta steps under explicit one-hole contexts. -/
theorem reduces_iff_contextual_path
    {signature : LFTyping.Sig} {source target : Term} :
    LFBetaEta.Reduces signature source target ↔
      Relation.ReflTransGen (ContextualStep signature) source target :=
  ⟨reduces_to_path, path_to_reduces⟩

/-! ## Executable boundaries -/

private def runtimeType : Term := .srt .type
private def runtimeIdentity : Term := .lam runtimeType (.var 0)
private def runtimePiBetaSource : Term :=
  .pi runtimeType (.app runtimeIdentity runtimeType)
private def runtimePiBetaTarget : Term :=
  .pi runtimeType runtimeType

/-- The non-reflexive product-body reduction missing from the original rooted
presentation is one ordinary contextual step in the complete certificate
language. -/
theorem pi_body_beta_contextual_step :
    ContextualStep [] runtimePiBetaSource runtimePiBetaTarget := by
  exact .inContext (.piBody runtimeType .hole) .beta

theorem pi_body_beta_contextual_path :
    Relation.ReflTransGen (ContextualStep [])
      runtimePiBetaSource runtimePiBetaTarget :=
  .single pi_body_beta_contextual_step

/-- Context composition records nested positions rather than flattening them
into an uncheckable endpoint equality. -/
example :
    ((Context.piBody runtimeType .hole).comp
        (Context.lamBody runtimeType .hole)).plug (.var 0) =
      Term.pi runtimeType (Term.lam runtimeType (.var 0)) := by
  rfl

private def capturedEta : Term :=
  .lam runtimeType (.app (.var 0) (.var 0))

/-- Negative fixture: eta cannot contract when the candidate function itself
contains the variable bound by the surrounding abstraction. -/
theorem captured_eta_not_root_step :
    ¬ RootStep [] capturedEta (.var 0) := by
  intro step
  cases step with
  | eta hunbind =>
      simp [unbind] at hunbind

#print axioms Context.plug_comp
#print axioms RootStep.sound
#print axioms Context.plug_reduces
#print axioms ContextualStep.sound
#print axioms ContextualStep.mapContext
#print axioms path_mapContext
#print axioms reduces_to_path
#print axioms path_to_reduces
#print axioms reduces_iff_contextual_path
#print axioms pi_body_beta_contextual_step
#print axioms captured_eta_not_root_step

end Mettapedia.GSLT.LanguageDef.LFContextualBetaEta
