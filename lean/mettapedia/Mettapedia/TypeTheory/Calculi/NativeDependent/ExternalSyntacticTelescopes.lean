import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualPresentation

/-!
# Telescopes in the generated contextual model

The generated context category retains its raw telescope objects. Chosen
comprehension therefore determines both the preceding object and the selected
family class. In this particular model a finite telescope over a fixed object
is unique. This is a property of the generated presentation, rather than an
assumption about arbitrary dependent models.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticTelescopes

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem raw_context_ext {first second : Context D}
    (arity : first.arity = second.arity) (raw : HEq first.raw second.raw) : first = second := by
  cases first
  cases second
  cases arity
  cases eq_of_heq raw
  rfl

theorem extension_injective {first second : QuotientCwf.QContext D}
    {left : QuotientCwf.Ty first} {right : QuotientCwf.Ty second}
    (equal : QuotientCwf.ext first left = QuotientCwf.ext second right) :
    first = second ∧ HEq left right := by
  have counts : first.as.arity = second.as.arity :=
    Nat.succ.inj (congrArg (fun context => context.as.arity) equal)
  cases first with
  | mk first =>
    cases second with
    | mk second =>
      cases first with
      | mk firstArity firstRaw firstFormed =>
        cases second with
        | mk secondArity secondRaw secondFormed =>
          dsimp only at counts
          cases counts
          have raws :
              ContextExpr.snoc firstRaw (QuotientCwf.typeRepresentative left).code =
                ContextExpr.snoc secondRaw (QuotientCwf.typeRepresentative right).code :=
            eq_of_heq (Sigma.mk.inj (congrArg
              (fun context => (⟨context.as.arity, context.as.raw⟩ : Σ n, ContextExpr S n)) equal)).2
          have parts := ContextExpr.snoc.inj raws
          cases parts.1
          have types : left = right := by
            calc
              left = QType.mk (QuotientCwf.typeRepresentative left) :=
                (QuotientCwf.typeRepresentative_class left).symm
              _ = QType.mk (QuotientCwf.typeRepresentative right) :=
                congrArg QType.mk (TypeOver.ext parts.2)
              _ = right := QuotientCwf.typeRepresentative_class right
          exact ⟨rfl, heq_of_eq types⟩

theorem telescope_heq : {n : Nat} → {firstContext secondContext : QuotientCwf.QContext D} →
    (first : Telescope (QuotientCwf.withTerminal D) n firstContext) →
    (second : Telescope (QuotientCwf.withTerminal D) n secondContext) →
    firstContext = secondContext → HEq first second
  | _, _, _, .nil, .nil, _ => HEq.rfl
  | _, _, _, .snoc previous type, .snoc earlier family, contexts => by
      have components := extension_injective contexts
      cases components.1
      cases eq_of_heq components.2
      cases eq_of_heq (telescope_heq previous earlier rfl)
      rfl

instance telescopeSubsingleton {n : Nat} (context : QuotientCwf.QContext D) :
    Subsingleton (Telescope (QuotientCwf.withTerminal D) n context) :=
  ⟨fun first second => eq_of_heq (telescope_heq first second rfl)⟩

theorem semantic_context_ext {n : Nat}
    (first second : Mettapedia.TypeTheory.ContextualModelTelescopes.Context
      (QuotientCwf.withTerminal D) n)
    (contexts : first.1 = second.1) : first = second :=
  Sigma.ext contexts (telescope_heq first.2 second.2 contexts)

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticTelescopes
