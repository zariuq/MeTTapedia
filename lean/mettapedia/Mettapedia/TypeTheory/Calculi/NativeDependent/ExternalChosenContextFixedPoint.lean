import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticTelescopes

/-!
# Fixed points of the chosen-context presentation

The presentation selector fixes every context built from the actual empty
context and chosen type representatives. Its extension step first transports
the admitted annotation, then selects the representative of its type class.
On the chosen image that class is the original supplied class. Raw contexts
outside this image still retain their distinct syntax and comparison maps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Presentation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes

universe u
variable {S : Symbols.{u}} {D : Signature S}

private theorem representative_code_at_equal_context {n : Nat}
    {first second : ContextExpr S n} (firstFormed : Formed D first)
    (secondFormed : Formed D second) (same : first = second)
    (type : QType (contextOf second secondFormed))
    (typed : Holds D (.type first (QuotientCwf.typeRepresentative type).code)) :
    (QuotientCwf.typeRepresentative
      (QType.mk (⟨(QuotientCwf.typeRepresentative type).code, typed⟩ :
        TypeOver (contextOf first firstFormed)))).code =
      (QuotientCwf.typeRepresentative type).code := by
  cases same
  change (QuotientCwf.typeRepresentative
    (QType.mk (QuotientCwf.typeRepresentative type))).code = _
  rw [QuotientCwf.typeRepresentative_class]

theorem selectedContext_fixed {context : Context D} (chosen : Chosen D context) :
    selectedContext context = context := by
  induction chosen with
  | empty => rfl
  | @extend context previous type earlier =>
    cases context with
    | mk n raw formed =>
      change (select raw formed).context = contextOf raw formed at earlier
      have raws : (select raw formed).selected = raw := by
        have same := congrArg
          (fun context : Context D => (⟨context.arity, context.raw⟩ : Σ n, ContextExpr S n)) earlier
        exact eq_of_heq (Sigma.mk.inj same).2
      refine SyntacticTelescopes.raw_context_ext
        (selected_arity (extend (contextOf raw formed) (QuotientCwf.typeRepresentative type))) ?_
      apply heq_of_eq
      change ContextExpr.snoc (select raw formed).selected _ = ContextExpr.snoc raw _
      apply congrArg₂ ContextExpr.snoc raws
      exact representative_code_at_equal_context (select raw formed).formed formed raws type _

theorem chosen_of_telescope : {n : Nat} → {context : QuotientCwf.QContext D} →
    Telescope (QuotientCwf.withTerminal D) n context → Chosen D context.as
  | _, _, .nil => .empty
  | _, _, .snoc previous type => .extend (chosen_of_telescope previous) type

theorem selectedContext_telescope_fixed {n : Nat} {context : QuotientCwf.QContext D}
    (telescope : Telescope (QuotientCwf.withTerminal D) n context) :
    selectedContext context.as = context.as :=
  selectedContext_fixed (chosen_of_telescope telescope)

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.Presentation
