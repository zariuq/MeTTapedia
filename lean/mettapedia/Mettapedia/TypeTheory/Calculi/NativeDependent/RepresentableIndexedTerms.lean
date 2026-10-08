import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedFibreReadout

/-!
# Generated forgetful terms and complete judgment soundness

The forgetful term is an actual two-argument primitive in the independently
authored dependent context. Its generated typing and raw evaluation are
proved separately. Every generated judgment is sound in the constructed
native model after local declaration realization has been earned.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations

open _root_.CategoryTheory Opposite
open ContextualModelTelescopes NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

def genericForget (arrow : ArrowSymbol C) : TermExpr (symbols C) 2 :=
  .primitive (.forget arrow) TermExpr.var

def genericForgetFormed (arrow : ArrowSymbol C) :
    Derivation (signature C) (.term (fibreContext arrow) (genericForget arrow)
      (objectType arrow.source 2)) := by
  have tree := deriveList (.primitive (fibreContext arrow) (.forget arrow) TermExpr.var)
    (.cons (fibreContextFormed arrow) (.cons (fibreContextFormed arrow)
      (.cons ((headers C).termResult (.forget arrow))
        (.cons (deriveList (.substitutionIdentity (fibreContext arrow))
          (.cons (fibreContextFormed arrow) .nil)) .nil))))
  change Derivation (signature C) (.term (fibreContext arrow) (genericForget arrow)
    ((objectType arrow.source 2).substitute TermExpr.var)) at tree
  rw [objectType_substitute] at tree
  exact tree

set_option backward.isDefEq.respectTransparency false in
theorem generic_forget_read (arrow : ArrowSymbol C) :
    (model C).evaluateTerm (fibreScope arrow) (genericForget arrow) =
      some ⟨forgetType arrow, forgetValue arrow⟩ := by
  have read := (model C).evaluate_primitive (fibreScope arrow) (.forget arrow)
    TermExpr.var (𝟙 (fibreScope arrow).1) (by
      intro position
      change (model C).evaluateTerm (fibreScope arrow) (.var position) =
        some (((fibreScope arrow).2.lookup position).substitute
          ((NativeModel C).toCwf.idS (fibreScope arrow).1))
      rw [Value.substitute_identity]
      rfl)
  change (model C).evaluateTerm (fibreScope arrow) (genericForget arrow) =
    some (Value.substitute (K := (NativeModel C).toCwf)
      (⟨forgetType arrow, forgetValue arrow⟩ : NativeValue (fibreScope arrow).1)
      (𝟙 (fibreScope arrow).1)) at read
  exact read.trans (congrArg some
    (Value.substitute_identity (K := (NativeModel C).toCwf)
      ⟨forgetType arrow, forgetValue arrow⟩))

theorem generated_sound {judgment : Judgment (symbols C)}
    (derivation : Derivation (signature C) judgment) : Interprets (model C) judgment :=
  derivation.sound (model C) (realization C)
    (NativeLocalTypeOperations.products_substitution C)
    (NativeLocalTypeOperations.products_beta C) (NativeLocalPiEta.products_eta C)

theorem indexed_comprehension_is_interpreted (arrow : ArrowSymbol C) :
    Interprets (model C) (.context (fibreContext arrow)) :=
  generated_sound (fibreContextFormed arrow)

theorem generated_forget_is_interpreted (arrow : ArrowSymbol C) :
    Interprets (model C) (.term (fibreContext arrow) (genericForget arrow)
      (objectType arrow.source 2)) :=
  generated_sound (genericForgetFormed arrow)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations
