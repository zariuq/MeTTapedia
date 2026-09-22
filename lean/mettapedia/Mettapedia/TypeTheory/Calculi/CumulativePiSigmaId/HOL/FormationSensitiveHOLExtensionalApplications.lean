import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLExtensionalConservativity

/-!
# Native applications of the extensional HOL declarations

The profile declarations are used here as ordinary native terms.  Each rule
application is a spine headed by its declared constant, and its premises are
explicit proof arguments.  The result is a proof inhabitant of native
Leibniz equality; no conversion rule or meta-level implication is used to
manufacture the conclusion.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLExtensionalApplications

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLExtensionalProfile
open FormationSensitiveHOLProofFamily (proof)
open FormationSensitiveHOLUniformList (rawImp)

variable {n : Nat}

/- Numeral notation for `Fin` does not expose successor form to the structural
substitution simp lemmas.  These lemmas expose precisely the projections used
by the four- and five-argument declaration spines. -/
@[simp] private theorem consSub2_one (newest : Tower.Tm n)
    (older : Sub Tower.Head 1 n) : consSub newest older (1 : Fin 2) = older 0 := by
  have index : (1 : Fin 2) = (0 : Fin 1).succ := by decide
  rw [index, consSub_succ]

@[simp] private theorem consSub3_one (newest : Tower.Tm n)
    (older : Sub Tower.Head 2 n) : consSub newest older (1 : Fin 3) = older 0 := by
  have index : (1 : Fin 3) = (0 : Fin 2).succ := by decide
  rw [index, consSub_succ]

@[simp] private theorem consSub3_two (newest : Tower.Tm n)
    (older : Sub Tower.Head 2 n) : consSub newest older (2 : Fin 3) = older 1 := by
  have index : (2 : Fin 3) = (1 : Fin 2).succ := by decide
  rw [index, consSub_succ]

@[simp] private theorem consSub4_one (newest : Tower.Tm n)
    (older : Sub Tower.Head 3 n) : consSub newest older (1 : Fin 4) = older 0 := by
  have index : (1 : Fin 4) = (0 : Fin 3).succ := by decide
  rw [index, consSub_succ]

@[simp] private theorem consSub4_two (newest : Tower.Tm n)
    (older : Sub Tower.Head 3 n) : consSub newest older (2 : Fin 4) = older 1 := by
  have index : (2 : Fin 4) = (1 : Fin 3).succ := by decide
  rw [index, consSub_succ]

@[simp] private theorem consSub4_three (newest : Tower.Tm n)
    (older : Sub Tower.Head 3 n) : consSub newest older (3 : Fin 4) = older 2 := by
  have index : (3 : Fin 4) = (2 : Fin 3).succ := by decide
  rw [index, consSub_succ]

@[simp] private theorem consSub5_one (newest : Tower.Tm n)
    (older : Sub Tower.Head 4 n) : consSub newest older (1 : Fin 5) = older 0 := by
  have index : (1 : Fin 5) = (0 : Fin 4).succ := by decide
  rw [index, consSub_succ]

@[simp] private theorem consSub5_two (newest : Tower.Tm n)
    (older : Sub Tower.Head 4 n) : consSub newest older (2 : Fin 5) = older 1 := by
  have index : (2 : Fin 5) = (1 : Fin 4).succ := by decide
  rw [index, consSub_succ]

@[simp] private theorem consSub5_three (newest : Tower.Tm n)
    (older : Sub Tower.Head 4 n) : consSub newest older (3 : Fin 5) = older 2 := by
  have index : (3 : Fin 5) = (2 : Fin 4).succ := by decide
  rw [index, consSub_succ]

@[simp] private theorem consSub5_four (newest : Tower.Tm n)
    (older : Sub Tower.Head 4 n) : consSub newest older (4 : Fin 5) = older 3 := by
  have index : (4 : Fin 5) = (3 : Fin 4).succ := by decide
  rw [index, consSub_succ]

@[simp] private theorem liftSub4_two (sigma : Sub Tower.Head 3 n) :
    liftSub sigma (2 : Fin 4) = rename wk (sigma 1) := by
  have index : (2 : Fin 4) = (1 : Fin 3).succ := by decide
  rw [index]
  rfl

@[simp] private theorem liftSub4_three (sigma : Sub Tower.Head 3 n) :
    liftSub sigma (3 : Fin 4) = rename wk (sigma 2) := by
  have index : (3 : Fin 4) = (2 : Fin 3).succ := by decide
  rw [index]
  rfl

def propositionExtensionalityApp {n : Nat}
    (p q forward backward : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.const propositionExtensionalityName) p) q)
    forward) backward

def functionExtensionalityApp {n : Nat}
    (domain codomain function other pointwise : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.app (.const functionExtensionalityName) domain)
    codomain) function) other) pointwise

/-- Propositional extensionality is a fully explicit four-argument native
application. -/
theorem propositionExtensionalityApp_typed {context : Tower.Ctx n}
    {p q forward backward : Tower.Tm n}
    (pTyped : Typing rules context p (liftClosed proposition))
    (qTyped : Typing rules context q (liftClosed proposition))
    (forwardTyped : Typing rules context forward (proof (rawImp p q)))
    (backwardTyped : Typing rules context backward (proof (rawImp q p))) :
    Typing rules context (propositionExtensionalityApp p q forward backward)
      (proof (rawLeibnizAt (liftClosed proposition) p q)) := by
  have appliedP := Typing.appElim
    (propositionExtensionality_typed context) pTyped
  rw [inst0_rename_liftRen_elim0] at appliedP
  have appliedQ := Typing.appElim appliedP qTyped
  rw [← subst_consSub] at appliedQ
  have appliedForward := Typing.appElim appliedQ (by
    simpa [subst, rawImp] using forwardTyped)
  rw [← subst_consSub] at appliedForward
  have appliedBackward := Typing.appElim appliedForward (by
    simpa [subst, rawImp] using backwardTyped)
  rw [← subst_consSub] at appliedBackward
  simpa [propositionExtensionalityApp, subst,
    rawLeibnizAt_subst] using appliedBackward

/-- Function extensionality remains universe-polymorphic at the object level:
the domain and codomain codes are the first two explicit arguments. -/
theorem functionExtensionalityApp_typed {context : Tower.Ctx n}
    {domain codomain function other pointwise : Tower.Tm n}
    (domainTyped : Typing rules context domain (sortTm Tower.zero))
    (codomainTyped : Typing rules context codomain (sortTm Tower.zero))
    (functionTyped : Typing rules context function (arrow domain codomain))
    (otherTyped : Typing rules context other (arrow domain codomain))
    (pointwiseTyped : Typing rules context pointwise
      (pointwiseEquality domain codomain function other)) :
    Typing rules context
      (functionExtensionalityApp domain codomain function other pointwise)
      (proof (rawLeibnizAt (arrow domain codomain) function other)) := by
  have appliedDomain := Typing.appElim
    (functionExtensionality_typed context) domainTyped
  rw [inst0_rename_liftRen_elim0] at appliedDomain
  have appliedCodomain := Typing.appElim appliedDomain codomainTyped
  rw [← subst_consSub] at appliedCodomain
  have appliedFunction := Typing.appElim appliedCodomain (by
    simpa [subst, arrow] using functionTyped)
  rw [← subst_consSub] at appliedFunction
  have appliedOther := Typing.appElim appliedFunction (by
    simpa [subst, arrow] using otherTyped)
  rw [← subst_consSub] at appliedOther
  have appliedOtherNormalized : Typing rules context
      (.app (.app (.app (.app (.const functionExtensionalityName) domain)
        codomain) function) other)
      (functionExtensionalityBody domain codomain function other) := by
    simpa [functionExtensionalityBody, subst, pointwiseEquality,
      rawLeibnizAt_subst, arrow,
      FormationSensitiveHOLProofFamily.proof_subst,
      FormationSensitiveHOLProofFamily.proof_rename] using appliedOther
  have bodyShape : functionExtensionalityBody domain codomain function other =
      .pi (pointwiseEquality domain codomain function other)
        (rename wk (proof
          (rawLeibnizAt (arrow domain codomain) function other))) := by
    simp only [functionExtensionalityBody]
  rw [bodyShape] at appliedOtherNormalized
  have appliedPointwise := Typing.appElim
    (g := .app (.app (.app (.app (.const functionExtensionalityName) domain)
      codomain) function) other)
    (a := pointwise)
    (A := pointwiseEquality domain codomain function other)
    (B := rename wk
      (proof (rawLeibnizAt (arrow domain codomain) function other)))
    appliedOtherNormalized (by
    simpa [subst, pointwiseEquality, rawLeibnizAt_subst,
      FormationSensitiveHOLProofFamily.proof_subst] using pointwiseTyped)
  simpa only [functionExtensionalityApp, inst0_rename_wk] using appliedPointwise

namespace Controls

/-- Supplying only the forward implication leaves an explicit function waiting
for the backward proof; it is not yet a proof of equality. -/
theorem proposition_one_direction_is_partial {context : Tower.Ctx n}
    {p q forward : Tower.Tm n}
    (pTyped : Typing rules context p (liftClosed proposition))
    (qTyped : Typing rules context q (liftClosed proposition))
    (forwardTyped : Typing rules context forward (proof (rawImp p q))) :
    Typing rules context
      (.app (.app (.app (.const propositionExtensionalityName) p) q) forward)
      (.pi (proof (rawImp q p))
        (rename wk (proof (rawLeibnizAt (liftClosed proposition) p q)))) := by
  have appliedP := Typing.appElim
    (propositionExtensionality_typed context) pTyped
  rw [inst0_rename_liftRen_elim0] at appliedP
  have appliedQ := Typing.appElim appliedP qTyped
  rw [← subst_consSub] at appliedQ
  have appliedForward := Typing.appElim appliedQ (by
    simpa [subst, rawImp] using forwardTyped)
  rw [← subst_consSub] at appliedForward
  simpa [subst, rawLeibnizAt_subst, rawImp,
    FormationSensitiveHOLProofFamily.proof_rename] using appliedForward

/-- Supplying two functions but no pointwise proof likewise leaves the final
premise visible in the native type. -/
theorem function_without_pointwise_is_partial {context : Tower.Ctx n}
    {domain codomain function other : Tower.Tm n}
    (domainTyped : Typing rules context domain (sortTm Tower.zero))
    (codomainTyped : Typing rules context codomain (sortTm Tower.zero))
    (functionTyped : Typing rules context function (arrow domain codomain))
    (otherTyped : Typing rules context other (arrow domain codomain)) :
    Typing rules context
      (.app (.app (.app (.app (.const functionExtensionalityName) domain)
        codomain) function) other)
      (functionExtensionalityBody domain codomain function other) := by
  have appliedDomain := Typing.appElim
    (functionExtensionality_typed context) domainTyped
  rw [inst0_rename_liftRen_elim0] at appliedDomain
  have appliedCodomain := Typing.appElim appliedDomain codomainTyped
  rw [← subst_consSub] at appliedCodomain
  have appliedFunction := Typing.appElim appliedCodomain (by
    simpa [subst, arrow] using functionTyped)
  rw [← subst_consSub] at appliedFunction
  have appliedOther := Typing.appElim appliedFunction (by
    simpa [subst, arrow] using otherTyped)
  rw [← subst_consSub] at appliedOther
  simpa [functionExtensionalityBody, subst, pointwiseEquality,
    rawLeibnizAt_subst, arrow,
    FormationSensitiveHOLProofFamily.proof_subst,
    FormationSensitiveHOLProofFamily.proof_rename] using appliedOther

end Controls

#print axioms propositionExtensionalityApp_typed
#print axioms functionExtensionalityApp_typed
#print axioms Controls.proposition_one_direction_is_partial
#print axioms Controls.function_without_pointwise_is_partial

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLExtensionalApplications
