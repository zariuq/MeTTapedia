import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualClosedUniverseCodes

/-!
# Seed-sensitive formation traces

The formation trace retains the actual declared seed, including its origin
context. Substitution coherence and constructor congruence preserve this
trace. Consequently the closed-code quotient does not merge distinct seeds
merely because their complete material interpretations coincide.

This is a provenance observation. It does not reflect semantic family
equality, and it deliberately omits identity endpoints and substitution
arrows. Those remain available in the raw derivations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCodeSeedTrace

open CategoryTheory ContextualGeneratedUniverse

universe u
variable {C : Type u} [Category.{u} C]
variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

inductive Trace : Type (u + 1) where
  | seed (origin : (context : LabelledContext C) × seeds context)
  | empty | unit
  | pi (domain body : Trace)
  | sigma (domain body : Trace)
  | w (domain body : Trace)
  | identity (domain : Trace)

def derivation : {context : LabelledContext C} → {domain : MaterialFamily context} →
    Generation seeds seedModel arrows domain → Trace seeds
  | _, _, .seed context label => .seed ⟨context, label⟩
  | _, _, .empty _ => .empty
  | _, _, .unit _ => .unit
  | _, _, .pi domain body => .pi (derivation domain) (derivation body)
  | _, _, .sigma domain body => .sigma (derivation domain) (derivation body)
  | _, _, .w domain body => .w (derivation domain) (derivation body)
  | _, _, .identity domain _ _ => .identity (derivation domain)
  | _, _, .reindex domain _ => derivation domain
  | _, _, .piUnder domain body _ => .pi (derivation domain) (derivation body)
  | _, _, .sigmaUnder domain body _ => .sigma (derivation domain) (derivation body)

theorem substitution {context : LabelledContext C}
    {first second : ContextualClosedUniverseCodes.RawCode seeds seedModel arrows context}
    (related : ContextualUniverseCodes.Equation seeds seedModel arrows first second) :
    derivation seeds seedModel arrows first.2 = derivation seeds seedModel arrows second.2 := by
  induction related with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ earlier later => exact earlier.trans later
  | reindex_identity => rfl
  | reindex_comp => rfl
  | reindex_cong _ _ ih => exact ih

theorem equation {context : LabelledContext C}
    {first second : ContextualClosedUniverseCodes.RawCode seeds seedModel arrows context}
    (related : ContextualClosedUniverseCodes.Equation seeds seedModel arrows first second) :
    derivation seeds seedModel arrows first.2 = derivation seeds seedModel arrows second.2 := by
  induction related with
  | substitution related => exact substitution seeds seedModel arrows related
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ earlier later => exact earlier.trans later
  | reindex_congr _ _ ih => exact ih
  | binary_congr kind _ _ domains bodies =>
    cases kind <;>
      dsimp only [ContextualClosedUniverseCodes.rawBinary,
        ContextualClosedUniverseCodes.generationBinary, derivation] <;> rw [domains, bodies]
  | identity_congr _ _ _ ih => exact congrArg Trace.identity ih
  | under_congr kind _ _ _ domains bodies =>
    cases kind <;>
      dsimp only [ContextualClosedUniverseCodes.rawUnder,
        ContextualClosedUniverseCodes.generationUnder, derivation] <;> rw [domains, bodies]

def codeTrace {context : LabelledContext C} :
    ContextualClosedUniverseCodes.Code seeds seedModel arrows context → Trace seeds :=
  Quotient.lift (fun raw => derivation seeds seedModel arrows raw.2)
    (fun _ _ related => equation seeds seedModel arrows related)

theorem codeTrace_seed (context : LabelledContext C) (label : seeds context) :
    codeTrace seeds seedModel arrows (ContextualClosedUniverseCodes.seed seeds seedModel arrows context label) =
      Trace.seed ⟨context, label⟩ := rfl

theorem codeTrace_reindex {context other : LabelledContext C}
    (change : NatTrans other.base context.base)
    (code : ContextualClosedUniverseCodes.Code seeds seedModel arrows context) :
    codeTrace seeds seedModel arrows
      (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change code) =
        codeTrace seeds seedModel arrows code := by
  induction code using Quotient.inductionOn with
  | _ raw => rfl

theorem seed_injective (context : LabelledContext C) :
    Function.Injective (ContextualClosedUniverseCodes.seed seeds seedModel arrows context) := by
  intro first second same
  have traces := congrArg (codeTrace seeds seedModel arrows) same
  rw [codeTrace_seed, codeTrace_seed] at traces
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Trace.seed.inj traces)).2

theorem codeTrace_binary (kind : ContextualClosedUniverseCodes.BinaryFormation)
    {context : LabelledContext C}
    (domain : ContextualClosedUniverseCodes.Code seeds seedModel arrows context)
    (body : ContextualClosedUniverseCodes.Code seeds seedModel arrows
      (ContextualClosedUniverseCodes.decodeFamily seeds seedModel arrows domain).extension) :
    codeTrace seeds seedModel arrows
        (ContextualClosedUniverseCodes.binary seeds seedModel arrows kind domain body) =
      (match kind with
      | .pi => Trace.pi
      | .sigma => Trace.sigma
      | .w => Trace.w) (codeTrace seeds seedModel arrows domain) (codeTrace seeds seedModel arrows body) := by
  revert body
  refine Quotient.inductionOn domain ?_
  intro raw body
  refine Quotient.inductionOn body ?_
  intro rawBody
  cases kind <;> rfl

theorem codeTrace_identity {context : LabelledContext C}
    (domain : ContextualClosedUniverseCodes.Code seeds seedModel arrows context)
    (left right : (ContextualClosedUniverseCodes.decodeFamily seeds seedModel arrows domain).family.sections) :
    codeTrace seeds seedModel arrows
        (ContextualClosedUniverseCodes.identity seeds seedModel arrows domain left right) =
      Trace.identity (codeTrace seeds seedModel arrows domain) := by
  revert left right
  refine Quotient.inductionOn domain ?_
  intro raw left right
  rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCodeSeedTrace
