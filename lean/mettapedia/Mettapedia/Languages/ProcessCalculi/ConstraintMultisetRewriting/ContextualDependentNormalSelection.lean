import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEndpointInversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSelectionCompatibility

/-!
# Selecting a normal dependent context without checker search

Each retained declaration is inverted along the already selected prefix.
Its formation is reflected from the original typed normal declaration.
Universe witnesses are used only in proofs; the operation does not extract
a universe choice from a proposition or run another bounded checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalSelection

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentNormalChecking ContextualDependentTypedInversion ContextualDependentPruning

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

inductive NormalContext : {n : Nat} → Ctx Head n → Prop
  | nil : NormalContext .nil
  | snoc {n : Nat} {Γ : Ctx Head n} {type : Tm Head n} :
      NormalContext Γ → Normal (S := S) type → NormalContext (.snoc Γ type)

theorem NormalContext.prefix {n : Nat} {Γ : Ctx Head n} {type : Tm Head n}
    (normal : NormalContext (S := S) (.snoc Γ type)) : NormalContext (S := S) Γ := by
  cases normal
  assumption

theorem NormalContext.last {n : Nat} {Γ : Ctx Head n} {type : Tm Head n}
    (normal : NormalContext (S := S) (.snoc Γ type)) : Normal (S := S) type := by
  cases normal
  assumption

structure Selected (Γ : Context S.R) (mask : Fin Γ.arity → Bool) extends ContextualDependentPruning.Selection Γ mask where
  compatible : CtxRen source.raw Γ.raw inclusion.forward

def Selected.drop {Γ : Context S.R} {type : Tm Head Γ.arity} {formed : IsType S.R Γ.raw type}
    {mask : Fin (Γ.arity + 1) → Bool}
    (prior : Selected Γ (fun index => mask index.succ)) (omitted : mask 0 = false) :
    Selected (extendKnown Γ type formed) mask where
  toSelection := prior.toSelection.drop omitted
  compatible := ContextualDependentSelectionCompatibility.drop_compatible prior.inclusion prior.compatible type formed

def keepKnown {Γ Δ : Context S.R} (inclusion : Inclusion Γ Δ)
    (source : Tm Head Γ.arity) (sourceFormed : IsType S.R Γ.raw source)
    (target : Tm Head Δ.arity) (targetFormed : IsType S.R Δ.raw target)
    (recovers : Presentation.rename inclusion.forward source = target) :
    Inclusion (extendKnown Γ source sourceFormed) (extendKnown Δ target targetFormed) where
  forward := liftRen inclusion.forward
  injective := liftRen_injective inclusion.injective
  typed := by
    have lifted := inclusion.typed.lift source
    rw [subst_renSub, recovers, liftSub_renSub] at lifted
    exact lifted

def Selected.keep {Γ : Context S.R} {type : Tm Head Γ.arity} {formed : IsType S.R Γ.raw type}
    {mask : Fin (Γ.arity + 1) → Bool} (prior : Selected Γ (fun index => mask index.succ))
    (retained : mask 0 = true) (source : Tm Head prior.source.arity)
    (sourceFormed : IsType S.R prior.source.raw source)
    (recovers : Presentation.rename prior.inclusion.forward source = type) :
    Selected (extendKnown Γ type formed) mask where
  source := extendKnown prior.source source sourceFormed
  inclusion := keepKnown prior.inclusion source sourceFormed type formed recovers
  compatible := by
    have lifted := prior.compatible.snoc source
    rwa [recovers] at lifted
  image target := by
    refine Fin.cases ?_ (fun target => ?_) target
    · exact ⟨fun _ => retained, fun _ => ⟨(0 : Fin (prior.source.arity + 1)), rfl⟩⟩
    · constructor
      · rintro ⟨index, same⟩
        revert same
        refine Fin.cases ?_ (fun index => ?_) index
        · intro impossible
          exact False.elim (Fin.succ_ne_zero _ impossible.symm)
        · intro same
          exact (prior.image target).mp ⟨index, Fin.succ_injective _ same⟩
      · intro selected
        obtain ⟨index, same⟩ := (prior.image target).mpr selected
        exact ⟨index.succ, congrArg Fin.succ same⟩

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)

include facts roots heads algebra headTypingUnique complete declared reflects in
theorem formation_reflects {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (body : Tm Head source.arity)
    (type : Tm Head target.arity) (formed : IsType S.R target.raw type)
    (normal : Normal (S := S) type) (image : Presentation.rename inclusion.forward body = type) :
    IsType S.R source.raw body := by
  obtain ⟨level, universeWitness, typed⟩ := formed
  have certificate := ContextualDependentCheckingReplay.normal_certificate facts algebra headTypingUnique complete
    target.formed typed normal
  have reflected := ContextualDependentCheckingReflection.checking_reflects reflects certificate
    source.raw inclusion.forward inclusion.injective compatible body (.head level) image rfl
  exact ⟨level, universeWitness, CheckingAlgorithm.sound facts roots heads algebra declared reflected source.formed
    (universe_type (S := S) universeWitness)⟩

private theorem prefixFormed {n : Nat} {Γ : Ctx Head n} {type : Tm Head n}
    (formed : CtxFormed S.R (.snoc Γ type)) : CtxFormed S.R Γ := by
  cases formed
  assumption

private theorem lastFormed {n : Nat} {Γ : Ctx Head n} {type : Tm Head n}
    (formed : CtxFormed S.R (.snoc Γ type)) : IsType S.R Γ type := by
  cases formed
  assumption

def select : {n : Nat} → (raw : Ctx Head n) → (formed : CtxFormed S.R raw) →
    NormalContext (S := S) raw → (mask : Fin n → Bool) → Option (Selected (⟨n, raw, formed⟩ : Context S.R) mask)
  | _, .nil, _, _, _ => some
      ⟨⟨empty S.R, ⟨Fin.elim0, fun index => index.elim0, fun index => index.elim0⟩,
        fun index => index.elim0⟩, fun index => index.elim0⟩
  | _, .snoc raw type, formed, normal, mask => do
      let prior ← select raw (prefixFormed formed) normal.prefix (fun index => mask index.succ)
      if retained : mask 0 = true then
        match inverted : ContextualDependentInversion.invert
            (ContextualDependentInversion.lookup prior.inclusion.forward) type with
        | none => none
        | some code =>
            have image := ContextualDependentInversion.invert_sound type prior.inclusion.forward _
              (ContextualDependentInversion.lookup_exact prior.inclusion.forward prior.inclusion.injective) code inverted
            some (prior.keep (formed := lastFormed formed) retained code
              (formation_reflects facts roots heads algebra headTypingUnique complete declared reflects
                prior.inclusion prior.compatible code type (lastFormed formed) normal.last image) image)
      else some (prior.drop (formed := lastFormed formed) (Bool.eq_false_iff.mpr retained))

/-- Every selected declaration retains all dependencies of its declared type. -/
def Closed {n : Nat} (raw : Ctx Head n) (mask : Fin n → Bool) : Prop :=
  ∀ index, mask index = true → ∀ dependency ∈ (Ctx.lookup raw index).support, mask dependency = true

theorem Closed.prefix {n : Nat} {raw : Ctx Head n} {type : Tm Head n} {mask : Fin (n + 1) → Bool}
    (closed : Closed (.snoc raw type) mask) : Closed raw (fun index => mask index.succ) := by
  intro index retained dependency present
  apply closed index.succ retained dependency.succ
  change dependency.succ ∈ (Presentation.rename wk (Ctx.lookup raw index)).support
  rw [ContextualDependentSupport.support_rename]
  exact Finset.mem_image.mpr ⟨dependency, present, rfl⟩

theorem Closed.last {n : Nat} {raw : Ctx Head n} {type : Tm Head n} {mask : Fin (n + 1) → Bool}
    (closed : Closed (.snoc raw type) mask) (retained : mask 0 = true) :
    ∀ dependency ∈ type.support, mask dependency.succ = true := by
  intro dependency present
  apply closed 0 retained dependency.succ
  change dependency.succ ∈ (Presentation.rename wk type).support
  rw [ContextualDependentSupport.support_rename]
  exact Finset.mem_image.mpr ⟨dependency, present, rfl⟩

theorem Selected.closed {Γ : Context S.R} {mask : Fin Γ.arity → Bool} (selected : Selected Γ mask) :
    Closed Γ.raw mask := by
  intro index retained dependency present
  obtain ⟨original, image⟩ := (selected.image index).mpr retained
  subst index
  rw [selected.compatible, ContextualDependentSupport.support_rename] at present
  obtain ⟨prior, _, image⟩ := Finset.mem_image.mp present
  exact (selected.image dependency).mp ⟨prior, image⟩

set_option backward.isDefEq.respectTransparency false in
theorem select_of_closed {n : Nat} (raw : Ctx Head n) :
    ∀ (formed : CtxFormed S.R raw) (normal : NormalContext (S := S) raw) (mask : Fin n → Bool),
      Closed raw mask →
      (select facts roots heads algebra headTypingUnique complete declared reflects raw formed normal mask).isSome = true := by
  induction raw with
  | nil => intros; rfl
  | snoc raw type ih =>
      intro formed normal mask closed
      obtain ⟨prior, priorFound⟩ := Option.isSome_iff_exists.mp
        (ih (prefixFormed formed) normal.prefix (fun index => mask index.succ) closed.prefix)
      simp only [select, priorFound]
      split
      · rename_i retained
        have invertible := (ContextualDependentSupport.invert_lookup_defined_iff
          prior.inclusion.forward prior.inclusion.injective type).mpr (by
            intro dependency present
            exact (prior.image dependency).mpr (closed.last retained dependency present))
        obtain ⟨code, found⟩ := Option.isSome_iff_exists.mp invertible
        dsimp only [Bind.bind, Option.bind]
        split
        · rename_i missing
          rw [missing] at found
          cases found
        · rfl
      · rfl

theorem select_success_iff {n : Nat} (raw : Ctx Head n) (formed : CtxFormed S.R raw)
    (normal : NormalContext (S := S) raw) (mask : Fin n → Bool) :
    (select facts roots heads algebra headTypingUnique complete declared reflects raw formed normal mask).isSome = true ↔
      Closed raw mask := by
  constructor
  · intro success
    obtain ⟨selected, _⟩ := Option.isSome_iff_exists.mp success
    exact selected.closed
  · exact select_of_closed facts roots heads algebra headTypingUnique complete declared reflects raw formed normal mask

end ContextualDependentNormalSelection
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
