import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentTypedInversion

/-!
# Executable dependency-checked telescope selection

Selected declarations are visited in telescope order. Each retained type is
inverted along the already constructed inclusion and checked in the smaller
prefix. A dropped declaration cannot silently remain in a later retained
type. Successful output contains a formed telescope, its typed inclusion,
and a proof that its image is exactly the requested selection.

This operation constructs a requested subcontext. A unification driver must
separately justify its selection from a constraint before replacing a
metavariable by one over the smaller context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPruning

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentTypedInversion

variable {Head : Type} {rules : Rules Head}

def extendKnown (Γ : Context rules) (type : Tm Head Γ.arity) (formed : IsType rules Γ.raw type) :
    Context rules := ⟨Γ.arity + 1, .snoc Γ.raw type, .snoc Γ.formed formed⟩

def drop {Γ Δ : Context rules} (inclusion : Inclusion Γ Δ)
    (type : Tm Head Δ.arity) (formed : IsType rules Δ.raw type) : Inclusion Γ (extendKnown Δ type formed) where
  forward index := (inclusion.forward index).succ
  injective := fun _ _ same => inclusion.injective (Fin.succ_injective _ same)
  typed := by
    intro index
    change Typed rules (.snoc Δ.raw type) (.var (inclusion.forward index).succ)
      (subst (renSub (fun index => (inclusion.forward index).succ)) (Ctx.lookup Γ.raw index))
    rw [subst_renSub]
    have weakened := (inclusion.typed index).weaken (extension := type)
    simpa only [renSub, rename, subst_renSub, rename_comp, wk] using weakened

theorem liftRen_injective {n m : Nat} {forward : Ren n m} (injective : Function.Injective forward) :
    Function.Injective (liftRen forward) := by
  intro first second
  refine Fin.cases ?_ (fun first => ?_) first
  · refine Fin.cases ?_ (fun second => ?_) second
    · intro _; rfl
    · intro same; exact False.elim (Fin.succ_ne_zero _ same.symm)
  · refine Fin.cases ?_ (fun second => ?_) second
    · intro same; exact False.elim (Fin.succ_ne_zero _ same)
    · intro same; exact congrArg Fin.succ (injective (Fin.succ_injective _ same))

def keep {Γ Δ : Context rules} (inclusion : Inclusion Γ Δ) (source : TypeOver Γ)
    (target : Tm Head Δ.arity) (formed : IsType rules Δ.raw target)
    (recovers : rename inclusion.forward source.code = target) :
    Inclusion (extend Γ source) (extendKnown Δ target formed) where
  forward := liftRen inclusion.forward
  injective := liftRen_injective inclusion.injective
  typed := by
    have lifted := inclusion.typed.lift source.code
    rw [subst_renSub, recovers, liftSub_renSub] at lifted
    exact lifted

structure Selection (Γ : Context rules) (requested : Fin Γ.arity → Bool) where
  source : Context rules
  inclusion : Inclusion source Γ
  image : ∀ target, (∃ index, inclusion.forward index = target) ↔ requested target = true

def Selection.drop {Γ : Context rules} {type : Tm Head Γ.arity} {formed : IsType rules Γ.raw type}
    {requested : Fin (Γ.arity + 1) → Bool}
    (prior : Selection Γ (fun index => requested index.succ)) (omitted : requested 0 = false) :
    Selection (extendKnown Γ type formed) requested where
  source := prior.source
  inclusion := ContextualDependentPruning.drop prior.inclusion type formed
  image target := by
    refine Fin.cases ?_ (fun target => ?_) target
    · constructor
      · rintro ⟨index, same⟩
        exact False.elim (Fin.succ_ne_zero _ same)
      · intro accepted
        rw [omitted] at accepted
        cases accepted
    · constructor
      · rintro ⟨index, same⟩
        exact (prior.image target).mp ⟨index, Fin.succ_injective _ same⟩
      · intro selected
        obtain ⟨index, same⟩ := (prior.image target).mpr selected
        exact ⟨index, congrArg Fin.succ same⟩

def Selection.keep {Γ : Context rules} {type : Tm Head Γ.arity} {formed : IsType rules Γ.raw type}
    {requested : Fin (Γ.arity + 1) → Bool}
    (prior : Selection Γ (fun index => requested index.succ)) (retained : requested 0 = true)
    (source : TypeOver prior.source) (recovers : rename prior.inclusion.forward source.code = type) :
    Selection (extendKnown Γ type formed) requested where
  source := extend prior.source source
  inclusion := ContextualDependentPruning.keep prior.inclusion source type formed recovers
  image target := by
    refine Fin.cases ?_ (fun target => ?_) target
    · exact ⟨fun _ => retained, fun _ => ⟨0, rfl⟩⟩
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

private theorem prefixFormed {n : Nat} {Γ : Ctx Head n} {type : Tm Head n}
    (formed : CtxFormed rules (.snoc Γ type)) : CtxFormed rules Γ := by
  cases formed
  assumption

private theorem lastFormed {n : Nat} {Γ : Ctx Head n} {type : Tm Head n}
    (formed : CtxFormed rules (.snoc Γ type)) : IsType rules Γ type := by
  cases formed
  assumption

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

def formType (fuel : Nat) (Γ : Context S.R) (code : Tm Head Γ.arity) :
    Option {type : TypeOver Γ // type.code = code} := do
  let synthesis ← ExecutableChecking.synth S.R choices reducer fuel Γ.raw code
  let universeResult ← ExecutableChecking.asUniverse S.R reducer fuel synthesis.1
  return ⟨⟨code, universeResult.val, universeResult.property.1, by
    have typed := CheckingAlgorithm.sound (S := S) facts roots heads algebra declared synthesis.2.down Γ.formed
    exact Typed.convType typed
      (Reduces.typeEq (S := S) facts roots heads Γ.formed universeResult.property.2 (Typed.isType typed Γ.formed))⟩, rfl⟩

def select (fuel : Nat) : {n : Nat} → (raw : Ctx Head n) →
    (formed : CtxFormed S.R raw) → (requested : Fin n → Bool) →
      Option (Selection (⟨n, raw, formed⟩ : Context S.R) requested)
  | _, .nil, formed, requested => some
      ⟨empty S.R, ⟨Fin.elim0, fun index => index.elim0, fun index => index.elim0⟩,
        fun index => index.elim0⟩
  | _, .snoc raw type, formed, requested => do
      let prior ← select fuel raw (prefixFormed formed) (fun index => requested index.succ)
      if retained : requested 0 = true then
        match inverted : ContextualDependentInversion.invert
            (ContextualDependentInversion.lookup prior.inclusion.forward) type with
        | none => none
        | some code => do
            let checked ← formType facts roots heads algebra declared choices reducer fuel prior.source code
            return prior.keep (formed := lastFormed formed) retained checked.val (by
              rw [checked.property]
              exact ContextualDependentInversion.invert_sound type prior.inclusion.forward _
                (ContextualDependentInversion.lookup_exact prior.inclusion.forward prior.inclusion.injective)
                code inverted)
      else return prior.drop (formed := lastFormed formed) (Bool.eq_false_iff.mpr retained)

end ContextualDependentPruning
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
