import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveRegularity
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SigmaConversionBoundary
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TowerConversionSkeleton
import Mettapedia.TypeTheory.ContextualDependentSequencing

/-!
# Effectful selection of formation-sensitive dependent pairs

The answer types of the existing contextual program carry complete native
formation-sensitive judgments. A selected admitted value `a : A` indexes the
continuation's admitted result `b : B[a]`; independently admitted Sigma
formation then licenses the existing native pair constructor.

The isolated-world handler retains the selected branch, final state and
ordered deferred intents. Renaming and substitution below concern native
values and their judgments, not effectful substitutions of an object-language
CBPV calculus. No new evaluator, total type checker, conversion qualification
or adoption of this candidate judgment is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive.DependentComputation

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualComputationKleisli.Program (bindSigma)
open Mettapedia.TypeTheory.ContextualDependentSequencing

variable {Head : Type} {R : Rules Head} {n m : Nat}
variable {Γ : Ctx Head n} {Δ : Ctx Head m} {A : Tm Head n} {B : Tm Head (n + 1)}

/-- An existing native term with its full formation-sensitive admission. -/
abbrev TypedValue (R : Rules Head) (Γ : Ctx Head n) (A : Tm Head n) :=
  { term : Tm Head n // Judgment R Γ term A }

namespace TypedValue

def rename {ρ : Ren n m} (target : ContextFormation R Δ) (compatible : CtxRen Γ Δ ρ)
    (value : TypedValue R Γ A) : TypedValue R Δ (Presentation.rename ρ A) :=
  ⟨Presentation.rename ρ value.val, target, value.property.typing.renameTyping compatible⟩

def substitute {σ : Sub Head n m} (target : ContextFormation R Δ) (typed : CtxMor R Γ Δ σ)
    (value : TypedValue R Γ A) : TypedValue R Δ (subst σ A) :=
  ⟨subst σ value.val, value.property.substitute target typed⟩

/-- Reindex the dependent fibre using the actual capture-avoiding law. -/
def renameFibre {ρ : Ren n m} (target : ContextFormation R Δ) (compatible : CtxRen Γ Δ ρ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue R Δ (inst0 (Presentation.rename ρ first.val)
      (Presentation.rename (liftRen ρ) B)) :=
  ⟨Presentation.rename ρ second.val, target, by
    have typing := second.property.typing.renameTyping compatible
    rw [rename_inst0] at typing
    exact typing⟩

/-- Typed substitution transports the fibre at the selected native value. -/
def substituteFibre {σ : Sub Head n m} (target : ContextFormation R Δ) (typed : CtxMor R Γ Δ σ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue R Δ (inst0 (subst σ first.val) (subst (liftSub σ) B)) :=
  ⟨subst σ second.val, target, by
    have typing := second.property.typing.substitute typed
    rw [subst_inst0] at typing
    exact typing⟩

end TypedValue

/-- Native pair introduction requires independently admitted Sigma formation. -/
def sigmaPair {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (first : TypedValue R Γ A)
    (second : TypedValue R Γ (inst0 first.val B)) : TypedValue R Γ (.sigma A B) :=
  ⟨.pair first.val second.val, formed.context,
    .pairIntro formed.typing universeWitness first.property.typing second.property.typing⟩

theorem rename_sigmaPair {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) {ρ : Ren n m}
    (target : ContextFormation R Δ) (compatible : CtxRen Γ Δ ρ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue.rename target compatible (sigmaPair formed universeWitness first second) =
      sigmaPair ⟨target, formed.typing.renameTyping compatible⟩ universeWitness
        (TypedValue.rename target compatible first)
        (TypedValue.renameFibre target compatible first second) := by
  apply Subtype.ext
  rfl

theorem substitute_sigmaPair {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) {σ : Sub Head n m}
    (target : ContextFormation R Δ) (typed : CtxMor R Γ Δ σ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue.substitute target typed (sigmaPair formed universeWitness first second) =
      sigmaPair (formed.substitute target typed) universeWitness
        (TypedValue.substitute target typed first)
        (TypedValue.substituteFibre target typed first second) := by
  apply Subtype.ext
  rfl

section Effects

variable {State Intent : Type}

/-- Existing dependent sequencing followed by native pair introduction. -/
def sigmaProgram {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (indices : Program State (TypedValue R Γ A) Intent)
    (next : (first : TypedValue R Γ A) → Program State (TypedValue R Γ (inst0 first.val B)) Intent) :
    Program State (TypedValue R Γ (.sigma A B)) Intent :=
  Program.map (fun value => sigmaPair formed universeWitness value.1 value.2)
    (bindSigma indices next)

/-- Each selected world supplies its own continuation state and branch. Its
intents precede the continuation's intents, and its index remains in the pair. -/
theorem runWorldsAt_sigmaProgram {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (indices : Program State (TypedValue R Γ A) Intent)
    (next : (first : TypedValue R Γ A) → Program State (TypedValue R Γ (inst0 first.val B)) Intent)
    (state : State) (branch : BranchTrace) :
    runWorldsAt (sigmaProgram formed universeWitness indices next) state branch =
      (runWorldsAt indices state branch).flatMap fun prior =>
        (runWorldsAt (next prior.answer) prior.state prior.branch).map fun suffix =>
          { branch := suffix.branch,
            answer := sigmaPair formed universeWitness prior.answer suffix.answer,
            state := suffix.state, intents := prior.intents ++ suffix.intents } := by
  rw [sigmaProgram, runWorldsAt_map, runWorldsAt_bindSigma]
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    WorldResult.mapAnswer, WorldResult.prependIntents]

/-- Forgetting the answer's admission evidence still yields an admitted
native term at every result of the actual contextual execution. -/
theorem result_judgment {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (indices : Program State (TypedValue R Γ A) Intent)
    (next : (first : TypedValue R Γ A) → Program State (TypedValue R Γ (inst0 first.val B)) Intent)
    (state : State) (branch : BranchTrace)
    (output : WorldResult State (Tm Head n) Intent)
    (retained : output ∈ runWorldsAt
      (Program.map Subtype.val (sigmaProgram formed universeWitness indices next)) state branch) :
    Judgment R Γ output.answer (.sigma A B) := by
  rw [runWorldsAt_map] at retained
  obtain ⟨typedOutput, _, equality⟩ := List.mem_map.mp retained
  subst output
  exact typedOutput.answer.property

end Effects

/-! ## A genuinely indexed native identity family -/

namespace Examples

def ground {n : Nat} : Tower.Tm n := .head .legacyGround

def context : Tower.Ctx 2 := .snoc (.snoc .nil ground) ground

theorem context_formed : ContextFormation Tower.rules context :=
  .snoc (.snoc .nil (.headType .legacyGround) (.sort Tower.zero))
    (.headType .legacyGround) (.sort Tower.zero)

def older : TypedValue Tower.rules context ground := ⟨.var 1, context_formed, .var 1⟩
def newer : TypedValue Tower.rules context ground := ⟨.var 0, context_formed, .var 0⟩

/-- The selected term occurs in both endpoints of an actual native identity type. -/
def family : Tower.Tm 3 := .id ground (.var 0) (.var 0)

theorem sigma_formed : Judgment Tower.rules context (.sigma ground family)
    (sortTm (.max Tower.zero Tower.zero)) := by
  refine ⟨context_formed, ?_⟩
  exact .sigmaForm (.headType .legacyGround) (.sort Tower.zero)
    (.idForm (.headType .legacyGround) (.sort Tower.zero) (.var 0) (.var 0))
    (.sort Tower.zero) (.sorts Tower.zero Tower.zero)

def reflexivity (first : TypedValue Tower.rules context ground) :
    TypedValue Tower.rules context (inst0 first.val family) :=
  ⟨.refl first.val, context_formed, by
    simpa only [family, inst0, subst, ground, subst0_zero] using
      (Typing.reflIntro first.property.typing)⟩

def indices : Program Bool (TypedValue Tower.rules context ground) Nat :=
  .choose
    (.write true (.intent 10 (.pure older)))
    (.write false (.intent 20 (.pure newer)))

/-- The effect inspects the selected world's state; the value remains in
the fibre of the selected native term, independently of that effect. -/
def next (first : TypedValue Tower.rules context ground) :
    Program Bool (TypedValue Tower.rules context (inst0 first.val family)) Nat :=
  .read fun state => .intent (if state then 30 else 40) (.pure (reflexivity first))

def result : Program Bool (TypedValue Tower.rules context (.sigma ground family)) Nat :=
  sigmaProgram sigma_formed (.sort _) indices next

theorem selected_worlds :
    runWorlds result false =
      [{ branch := [false], answer := sigmaPair sigma_formed (.sort _) older (reflexivity older),
          state := true, intents := [10, 30] },
       { branch := [true], answer := sigmaPair sigma_formed (.sort _) newer (reflexivity newer),
          state := false, intents := [20, 40] }] := rfl

theorem native_pair_answers :
    (runWorlds result false).map (fun world => world.answer.val) =
      [.pair (.var 1) (.refl (.var 1)), .pair (.var 0) (.refl (.var 0))] := rfl

theorem initial_state_reset_changes_intents :
    (runWorlds result false).map WorldResult.intents ≠
      ((runWorlds indices false).flatMap fun prior =>
        (runWorldsAt (next prior.answer) false prior.branch).map fun suffix =>
          prior.intents ++ suffix.intents) := by decide

theorem selected_types_differ : inst0 older.val family ≠ inst0 newer.val family := by decide

private theorem reflGeneration {n : Nat} {Γ : Tower.Ctx n} {term type : Tower.Tm n}
    (typing : Typing Tower.rules Γ term type) :
    ∀ {value : Tower.Tm n}, term = .refl value →
      ∃ carrier, Typing Tower.rules Γ value carrier ∧
        TypeAdjustment Tower.rules (.id carrier value value) type := by
  induction typing with
  | reflIntro typed _ =>
      intro value equality
      cases equality
      exact ⟨_, typed, .refl _⟩
  | cumul _ order ih =>
      intro value equality
      obtain ⟨carrier, typed, adjustment⟩ := ih equality
      exact ⟨carrier, typed, .trans adjustment (.cumulative order)⟩
  | conv _ _ _ conversion ih _ =>
      intro value equality
      obtain ⟨carrier, typed, adjustment⟩ := ih equality
      exact ⟨carrier, typed, .trans adjustment (.conversion conversion)⟩
  | _ => intro value equality; cases equality

/-- The other branch's selected index cannot be substituted into the fibre
of this reflexivity value, even allowing the native conversion tail rules. -/
theorem wrong_selected_index_not_admitted :
    ¬ Judgment Tower.rules context (.refl older.val) (inst0 newer.val family) := by
  intro judgment
  obtain ⟨carrier, _, adjustment⟩ := reflGeneration judgment.typing rfl
  have conversion := adjustment.toConvOfSourceDisjointHeads
    (fun head => TowerConversionSkeleton.not_conv_id_head carrier older.val older.val head)
  have endpoint := (TowerConversionSkeleton.id_components_of_conv conversion).2.1
  have equality := Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary.normalForms_eq_of_conv
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction.RedStar.refl _)
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction.RedStar.refl _)
    (TowerConversionSkeleton.erase_var_normal (1 : Fin 2))
    (TowerConversionSkeleton.erase_var_normal (0 : Fin 2)) endpoint
  cases equality

end Examples

#print axioms rename_sigmaPair
#print axioms substitute_sigmaPair
#print axioms runWorldsAt_sigmaProgram
#print axioms result_judgment
#print axioms Examples.sigma_formed
#print axioms Examples.selected_worlds
#print axioms Examples.native_pair_answers
#print axioms Examples.initial_state_reset_changes_intents
#print axioms Examples.wrong_selected_index_not_admitted

end FormationSensitive.DependentComputation
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
