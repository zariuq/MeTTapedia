import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentHereditary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongWeakening

/-!
# η-long spines of a variable along its declared Π binders

The two spine facts that hereditary substitution of a pruning answer on η-long forms needs, for a variable `x` whose
declared type has at least as many literal Π binders as the spine has arguments:

* **inversion** (`spine_args`): an η-long spine `x a₁ … aₖ` has each argument η-long at the domain of its position,
  read along the declared type instantiated at the arguments before it (`piAfter`), and the spine's type is the
  declared type instantiated at all of them;
* **construction** (`spine_build`): conversely, arguments η-long at those domains make an η-long spine of `x`, at the
  instantiated declared type.

They are stated for every context and every variable, with the arguments listed last first (`appsRev`), the order in
which a spine judgment is built.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentHereditary

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentEtaLong ContextualDependentDynamicFragment

variable {Head : Type}

/-! ## Spines along literal Π binders -/

/-- `appsRev t [aₖ, …, a₁] = t a₁ … aₖ`: a head applied to arguments, the last one first. -/
def appsRev {n : Nat} (head : Tm Head n) : List (Tm Head n) → Tm Head n
  | [] => head
  | argument :: rest => .app (appsRev head rest) argument

/-- The type of a spine after its arguments (the last one first), read along literal Π binders. -/
def piAfter {n : Nat} (type : Tm Head n) : List (Tm Head n) → Tm Head n
  | [] => type
  | argument :: rest =>
      match piAfter type rest with
      | .pi _ codomain => inst0 argument codomain
      | other => other

/-- The domain of a literal Π type. -/
def piDomain {n : Nat} : Tm Head n → Tm Head n
  | .pi domain _ => domain
  | other => other

/-- Substitution never removes a leading Π binder. -/
theorem piCount_le_subst : ∀ {n m : Nat} (σ : Sub Head n m) (t : Tm Head n), piCount t ≤ piCount (subst σ t)
  | _, _, σ, .pi _ B => by
      simp only [piCount, subst]
      exact Nat.succ_le_succ (piCount_le_subst (liftSub σ) B)
  | _, _, _, .var _ | _, _, _, .const _ | _, _, _, .head _ | _, _, _, .sigma _ _ | _, _, _, .id _ _ _
  | _, _, _, .lam _ | _, _, _, .app _ _ | _, _, _, .pair _ _ | _, _, _, .fst _ | _, _, _, .snd _
  | _, _, _, .refl _ => Nat.zero_le _

theorem pi_of_piCount {n : Nat} : ∀ {t : Tm Head n}, 0 < piCount t → ∃ A B, t = .pi A B
  | .pi A B, _ => ⟨A, B, rfl⟩
  | .var _, h | .const _, h | .head _, h | .sigma _ _, h | .id _ _ _, h | .lam _, h | .app _ _, h | .pair _ _, h
  | .fst _, h | .snd _, h | .refl _, h => by simp [piCount] at h

/-- Instantiating along literal Π binders consumes one binder per argument. -/
theorem piCount_piAfter {n : Nat} (type : Tm Head n) :
    ∀ (arguments : List (Tm Head n)), arguments.length ≤ piCount type →
      piCount type ≤ piCount (piAfter type arguments) + arguments.length
  | [], _ => by simp [piAfter]
  | argument :: rest, short => by
      have earlier := piCount_piAfter type rest (by simp at short; omega)
      obtain ⟨A, B, isPi⟩ := pi_of_piCount (t := piAfter type rest) (by simp at short; omega)
      have instantiated := piCount_le_subst (subst0 argument) B
      rw [isPi] at earlier
      simp only [piAfter, isPi, List.length_cons]
      simp only [piCount] at earlier
      change piCount type ≤ piCount (inst0 argument B) + (rest.length + 1)
      unfold inst0
      omega

/-- Before its last argument, a spine's type along enough literal Π binders is a Π type. -/
theorem piAfter_pi {n : Nat} (type : Tm Head n) (rest : List (Tm Head n)) (short : rest.length < piCount type) :
    ∃ A B, piAfter type rest = .pi A B := by
  have := piCount_piAfter type rest (by omega)
  exact pi_of_piCount (by omega)

/-- Each argument is η-long at the domain of its position. -/
def ArgsLong (R : Rules Head) (roles : Roles Head) {n : Nat} (Γ : Ctx Head n) (type : Tm Head n) :
    List (Tm Head n) → Prop
  | [] => True
  | argument :: rest => ArgsLong R roles Γ type rest ∧ Long R roles (.term Γ argument (piDomain (piAfter type rest)))

/-! ## Inversion and construction -/

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **Inversion of an η-long variable spine** along the variable's literal Π binders. -/
theorem spine_args (facts : FormFacts S.R S.roles) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (x : Fin n) :
    ∀ (arguments : List (Tm Head n)) {U : Tm Head n}, Long S.R S.roles (.spine Γ (appsRev (.var x) arguments) U) →
      arguments.length ≤ piCount (Ctx.lookup Γ x) →
      ArgsLong S.R S.roles Γ (Ctx.lookup Γ x) arguments ∧ TypeEq S.R Γ U (piAfter (Ctx.lookup Γ x) arguments)
  | [], _, long, _ => by
      cases long with
      | var _ e => exact ⟨trivial, e⟩
  | argument :: rest, U, long, short => by
      cases long with
      | app lf eF la eU =>
          obtain ⟨restLong, restType⟩ := spine_args facts formed x rest lf (by simp at short; omega)
          obtain ⟨A', B', isPi⟩ := piAfter_pi (Ctx.lookup Γ x) rest (by simp at short; omega)
          rw [isPi] at restType
          obtain ⟨domains, codomains⟩ := TypeEq.pi_injective facts (TypeEq.trans S.levels eF.symm restType) formed
          refine ⟨⟨restLong, ?_⟩, ?_⟩
          · rw [isPi]
            exact la.convType S.levels domains
          · simp only [piAfter, isPi]
            exact TypeEq.trans S.levels eU (TypeEq.instantiate codomains la.typed)

/-- **Construction of an η-long variable spine** from arguments η-long at their domains. -/
theorem spine_build {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (x : Fin n) :
    ∀ (arguments : List (Tm Head n)), ArgsLong S.R S.roles Γ (Ctx.lookup Γ x) arguments →
      arguments.length ≤ piCount (Ctx.lookup Γ x) →
      Long S.R S.roles (.spine Γ (appsRev (.var x) arguments) (piAfter (Ctx.lookup Γ x) arguments)) ∧
        Typed S.R Γ (appsRev (.var x) arguments) (piAfter (Ctx.lookup Γ x) arguments)
  | [], _, _ => by
      have typed : Typed S.R Γ (.var x) (Ctx.lookup Γ x) := Derivable.var x
      exact ⟨.var x (IsType.refl (Typed.isType typed formed)), typed⟩
  | argument :: rest, ⟨restLong, argumentLong⟩, short => by
      obtain ⟨spineLong, spineTyped⟩ := spine_build formed x rest restLong (by simp at short; omega)
      obtain ⟨A, B, isPi⟩ := piAfter_pi (Ctx.lookup Γ x) rest (by simp at short; omega)
      rw [isPi] at spineLong spineTyped argumentLong
      have applied : Typed S.R Γ (.app (appsRev (.var x) rest) argument) (inst0 argument B) :=
        Derivable.appElim spineTyped argumentLong.typed
      have result : piAfter (Ctx.lookup Γ x) (argument :: rest) = inst0 argument B := by
        simp only [piAfter, isPi]
      rw [result]
      exact ⟨.app spineLong (IsType.refl (Typed.isType spineTyped formed)) argumentLong
        (IsType.refl (Typed.isType applied formed)), applied⟩

end ContextualDependentHereditary
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
