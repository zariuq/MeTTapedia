import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContext

/-!
# Why semantic typing of extracted result types requires coherence

Two accepted replay trees for t : A can be placed in the two endpoints of
the independently checked identity formation in Σ(_:A). Id A t t. The term
(t, refl t) checks against this Sigma type, and its resultFormation is exactly
that supplied formation. Its set value is (a, ∅); its fibre is truthCode(a = b).

Thus membership of this actual pair in its own extracted result type entails
agreement of the original interpretations. Conversely, agreement and membership
of a in A give membership of the pair. No general typing-soundness or coherence
assumption is made. The result identifies a necessary obligation, rather than
introducing an alternative semantic model or restricting accepted programs.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation.CoherenceWitness

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (sigmaSet mem_sigmaSet)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u
variable {Head : Type} {n : Nat}

def term (subject : Tm Head n) : Tm Head n := .pair subject (.refl subject)

def type (A subject : Tm Head n) : Tm Head n :=
  .sigma A (rename wk (.id A subject subject))

def formation (level : Head) (domain first second : Code Head NoConversion n) :
    Code Head NoConversion n :=
  .sigmaForm level level domain
    (.idForm level (domain.rename noConversionRename wk)
      (first.rename noConversionRename wk) (second.rename noConversionRename wk))

def code (level joined : Head) (A : Tm Head n)
    (domain first second : Code Head NoConversion n) : Code Head NoConversion n :=
  .pairIntro joined (formation level domain first second) first (.reflIntro A first)

theorem resultFormation_exact (universeSuccessor : Head → Head)
    (contextCode : ContextCode Head NoConversion n) (level joined : Head)
    (A subject : Tm Head n) (domain first second : Code Head NoConversion n) :
    (code level joined A domain first second).resultFormation noConversionRename noConversionSubstitute
      universeSuccessor contextCode (term subject) (type A subject) =
        some (joined, formation level domain first second) := rfl

section Checking

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

theorem formation_checked (context : Ctx Head n) (level joined : Head)
    (A subject : Tm Head n) (domain first second : Code Head NoConversion n)
    (isUniverse : R.isUniverse level) (atJoin : R.join level level joined)
    (domainChecked : check R noConversionCheck context A (.head level) domain = true)
    (firstChecked : check R noConversionCheck context subject A first = true)
    (secondChecked : check R noConversionCheck context subject A second = true) :
    check R noConversionCheck context (type A subject) (.head joined)
      (formation level domain first second) = true := by
  have renamedDomain := check_rename noConversionRename R noConversionCheck
    (fun _ impossible => nomatch impossible) domain domainChecked
    (target := context.snoc A) (rho := wk) (fun _ => rfl)
  have renamedFirst := check_rename noConversionRename R noConversionCheck
    (fun _ impossible => nomatch impossible) first firstChecked
    (target := context.snoc A) (rho := wk) (fun _ => rfl)
  have renamedSecond := check_rename noConversionRename R noConversionCheck
    (fun _ impossible => nomatch impossible) second secondChecked
    (target := context.snoc A) (rho := wk) (fun _ => rfl)
  simp only [type, formation, rename, check, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨isUniverse, isUniverse⟩, atJoin⟩, domainChecked⟩,
    ⟨⟨⟨⟨isUniverse, renamedDomain⟩, renamedFirst⟩, renamedSecond⟩, True.intro⟩⟩

theorem checked (context : Ctx Head n) (level joined : Head)
    (A subject : Tm Head n) (domain first second : Code Head NoConversion n)
    (isUniverse : R.isUniverse level) (joinedUniverse : R.isUniverse joined)
    (atJoin : R.join level level joined)
    (domainChecked : check R noConversionCheck context A (.head level) domain = true)
    (firstChecked : check R noConversionCheck context subject A first = true)
    (secondChecked : check R noConversionCheck context subject A second = true) :
    check R noConversionCheck context (term subject) (type A subject)
      (code level joined A domain first second) = true := by
  have formed := formation_checked R context level joined A subject domain first second
    isUniverse atJoin domainChecked firstChecked secondChecked
  simp only [code, term, type, check, inst0_rename_wk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨joinedUniverse, formed⟩, firstChecked⟩, firstChecked, True.intro⟩

/-- The same construction checks as a whole formed judgment. The context
certificate is used here, rather than added as an unused semantic premise. -/
theorem judgment_checked (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    (level joined : Head) (A subject : Tm Head n) (domain first second : Code Head NoConversion n)
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (isUniverse : R.isUniverse level) (joinedUniverse : R.isUniverse joined)
    (atJoin : R.join level level joined)
    (domainChecked : check R noConversionCheck context A (.head level) domain = true)
    (firstChecked : check R noConversionCheck context subject A first = true)
    (secondChecked : check R noConversionCheck context subject A second = true) :
    checkJudgment R noConversionCheck context (term subject) (type A subject) contextCode
      (code level joined A domain first second) = true := by
  simp only [checkJudgment, Bool.and_eq_true]
  exact ⟨contextChecked, checked R context level joined A subject domain first second
    isUniverse joinedUniverse atJoin domainChecked firstChecked secondChecked⟩

end Checking

noncomputable def termMeaning (first : Meaning.{u} n) : Meaning.{u} n :=
  .plain (fun env => ZFSet.pair (first.value env) ∅)

noncomputable def typeMeaning (domain first second : Meaning.{u} n) : Meaning.{u} n :=
  .plain (fun env => sigmaSet (domain.value env) (fun _ => truthCode (first.value env = second.value env)))

variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

theorem formation_assembles (level : Head) (A subject : Tm Head n)
    (domain first second : Code Head NoConversion n) (d a b : Meaning.{u} n)
    (atDomain : assemble heads constants domain A (.head level) = some d)
    (atFirst : assemble heads constants first subject A = some a)
    (atSecond : assemble heads constants second subject A = some b) (joined : Head) :
    assemble heads constants (formation level domain first second) (type A subject) (.head joined) =
      some (typeMeaning d a b) := by
  have left := assemble_rename noConversionRename heads constants first subject A a atFirst wk
  have right := assemble_rename noConversionRename heads constants second subject A b atSecond wk
  simp only [formation, type, rename, assemble, atDomain, left, right, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]
  rfl

theorem term_assembles (level joined : Head) (A subject : Tm Head n)
    (domain first second : Code Head NoConversion n) (a : Meaning.{u} n)
    (atFirst : assemble heads constants first subject A = some a) :
    assemble heads constants (code level joined A domain first second) (term subject) (type A subject) =
      some (termMeaning a) := by
  simp only [code, term, type, assemble, atFirst, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rfl

/-- Pair membership contains both an ordinary domain obligation and the
agreement of the two replay interpretations. Equality alone is insufficient. -/
theorem membership_iff (d a b : Meaning.{u} n) (env : Environment.{u} n) :
    (termMeaning a).value env ∈ (typeMeaning d a b).value env ↔
      a.value env ∈ d.value env ∧ a.value env = b.value env := by
  constructor
  · intro member
    obtain ⟨x, inside, y, proof, equal⟩ := mem_sigmaSet.mp member
    have coordinates := ZFSet.pair_inj.mp equal
    exact ⟨coordinates.1.symm ▸ inside, (mem_truthCode _ _).mp proof |>.2⟩
  · rintro ⟨inside, same⟩
    exact mem_sigmaSet.mpr ⟨a.value env, inside, ∅, (mem_truthCode _ _).mpr ⟨rfl, same⟩, rfl⟩

/-- This statement uses arbitrary successful source and witness assemblies.
The witness formation is exactly the output of resultFormation_exact. -/
theorem assembled_membership_iff (level joined : Head) (A subject : Tm Head n)
    (domain first second : Code Head NoConversion n) (d a b witness formed : Meaning.{u} n)
    (atDomain : assemble heads constants domain A (.head level) = some d)
    (atFirst : assemble heads constants first subject A = some a)
    (atSecond : assemble heads constants second subject A = some b)
    (atWitness : assemble heads constants (code level joined A domain first second)
      (term subject) (type A subject) = some witness)
    (atFormation : assemble heads constants (formation level domain first second)
      (type A subject) (.head joined) = some formed)
    (env : Environment.{u} n) :
    witness.value env ∈ formed.value env ↔ a.value env ∈ d.value env ∧ a.value env = b.value env := by
  rw [term_assembles heads constants level joined A subject domain first second a atFirst] at atWitness
  rw [formation_assembles heads constants level A subject domain first second d a b
    atDomain atFirst atSecond joined] at atFormation
  cases Option.some.inj atWitness
  cases Option.some.inj atFormation
  exact membership_iff d a b env

theorem unequal_values_reject_witness (d a b : Meaning.{u} n) (env : Environment.{u} n)
    (different : a.value env ≠ b.value env) :
    (termMeaning a).value env ∉ (typeMeaning d a b).value env :=
  fun member => different ((membership_iff d a b env).mp member).2

#print axioms resultFormation_exact
#print axioms formation_checked
#print axioms checked
#print axioms judgment_checked
#print axioms formation_assembles
#print axioms term_assembles
#print axioms assembled_membership_iff
#print axioms unequal_values_reject_witness

end ZFSetReplayInterpretation.CoherenceWitness
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
