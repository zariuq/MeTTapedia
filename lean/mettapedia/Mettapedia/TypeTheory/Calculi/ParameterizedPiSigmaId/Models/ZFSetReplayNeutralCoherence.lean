import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayNeutral

/-!
# Certificate independence for neutral-elimination replay

The finite replay predicate follows the subtrees used by set interpretation.
Every interpreted application or projection must eliminate a variable- or
constant-headed term. Lambda domains are checked recursively through their actual formation
trees. This excludes introduction/elimination redexes without asserting
normalization of arbitrary checked terms or unfolding declared constants.

The comparison retains the set value and the interpreted product domain.
It concerns the existing no-conversion checker, including cumulative universe
wrappers; it is not a qualification of arbitrary conversion rules.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace ZFSetReplayInterpretation

open StructuralTypingReplay

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]

private theorem compare_principal {context : Ctx Head n} {subject firstType : Tm Head n}
    (a : Meaning.{u} n)
    (compare : ∀ (second : Code Head NoConversion n) (secondType : Tm Head n)
      (b : Meaning.{u} n), second.isPrincipal = true →
      check R noConversionCheck context subject secondType second = true →
      assemble heads constants second subject secondType = some b →
      EqualOrHeads firstType secondType → a = b)
    (second : Code Head NoConversion n) (secondType : Tm Head n) (b : Meaning.{u} n)
    (checked : check R noConversionCheck context subject secondType second = true)
    (assembled : assemble heads constants second subject secondType = some b)
    (compatible : EqualOrHeads firstType secondType) : a = b := by
  obtain ⟨view, computed, accepted, _⟩ :=
    second.principalView_checked R noConversionCheck checked
  have principal := (second.principalView_reconstruct computed).2
  have atView := assemble_principalView heads constants second computed subject
  rw [atView] at assembled
  exact compare view.code view.type b principal accepted assembled
    (compatible.trans (second.principalView_equalOrHeads computed).symm)

/-- A qualified replay tree fixes its entire assembled meaning against every
other accepted no-conversion certificate at the same displayed type, or at
another universe head. The competing certificate need not be qualified.
The equality includes the retained product domain and holds on all raw
environments. General redex-bearing replay does not have this property. -/
theorem assemble_neutralEliminations_coherent (first : Code Head NoConversion n) :
    ∀ {context : Ctx Head n} {subject firstType secondType : Tm Head n}
      {second : Code Head NoConversion n} {a b : Meaning.{u} n},
      check R noConversionCheck context subject firstType first = true →
      first.neutralEliminations subject firstType = true →
      assemble heads constants first subject firstType = some a →
      check R noConversionCheck context subject secondType second = true →
      assemble heads constants second subject secondType = some b →
      EqualOrHeads firstType secondType → a = b := by
  induction first with
  | convert _ _ _ _ payload _ _ => exact nomatch payload
  | cumul level source ih =>
      intro context subject firstType secondType second a b checked normal atFirst
        otherChecked atSecond compatible
      cases firstType <;> simp only [check, Bool.false_eq_true] at checked
      simp only [Bool.and_eq_true] at checked
      exact ih checked.1 normal atFirst otherChecked atSecond
        ((EqualOrHeads.heads _ _).trans compatible)
  | headType | var | const _ _ _ | reflIntro _ _ _ =>
      intro context subject firstType secondType second a b checked normal atFirst
        otherChecked atSecond compatible
      cases subject <;> simp only [assemble, reduceCtorEq, Option.some.injEq] at atFirst
      all_goals
        subst a
        apply compare_principal heads constants R _ ?_ second secondType b
          otherChecked atSecond compatible
        intro other otherType result principal accepted assembled _
        cases other <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
        all_goals simp only [assemble, reduceCtorEq, Option.some.injEq] at assembled
        all_goals exact assembled
  | piForm u v domain body ihA ihB | sigmaForm u v domain body ihA ihB =>
      intro context subject firstType secondType second a b checked normal atFirst
        otherChecked atSecond compatible
      cases subject <;> cases firstType <;>
        simp only [check, Bool.false_eq_true] at checked
      all_goals
        simp only [Bool.and_eq_true] at checked
        simp only [Code.neutralEliminations, Bool.and_eq_true] at normal
        simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at atFirst
        obtain ⟨da, atDA, ba, atBA, rfl⟩ := atFirst
        apply compare_principal heads constants R _ ?_ second secondType b
          otherChecked atSecond compatible
        intro other otherType result principal accepted assembled _
        cases other <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
        all_goals try { solve | simp only [assemble, reduceCtorEq] at assembled }
        all_goals
          cases otherType <;> simp only [check, Bool.false_eq_true] at accepted
          simp only [Bool.and_eq_true] at accepted
          simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at assembled
          obtain ⟨db, atDB, bb, atBB, rfl⟩ := assembled
          cases ihA checked.1.2 normal.1 atDA accepted.1.2 atDB (EqualOrHeads.heads _ _)
          cases ihB checked.2 normal.2 atBA accepted.2 atBB (EqualOrHeads.heads _ _)
          rfl
  | lamIntro level formation body ihFormation ihBody =>
      intro context subject firstType secondType second a b checked normal atFirst
        otherChecked atSecond compatible
      cases subject <;> cases firstType <;>
        simp only [check, Bool.false_eq_true] at checked
      rename_i term A B
      simp only [Bool.and_eq_true] at checked
      simp only [Code.neutralEliminations, Bool.and_eq_true] at normal
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at atFirst
      obtain ⟨fa, atFA, da, atDA, ba, atBA, rfl⟩ := atFirst
      apply compare_principal heads constants R _ ?_ second secondType b
        otherChecked atSecond compatible
      intro other otherType result principal accepted assembled types
      have sameType : otherType = .pi A B := types.eq_of_pi.symm
      subst otherType
      cases other <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
      all_goals try { solve | simp only [assemble, reduceCtorEq] at assembled }
      simp only [check, Bool.and_eq_true] at accepted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨fb, atFB, db, atDB, bb, atBB, rfl⟩ := assembled
      cases ihFormation checked.1.2 normal.1 atFA accepted.1.2 atFB (EqualOrHeads.heads _ _)
      cases Option.some.inj (atDA.symm.trans atDB)
      cases ihBody checked.2 normal.2 atBA accepted.2 atBB (EqualOrHeads.refl _)
      rfl
  | appElim A B function argument ihF ihA =>
      intro context subject firstType secondType second a b checked normal atFirst
        otherChecked atSecond compatible
      cases subject <;> simp only [check, Bool.false_eq_true] at checked
      rename_i f x
      simp only [Bool.and_eq_true] at checked
      simp only [Code.neutralEliminations, Bool.and_eq_true] at normal
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at atFirst
      obtain ⟨fa, atFA, xa, atXA, rfl⟩ := atFirst
      apply compare_principal heads constants R _ ?_ second secondType b
        otherChecked atSecond compatible
      intro other otherType result principal accepted assembled _
      cases other <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
      all_goals try { solve | simp only [assemble, reduceCtorEq] at assembled }
      rename_i A' B' function' argument'
      simp only [check, Bool.and_eq_true] at accepted
      have sameType := neutral_type_equalOrHeads R f function function'
        normal.1.1 checked.1.1 accepted.1.1
      have components : A' = A ∧ B' = B := by
        exact Tm.pi.inj sameType.eq_of_pi.symm
      rcases components with ⟨rfl, rfl⟩
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨fb, atFB, xb, atXB, rfl⟩ := assembled
      cases ihF checked.1.1 normal.1.2 atFA accepted.1.1 atFB (EqualOrHeads.refl _)
      cases ihA checked.1.2 normal.2 atXA accepted.1.2 atXB (EqualOrHeads.refl _)
      rfl
  | pairIntro level formation first second _ ihX ihY =>
      intro context subject firstType secondType other a b checked normal atFirst
        otherChecked atSecond compatible
      cases subject <;> cases firstType <;>
        simp only [check, Bool.false_eq_true] at checked
      rename_i x y A B
      simp only [Bool.and_eq_true] at checked
      simp only [Code.neutralEliminations, Bool.and_eq_true] at normal
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at atFirst
      obtain ⟨xa, atXA, ya, atYA, rfl⟩ := atFirst
      apply compare_principal heads constants R _ ?_ other secondType b
        otherChecked atSecond compatible
      intro other otherType result principal accepted assembled types
      have sameType : otherType = .sigma A B := types.eq_of_sigma.symm
      subst otherType
      cases other <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
      all_goals try { solve | simp only [assemble, reduceCtorEq] at assembled }
      simp only [check, Bool.and_eq_true] at accepted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨xb, atXB, yb, atYB, rfl⟩ := assembled
      cases ihX checked.1.2 normal.1 atXA accepted.1.2 atXB (EqualOrHeads.refl _)
      cases ihY checked.2 normal.2 atYA accepted.2 atYB (EqualOrHeads.refl _)
      rfl
  | fstElim B pair ihPair =>
      intro context subject firstType secondType second a b checked normal atFirst
        otherChecked atSecond compatible
      cases subject <;> simp only [check, Bool.false_eq_true] at checked
      rename_i p
      simp only [Code.neutralEliminations, Bool.and_eq_true] at normal
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at atFirst
      obtain ⟨pa, atPA, rfl⟩ := atFirst
      apply compare_principal heads constants R _ ?_ second secondType b
        otherChecked atSecond compatible
      intro other otherType result principal accepted assembled _
      cases other <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
      all_goals try { solve | simp only [assemble, reduceCtorEq] at assembled }
      rename_i B' pair'
      simp only [check] at accepted
      have sameType := neutral_type_equalOrHeads R p pair pair' normal.1 checked accepted
      have components : otherType = firstType ∧ B' = B :=
        Tm.sigma.inj sameType.eq_of_sigma.symm
      rcases components with ⟨rfl, rfl⟩
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨pb, atPB, rfl⟩ := assembled
      cases ihPair checked normal.2 atPA accepted atPB (EqualOrHeads.refl _)
      rfl
  | sndElim A B pair ihPair =>
      intro context subject firstType secondType second a b checked normal atFirst
        otherChecked atSecond compatible
      cases subject <;> simp only [check, Bool.false_eq_true] at checked
      rename_i p
      simp only [Bool.and_eq_true] at checked
      simp only [Code.neutralEliminations, Bool.and_eq_true] at normal
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at atFirst
      obtain ⟨pa, atPA, rfl⟩ := atFirst
      apply compare_principal heads constants R _ ?_ second secondType b
        otherChecked atSecond compatible
      intro other otherType result principal accepted assembled _
      cases other <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
      all_goals try { solve | simp only [assemble, reduceCtorEq] at assembled }
      rename_i A' B' pair'
      simp only [check, Bool.and_eq_true] at accepted
      have sameType := neutral_type_equalOrHeads R p pair pair' normal.1 checked.1 accepted.1
      have components : A' = A ∧ B' = B := Tm.sigma.inj sameType.eq_of_sigma.symm
      rcases components with ⟨rfl, rfl⟩
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨pb, atPB, rfl⟩ := assembled
      cases ihPair checked.1 normal.2 atPA accepted.1 atPB (EqualOrHeads.refl _)
      rfl
  | idForm level formation left right _ ihX ihY =>
      intro context subject firstType secondType second a b checked normal atFirst
        otherChecked atSecond compatible
      cases subject <;> cases firstType <;>
        simp only [check, Bool.false_eq_true] at checked
      simp only [Bool.and_eq_true] at checked
      simp only [Code.neutralEliminations, Bool.and_eq_true] at normal
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at atFirst
      obtain ⟨xa, atXA, ya, atYA, rfl⟩ := atFirst
      apply compare_principal heads constants R _ ?_ second secondType b
        otherChecked atSecond compatible
      intro other otherType result principal accepted assembled _
      cases other <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
      all_goals try { solve | simp only [assemble, reduceCtorEq] at assembled }
      cases otherType <;> simp only [check, Bool.false_eq_true] at accepted
      simp only [Bool.and_eq_true] at accepted
      simp only [assemble, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at assembled
      obtain ⟨xb, atXB, yb, atYB, rfl⟩ := assembled
      cases ihX checked.1.1.2 normal.1 atXA accepted.1.1.2 atXB (EqualOrHeads.refl _)
      cases ihY checked.1.2 normal.2 atYA accepted.1.2 atYB (EqualOrHeads.refl _)
      rfl

#print axioms assemble_neutralEliminations_coherent

/-- Substitute arbitrary assembled images through the two accepted source
certificates. The resulting terms can contain beta and projection redexes;
the comparison follows these exact transformed trees, not arbitrary new
certificates selected for the erased result. -/
theorem assemble_substitute_neutralEliminations_values {m : Nat}
    {context : Ctx Head n} {subject firstType secondType : Tm Head n}
    (first second : Code Head NoConversion n) (a b : Meaning.{u} n)
    (normal : first.neutralEliminations subject firstType = true)
    (firstChecked : check R noConversionCheck context subject firstType first = true)
    (secondChecked : check R noConversionCheck context subject secondType second = true)
    (atFirst : assemble heads constants first subject firstType = some a)
    (atSecond : assemble heads constants second subject secondType = some b)
    (compatible : EqualOrHeads firstType secondType)
    (σ : Sub Head n m) (codes : Fin n → Code Head NoConversion m)
    (images : Fin n → Meaning.{u} m)
    (atImages : ∀ index, assemble heads constants (codes index) (σ index)
      (subst σ (context.lookup index)) = some (images index)) :
    ∃ left right,
      assemble heads constants
        (first.substitute noConversionRename noConversionSubstitute σ codes subject firstType)
        (subst σ subject) (subst σ firstType) = some left ∧
      assemble heads constants
        (second.substitute noConversionRename noConversionSubstitute σ codes subject secondType)
        (subst σ subject) (subst σ secondType) = some right ∧
      left.value = right.value := by
  obtain ⟨left, atLeft, leftValues, _⟩ :=
    assemble_substitute noConversionRename noConversionSubstitute heads constants R noConversionCheck
      first a firstChecked atFirst σ codes images atImages
  obtain ⟨right, atRight, rightValues, _⟩ :=
    assemble_substitute noConversionRename noConversionSubstitute heads constants R noConversionCheck
      second b secondChecked atSecond σ codes images atImages
  have agreement := assemble_neutralEliminations_coherent heads constants R first firstChecked
    normal atFirst secondChecked atSecond compatible
  refine ⟨left, right, atLeft, atRight, ?_⟩
  funext env
  rw [leftValues, rightValues, agreement]

/-- In particular a binder may be opened with a function or pair expression.
No normality condition is imposed on that argument or on the resulting term. -/
theorem assemble_instantiate_neutralEliminations_values
    {context : Ctx Head n} {A argument : Tm Head n}
    {subject firstType secondType : Tm Head (n + 1)}
    (first second : Code Head NoConversion (n + 1)) (argumentCode : Code Head NoConversion n)
    (a b : Meaning.{u} (n + 1)) (argumentMeaning : Meaning.{u} n)
    (normal : first.neutralEliminations subject firstType = true)
    (firstChecked : check R noConversionCheck (.snoc context A) subject firstType first = true)
    (secondChecked : check R noConversionCheck (.snoc context A) subject secondType second = true)
    (atFirst : assemble heads constants first subject firstType = some a)
    (atSecond : assemble heads constants second subject secondType = some b)
    (compatible : EqualOrHeads firstType secondType)
    (atArgument : assemble heads constants argumentCode argument A = some argumentMeaning) :
    ∃ left right,
      assemble heads constants
        (Code.instantiate noConversionRename noConversionSubstitute subject firstType argument first argumentCode)
        (inst0 argument subject) (inst0 argument firstType) = some left ∧
      assemble heads constants
        (Code.instantiate noConversionRename noConversionSubstitute subject secondType argument second argumentCode)
        (inst0 argument subject) (inst0 argument secondType) = some right ∧
      left.value = right.value := by
  obtain ⟨left, atLeft, leftValues⟩ :=
    assemble_instantiate noConversionRename noConversionSubstitute heads constants R noConversionCheck
      first argumentCode a argumentMeaning firstChecked atFirst atArgument
  obtain ⟨right, atRight, rightValues⟩ :=
    assemble_instantiate noConversionRename noConversionSubstitute heads constants R noConversionCheck
      second argumentCode b argumentMeaning secondChecked atSecond atArgument
  have agreement := assemble_neutralEliminations_coherent heads constants R first firstChecked
    normal atFirst secondChecked atSecond compatible
  refine ⟨left, right, atLeft, atRight, ?_⟩
  funext env
  rw [leftValues, rightValues, agreement]

#print axioms assemble_substitute_neutralEliminations_values
#print axioms assemble_instantiate_neutralEliminations_values

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
