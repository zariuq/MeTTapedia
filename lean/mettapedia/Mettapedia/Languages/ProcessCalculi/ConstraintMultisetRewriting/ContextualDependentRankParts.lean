import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRank

/-!
# Every decomposition lowers the normal weight

For each rigid-former decomposition of R94 (identity types, Π and Σ types through the family twin,
pairs), the pieces weigh exactly two less than the decomposed equation (`IdShape.weight`,
`BinderShape.weight`, `PairShape.weight`, collected in `formerParts_weight`). The conversion scan
lowers the weight whenever it removes an equation (`scan_weight_lt`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRank

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentInPlace
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentOccursCheck

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra complete in
/-- The normal weight of a side given by its parts. -/
theorem sideWeight_mk {Θ : Context S.R} (type : TypeOver Θ) (code : Tm Head Θ.arity)
    (typed : Typed S.R Θ.raw code type.code) {T v : Tm Head Θ.arity} (same : type.code = T)
    (normal : NormalForm S.R S.roles Θ.raw code v T) :
    sideWeight facts roots heads algebra rigid complete (⟨type, ⟨code, typed⟩⟩ : TotalTerm Θ) = weight v :=
  sideWeight_eq facts roots heads algebra rigid complete _ (by subst same; exact normal)

theorem binder_weight (isPi : Bool) {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) :
    weight (binder isPi A B) = weight A + weight B + 1 := by
  cases isPi <;> rfl

/-! ## Identity types -/

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra complete in
/-- **An identity decomposition lowers the normal weight by two.** -/
theorem IdShape.weight {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : IdShape equation)
    (carrier : {type : TypeOver Θ // type.code = shape.carrier})
    (carrier' : {type : TypeOver Θ // type.code = shape.carrier'}) :
    storeWeight facts roots heads algebra rigid complete (shape.parts carrier carrier') + 2 =
      equationWeight facts roots heads algebra rigid complete equation := by
  have formed := Θ.formed
  have hu := shape.universal
  obtain ⟨tC, ta, tb⟩ := shape.leftTyped
  obtain ⟨tC', ta', tb'⟩ := shape.rightTyped
  obtain ⟨N, lN, nC⟩ := universe_normalForm facts roots heads algebra rigid complete formed hu tC
  obtain ⟨N', lN', nC'⟩ := universe_normalForm facts roots heads algebra rigid complete formed hu tC'
  obtain ⟨na, nA⟩ := long_exists facts roots heads algebra rigid complete formed ta
  obtain ⟨nb, nB⟩ := long_exists facts roots heads algebra rigid complete formed tb
  obtain ⟨na', nA'⟩ := long_exists facts roots heads algebra rigid complete formed ta'
  obtain ⟨nb', nB'⟩ := long_exists facts roots heads algebra rigid complete formed tb'
  have left := id_normalForm hu lN nC nA nB (universe_typeEq Θ.raw hu)
  have right := id_normalForm hu lN' nC' nA' nB' (universe_typeEq Θ.raw hu)
  have leftWeight := sideWeight_eq facts roots heads algebra rigid complete equation.1
    (by rw [shape.leftCode, shape.annotation]; exact left)
  have rightWeight := sideWeight_eq facts roots heads algebra rigid complete equation.2
    (by rw [shape.rightCode, shape.same]; exact right)
  simp only [IdShape.parts, storeWeight, equationWeight]
  rw [sideWeight_mk facts roots heads algebra rigid complete _ _ _ shape.annotation nC,
    sideWeight_mk facts roots heads algebra rigid complete _ _ _ shape.annotation nC',
    sideWeight_mk facts roots heads algebra rigid complete _ _ _ carrier.property nA,
    sideWeight_mk facts roots heads algebra rigid complete _ _ _ carrier'.property nA',
    sideWeight_mk facts roots heads algebra rigid complete _ _ _ carrier.property nB,
    sideWeight_mk facts roots heads algebra rigid complete _ _ _ carrier'.property nB', leftWeight, rightWeight]
  simp only [ContextualDependentRank.weight]
  omega

/-! ## Π and Σ types -/

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra complete in
/-- **A binder decomposition lowers the normal weight by two**: abstractions weigh nothing, so the
family twin weighs what the two codomains weigh. -/
theorem BinderShape.weight {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : BinderShape equation)
    (family : {type : TypeOver Θ // type.code = .pi shape.domain (.head shape.u)})
    (family' : {type : TypeOver Θ // type.code = .pi shape.domain' (.head shape.u)}) :
    storeWeight facts roots heads algebra rigid complete (shape.parts facts algebra family family') + 2 =
      equationWeight facts roots heads algebra rigid complete equation := by
  have formed := Θ.formed
  have hu := shape.universal
  obtain ⟨tA, tB⟩ := shape.leftTyped facts algebra
  obtain ⟨tA', tB'⟩ := shape.rightTyped facts algebra
  obtain ⟨D, lD, nA⟩ := universe_normalForm facts roots heads algebra rigid complete formed hu tA
  obtain ⟨D', lD', nA'⟩ := universe_normalForm facts roots heads algebra rigid complete formed hu tA'
  obtain ⟨E, lE, nB⟩ :=
    universe_normalForm facts roots heads algebra rigid complete (formed.snoc ⟨_, hu, tA⟩) hu tB
  obtain ⟨E', lE', nB'⟩ :=
    universe_normalForm facts roots heads algebra rigid complete (formed.snoc ⟨_, hu, tA'⟩) hu tB'
  have left := binder_normalForm facts roots heads algebra complete shape.isPi formed hu tA tB lD nA lE nB
  have right := binder_normalForm facts roots heads algebra complete shape.isPi formed hu tA' tB' lD' nA' lE' nB'
  have leftWeight := sideWeight_eq facts roots heads algebra rigid complete equation.1
    (by rw [shape.leftCode, shape.annotation]; exact left)
  have rightWeight := sideWeight_eq facts roots heads algebra rigid complete equation.2
    (by rw [shape.rightCode, shape.same]; exact right)
  have tPi : Typed S.R Θ.raw (.pi shape.domain (.head shape.u)) (.head family.val.level) := by
    have h := family.val.formed
    rw [family.property] at h
    exact h
  have tPi' : Typed S.R Θ.raw (.pi shape.domain' (.head shape.u)) (.head family'.val.level) := by
    have h := family'.val.formed
    rw [family'.property] at h
    exact h
  have twin := family_normalForm family.val.universeWitness tPi ⟨_, hu, tA⟩ nB
  have twin' := family_normalForm family'.val.universeWitness tPi' ⟨_, hu, tA'⟩ nB'
  simp only [BinderShape.parts, storeWeight, equationWeight]
  rw [sideWeight_mk facts roots heads algebra rigid complete _ _ _ shape.annotation nA,
    sideWeight_mk facts roots heads algebra rigid complete _ _ _ shape.annotation nA',
    sideWeight_mk facts roots heads algebra rigid complete _ _ _ family.property twin,
    sideWeight_mk facts roots heads algebra rigid complete _ _ _ family'.property twin', leftWeight, rightWeight,
    binder_weight, binder_weight]
  simp only [ContextualDependentRank.weight]
  omega

/-! ## Pairs -/

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra complete in
/-- **A pair decomposition lowers the normal weight by two.** -/
theorem PairShape.weight {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : PairShape equation)
    (domain : {type : TypeOver Θ // type.code = shape.domain})
    (fibre : {type : TypeOver Θ // type.code = inst0 shape.first shape.family})
    (fibre' : {type : TypeOver Θ // type.code = inst0 shape.first' shape.family}) :
    storeWeight facts roots heads algebra rigid complete (shape.parts facts domain fibre fibre') + 2 =
      equationWeight facts roots heads algebra rigid complete equation := by
  have formed := Θ.formed
  obtain ⟨ta, tb⟩ := shape.leftTyped facts
  obtain ⟨ta', tb'⟩ := shape.rightTyped facts
  obtain ⟨na, nA⟩ := long_exists facts roots heads algebra rigid complete formed ta
  obtain ⟨nb, nB⟩ := long_exists facts roots heads algebra rigid complete formed tb
  obtain ⟨na', nA'⟩ := long_exists facts roots heads algebra rigid complete formed ta'
  obtain ⟨nb', nB'⟩ := long_exists facts roots heads algebra rigid complete formed tb'
  have tSigma : Typed S.R Θ.raw (.sigma shape.domain shape.family) (.head equation.1.1.level) := by
    have h := equation.1.1.formed
    rw [shape.annotation] at h
    exact h
  have tSigma' : Typed S.R Θ.raw (.sigma shape.domain shape.family) (.head equation.2.1.level) := by
    have h := equation.2.1.formed
    rw [shape.same] at h
    exact h
  obtain ⟨_, v, _, _, _, tFamily, hv, _, _⟩ := tSigma.generation
  have left := pair_normalForm tSigma equation.1.1.universeWitness tFamily hv ta nA nB
  have right := pair_normalForm tSigma' equation.2.1.universeWitness tFamily hv ta' nA' nB'
  have leftWeight := sideWeight_eq facts roots heads algebra rigid complete equation.1
    (by rw [shape.leftCode, shape.annotation]; exact left)
  have rightWeight := sideWeight_eq facts roots heads algebra rigid complete equation.2
    (by rw [shape.rightCode, shape.same]; exact right)
  simp only [PairShape.parts, storeWeight, equationWeight]
  rw [sideWeight_mk facts roots heads algebra rigid complete _ _ _ domain.property nA,
    sideWeight_mk facts roots heads algebra rigid complete _ _ _ domain.property nA',
    sideWeight_mk facts roots heads algebra rigid complete _ _ _ fibre.property nB,
    sideWeight_mk facts roots heads algebra rigid complete _ _ _ fibre'.property nB', leftWeight, rightWeight]
  simp only [ContextualDependentRank.weight]
  omega

/-! ## Every decomposition -/

variable [DecidableRel S.R.headEq] [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R)

include facts roots heads algebra complete in
theorem idParts_weight (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} {parts : Parts equation}
    (found : idParts facts roots heads algebra complete declared choices reducer fuel equation = some parts) :
    storeWeight facts roots heads algebra rigid complete parts.val + 2 =
      equationWeight facts roots heads algebra rigid complete equation := by
  unfold idParts at found
  split at found
  · cases found
  · rename_i shape _
    obtain ⟨carrier, _, mapped⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨carrier', _, made⟩ := Option.map_eq_some_iff.mp mapped
    subst made
    exact IdShape.weight facts roots heads algebra rigid complete shape carrier carrier'

include facts roots heads algebra complete in
theorem binderParts_weight (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {parts : Parts equation}
    (found : binderParts facts roots heads algebra complete declared choices reducer fuel equation = some parts) :
    storeWeight facts roots heads algebra rigid complete parts.val + 2 =
      equationWeight facts roots heads algebra rigid complete equation := by
  unfold binderParts at found
  split at found
  · cases found
  · rename_i shape _
    obtain ⟨family, _, mapped⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨family', _, made⟩ := Option.map_eq_some_iff.mp mapped
    subst made
    exact BinderShape.weight facts roots heads algebra rigid complete shape family family'

include facts roots heads algebra complete in
theorem pairParts_weight (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {parts : Parts equation}
    (found : pairParts facts roots heads algebra declared choices reducer fuel equation = some parts) :
    storeWeight facts roots heads algebra rigid complete parts.val + 2 =
      equationWeight facts roots heads algebra rigid complete equation := by
  unfold pairParts at found
  split at found
  · cases found
  · rename_i shape _
    obtain ⟨domain, _, chained⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨fibre, _, mapped⟩ := Option.bind_eq_some_iff.mp chained
    obtain ⟨fibre', _, made⟩ := Option.map_eq_some_iff.mp mapped
    subst made
    exact PairShape.weight facts roots heads algebra rigid complete shape domain fibre fibre'

include facts roots heads algebra complete in
/-- **Every rigid-former decomposition lowers the normal weight by two.** -/
theorem formerParts_weight (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)}
    {parts : Parts equation}
    (found : formerParts facts roots heads algebra complete declared choices reducer fuel equation = some parts) :
    storeWeight facts roots heads algebra rigid complete parts.val + 2 =
      equationWeight facts roots heads algebra rigid complete equation := by
  unfold formerParts at found
  cases hId : idParts facts roots heads algebra complete declared choices reducer fuel equation with
  | some first =>
      rw [hId, Option.some_or] at found
      cases found
      exact idParts_weight facts roots heads algebra rigid complete declared choices reducer fuel hId
  | none =>
      rw [hId, Option.none_or] at found
      cases hBinder : binderParts facts roots heads algebra complete declared choices reducer fuel equation with
      | some second =>
          rw [hBinder, Option.some_or] at found
          cases found
          exact binderParts_weight facts roots heads algebra rigid complete declared choices reducer fuel hBinder
      | none =>
          rw [hBinder, Option.none_or] at found
          exact pairParts_weight facts roots heads algebra rigid complete declared choices reducer fuel found

/-! ## The conversion scan -/

omit [DecidableRel S.R.cumulative] in
include facts roots heads algebra complete in
/-- The conversion scan never raises the normal weight, and lowers it by at least the number of
equations it removes. -/
theorem scan_weight (fuel : Nat) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ),
      storeWeight facts roots heads algebra rigid complete
          (ContextualDependentEta.Conversion.scan facts roots heads algebra reducer fuel problem) +
        (problem.length - (ContextualDependentEta.Conversion.scan facts roots heads algebra reducer fuel problem).length) ≤
        storeWeight facts roots heads algebra rigid complete problem ∧
      (ContextualDependentEta.Conversion.scan facts roots heads algebra reducer fuel problem).length ≤ problem.length
  | [] => by simp [ContextualDependentEta.Conversion.scan, storeWeight]
  | equation :: rest => by
      have ih := scan_weight fuel rest
      have positive := equationWeight_pos facts roots heads algebra rigid complete equation
      simp only [ContextualDependentEta.Conversion.scan]
      split
      · simp only [storeWeight, List.length_cons]
        omega
      · simp only [storeWeight, List.length_cons]
        omega

omit [DecidableRel S.R.cumulative] in
include facts roots heads algebra complete in
/-- **The conversion scan lowers the normal weight when it removes an equation.** -/
theorem scan_weight_lt (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (shorter : (ContextualDependentEta.Conversion.scan facts roots heads algebra reducer fuel problem).length <
      problem.length) :
    storeWeight facts roots heads algebra rigid complete
        (ContextualDependentEta.Conversion.scan facts roots heads algebra reducer fuel problem) <
      storeWeight facts roots heads algebra rigid complete problem := by
  have := (scan_weight facts roots heads algebra rigid complete reducer fuel problem).1
  omega

end ContextualDependentRank
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
