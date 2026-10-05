import Mettapedia.GSLT.Distinction.Constructive.DepthBound

/-!
# Exact-value modal observations for a presented graded system

The ordinary atomic signature constructed here consists of an authored
observation and an exact value. Its labelled actions are precisely the
authored actions. Ordinary bisimulation for this signature is proved to be
graded bisimulation, by testing each left-hand value against itself.

The inherited Boolean atoms have a separate signature. Interpreting those
atoms by exact-value modal formulas gives a sound translation of their full
formula language; interpreting the exact-value atoms back gives the converse
bisimulation comparison. Neither interpretation is assumed by the graded
system, and the exact-value atomic carrier need not be finite.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.GradedValueObserver

open HennessyMilner Distinction.Constructive

universe uS uAtom uLabel uObs uV

variable {V : Type uV} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
variable {S : GSLT.{uS}} {K : Scale V}
variable (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S K)

/-- The actual ordinary observer of the graded values, retaining the authored
labelled dynamics. -/
def valueSystem : System.{max uObs uV, uLabel} S where
  Atom := Q.Obs × V
  observes atom term := Q.value atom.1 term = atom.2
  observes_resp atom _ _ same := by
    rw [Q.value_resp atom.1 same]
  Label := Q.dynamics.Label
  act := Q.dynamics.act
  act_resp_left := Q.dynamics.act_resp_left
  act_resp_right := Q.dynamics.act_resp_right

theorem atomic_agreement_iff (left right : S.Term) :
    (∀ atom, (valueSystem Q).observes atom left ↔ (valueSystem Q).observes atom right) ↔
      ∀ observation, Q.value observation left = Q.value observation right := by
  constructor
  · intro agreement observation
    exact ((agreement (observation, Q.value observation left)).mp rfl).symm
  · intro equal atom
    change Q.value atom.1 left = atom.2 ↔ Q.value atom.1 right = atom.2
    rw [equal atom.1]

/-- No reflection hypothesis is used: the two notions require exactly the
same actions and, by equality tests, exactly the same atomic information. -/
theorem isBisimulation_iff_graded (relation : S.Term → S.Term → Prop) :
    (valueSystem Q).IsBisimulation relation ↔ Q.IsGradedBisimulation relation := by
  constructor
  · rintro ⟨forward, backward, atoms⟩
    exact ⟨forward, backward, fun {left right} related =>
      (atomic_agreement_iff Q _ _).mp (atoms related)⟩
  · rintro ⟨forward, backward, values⟩
    exact ⟨forward, backward, fun {left right} related =>
      (atomic_agreement_iff Q _ _).mpr (values related)⟩

theorem bisimilar_iff_graded (left right : S.Term) :
    (valueSystem Q).Bisimilar left right ↔ Q.GradedBisimilar left right := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨relation, (isBisimulation_iff_graded Q relation).mp bisimulation, related⟩
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨relation, (isBisimulation_iff_graded Q relation).mpr bisimulation, related⟩

theorem formula_preservation {relation : S.Term → S.Term → Prop}
    (bisimulation : Q.IsGradedBisimulation relation)
    (formula : Formula (valueSystem Q).Atom (valueSystem Q).Label)
    {left right : S.Term} (related : relation left right) :
    (valueSystem Q).sat formula left ↔ (valueSystem Q).sat formula right :=
  (valueSystem Q).sat_iff_of_isBisimulation
    ((isBisimulation_iff_graded Q relation).mpr bisimulation) formula related

theorem logicallyEquivalent_of_graded {left right : S.Term}
    (related : Q.GradedBisimilar left right) :
    (valueSystem Q).LogicallyEquivalent left right :=
  (valueSystem Q).logicallyEquivalent_of_bisimilar
    ((bisimilar_iff_graded Q left right).mpr related)

/-- Agreement on full modal formulas in particular retains every numeric
reading. This is not an unrestricted modal-to-bisimulation converse. -/
theorem values_eq_of_logicallyEquivalent {left right : S.Term}
    (agreement : (valueSystem Q).LogicallyEquivalent left right) :
    ∀ observation, Q.value observation left = Q.value observation right :=
  (atomic_agreement_iff Q left right).mp fun atom => agreement (.atom atom)

/-- An explicit interpretation of the old atomic signature by formulas over
the constructed exact-value observer. -/
structure OriginalAtomInterpretation where
  formula : Q.dynamics.Atom → Formula (valueSystem Q).Atom Q.dynamics.Label
  correct : ∀ atom term,
    (valueSystem Q).sat (formula atom) term ↔ Q.dynamics.observes atom term

/-- Substitution of the interpreted atoms preserves all Boolean connectives
and the authored labelled diamonds. -/
def translateOriginal (interpretation : OriginalAtomInterpretation Q) :
    Formula Q.dynamics.Atom Q.dynamics.Label →
      Formula (valueSystem Q).Atom Q.dynamics.Label
  | .top => .top
  | .atom atom => interpretation.formula atom
  | .conj left right => .conj (translateOriginal interpretation left)
      (translateOriginal interpretation right)
  | .neg inner => .neg (translateOriginal interpretation inner)
  | .dia label inner => .dia label (translateOriginal interpretation inner)

theorem translateOriginal_sat (interpretation : OriginalAtomInterpretation Q) :
    ∀ (formula : Formula Q.dynamics.Atom Q.dynamics.Label) (term : S.Term),
      (valueSystem Q).sat (translateOriginal Q interpretation formula) term ↔
        Q.dynamics.sat formula term
  | .top, _ => Iff.rfl
  | .atom atom, term => interpretation.correct atom term
  | .conj left right, term =>
      and_congr (translateOriginal_sat interpretation left term)
        (translateOriginal_sat interpretation right term)
  | .neg inner, term => not_congr (translateOriginal_sat interpretation inner term)
  | .dia label inner, term => by
      change (∃ target, Q.dynamics.act label term target ∧
        (valueSystem Q).sat (translateOriginal Q interpretation inner) target) ↔ _
      exact exists_congr fun target =>
        and_congr Iff.rfl (translateOriginal_sat interpretation inner target)

theorem original_isBisimulation_of_graded (interpretation : OriginalAtomInterpretation Q)
    {relation : S.Term → S.Term → Prop} (bisimulation : Q.IsGradedBisimulation relation) :
    Q.dynamics.IsBisimulation relation := by
  refine ⟨bisimulation.1, bisimulation.2.1, ?_⟩
  intro left right related atom
  exact (interpretation.correct atom left).symm.trans
    ((formula_preservation Q bisimulation (interpretation.formula atom) related).trans
      (interpretation.correct atom right))

/-- The reverse signature interpretation is independent extra data. -/
structure ValueAtomInterpretation where
  formula : (valueSystem Q).Atom → Formula Q.dynamics.Atom Q.dynamics.Label
  correct : ∀ atom term,
    Q.dynamics.sat (formula atom) term ↔ (valueSystem Q).observes atom term

theorem graded_of_original_isBisimulation (interpretation : ValueAtomInterpretation Q)
    {relation : S.Term → S.Term → Prop} (bisimulation : Q.dynamics.IsBisimulation relation) :
    Q.IsGradedBisimulation relation := by
  refine (isBisimulation_iff_graded Q relation).mp ⟨bisimulation.1, bisimulation.2.1, ?_⟩
  intro left right related atom
  exact (interpretation.correct atom left).symm.trans
    ((Q.dynamics.sat_iff_of_isBisimulation bisimulation (interpretation.formula atom) related).trans
      (interpretation.correct atom right))

theorem original_isBisimulation_iff_graded
    (original : OriginalAtomInterpretation Q) (values : ValueAtomInterpretation Q)
    (relation : S.Term → S.Term → Prop) :
    Q.dynamics.IsBisimulation relation ↔ Q.IsGradedBisimulation relation :=
  ⟨graded_of_original_isBisimulation Q values,
    original_isBisimulation_of_graded Q original⟩

theorem original_bisimilar_iff_graded
    (original : OriginalAtomInterpretation Q) (values : ValueAtomInterpretation Q)
    (left right : S.Term) :
    Q.dynamics.Bisimilar left right ↔ Q.GradedBisimilar left right := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨relation, graded_of_original_isBisimulation Q values bisimulation, related⟩
  · rintro ⟨relation, bisimulation, related⟩
    exact ⟨relation, original_isBisimulation_of_graded Q original bisimulation, related⟩

end Mettapedia.GSLT.GradedValueObserver
