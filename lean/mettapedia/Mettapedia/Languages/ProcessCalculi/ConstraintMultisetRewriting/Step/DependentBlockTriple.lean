import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullTelescopes

/-!
# Three independent blocks of dependent helpers

Each block is an arbitrary telescope over the common base. Its internal
dependencies are retained. The combined frame is constructed by the existing
successive telescope pullbacks, and maps into it are determined by their
three block projections. This characterizes the actual substitution maps,
not only the lengths or permutations of declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head : Type} {rules : Rules Head} {Γ : Context rules}

abbrev pairFrame (first second : Helpers Γ) : Context rules :=
  (second.reindex first.weaken).frame

def pairBase (first second : Helpers Γ) : pairFrame first second ⟶ Γ :=
  (second.reindex first.weaken).weaken ≫ first.weaken

abbrev frame (first second third : Helpers Γ) : Context rules :=
  (third.reindex (pairBase first second)).frame

def toPair (first second third : Helpers Γ) : frame first second third ⟶ pairFrame first second :=
  (third.reindex (pairBase first second)).weaken

def toFirst (first second third : Helpers Γ) : frame first second third ⟶ first.frame :=
  toPair first second third ≫ (second.reindex first.weaken).weaken

def toSecond (first second third : Helpers Γ) : frame first second third ⟶ second.frame :=
  toPair first second third ≫ Helpers.lift first.weaken second

def toThird (first second third : Helpers Γ) : frame first second third ⟶ third.frame :=
  Helpers.lift (pairBase first second) third

def base (first second third : Helpers Γ) : frame first second third ⟶ Γ :=
  toPair first second third ≫ pairBase first second

theorem first_base (first second third : Helpers Γ) :
    toFirst first second third ≫ first.weaken = base first second third :=
  Category.assoc _ _ _

theorem second_base (first second third : Helpers Γ) :
    toSecond first second third ≫ second.weaken = base first second third := by
  unfold toSecond base pairBase
  rw [Category.assoc, Helpers.lift_weaken]

theorem third_base (first second third : Helpers Γ) :
    toThird first second third ≫ third.weaken = base first second third :=
  Helpers.lift_weaken _ _

def into (first second third : Helpers Γ) {X : Context rules}
    (a : X ⟶ first.frame) (b : X ⟶ second.frame) (c : X ⟶ third.frame)
    (ab : a ≫ first.weaken = b ≫ second.weaken)
    (ac : a ≫ first.weaken = c ≫ third.weaken) : X ⟶ frame first second third :=
  Helpers.into (pairBase first second) third (Helpers.into first.weaken second a b ab) c
    (by rw [pairBase, ← Category.assoc, Helpers.into_weaken]; exact ac)

theorem into_first (first second third : Helpers Γ) {X : Context rules}
    (a : X ⟶ first.frame) (b : X ⟶ second.frame) (c : X ⟶ third.frame)
    (ab : a ≫ first.weaken = b ≫ second.weaken)
    (ac : a ≫ first.weaken = c ≫ third.weaken) :
    into first second third a b c ab ac ≫ toFirst first second third = a := by
  unfold into toFirst toPair
  rw [← Category.assoc, Helpers.into_weaken, Helpers.into_weaken]

theorem into_second (first second third : Helpers Γ) {X : Context rules}
    (a : X ⟶ first.frame) (b : X ⟶ second.frame) (c : X ⟶ third.frame)
    (ab : a ≫ first.weaken = b ≫ second.weaken)
    (ac : a ≫ first.weaken = c ≫ third.weaken) :
    into first second third a b c ab ac ≫ toSecond first second third = b := by
  unfold into toSecond toPair
  rw [← Category.assoc, Helpers.into_weaken, Helpers.into_lift]

theorem into_third (first second third : Helpers Γ) {X : Context rules}
    (a : X ⟶ first.frame) (b : X ⟶ second.frame) (c : X ⟶ third.frame)
    (ab : a ≫ first.weaken = b ≫ second.weaken)
    (ac : a ≫ first.weaken = c ≫ third.weaken) :
    into first second third a b c ab ac ≫ toThird first second third = c :=
  Helpers.into_lift _ _ _ _ _

private theorem pullback_ext {Δ X : Context rules} (substitution : Δ ⟶ Γ) (helpers : Helpers Γ)
    {one two : X ⟶ (helpers.reindex substitution).frame}
    (sameBase : one ≫ (helpers.reindex substitution).weaken = two ≫ (helpers.reindex substitution).weaken)
    (sameBlock : one ≫ Helpers.lift substitution helpers = two ≫ Helpers.lift substitution helpers) :
    one = two := by
  have compatible : (two ≫ (helpers.reindex substitution).weaken) ≫ substitution =
      (two ≫ Helpers.lift substitution helpers) ≫ helpers.weaken := by
    rw [Category.assoc, Category.assoc, Helpers.lift_weaken]
  exact (Helpers.into_unique substitution helpers _ _ compatible one sameBase sameBlock).trans
    (Helpers.into_unique substitution helpers _ _ compatible two rfl rfl).symm

theorem hom_ext (first second third : Helpers Γ) {X : Context rules}
    {one two : X ⟶ frame first second third}
    (sameFirst : one ≫ toFirst first second third = two ≫ toFirst first second third)
    (sameSecond : one ≫ toSecond first second third = two ≫ toSecond first second third)
    (sameThird : one ≫ toThird first second third = two ≫ toThird first second third) : one = two := by
  apply pullback_ext (pairBase first second) third
  · apply pullback_ext first.weaken second
    · simpa only [toFirst, toPair, Category.assoc] using sameFirst
    · simpa only [toSecond, toPair, Category.assoc] using sameSecond
  · exact sameThird

theorem into_unique (first second third : Helpers Γ) {X : Context rules}
    (a : X ⟶ first.frame) (b : X ⟶ second.frame) (c : X ⟶ third.frame)
    (ab : a ≫ first.weaken = b ≫ second.weaken)
    (ac : a ≫ first.weaken = c ≫ third.weaken)
    (candidate : X ⟶ frame first second third)
    (keepsFirst : candidate ≫ toFirst first second third = a)
    (keepsSecond : candidate ≫ toSecond first second third = b)
    (keepsThird : candidate ≫ toThird first second third = c) :
    candidate = into first second third a b c ab ac := by
  apply hom_ext first second third
  · exact keepsFirst.trans (into_first _ _ _ _ _ _ _ _).symm
  · exact keepsSecond.trans (into_second _ _ _ _ _ _ _ _).symm
  · exact keepsThird.trans (into_third _ _ _ _ _ _ _ _).symm

theorem pair_hom_ext (first second : Helpers Γ) {X : Context rules}
    {one two : X ⟶ pairFrame first second}
    (sameFirst : one ≫ (second.reindex first.weaken).weaken =
      two ≫ (second.reindex first.weaken).weaken)
    (sameSecond : one ≫ Helpers.lift first.weaken second = two ≫ Helpers.lift first.weaken second) :
    one = two := pullback_ext first.weaken second sameFirst sameSecond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple.hom_ext
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.BlockTriple.into_unique
