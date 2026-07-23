import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ExactNormal
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.FreshnessCore

/-!
# Freshness preservation for finite type presentations

The runtime checks one function candidate in a private type-binding scope.
To relate that private computation to the published evaluator's threaded
binding state, every private name must avoid the caller-visible scope.

`TypeSubst.Avoids` records both halves needed by substitution: assigned keys
and variables retained in stored values.  The presentation matcher preserves
this property structurally.  Consequently an alpha-freshened empty-seed
argument fold cannot capture a caller variable, while an arbitrary seeded
fold receives no such theorem.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- A finite presentation mentions no forbidden name, either as an assigned
key or in a stored value. -/
structure Avoids (substitution : TypeSubst)
    (forbidden : List String) : Prop where
  keys : ∀ name, name ∈ substitution.keys → name ∉ forbidden
  values : ∀ key value, (key, value) ∈ substitution →
    ∀ name, name ∈ typeVars value → name ∉ forbidden

/-- The empty presentation avoids every scope. -/
theorem avoids_empty (forbidden : List String) :
    Avoids [] forbidden := by
  constructor <;> simp [TypeSubst.keys]

/-- One capture-avoiding bind preserves presentation freshness. -/
theorem Avoids.bind
    {substitution : TypeSubst} {forbidden : List String}
    (avoids : substitution.Avoids forbidden)
    {name : String} {value : Atom}
    (nameFresh : name ∉ forbidden)
    (valueFresh : ∀ candidate,
      candidate ∈ typeVars value → candidate ∉ forbidden) :
    (substitution.bind name value).Avoids forbidden := by
  let resolved := substitution.apply value
  have resolvedFresh : ∀ candidate,
      candidate ∈ typeVars resolved → candidate ∉ forbidden := by
    exact apply_variable_avoids avoids.values value valueFresh
  constructor
  · intro candidate member
    rw [keys_bind] at member
    rcases List.mem_cons.mp member with rfl | tailMember
    · exact nameFresh
    · exact avoids.keys candidate (by
        have filtered := (List.mem_filter.mp tailMember).1
        simpa [TypeSubst.keys] using filtered)
  · intro key stored member candidate candidateMember
    simp only [TypeSubst.bind, List.mem_cons] at member
    rcases member with head | tail
    · rcases Prod.mk.inj head with ⟨rfl, rfl⟩
      exact resolvedFresh candidate candidateMember
    · obtain ⟨oldEntry, oldMember, transformed⟩ := List.mem_map.mp tail
      rcases oldEntry with ⟨oldKey, oldValue⟩
      have oldInSubstitution : (oldKey, oldValue) ∈ substitution :=
        (List.mem_filter.mp oldMember).1
      have oldValueFresh : ∀ other,
          other ∈ typeVars oldValue → other ∉ forbidden :=
        avoids.values oldKey oldValue oldInSubstitution
      have transformedFresh : ∀ other,
          other ∈ typeVars (applyAssignment name resolved oldValue) →
            other ∉ forbidden := by
        apply apply_variable_avoids
            (substitution := [(name, resolved)])
            (forbidden := forbidden)
        · intro assignedKey assignedValue assignedMember other otherMember
          simp only [List.mem_singleton, Prod.mk.injEq] at assignedMember
          rcases assignedMember with ⟨rfl, rfl⟩
          exact resolvedFresh other otherMember
        · exact oldValueFresh
      have keyEquation := congrArg Prod.fst transformed
      have valueEquation := congrArg Prod.snd transformed
      simp only at keyEquation valueEquation
      subst key
      rw [← valueEquation] at candidateMember
      exact transformedFresh candidate candidateMember

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact

/-- Variables of a member atom occur in the variable list of the enclosing
atom list. -/
theorem typeVars_mem_typeVarsList_of_mem
    {atom : Atom} {atoms : List Atom} (member : atom ∈ atoms) :
    ∀ name, name ∈ TypeSubst.typeVars atom →
      name ∈ TypeSubst.typeVarsList atoms := by
  induction atoms with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · intro name occurrence
        simp [TypeSubst.typeVarsList, occurrence]
      · intro name occurrence
        simp only [TypeSubst.typeVarsList, List.mem_append]
        exact Or.inr (inductionHypothesis member name occurrence)

/-- Membership in a list's variable collection comes from one member atom. -/
theorem exists_mem_of_mem_typeVarsList
    {name : String} {atoms : List Atom}
    (occurrence : name ∈ TypeSubst.typeVarsList atoms) :
    ∃ atom ∈ atoms, name ∈ TypeSubst.typeVars atom := by
  induction atoms with
  | nil => simp [TypeSubst.typeVarsList] at occurrence
  | cons head tail inductionHypothesis =>
      simp only [TypeSubst.typeVarsList, List.mem_append] at occurrence
      rcases occurrence with headOccurrence | tailOccurrence
      · exact ⟨head, by simp, headOccurrence⟩
      · obtain ⟨atom, member, atomOccurrence⟩ :=
          inductionHypothesis tailOccurrence
        exact ⟨atom, by simp [member], atomOccurrence⟩

/-- Every member of a list that avoids a name scope avoids that scope. -/
theorem AtomsAvoid.atom
    {atoms : List Atom} {forbidden : List String}
    (avoids : AtomsAvoid atoms forbidden) {atom : Atom}
    (member : atom ∈ atoms) : AtomAvoids atom forbidden := by
  intro name occurrence
  exact avoids name
    (typeVars_mem_typeVarsList_of_mem member name occurrence)

/-- Fresh-family separation is inherited by ordered subfamilies.  This is
the selection-facing interface: choosing one declaration from each family
cannot introduce a private-name collision that was absent from the complete
families. -/
theorem FreshFamiliesSeparated.mono
    {left right left' right' : List Atom}
    (separated : FreshFamiliesSeparated left right)
    (leftSubset : ∀ atom, atom ∈ left' → atom ∈ left)
    (rightSubset : ∀ atom, atom ∈ right' → atom ∈ right) :
    FreshFamiliesSeparated left' right' := by
  intro name leftOccurrence rightOccurrence
  obtain ⟨leftAtom, leftMember, leftVariable⟩ :=
    exists_mem_of_mem_typeVarsList leftOccurrence
  obtain ⟨rightAtom, rightMember, rightVariable⟩ :=
    exists_mem_of_mem_typeVarsList rightOccurrence
  exact separated name
    (typeVars_mem_typeVarsList_of_mem
      (leftSubset leftAtom leftMember) name leftVariable)
    (typeVars_mem_typeVarsList_of_mem
      (rightSubset rightAtom rightMember) name rightVariable)

private theorem atomsAvoid_cons_iff
    {head : Atom} {tail : List Atom} {forbidden : List String} :
    AtomsAvoid (head :: tail) forbidden ↔
      AtomAvoids head forbidden ∧ AtomsAvoid tail forbidden := by
  simp only [AtomsAvoid, AtomAvoids, TypeSubst.typeVarsList,
    List.mem_append]
  constructor
  · intro avoids
    constructor
    · intro name member
      exact avoids name (Or.inl member)
    · intro name member
      exact avoids name (Or.inr member)
  · rintro ⟨headAvoids, tailAvoids⟩ name (member | member)
    · exact headAvoids name member
    · exact tailAvoids name member

private def AppliedReducedFreshMotive (forbidden : List String)
    (substitution : TypeSubst) (left right : Atom)
    (output : TypeSubst)
    (_ : AppliedReducedTypeMatchRel substitution left right output) : Prop :=
  substitution.Avoids forbidden → AtomAvoids left forbidden →
    AtomAvoids right forbidden → output.Avoids forbidden

private def AppliedPresentationFreshMotive (forbidden : List String)
    (substitution : TypeSubst) (left right : Atom)
    (output : TypeSubst)
    (_ : AppliedTypePresentationMatchRel substitution left right output) : Prop :=
  substitution.Avoids forbidden → AtomAvoids left forbidden →
    AtomAvoids right forbidden → output.Avoids forbidden

private def AppliedReducedListFreshMotive (forbidden : List String)
    (substitution : TypeSubst) (left right : List Atom)
    (output : TypeSubst)
    (_ : AppliedReducedTypeListMatchRel substitution left right output) : Prop :=
  substitution.Avoids forbidden → AtomsAvoid left forbidden →
    AtomsAvoid right forbidden → output.Avoids forbidden

private theorem appliedFresh_identical (forbidden : List String)
    (substitution : TypeSubst) (atom : Atom) :
    AppliedReducedFreshMotive forbidden substitution atom atom substitution
      (.identical substitution atom) := by
  intro substitutionAvoids _ _
  exact substitutionAvoids

private theorem appliedFresh_bindLeft (forbidden : List String)
    {substitution : TypeSubst} {name : String} {right : Atom}
    (occurs : name ∉ TypeSubst.typeVars right) :
    AppliedReducedFreshMotive forbidden substitution (.var name) right
      (substitution.bind name right) (.bindLeft occurs) := by
  intro substitutionAvoids leftAvoids rightAvoids
  exact substitutionAvoids.bind
    (leftAvoids name (by simp [TypeSubst.typeVars]))
    rightAvoids

private theorem appliedFresh_bindRight (forbidden : List String)
    {substitution : TypeSubst} {left : Atom} {name : String}
    (notVariable : ∀ other, left ≠ .var other)
    (occurs : name ∉ TypeSubst.typeVars left) :
    AppliedReducedFreshMotive forbidden substitution left (.var name)
      (substitution.bind name left) (.bindRight notVariable occurs) := by
  intro substitutionAvoids leftAvoids rightAvoids
  exact substitutionAvoids.bind
    (rightAvoids name (by simp [TypeSubst.typeVars]))
    leftAvoids

private theorem appliedFresh_expression (forbidden : List String)
    {substitution output : TypeSubst} {left right : List Atom}
    (children : AppliedReducedTypeListMatchRel
      substitution left right output)
    (childrenIH : AppliedReducedListFreshMotive forbidden
      substitution left right output children) :
    AppliedReducedFreshMotive forbidden substitution
      (.expression left) (.expression right) output (.expression children) := by
  intro substitutionAvoids leftAvoids rightAvoids
  exact childrenIH substitutionAvoids
    (by simpa [AtomAvoids, AtomsAvoid, TypeSubst.typeVars]
      using leftAvoids)
    (by simpa [AtomAvoids, AtomsAvoid, TypeSubst.typeVars]
      using rightAvoids)

private theorem appliedFresh_ordinary (forbidden : List String)
    {substitution output : TypeSubst}
    {left right resolvedLeft resolvedRight : Atom}
    (leftEquation : substitution.apply left = resolvedLeft)
    (rightEquation : substitution.apply right = resolvedRight)
    (applied : AppliedReducedTypeMatchRel
      substitution resolvedLeft resolvedRight output)
    (appliedIH : AppliedReducedFreshMotive forbidden substitution
      resolvedLeft resolvedRight output applied) :
    AppliedPresentationFreshMotive forbidden substitution left right output
      (.ordinary leftEquation rightEquation applied) := by
  intro substitutionAvoids leftAvoids rightAvoids
  apply appliedIH substitutionAvoids
  · rw [← leftEquation]
    exact TypeSubst.apply_variable_avoids
      substitutionAvoids.values left leftAvoids
  · rw [← rightEquation]
    exact TypeSubst.apply_variable_avoids
      substitutionAvoids.values right rightAvoids

private theorem appliedFresh_nil (forbidden : List String)
    (substitution : TypeSubst) :
    AppliedReducedListFreshMotive forbidden substitution [] [] substitution
      (.nil substitution) := by
  intro substitutionAvoids _ _
  exact substitutionAvoids

private theorem appliedFresh_cons (forbidden : List String)
    {substitution next output : TypeSubst} {left right : Atom}
    {lefts rights : List Atom}
    (head : AppliedTypePresentationMatchRel substitution left right next)
    (tail : AppliedReducedTypeListMatchRel next lefts rights output)
    (headIH : AppliedPresentationFreshMotive forbidden
      substitution left right next head)
    (tailIH : AppliedReducedListFreshMotive forbidden
      next lefts rights output tail) :
    AppliedReducedListFreshMotive forbidden substitution
      (left :: lefts) (right :: rights) output (.cons head tail) := by
  intro substitutionAvoids leftAvoids rightAvoids
  have leftParts := atomsAvoid_cons_iff.mp leftAvoids
  have rightParts := atomsAvoid_cons_iff.mp rightAvoids
  exact tailIH
    (headIH substitutionAvoids leftParts.1 rightParts.1)
    leftParts.2 rightParts.2

/-- Applied reduced matching preserves avoidance of a finite public scope. -/
theorem appliedReducedTypeMatch_output_avoids
    {substitution output : TypeSubst} {left right : Atom}
    {forbidden : List String}
    (derivation : AppliedReducedTypeMatchRel
      substitution left right output) :
    AppliedReducedFreshMotive forbidden substitution left right output
      derivation :=
  AppliedReducedTypeMatchRel.rec
    (motive_1 := AppliedReducedFreshMotive forbidden)
    (motive_2 := AppliedPresentationFreshMotive forbidden)
    (motive_3 := AppliedReducedListFreshMotive forbidden)
    (appliedFresh_identical forbidden)
    (appliedFresh_bindLeft forbidden)
    (appliedFresh_bindRight forbidden)
    (appliedFresh_expression forbidden)
    (appliedFresh_ordinary forbidden)
    (appliedFresh_nil forbidden)
    (appliedFresh_cons forbidden) derivation

/-- List companion of `appliedReducedTypeMatch_output_avoids`. -/
theorem appliedReducedTypeListMatch_output_avoids
    {substitution output : TypeSubst} {left right : List Atom}
    {forbidden : List String}
    (derivation : AppliedReducedTypeListMatchRel
      substitution left right output) :
    AppliedReducedListFreshMotive forbidden substitution left right output
      derivation :=
  AppliedReducedTypeListMatchRel.rec
    (motive_1 := AppliedReducedFreshMotive forbidden)
    (motive_2 := AppliedPresentationFreshMotive forbidden)
    (motive_3 := AppliedReducedListFreshMotive forbidden)
    (appliedFresh_identical forbidden)
    (appliedFresh_bindLeft forbidden)
    (appliedFresh_bindRight forbidden)
    (appliedFresh_expression forbidden)
    (appliedFresh_ordinary forbidden)
    (appliedFresh_nil forbidden)
    (appliedFresh_cons forbidden) derivation

/-- Resolving the two raw atoms through an avoiding presentation and then
matching them cannot introduce a forbidden name. -/
theorem appliedTypePresentationMatch_output_avoids
    {substitution output : TypeSubst} {left right : Atom}
    {forbidden : List String}
    (derivation : AppliedTypePresentationMatchRel
      substitution left right output) :
    AppliedPresentationFreshMotive forbidden substitution left right output
      derivation :=
  AppliedTypePresentationMatchRel.rec
    (motive_1 := AppliedReducedFreshMotive forbidden)
    (motive_2 := AppliedPresentationFreshMotive forbidden)
    (motive_3 := AppliedReducedListFreshMotive forbidden)
    (appliedFresh_identical forbidden)
    (appliedFresh_bindLeft forbidden)
    (appliedFresh_bindRight forbidden)
    (appliedFresh_expression forbidden)
    (appliedFresh_ordinary forbidden)
    (appliedFresh_nil forbidden)
    (appliedFresh_cons forbidden) derivation

private def ReducedFreshMotive (forbidden : List String)
    (substitution : TypeSubst) (left right : Atom)
    (output : TypeSubst)
    (_ : ReducedTypePresentationMatchRel substitution left right output) : Prop :=
  substitution.Avoids forbidden → AtomAvoids left forbidden →
    AtomAvoids right forbidden → output.Avoids forbidden

private def ReducedListFreshMotive (forbidden : List String)
    (substitution : TypeSubst) (left right : List Atom)
    (output : TypeSubst)
    (_ : ReducedTypePresentationListMatchRel
      substitution left right output) : Prop :=
  substitution.Avoids forbidden → AtomsAvoid left forbidden →
    AtomsAvoid right forbidden → output.Avoids forbidden

private theorem reducedFresh_undefinedLeft (forbidden : List String)
    (substitution : TypeSubst) (right : Atom) :
    ReducedFreshMotive forbidden substitution Atom.undefinedType right
      substitution (.undefinedLeft substitution right) := by
  intro substitutionAvoids _ _
  exact substitutionAvoids

private theorem reducedFresh_undefinedRight (forbidden : List String)
    (substitution : TypeSubst) (left : Atom) :
    ReducedFreshMotive forbidden substitution left Atom.undefinedType
      substitution (.undefinedRight substitution left) := by
  intro substitutionAvoids _ _
  exact substitutionAvoids

private theorem reducedFresh_expression (forbidden : List String)
    {substitution output : TypeSubst} {left right : List Atom}
    (children : ReducedTypePresentationListMatchRel
      substitution left right output)
    (childrenIH : ReducedListFreshMotive forbidden
      substitution left right output children) :
    ReducedFreshMotive forbidden substitution
      (.expression left) (.expression right) output (.expression children) := by
  intro substitutionAvoids leftAvoids rightAvoids
  exact childrenIH substitutionAvoids
    (by simpa [AtomAvoids, AtomsAvoid, TypeSubst.typeVars]
      using leftAvoids)
    (by simpa [AtomAvoids, AtomsAvoid, TypeSubst.typeVars]
      using rightAvoids)

private theorem reducedFresh_ordinary (forbidden : List String)
    {substitution output : TypeSubst}
    {left right resolvedLeft resolvedRight : Atom}
    (leftNotUndefined : left ≠ Atom.undefinedType)
    (rightNotUndefined : right ≠ Atom.undefinedType)
    (leafShape : ReducedTypeLeafShape left right)
    (leftEquation : substitution.apply left = resolvedLeft)
    (rightEquation : substitution.apply right = resolvedRight)
    (applied : AppliedReducedTypeMatchRel
      substitution resolvedLeft resolvedRight output) :
    ReducedFreshMotive forbidden substitution left right output
      (.ordinary leftNotUndefined rightNotUndefined leafShape
        leftEquation rightEquation applied) := by
  intro substitutionAvoids leftAvoids rightAvoids
  apply appliedReducedTypeMatch_output_avoids applied substitutionAvoids
  · rw [← leftEquation]
    exact TypeSubst.apply_variable_avoids
      substitutionAvoids.values left leftAvoids
  · rw [← rightEquation]
    exact TypeSubst.apply_variable_avoids
      substitutionAvoids.values right rightAvoids

private theorem reducedFresh_nil (forbidden : List String)
    (substitution : TypeSubst) :
    ReducedListFreshMotive forbidden substitution [] [] substitution
      (.nil substitution) := by
  intro substitutionAvoids _ _
  exact substitutionAvoids

private theorem reducedFresh_cons (forbidden : List String)
    {substitution next output : TypeSubst} {left right : Atom}
    {lefts rights : List Atom}
    (head : ReducedTypePresentationMatchRel substitution left right next)
    (tail : ReducedTypePresentationListMatchRel next lefts rights output)
    (headIH : ReducedFreshMotive forbidden
      substitution left right next head)
    (tailIH : ReducedListFreshMotive forbidden
      next lefts rights output tail) :
    ReducedListFreshMotive forbidden substitution
      (left :: lefts) (right :: rights) output (.cons head tail) := by
  intro substitutionAvoids leftAvoids rightAvoids
  have leftParts := atomsAvoid_cons_iff.mp leftAvoids
  have rightParts := atomsAvoid_cons_iff.mp rightAvoids
  exact tailIH
    (headIH substitutionAvoids leftParts.1 rightParts.1)
    leftParts.2 rightParts.2

/-- Recursive R2 presentation matching preserves avoidance. -/
theorem reducedTypePresentationMatch_output_avoids
    {substitution output : TypeSubst} {left right : Atom}
    {forbidden : List String}
    (derivation : ReducedTypePresentationMatchRel
      substitution left right output) :
    ReducedFreshMotive forbidden substitution left right output derivation :=
  ReducedTypePresentationMatchRel.rec
    (motive_1 := ReducedFreshMotive forbidden)
    (motive_2 := ReducedListFreshMotive forbidden)
    (reducedFresh_undefinedLeft forbidden)
    (reducedFresh_undefinedRight forbidden)
    (reducedFresh_expression forbidden)
    (reducedFresh_ordinary forbidden)
    (reducedFresh_nil forbidden)
    (reducedFresh_cons forbidden) derivation

/-- List companion of `reducedTypePresentationMatch_output_avoids`. -/
theorem reducedTypePresentationListMatch_output_avoids
    {substitution output : TypeSubst} {left right : List Atom}
    {forbidden : List String}
    (derivation : ReducedTypePresentationListMatchRel
      substitution left right output) :
    ReducedListFreshMotive forbidden substitution left right output
      derivation :=
  ReducedTypePresentationListMatchRel.rec
    (motive_1 := ReducedFreshMotive forbidden)
    (motive_2 := ReducedListFreshMotive forbidden)
    (reducedFresh_undefinedLeft forbidden)
    (reducedFresh_undefinedRight forbidden)
    (reducedFresh_expression forbidden)
    (reducedFresh_ordinary forbidden)
    (reducedFresh_nil forbidden)
    (reducedFresh_cons forbidden) derivation

/-- Published top-level wildcards and the recursive R2 lane both preserve
private-scope freshness. -/
theorem corePlusR2TypePresentationMatch_output_avoids
    {substitution output : TypeSubst} {left right : Atom}
    {forbidden : List String}
    (derivation : CorePlusR2TypePresentationMatchRel
      substitution left right output)
    (substitutionAvoids : substitution.Avoids forbidden)
    (leftAvoids : AtomAvoids left forbidden)
    (rightAvoids : AtomAvoids right forbidden) :
    output.Avoids forbidden := by
  cases derivation with
  | undefinedLeft => exact substitutionAvoids
  | undefinedRight => exact substitutionAvoids
  | atomLeft => exact substitutionAvoids
  | atomRight => exact substitutionAvoids
  | reduced _ _ _ _ reduced =>
      exact reducedTypePresentationMatch_output_avoids reduced
        substitutionAvoids leftAvoids rightAvoids

/-- The complete ordered argument fold preserves private-scope freshness. -/
theorem presentationArgumentList_output_avoids
    {expected actual : List Atom} {incoming output : TypeSubst}
    {forbidden : List String}
    (derivation : PresentationArgumentListMatchRel
      expected actual incoming output)
    (incomingAvoids : incoming.Avoids forbidden)
    (expectedAvoids : AtomsAvoid expected forbidden)
    (actualAvoids : AtomsAvoid actual forbidden) :
    output.Avoids forbidden := by
  induction derivation with
  | nil => exact incomingAvoids
  | @cons expected actual expecteds actuals incoming next output head tail ih =>
      have expectedParts := atomsAvoid_cons_iff.mp expectedAvoids
      have actualParts := atomsAvoid_cons_iff.mp actualAvoids
      exact ih
        (corePlusR2TypePresentationMatch_output_avoids head incomingAvoids
          expectedParts.1 actualParts.1)
        expectedParts.2 actualParts.2

/-! ## Boundary canaries -/

/-- Positive: a private binding for `t` avoids an unrelated public name. -/
theorem private_t_avoids_public :
    TypeSubst.Avoids [("t", .symbol "A")] ["public"] := by
  constructor
  · simp [TypeSubst.keys]
  · simp [TypeSubst.typeVars]

/-- Negative: assigning the public name itself violates the boundary. -/
theorem public_key_does_not_avoid_itself :
    ¬TypeSubst.Avoids [("public", .symbol "A")] ["public"] := by
  intro avoids
  exact avoids.keys "public" (by simp [TypeSubst.keys]) (by simp)

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness
