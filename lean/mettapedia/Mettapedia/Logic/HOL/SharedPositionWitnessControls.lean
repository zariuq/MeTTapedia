import Mettapedia.Logic.HOL.OrderedConstructorChildExistence
import Mettapedia.Logic.HOL.OrderedPositionProofControls

/-!
# Shared-position witnesses and independent existential queries

Two different slots can return the same child index. Each constrained lookup
has a retained existential proof, but their two position requirements cannot
be conjoined under one slot. The natural model independently refutes that
conjunction and therefore prevents existential witness identification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SharedPositionWitnessControls

open OrderedPositionPrograms SuccessorOrder
open OrderedPositionProofControls (number Symbol zero successor one model values full)

def plan : Plan Symbol [] number .prop := [(one, .top), (one, .top)]

def firstQuery : ProofSyntax Symbol [] (compileAt zero successor plan Subst.id zero .top) :=
  compileAt_here zero successor (one, .top) [(one, .top)] Subst.id zero .top
    (lessNext successor zero) (.eqRefl .top)

def secondQuery : ProofSyntax Symbol [] (compileAt zero successor plan Subst.id one .top) :=
  compileAt_later zero successor (one, .top) [(one, .top)] Subst.id one zero .top
    (sumZero successor zero one)
    (compileAt_here zero successor (one, .top) [] Subst.id zero .top
      (lessNext successor zero) (.eqRefl .top))

theorem firstQuery_free : firstQuery.FunctionExtensionalityFree :=
  compileAt_here_free zero successor (one, .top) [(one, .top)] Subst.id zero .top
    (lessNext successor zero) (.eqRefl .top) (lessNext_free successor zero) True.intro

theorem secondQuery_free : secondQuery.FunctionExtensionalityFree := by
  apply compileAt_later_free
  · exact sumZero_free _ _ _
  · apply compileAt_here_free
    · exact lessNext_free _ _
    · trivial

def atPosition (slot : ClosedTerm Symbol number) : Formula Symbol [number] :=
  .and (.eq (.var .vz) (weaken slot))
    (compileAt zero successor plan (fun entry => weaken (Subst.id entry)) (.var .vz) .top)

def atPosition_intro (slot : ClosedTerm Symbol number)
    (query : ProofSyntax Symbol [] (compileAt zero successor plan Subst.id slot .top)) :
    ProofSyntax Symbol [] (.ex (atPosition slot)) := by
  apply ProofSyntax.exI slot
  apply ProofSyntax.castIndices rfl ?_ (.andI (.eqRefl slot) query)
  simp only [atPosition, instantiate, HOL.subst, Subst.single, compileAt_subst,
    PredicateFixedPoint.subst_single_weaken]

theorem atPosition_intro_free (slot : ClosedTerm Symbol number)
    (query : ProofSyntax Symbol [] (compileAt zero successor plan Subst.id slot .top))
    (free : query.FunctionExtensionalityFree) :
    (atPosition_intro slot query).FunctionExtensionalityFree := by
  unfold atPosition_intro
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨True.intro, free⟩

def independentWitnesses : ProofSyntax Symbol [] (.and (.ex (atPosition zero)) (.ex (atPosition one))) :=
  .andI (atPosition_intro zero firstQuery) (atPosition_intro one secondQuery)

theorem independentWitnesses_free : independentWitnesses.FunctionExtensionalityFree :=
  ⟨atPosition_intro_free zero firstQuery firstQuery_free, atPosition_intro_free one secondQuery secondQuery_free⟩

theorem independentWitnesses_realized :
    (model.denote (.and (.ex (atPosition zero)) (.ex (atPosition one))) @values).down :=
  Soundness.extDerivation_sound independentWitnesses.erase (M := model) (ρ := @values)
    (model.functionsRespectEqv_of_fullDomains full) (by intro _ absent; nomatch absent)
    (by intro _ absent; nomatch absent)

def sharedWitness : ClosedFormula Symbol := .ex (.and (atPosition zero) (atPosition one))

theorem sharedWitness_false : ¬ (model.denote sharedWitness @values).down := by
  intro present
  change ∃ slot : ULift.{1} Nat, True ∧
    ((slot = ULift.up 0 ∧ _) ∧ (slot = ULift.up 1 ∧ _)) at present
  obtain ⟨slot, _, ⟨⟨first, _⟩, ⟨second, _⟩⟩⟩ := present
  have impossible : (0 : Nat) = 1 := congrArg ULift.down (first.symm.trans second)
  exact Nat.noConfusion impossible

theorem sharedWitness_refused : ¬ Nonempty (ProofSyntax Symbol [] sharedWitness) := by
  rintro ⟨present⟩
  exact sharedWitness_false (Soundness.extDerivation_sound present.erase (M := model) (ρ := @values)
    (model.functionsRespectEqv_of_fullDomains full) (by intro _ absent; nomatch absent)
    (by intro _ absent; nomatch absent))

#print axioms independentWitnesses_free
#print axioms independentWitnesses_realized
#print axioms sharedWitness_refused

end Mettapedia.Logic.HOL.SharedPositionWitnessControls
