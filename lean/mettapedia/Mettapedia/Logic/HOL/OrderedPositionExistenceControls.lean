import Mettapedia.Logic.HOL.OrderedPositionExistence
import Mettapedia.Logic.HOL.OrderedPositionFunctionalityControls

/-!
# Open and closed dynamic-prefix controls

The same suffix child survives zero, repeated and heterogeneous prefix
segments. Open counts retain their original variables. Empty plans and
unrepresented indices cannot supply a lookup witness in the natural model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.OrderedPositionExistenceControls

open OrderedPositionPrograms SuccessorOrder
open OrderedPositionProofControls (number Symbol zero successor one model values full)
open OrderedPositionFunctionalityControls (assumptions arithmetic arithmetic_free assumptions_realizable)

def suffix (context : Ctx Unit) : Plan Symbol context number .prop :=
  [(.app (weakenCtx context successor) (weakenCtx context zero), .top)]

def seed {Γ : Ctx Unit} {hypotheses : List (Formula Symbol Γ)} :
    ProofSyntax Symbol hypotheses (lookupExists zero successor (suffix Γ) Subst.id .top) := by
  apply lookupExists_intro zero successor (suffix Γ) Subst.id (weakenCtx Γ zero) .top
  apply compileAt_here
  · apply ProofSyntax.castIndices rfl ?_ (lessNext successor (weakenCtx Γ zero))
    simp only [subst_id]
  · exact .eqRefl .top

theorem seed_free {Γ : Ctx Unit} {hypotheses : List (Formula Symbol Γ)} :
    (seed (Γ := Γ) (hypotheses := hypotheses)).FunctionExtensionalityFree := by
  unfold seed
  apply lookupExists_intro_free
  apply compileAt_here_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact lessNext_free _ _
  · trivial

def closedPrefix : Plan Symbol [] number .prop :=
  [(zero, .top), (one, .bot), (zero, .bot), (one, .top)]

def closedWitness : ProofSyntax Symbol assumptions
    (lookupExists zero successor (closedPrefix ++ suffix []) Subst.id .top) :=
  lookupExists_prefix zero successor closedPrefix (suffix []) Subst.id .top arithmetic.induction seed

theorem closedWitness_free : closedWitness.FunctionExtensionalityFree :=
  lookupExists_prefix_free zero successor closedPrefix (suffix []) Subst.id .top arithmetic.induction seed
    arithmetic_free.2.2 seed_free

abbrev context : Ctx Unit := [number, number]

def openPrefix : Plan Symbol context number .prop :=
  [(.var .vz, .top), (.var (.vs .vz), .bot), (.var .vz, .top)]

def openAssumptions : List (Formula Symbol context) :=
  [NaturalRecursionProofs.inductionPrinciple (weakenCtx context zero) (weakenCtx context successor)]

def openWitness : ProofSyntax Symbol openAssumptions
    (lookupExists zero successor (openPrefix ++ suffix context) Subst.id .top) :=
  lookupExists_prefix zero successor openPrefix (suffix context) Subst.id .top
    (.hyp (Δ := openAssumptions) ⟨0, by decide⟩) seed

theorem openWitness_free : openWitness.FunctionExtensionalityFree := by
  unfold openWitness
  apply lookupExists_prefix_free
  · trivial
  · exact seed_free

theorem openAssumptions_realizable (environment : model.Valuation context) :
    ∀ formula ∈ openAssumptions, (model.denote formula environment).down := by
  intro formula member
  have same := List.mem_singleton.mp member
  subst formula
  change ∀ predicate : Ty.denote model.Carrier (number ⇒ .prop), True →
    ((predicate (ULift.up 0)).down ∧
      (∀ value : ULift.{1} Nat, True → (predicate value).down →
        (predicate (ULift.up (value.down + 1))).down)) →
    ∀ value : ULift.{1} Nat, True → (predicate value).down
  intro predicate _ premises value _
  rcases value with ⟨n⟩
  induction n with
  | zero => exact premises.1
  | succ n previous => exact premises.2 (ULift.up n) trivial previous

theorem empty_plan_refused :
    ¬ Nonempty (ProofSyntax Symbol assumptions
      (lookupExists zero successor ([] : Plan Symbol [] number .prop) Subst.id .top)) := by
  rintro ⟨present⟩
  have impossible := Soundness.extDerivation_sound present.erase (M := model) (ρ := @values)
    (model.functionsRespectEqv_of_fullDomains full) (by intro _ absent; nomatch absent) assumptions_realizable
  change ∃ slot : ULift.{1} Nat, True ∧ False at impossible
  obtain ⟨_, _, invalid⟩ := impossible
  exact invalid

theorem absent_index_refused :
    ¬ Nonempty (ProofSyntax Symbol assumptions
      (lookupExists zero successor (suffix []) Subst.id .bot)) := by
  rintro ⟨present⟩
  have equal : ProofSyntax Symbol assumptions (.eq (.bot : ClosedFormula Symbol) .top) := by
    apply ProofSyntax.exE present
    let body := compileAt zero successor (suffix [])
      (fun entry => weaken (Subst.id entry)) (.var .vz) (weaken (.bot : ClosedFormula Symbol))
    let hypotheses := body :: weakenHyps assumptions
    apply compileAt_result zero successor (suffix []) (fun entry => weaken (Subst.id entry))
      (.var .vz) (weaken (.bot : ClosedFormula Symbol)) (weaken (.top : ClosedFormula Symbol))
    · intro occurrence
      have only : occurrence = ⟨0, by decide⟩ := Fin.eq_zero occurrence
      subst occurrence
      exact .eqRefl .top
    · exact .hyp (Δ := hypotheses) 0
  have impossible := Soundness.extDerivation_sound equal.erase (M := model) (ρ := @values)
    (model.functionsRespectEqv_of_fullDomains full) (by intro _ absent; nomatch absent) assumptions_realizable
  change False ↔ True at impossible
  exact impossible.mpr True.intro

#print axioms closedWitness_free
#print axioms openWitness_free
#print axioms empty_plan_refused
#print axioms absent_index_refused

end Mettapedia.Logic.HOL.OrderedPositionExistenceControls
