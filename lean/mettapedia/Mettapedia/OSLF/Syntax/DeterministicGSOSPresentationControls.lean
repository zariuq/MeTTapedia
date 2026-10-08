import Mettapedia.OSLF.Syntax.DeterministicGSOSFinitePresentation
import Mettapedia.OSLF.Syntax.DeterministicGSOSControls

/-!
# Independent finite-rule construction and occurrence controls

Two separately authored prefix clauses have identical targets and retain
different firing origins. Their independently constructed natural law
returns the exact supplied original argument, including under a variable
collision. A second specification has overlapping clauses with a hole
target and a constructor target; it admits no law denoting all its firings.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.PresentationControls

open CategoryTheory Mettapedia.TypeTheory Controls

/-- A finite clause with no observations and the exact original child target. -/
noncomputable def prefixClause (label : Nat) :
    FiniteRule actions (sort := ()) (Operator.prefix label) where
  observed := ∅
  pattern address := False.elim (Finset.notMem_empty address.val address.property)
  target := Controls.pure (.original ())

/-- Prefix declarations have two separately retained authored positions. -/
def clauseOrigins (_sort : signature.Srt) (operator : Operator) (action : Nat) : Type :=
  match operator with
  | .prefix label => {_origin : Fin 2 // action = label}
  | .stopped => Empty
  | .priority => Empty

noncomputable def authored : AuthoredFinitePresentation actions where
  Origin := clauseOrigins
  rule := fun sort operator _ origin => by
    cases sort
    cases operator with
    | stopped => exact origin.elim
    | priority => exact origin.elim
    | «prefix» label => exact prefixClause label

/-- The two authored positions agree locally on every simultaneously firing target. -/
theorem authored_consistent : FinitePresentation.Consistent actions authored.readoutSet := by
  intro sort operator action guard first second firstMember _ secondMember _
  obtain ⟨firstOrigin, firstEq⟩ := firstMember
  obtain ⟨secondOrigin, secondEq⟩ := secondMember
  subst first
  subst second
  cases sort
  cases operator with
  | stopped => exact firstOrigin.elim
  | priority => exact firstOrigin.elim
  | «prefix» _ => rfl

noncomputable def constructedLaw : Law signature actions := authored.toLaw

noncomputable def firstFiring :
    authored.Firing (sort := ()) (Operator.prefix 7) 7 (fun _ => false) :=
  ⟨⟨0, rfl⟩, by intro address present; simp [authored, prefixClause] at present⟩

noncomputable def secondFiring :
    authored.Firing (sort := ()) (Operator.prefix 7) 7 (fun _ => false) :=
  ⟨⟨1, rfl⟩, by intro address present; simp [authored, prefixClause] at present⟩

theorem authored_firings_differ : firstFiring ≠ secondFiring := by
  intro same
  exact Fin.zero_ne_one (congrArg (fun firing => firing.val.val) same)

theorem duplicate_clause_readouts_agree : firstFiring.readout = secondFiring.readout := rfl

/-- Each separately supplied occurrence is accepted by the actually constructed law. -/
theorem first_firing_readout :
    universalReadout actions (fromLaw actions constructedLaw) (Operator.prefix 7)
      (fun _ => false) 7 = some firstFiring.readout :=
  AuthoredFinitePresentation.firing_readout authored_consistent firstFiring

theorem second_firing_readout :
    universalReadout actions (fromLaw actions constructedLaw) (Operator.prefix 7)
      (fun _ => false) 7 = some secondFiring.readout :=
  AuthoredFinitePresentation.firing_readout authored_consistent secondFiring

/-- Both original and derivative input values are independently supplied. -/
def prefixInputs : BehaviourArguments signature actions naturals (sort := ()) (Operator.prefix 7) :=
  fun _ => (10, fun action => if action = 7 then some 11 else none)

theorem prefix_clause_matches (guard : Guard actions (sort := ()) (Operator.prefix 7)) :
    (prefixClause 7).Matches guard := by
  intro address present
  simp [prefixClause] at present

/-- Selecting any matching authored position returns the full original argument. -/
theorem constructed_prefix_readout :
    constructedLaw.app naturals PUnit.unit () ⟨Operator.prefix 7, prefixInputs⟩ 7 =
      some (Controls.pure (X := naturals) 10) := by
  have member : prefixClause 7 ∈ authored.readoutSet () (Operator.prefix 7) 7 :=
    ⟨⟨0, rfl⟩, rfl⟩
  have chosen := FinitePresentation.toSchemas_firing actions authored.readoutSet authored_consistent
    7 (inputGuard actions prefixInputs) (prefixClause 7) member
    (prefix_clause_matches (inputGuard actions prefixInputs))
  change instantiate actions (FinitePresentation.toSchemas actions authored.readoutSet)
    (X := naturals) (sort := ()) (Operator.prefix 7) prefixInputs 7 = _
  simp only [instantiate, instantiateAt, chosen, Option.map_some]
  rfl

/-- The constructed ordinary-format law commutes with a real variable collision. -/
theorem constructed_collision_readout :
    constructedLaw.app units PUnit.unit ()
      ⟨Operator.prefix 7, mapArguments actions collapse prefixInputs⟩ 7 =
      (some (Controls.pure (X := naturals) 10)).map (signature.rename collapse) := by
  have natural := congrArg
    (fun mapping => mapping PUnit.unit () ⟨Operator.prefix 7, prefixInputs⟩ 7)
    (constructedLaw.naturality collapse)
  change constructedLaw.app units PUnit.unit ()
    ⟨Operator.prefix 7, mapArguments actions collapse prefixInputs⟩ 7 =
      (constructedLaw.app naturals PUnit.unit () ⟨Operator.prefix 7, prefixInputs⟩ 7).map
        (signature.rename collapse) at natural
  exact natural.trans (congrArg (Option.map (signature.rename collapse)) constructed_prefix_readout)

/-- The complete erased target does not determine an authored firing origin. -/
theorem no_firing_origin_recovery :
    ¬ ∃ recover : signature.Term (universalVariables actions (sort := ()) (Operator.prefix 7)) () →
        authored.Firing (sort := ()) (Operator.prefix 7) 7 (fun _ => false),
      recover firstFiring.readout = firstFiring ∧ recover secondFiring.readout = secondFiring := by
  rintro ⟨recover, first, second⟩
  exact authored_firings_differ (first.symm.trans
    ((congrArg recover duplicate_clause_readouts_agree).trans second))

/-- An incompatible independently authored clause inserts a real constructor. -/
noncomputable def prefixTerm {X : signature.Families} (label : Nat)
    (child : signature.Term X ()) : signature.Term X () :=
  IndexedPolynomial.Free.node signature.polynomial (.prefix label) (fun _ => child)

/-- The variant has the same finite premises and a different constructor target. -/
noncomputable def variantClause (label : Nat) :
    FiniteRule actions (sort := ()) (Operator.prefix label) :=
  {prefixClause label with target := prefixTerm 8 (prefixClause label).target}

theorem clause_targets_differ : (prefixClause 7).readout ≠ (variantClause 7).readout := by
  intro same
  unfold FiniteRule.readout variantClause prefixClause prefixTerm Controls.pure Signature.rename at same
  rw [IndexedPolynomial.Free.map_pure, IndexedPolynomial.Free.map_node] at same
  cases same

/-- These two clauses have identical empty premises but different complete targets. -/
noncomputable def conflicting : FinitePresentation actions :=
  fun _ operator action => match operator with
    | .prefix label => if label = 7 ∧ action = 7 then {prefixClause label, variantClause label} else ∅
    | .stopped => ∅
    | .priority => ∅

theorem variant_clause_matches (guard : Guard actions (sort := ()) (Operator.prefix 7)) :
    (variantClause 7).Matches guard := by
  intro address present
  simp [variantClause, prefixClause] at present

/-- Local deterministic consistency fails on an actual constructor distinction. -/
theorem conflicting_not_consistent : ¬ FinitePresentation.Consistent actions conflicting := by
  intro consistent
  have same := consistent () (Operator.prefix 7) 7 (fun _ => false)
    (prefixClause 7) (variantClause 7)
    (by simp [conflicting]) (prefix_clause_matches _)
    (by simp [conflicting]) (variant_clause_matches _)
  exact clause_targets_differ same

/-- No desired law is supplied: the conflicting authored format admits none. -/
theorem conflicting_has_no_denoting_law :
    ¬ ∃ candidate : Law signature actions,
      Denotes actions conflicting (fromLaw actions candidate) := by
  rw [FinitePresentation.admits_law_iff_consistent]
  exact conflicting_not_consistent

/-- An independently supplied law with the same firings must be the constructed law. -/
theorem denoting_law_unique (candidate : Law signature actions)
    (denotes : Denotes actions authored.readoutSet (fromLaw actions candidate)) :
    candidate = constructedLaw :=
  FinitePresentation.law_unique actions authored.readoutSet authored_consistent candidate denotes

end Mettapedia.OSLF.DeterministicGSOS.PresentationControls
