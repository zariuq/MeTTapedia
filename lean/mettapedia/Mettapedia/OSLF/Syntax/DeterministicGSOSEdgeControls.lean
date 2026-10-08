import Mettapedia.OSLF.Syntax.DeterministicGSOSEdgeReadout
import Mettapedia.OSLF.Syntax.DeterministicGSOSControls
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Actual operational edges with varying native certificates

The priority/prefix law supplies a real operational edge, not a hand-written
transition relation. Its target family has type `Fin (weight target + 2)`.
Two supplied occurrence identifiers produce different native receipts with
the same source, target and finite witness. Complete native event readout
retains the identifier that scalar observation omits.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.EdgeControls

open _root_.CategoryTheory Mettapedia.TypeTheory
open Controls EdgeReadout PresheafEventCertificates DisplayedPresheafTransport

abbrev World := Discrete Unit
abbrev world : Worldᵒᵖ := Opposite.op ⟨()⟩

abbrev worlds : Worldᵒᵖ ⥤ signature.Families := (Functor.const _).obj naturals

def variableSteps : worlds ⟶ worlds ⋙ behaviourFunctor signature actions where
  app _ := noSteps
  naturality {first second} change := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro value
    funext action
    rfl

noncomputable abbrev programs : Worldᵒᵖ ⥤ Type := terms worlds ()

theorem programs_map (first second : Worldᵒᵖ) (change : first ⟶ second)
    (term : signature.Term naturals ()) : programs.map change term = term :=
  IndexedPolynomial.Free.map_id signature.polynomial term

/-- A genuine fold observes each leaf and both priority arguments. -/
def weightAlgebra : signature.polynomial.Algebra (fun _ _ => Nat) where
  act := fun _ _ layer => match layer with
    | ⟨.stopped, _⟩ => 0
    | ⟨.prefix _, children⟩ => children ()
    | ⟨.priority, children⟩ => children left + children right

noncomputable def weight (term : signature.Term naturals ()) : Nat :=
  IndexedPolynomial.Free.fold signature.polynomial (fun _ _ value => value)
    weightAlgebra PUnit.unit () term

theorem elements_endpoint {first second : programs.Elements} (change : first ⟶ second) :
    first.2 = second.2 :=
  (programs_map first.1 second.1 change.val first.2).symm.trans change.property

/-- The witness type varies with the actual complete target term. -/
noncomputable abbrev targetFamily : DisplayedFamily programs where
  obj point := Fin (weight point.2 + 2)
  map change := ↾(Fin.cast (congrArg (fun term => weight term + 2) (elements_endpoint change)))
  map_id _ := by ext witness; rfl
  map_comp _ _ := by ext witness; rfl

noncomputable def firstEvent : Event law worlds variableSteps (Fin 2) () world where
  origin := 0
  source := prefixed 7 (Controls.pure (X := naturals) 10)
  action := 7
  target := Controls.pure (X := naturals) 10
  valid := operational_prefix_readout

noncomputable def secondEvent : Event law worlds variableSteps (Fin 2) () world where
  origin := 1
  source := prefixed 7 (Controls.pure (X := naturals) 10)
  action := 7
  target := Controls.pure (X := naturals) 10
  valid := operational_prefix_readout

noncomputable abbrev span := eventSpan law worlds variableSteps (Fin 2) ()

def suppliedWitness : targetFamily.obj ⟨world, Controls.pure (X := naturals) 10⟩ := ⟨11, by decide⟩

noncomputable def firstReceipt : (span.certificates targetFamily).obj ⟨world, firstEvent.source⟩ :=
  span.introduce targetFamily world firstEvent suppliedWitness

noncomputable def secondReceipt : (span.certificates targetFamily).obj ⟨world, firstEvent.source⟩ :=
  span.introduce targetFamily world secondEvent suppliedWitness

/-- Universal native elimination reads the exact supplied operational occurrence. -/
theorem first_origin_retained :
    ((span.eventReadout targetFamily).app world ⟨firstEvent.source, firstReceipt⟩).origin = 0 := rfl

theorem second_origin_retained :
    ((span.eventReadout targetFamily).app world ⟨firstEvent.source, secondReceipt⟩).origin = 1 := rfl

/-- The actual result readout retains the complete dependent finite witness. -/
theorem complete_target_witness_retained :
    (span.resultReadout targetFamily).app world ⟨firstEvent.source, firstReceipt⟩ =
      ⟨Controls.pure (X := naturals) 10, suppliedWitness⟩ := rfl

theorem receipts_differ : firstReceipt ≠ secondReceipt := by
  intro same
  have read := congrArg (fun receipt =>
    ((span.eventReadout targetFamily).app world ⟨firstEvent.source, receipt⟩).origin) same
  exact Fin.zero_ne_one read

theorem scalar_readouts_agree :
    ((span.resultReadout targetFamily).app world ⟨firstEvent.source, firstReceipt⟩).2.val =
      ((span.resultReadout targetFamily).app world ⟨firstEvent.source, secondReceipt⟩).2.val := rfl

/-- Erasing occurrence origin cannot recover both complete native receipts. -/
theorem no_origin_recovery :
    ¬ ∃ recover : Nat → (span.certificates targetFamily).obj ⟨world, firstEvent.source⟩,
      recover 11 = firstReceipt ∧ recover 11 = secondReceipt := by
  rintro ⟨recover, first, second⟩
  exact receipts_differ (first.symm.trans second)

/-- The target family's actual bound changes under a different supplied target. -/
theorem witness_bounds_vary :
    weight (Controls.pure (X := naturals) 10) + 2 ≠ weight (Controls.pure (X := naturals) 20) + 2 := by decide

noncomputable abbrev premiseChildren :
    ∀ position : signature.Position (sort := ()) (Operator.prefix 9),
      signature.Term (worlds.obj world) (signature.argument (sort := ()) (Operator.prefix 9) position) :=
  fun _ => firstEvent.source

/-- Complete availability is supplied separately from the selected premise. -/
noncomputable def premiseGuard : Guard actions (sort := ()) (Operator.prefix 9) :=
  inputGuard actions (fun position =>
    (premiseChildren position,
      Operational.coalgebra law (variableSteps.app world) PUnit.unit _ (premiseChildren position)))

noncomputable def continuation :
    signature.Term (ruleVariables actions (sort := ()) (Operator.prefix 9) premiseGuard) () :=
  Controls.pure (.original ())

/-- The independent rule parser selects the original supplied child. -/
theorem continuation_rule_read :
    fromLaw actions law () (Operator.prefix 9) premiseGuard 9 = some continuation := by
  rw [show fromLaw actions law = rules from fromLaw_toLaw actions rules]
  simp only [rules]
  rfl

/-- A literal source-fibre rule application retains the selected actual
child edge, separately checked full availability and a new conclusion origin. -/
noncomputable def constructorOccurrence :
    FibreOccurrence law worlds variableSteps (Fin 2) (Fin 2) world
      (sort := ()) (Operator.prefix 9) premiseChildren :=
  guardedSourceFibre law worlds variableSteps 1 world (Operator.prefix 9) premiseChildren
    (fun _ => ⟨firstEvent, rfl⟩) premiseGuard 9 continuation rfl continuation_rule_read

theorem selected_premise_origin_retained :
    (constructorOccurrence.premises ()).val.origin = 0 := rfl

theorem guarded_constructor_origin_retained : constructorOccurrence.result.val.origin = 1 := rfl

theorem selected_premise_in_full_guard : premiseGuard ⟨(), 7⟩ = true :=
  selected_premise_available law worlds variableSteps world (Operator.prefix 9) premiseChildren
    (fun _ => ⟨firstEvent, rfl⟩) premiseGuard rfl ()

/-- The derived edge's complete target is the actual supplied child process. -/
theorem guarded_constructor_target_readout :
    constructorOccurrence.result.val.target = prefixed 7 (Controls.pure (X := naturals) 10) := by
  change IndexedPolynomial.Free.join signature.polynomial
    (signature.rename _ continuation) = firstEvent.source
  unfold continuation Controls.pure Signature.rename
  rw [IndexedPolynomial.Free.map_pure, IndexedPolynomial.Free.join_pure]
  rfl

end Mettapedia.OSLF.DeterministicGSOS.EdgeControls
