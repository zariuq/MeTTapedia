import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeIterated

/-!
# Every order of a clear family agrees up to dead names, through the cube

`Step/NativeIterated` shows that every order of a clear family of live firings is a sequential run.
This module shows that all of them end in states that agree up to dead names.

## Carrying firings

A live firing is carried along a map of rule frames and a map of information frames
(`carryAlong`); residuals (`residualAt_eq`) and carryings along inclusions (`firing_eq`) are such
carryings, and carryings compose (`carryAlong_comp`).

## Residuals are carried from the core

The **core residual** (`coreResidual`) reads a firing at the core of another's step: rule locals and
state names as they are, the opened rule locals relocated by the scopes the step reserves. It
mentions no solver return.

* **The residual is the core residual, carried** (`coreResidual_carried`): along the published
  result's dead-name extension of the core, for every solver return.
* **Core residuals are natural** (`coreResidual_coreCarried`): along every dead-name extension, the
  core residual of the carried firings is the carried core residual.

So **sequential runs move along dead-name extensions** (`sequential_along`): a word runs at a state
exactly when its carrying runs at a dead-name extension, and the two final states agree up to dead
names.

## The cube

The **joint residual** (`jointResidual`) reads a third firing at the joint state of a clear diamond
(`NativeDead.jointState`). **Its carryings along the joint state's two inclusions are the two
residuals of residuals** (`cube`): `(k / g) / (f / g)` along the first and `(k / f) / (g / f)` along the
second. This is the cube condition: the two orders of the diamond are not just related; everything
read after them is read from one firing at the joint state.

## Every order agrees

* **Swapping two adjacent firings** keeps the final state up to dead names (`swap_agree`).
* **Bubbling a firing to the front** does too (`bubble`).
* **Every order of a clear family agrees** with every other (`orders_agree`), so all of them agree
  with the run of the family as given (`every_order_agrees`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open NativeResidual NativeDead

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeIterated

/-! ## Carrying firings along maps of frames -/

section Carrying

variable {s u w : NativeState S O Γ sort}

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem liveFiring_ext {f g : LiveFiring s} (rule : f.rule = g.rule) (selection : f.selection = g.selection)
    (outputs : f.outputs = g.outputs) (patterns : f.patterns = g.patterns) (fuel : f.fuel = g.fuel) : f = g := by
  obtain ⟨_, _, _, _, _⟩ := f
  obtain ⟨_, _, _, _, _⟩ := g
  dsimp only at rule selection outputs patterns fuel
  subst rule selection outputs patterns fuel
  rfl

/-- **A live firing carried** along a map of rule frames and a map of information frames. -/
def carryAlong
    (φ : Assignment (ContextualActivatedStep.source s.locals s.state.declarations)
      (ContextualActivatedStep.source u.locals u.state.declarations))
    (ψ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations)
      (ContextualActivatedStep.target u.locals u.state.declarations)) (f : LiveFiring s) : LiveFiring u where
  rule := f.rule.map (instantiate φ)
  selection := f.selection
  outputs o := instantiate ψ (f.outputs o)
  patterns := f.patterns.map fun pattern => (instantiate ψ pattern.1, pattern.2)
  fuel := f.fuel

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Carryings compose.** -/
theorem carryAlong_comp
    (φ : Assignment (ContextualActivatedStep.source s.locals s.state.declarations)
      (ContextualActivatedStep.source u.locals u.state.declarations))
    (ψ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations)
      (ContextualActivatedStep.target u.locals u.state.declarations))
    (φ' : Assignment (ContextualActivatedStep.source u.locals u.state.declarations)
      (ContextualActivatedStep.source w.locals w.state.declarations))
    (ψ' : Assignment (ContextualActivatedStep.target u.locals u.state.declarations)
      (ContextualActivatedStep.target w.locals w.state.declarations)) (f : LiveFiring s) :
    carryAlong φ' ψ' (carryAlong φ ψ f) = carryAlong (Assignment.compose φ' φ) (Assignment.compose ψ' ψ) f := by
  refine liveFiring_ext ?_ rfl (funext fun o => (Assignment.instantiate_compose ψ' ψ (f.outputs o)).symm) ?_ rfl
  · show (f.rule.map (instantiate φ)).map (instantiate φ') = f.rule.map (instantiate (Assignment.compose φ' φ))
    rw [OccurrenceRelabeling.rule_map_comp]
    exact congrArg (fun mapping => f.rule.map mapping)
      (funext fun term => (Assignment.instantiate_compose φ' φ term).symm)
  · show (f.patterns.map fun pattern => (instantiate ψ pattern.1, pattern.2)).map
        (fun pattern => (instantiate ψ' pattern.1, pattern.2)) =
      f.patterns.map fun pattern => (instantiate (Assignment.compose ψ' ψ) pattern.1, pattern.2)
    rw [List.map_map]
    exact List.map_congr_left fun pattern _ =>
      congrArg (fun term => (term, pattern.2)) (Assignment.instantiate_compose ψ' ψ pattern.1).symm

/-- The rule frame carried to an execution's published result, typed at its native state. -/
def sourceCarryAt (G : ContextualConditionalExecution.Firing s.locals s.state) :
    Assignment (ContextualActivatedStep.source s.locals s.state.declarations)
      (ContextualActivatedStep.source (rawTarget G).locals (rawTarget G).state.declarations) :=
  sourceCarry G

/-- The information frame carried to an execution's published result, typed at its native state. -/
def carryAt (G : ContextualConditionalExecution.Firing s.locals s.state) :
    Assignment (ContextualActivatedStep.target s.locals s.state.declarations)
      (ContextualActivatedStep.target (rawTarget G).locals (rawTarget G).state.declarations) :=
  carry G

theorem residualAt_eq (G : ContextualConditionalExecution.Firing s.locals s.state) (f : LiveFiring s) :
    f.residualAt G = carryAlong (sourceCarryAt G) (carryAt G) f :=
  rfl

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem firing_eq (e : Inclusion s u) (f : LiveFiring s) : e.firing f = carryAlong e.source e.target f :=
  rfl

end Carrying

/-! ## Residuals are carried from the core -/

section Core

variable {s u : NativeState S O Γ sort}

/-- How far the scopes of a later activation lie beyond the state's, after a selection's step. -/
abbrev coreShift (s : NativeState S O Γ sort) (selection : Selection O) : ℕ :=
  ContextualActivationScopes.start (ContextualFreshFrameScopeLedger.helperLedger
    (ContextualActivationScopes.after s.state.occupied selection)) -
    ContextualActivationScopes.start s.state.occupied

/-- The rule frame, read at a core: rule locals and state names as they are. -/
def coreSourceOf (s : NativeState S O Γ sort) :
    Assignment (ContextualActivatedStep.source s.locals s.state.declarations)
      (ContextualActivatedStep.source s.locals (ContextualActivatedStep.target s.locals s.state.declarations))
  | .inl name => generator (ContextualActivatedStep.source s.locals
      (ContextualActivatedStep.target s.locals s.state.declarations)) (.inl name)
  | .inr name => generator (ContextualActivatedStep.source s.locals
      (ContextualActivatedStep.target s.locals s.state.declarations)) (.inr (.inr name))

/-- The information frame, read at a core: opened rule locals relocated by `shift` scopes, state
names as they are. -/
def coreCarryAt (s : NativeState S O Γ sort) (shift : ℕ) :
    Assignment (ContextualActivatedStep.target s.locals s.state.declarations)
      (ContextualActivatedStep.target s.locals (ContextualActivatedStep.target s.locals s.state.declarations))
  | .inl name => generator (ContextualActivatedStep.target s.locals
      (ContextualActivatedStep.target s.locals s.state.declarations)) (.inl (ScopedVar.at (name.scope + shift) name.name))
  | .inr name => generator (ContextualActivatedStep.target s.locals
      (ContextualActivatedStep.target s.locals s.state.declarations)) (.inr (.inr name))

/-- The rule frame of a core: rule locals and state names as they are. -/
def coreSource (k : LiveFiring s) :
    Assignment (ContextualActivatedStep.source s.locals s.state.declarations)
      (ContextualActivatedStep.source (core k).locals (core k).state.declarations) :=
  coreSourceOf s

/-- The information frame of a core: opened rule locals relocated by the scopes the step reserves. -/
def coreCarry (k : LiveFiring s) :
    Assignment (ContextualActivatedStep.target s.locals s.state.declarations)
      (ContextualActivatedStep.target (core k).locals (core k).state.declarations) :=
  coreCarryAt s (coreShift s k.selection)

/-- **The core residual**: a live firing read at the core of another's step. -/
def coreResidual (k h : LiveFiring s) : LiveFiring (core k) :=
  carryAlong (coreSource k) (coreCarry k) h

theorem coreInclusion_source (G : ContextualConditionalExecution.Firing s.locals s.state) (k : LiveFiring s) :
    Assignment.compose (coreInclusion G k).source (coreSource k) = sourceCarry G := by
  funext name
  cases name with
  | inl name => exact instantiate_generator _ _
  | inr name => exact instantiate_generator _ _

theorem coreInclusion_target (G : ContextualConditionalExecution.Firing s.locals s.state) (k : LiveFiring s)
    (selection : G.selection = k.selection) :
    Assignment.compose (coreInclusion G k).target (coreCarry k) = carry G := by
  have shifted : coreShift s k.selection = shift G := by
    show _ = ContextualActivationScopes.start (ContextualFreshFrameScopeLedger.helperLedger
        (ContextualActivationScopes.after s.state.occupied G.selection)) - _
    rw [selection]
  have carried : coreCarry k = coreCarryAt s (shift G) := congrArg (coreCarryAt s) shifted
  rw [carried]
  funext name
  cases name with
  | inl name => exact instantiate_generator _ _
  | inr name => exact instantiate_generator _ _

/-- **The residual is the core residual, carried** along the published result's dead-name
extension of the core. Any solver return. -/
theorem coreResidual_carried (k : LiveFiring s) (admitted : k.toNative.Realized) (h : LiveFiring s) :
    (result_core k admitted).firing (coreResidual k h) = residualAfter admitted h := by
  show carryAlong (coreInclusion (LiveFiring.execution admitted) k).source
      (coreInclusion (LiveFiring.execution admitted) k).target (carryAlong (coreSource k) (coreCarry k) h) =
    carryAlong (u := rawTarget (LiveFiring.execution admitted)) (sourceCarry (LiveFiring.execution admitted))
      (carry (LiveFiring.execution admitted)) h
  rw [carryAlong_comp, coreInclusion_source,
    coreInclusion_target _ _ (LiveFiring.execution_data admitted).2.1]

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem coreCarried_source (e : DeadExtension s u) (k : LiveFiring s) :
    Assignment.compose (coreCarriedInclusion e k).source (coreSource k) =
      Assignment.compose (coreSource (e.firing k)) e.source := by
  funext name
  cases name with
  | inl name =>
      exact (instantiate_generator _ _).trans
        (instantiate_reindex (Sum.map e.locals e.names) e.source_preserves (coreSource (e.firing k)) (.inl name)).symm
  | inr name =>
      exact (instantiate_generator _ _).trans
        (instantiate_reindex (Sum.map e.locals e.names) e.source_preserves (coreSource (e.firing k)) (.inr name)).symm

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem coreCarried_target (e : DeadExtension s u) (k : LiveFiring s) :
    Assignment.compose (coreCarriedInclusion e k).target (coreCarry k) =
      Assignment.compose (coreCarry (e.firing k)) e.target := by
  have shifted : coreShift u (e.firing k).selection = coreShift s k.selection := by
    show ContextualActivationScopes.start (ContextualFreshFrameScopeLedger.helperLedger
        (ContextualActivationScopes.after u.state.occupied k.selection)) - ContextualActivationScopes.start u.state.occupied = _
    rw [e.occupied]
  have carried : coreCarry (e.firing k) = coreCarryAt u (coreShift s k.selection) :=
    congrArg (coreCarryAt u) shifted
  rw [carried]
  funext name
  cases name with
  | inl name =>
      exact (instantiate_generator _ _).trans
        (instantiate_reindex (Sum.map e.scopedName e.names) e.target_preserves
          (coreCarryAt u (coreShift s k.selection)) (.inl name)).symm
  | inr name =>
      exact (instantiate_generator _ _).trans
        (instantiate_reindex (Sum.map e.scopedName e.names) e.target_preserves
          (coreCarryAt u (coreShift s k.selection)) (.inr name)).symm

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Core residuals are natural**: along every dead-name extension, the core residual of the
carried firings is the carried core residual. -/
theorem coreResidual_coreCarried (e : DeadExtension s u) (k h : LiveFiring s) :
    (coreCarried e k).firing (coreResidual k h) = coreResidual (e.firing k) (e.firing h) := by
  show carryAlong (coreCarriedInclusion e k).source (coreCarriedInclusion e k).target
      (carryAlong (coreSource k) (coreCarry k) h) =
    carryAlong (coreSource (e.firing k)) (coreCarry (e.firing k)) (carryAlong e.source e.target h)
  rw [carryAlong_comp, carryAlong_comp, coreCarried_source, coreCarried_target]

end Core

/-! ## Sequential runs move along dead-name extensions -/

section Along

/-- **Sequential runs move along dead-name extensions**: a word runs at a state exactly when its
carrying runs at a dead-name extension, and the final states agree up to dead names. -/
theorem sequential_along : ∀ (n : ℕ) {s u : NativeState S O Γ sort} (e : DeadExtension s u)
    (l : List (LiveFiring s)), l.length = n →
    (∀ {t : NativeState S O Γ sort}, Sequential s l t →
        ∃ t', Sequential u (l.map e.firing) t' ∧ DeadEquiv t t') ∧
      ∀ {t' : NativeState S O Γ sort}, Sequential u (l.map e.firing) t' →
        ∃ t, Sequential s l t ∧ DeadEquiv t t'
  | _, s, u, e, [], _ =>
      ⟨fun {t} run => ⟨u, .nil u, by rw [sequential_nil_iff.mp run]; exact DeadEquiv.of_extension e⟩,
        fun {t'} run => ⟨s, .nil s, by rw [sequential_nil_iff.mp run]; exact DeadEquiv.of_extension e⟩⟩
  | 0, _, _, _, _ :: _, length => absurd length (by simp)
  | n + 1, s, u, e, k :: rest, length => by
      have short : rest.length = n := Nat.succ.inj length
      have lengthCore : (rest.map (coreResidual k)).length = n := by rw [List.length_map]; exact short
      have lengthCarried : ((rest.map (coreResidual k)).map (coreCarried e k).firing).length = n := by
        rw [List.length_map, List.length_map]; exact short
      have here : ∀ admitted : k.toNative.Realized,
          rest.map (residualAfter admitted) = (rest.map (coreResidual k)).map (result_core k admitted).firing := by
        intro admitted
        rw [List.map_map]
        exact List.map_congr_left fun h _ => (coreResidual_carried k admitted h).symm
      have there : ∀ admitted : (e.firing k).toNative.Realized,
          (rest.map e.firing).map (residualAfter admitted) =
            ((rest.map (coreResidual k)).map (coreCarried e k).firing).map
              (result_core (e.firing k) admitted).firing := by
        intro admitted
        rw [List.map_map, List.map_map, List.map_map]
        refine List.map_congr_left fun h _ => ?_
        show residualAfter admitted (e.firing h) =
          (result_core (e.firing k) admitted).firing ((coreCarried e k).firing (coreResidual k h))
        rw [coreResidual_coreCarried, coreResidual_carried]
      refine ⟨fun {t} run => ?_, fun {t'} run => ?_⟩
      · obtain ⟨admitted, later⟩ := sequential_cons_iff.mp run
        have admitted' := (e.admits_iff k).mp admitted
        rw [here admitted] at later
        obtain ⟨t₀, atCore, first⟩ := (sequential_along n (result_core k admitted) _ lengthCore).2 later
        obtain ⟨t₁, atCarried, second⟩ := (sequential_along n (coreCarried e k) _ lengthCore).1 atCore
        obtain ⟨t', atResult, third⟩ :=
          (sequential_along n (result_core (e.firing k) admitted') _ lengthCarried).1 atCarried
        rw [← there admitted'] at atResult
        exact ⟨t', .cons (e.firing k) (rest.map e.firing) admitted' atResult, first.symm.trans (second.trans third)⟩
      · obtain ⟨admitted', later⟩ := sequential_cons_iff.mp run
        have admitted := (e.admits_iff k).mpr admitted'
        rw [there admitted'] at later
        obtain ⟨t₁, atCarried, third⟩ :=
          (sequential_along n (result_core (e.firing k) admitted') _ lengthCarried).2 later
        obtain ⟨t₀, atCore, second⟩ := (sequential_along n (coreCarried e k) _ lengthCore).2 atCarried
        obtain ⟨t, atResult, first⟩ := (sequential_along n (result_core k admitted) _ lengthCore).1 atCore
        rw [← here admitted] at atResult
        exact ⟨t, .cons k rest admitted atResult, first.symm.trans (second.trans third)⟩

end Along

/-! ## The cube -/

section Cube

variable {s : NativeState S O Γ sort} {f g : LiveFiring s}

/-- The rule frame of a joint state: rule locals as they are, state names in the shared copy. -/
def jointSourceOf (s : NativeState S O Γ sort) :
    Assignment (ContextualActivatedStep.source s.locals s.state.declarations)
      (ContextualActivatedStep.source s.locals (NativeClosing.jointFrame s))
  | .inl name => generator (ContextualActivatedStep.source s.locals (NativeClosing.jointFrame s)) (.inl name)
  | .inr name => generator (ContextualActivatedStep.source s.locals (NativeClosing.jointFrame s)) (.inr (.inr (.inr name)))

/-- The information frame of a joint state: opened rule locals relocated by `shift` scopes, state
names in the shared copy. -/
def jointCarryAt (s : NativeState S O Γ sort) (shift : ℕ) :
    Assignment (ContextualActivatedStep.target s.locals s.state.declarations)
      (ContextualActivatedStep.target s.locals (NativeClosing.jointFrame s))
  | .inl name => generator (ContextualActivatedStep.target s.locals (NativeClosing.jointFrame s))
      (.inl (ScopedVar.at (name.scope + shift) name.name))
  | .inr name => generator (ContextualActivatedStep.target s.locals (NativeClosing.jointFrame s)) (.inr (.inr (.inr name)))

/-- The scopes both firings of a diamond reserve. -/
noncomputable abbrev jointShift (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) : ℕ :=
  ContextualActivationScopes.start (jointState first second clearF).state.occupied -
    ContextualActivationScopes.start s.state.occupied

/-- The rule frame of the joint state. -/
noncomputable def jointSource (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) :
    Assignment (ContextualActivatedStep.source s.locals s.state.declarations)
      (ContextualActivatedStep.source (jointState first second clearF).locals
        (jointState first second clearF).state.declarations) :=
  jointSourceOf s

/-- The information frame of the joint state. -/
noncomputable def jointCarry (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) :
    Assignment (ContextualActivatedStep.target s.locals s.state.declarations)
      (ContextualActivatedStep.target (jointState first second clearF).locals
        (jointState first second clearF).state.declarations) :=
  jointCarryAt s (jointShift first second clearF)

/-- **The joint residual**: a third firing read at the joint state of a clear diamond. -/
noncomputable def jointResidual (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (k : LiveFiring s) : LiveFiring (jointState first second clearF) :=
  carryAlong (jointSource first second clearF) (jointCarry first second clearF) k

theorem jointShift_first (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) :
    jointShift first second clearF =
      shift (LiveFiring.execution second) + shift (LiveFiring.residualExecution first second clearF) := by
  have one := start_le (LiveFiring.execution second)
  have two := start_le (LiveFiring.residualExecution first second clearF)
  have link : ContextualActivationScopes.start (rawTarget (LiveFiring.execution second)).state.occupied =
      ContextualActivationScopes.start (LiveFiring.execution second).target.occupied := rfl
  have link₂ : ContextualActivationScopes.start (jointState first second clearF).state.occupied =
      ContextualActivationScopes.start (LiveFiring.residualExecution first second clearF).target.occupied := rfl
  unfold jointShift shift
  omega

theorem jointShift_second (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    jointShift first second clearF =
      shift (LiveFiring.execution first) + shift (LiveFiring.residualExecution second first clearG) := by
  have one := start_le (LiveFiring.execution first)
  have two := start_le (LiveFiring.residualExecution second first clearG)
  have link : ContextualActivationScopes.start (rawTarget (LiveFiring.execution first)).state.occupied =
      ContextualActivationScopes.start (LiveFiring.execution first).target.occupied := rfl
  have link₂ : ContextualActivationScopes.start (jointState first second clearF).state.occupied =
      ContextualActivationScopes.start (LiveFiring.residualExecution second first clearG).target.occupied :=
    congrArg ContextualActivationScopes.start (LiveFiring.closing_occupied first second clearF clearG)
  unfold jointShift shift
  omega

theorem firstInclusion_source (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) :
    Assignment.compose (firstInclusion first second clearF).source (jointSource first second clearF) =
      Assignment.compose (sourceCarryAt (LiveFiring.residualExecution first second clearF))
        (sourceCarryAt (LiveFiring.execution second)) := by
  funext name
  cases name with
  | inl name =>
      exact (instantiate_generator _ _).trans
        (instantiate_generator (sourceCarry (LiveFiring.residualExecution first second clearF)) (.inl (.inl name))).symm
  | inr name =>
      exact (instantiate_generator _ _).trans
        (instantiate_generator (sourceCarry (LiveFiring.residualExecution first second clearF))
          (.inr (.inl (.inr name)))).symm

theorem firstInclusion_target (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) :
    Assignment.compose (firstInclusion first second clearF).target (jointCarry first second clearF) =
      Assignment.compose (carryAt (LiveFiring.residualExecution first second clearF))
        (carryAt (LiveFiring.execution second)) := by
  have carried : jointCarry first second clearF =
      jointCarryAt s (shift (LiveFiring.execution second) + shift (LiveFiring.residualExecution first second clearF)) :=
    congrArg (jointCarryAt s) (jointShift_first first second clearF)
  rw [carried]
  funext name
  cases name with
  | inl name =>
      refine (instantiate_generator _ _).trans (Eq.trans ?_
        (instantiate_generator (carry (LiveFiring.residualExecution first second clearF))
          (.inl (ScopedVar.at (name.scope + shift (LiveFiring.execution second)) (.inl name.name)))).symm)
      rw [← Nat.add_assoc]
      rfl
  | inr name =>
      exact (instantiate_generator _ _).trans
        (instantiate_generator (carry (LiveFiring.residualExecution first second clearF))
          (.inr (.inl (.inr name)))).symm

theorem secondInclusion_source (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    Assignment.compose (secondInclusion first second clearF clearG).source (jointSource first second clearF) =
      Assignment.compose (sourceCarryAt (LiveFiring.residualExecution second first clearG))
        (sourceCarryAt (LiveFiring.execution first)) := by
  funext name
  cases name with
  | inl name =>
      exact (instantiate_generator _ _).trans
        (instantiate_generator (sourceCarry (LiveFiring.residualExecution second first clearG)) (.inl (.inl name))).symm
  | inr name =>
      exact (instantiate_generator _ _).trans
        (instantiate_generator (sourceCarry (LiveFiring.residualExecution second first clearG))
          (.inr (.inl (.inr name)))).symm

theorem secondInclusion_target (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    Assignment.compose (secondInclusion first second clearF clearG).target (jointCarry first second clearF) =
      Assignment.compose (carryAt (LiveFiring.residualExecution second first clearG))
        (carryAt (LiveFiring.execution first)) := by
  have carried : jointCarry first second clearF =
      jointCarryAt s (shift (LiveFiring.execution first) + shift (LiveFiring.residualExecution second first clearG)) :=
    congrArg (jointCarryAt s) (jointShift_second first second clearF clearG)
  rw [carried]
  funext name
  cases name with
  | inl name =>
      refine (instantiate_generator _ _).trans (Eq.trans ?_
        (instantiate_generator (carry (LiveFiring.residualExecution second first clearG))
          (.inl (ScopedVar.at (name.scope + shift (LiveFiring.execution first)) (.inl name.name)))).symm)
      rw [← Nat.add_assoc]
      rfl
  | inr name =>
      exact (instantiate_generator _ _).trans
        (instantiate_generator (carry (LiveFiring.residualExecution second first clearG))
          (.inr (.inl (.inr name)))).symm

/-- **The cube.** A third live firing read at the joint state of a clear diamond is carried, along
the joint state's first inclusion, to its residual after `g` and then `f / g`, and along the second
inclusion to its residual after `f` and then `g / f`. Any solver returns. -/
theorem cube (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs)
    (k : LiveFiring s) :
    (joint_first first second clearF clearG).firing (jointResidual first second clearF k) =
        residualAfter (LiveFiring.after first second clearF) (residualAfter second k) ∧
      (joint_second first second clearF clearG).firing (jointResidual first second clearF k) =
        residualAfter (LiveFiring.after second first clearG) (residualAfter first k) := by
  constructor
  · show carryAlong (firstInclusion first second clearF).source (firstInclusion first second clearF).target
        (carryAlong (jointSource first second clearF) (jointCarry first second clearF) k) =
      carryAlong (sourceCarryAt (LiveFiring.residualExecution first second clearF))
        (carryAt (LiveFiring.residualExecution first second clearF))
        (carryAlong (sourceCarryAt (LiveFiring.execution second)) (carryAt (LiveFiring.execution second)) k)
    rw [carryAlong_comp, carryAlong_comp, firstInclusion_source, firstInclusion_target]
  · show carryAlong (secondInclusion first second clearF clearG).source
        (secondInclusion first second clearF clearG).target
        (carryAlong (jointSource first second clearF) (jointCarry first second clearF) k) =
      carryAlong (sourceCarryAt (LiveFiring.residualExecution second first clearG))
        (carryAt (LiveFiring.residualExecution second first clearG))
        (carryAlong (sourceCarryAt (LiveFiring.execution first)) (carryAt (LiveFiring.execution first)) k)
    rw [carryAlong_comp, carryAlong_comp, secondInclusion_source, secondInclusion_target]

end Cube

/-! ## Every order agrees -/

section Orders

variable {s : NativeState S O Γ sort}

/-- **Swapping two adjacent firings keeps the final state, up to dead names.** -/
theorem swap_agree {a b : LiveFiring s} {r : List (LiveFiring s)} (clears : Clears a b)
    {t t' : NativeState S O Γ sort} (first : Sequential s (b :: a :: r) t) (second : Sequential s (a :: b :: r) t') :
    DeadEquiv t t' := by
  obtain ⟨ab, firstLater⟩ := sequential_cons_iff.mp first
  obtain ⟨aab, firstRest⟩ := sequential_cons_iff.mp firstLater
  obtain ⟨aa, secondLater⟩ := sequential_cons_iff.mp second
  obtain ⟨aba, secondRest⟩ := sequential_cons_iff.mp secondLater
  have listFirst : (r.map (residualAfter ab)).map (residualAfter aab) =
      (r.map (jointResidual aa ab clears.1)).map (joint_first aa ab clears.1 clears.2).firing := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun k _ => (cube aa ab clears.1 clears.2 k).1.symm
  have listSecond : (r.map (residualAfter aa)).map (residualAfter aba) =
      (r.map (jointResidual aa ab clears.1)).map (joint_second aa ab clears.1 clears.2).firing := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun k _ => (cube aa ab clears.1 clears.2 k).2.symm
  rw [listFirst] at firstRest
  rw [listSecond] at secondRest
  have lengthJ : (r.map (jointResidual aa ab clears.1)).length = r.length := List.length_map _
  obtain ⟨t₀, atJoint, toFirst⟩ :=
    (sequential_along _ (joint_first aa ab clears.1 clears.2) _ lengthJ).2 firstRest
  obtain ⟨t₂, atSecond, toSecond⟩ :=
    (sequential_along _ (joint_second aa ab clears.1 clears.2) _ lengthJ).1 atJoint
  rw [atSecond.unique secondRest] at toSecond
  exact toFirst.symm.trans toSecond

/-- **Bubbling a firing to the front keeps the final state, up to dead names.** -/
theorem bubble : ∀ (n : ℕ) {s : NativeState S O Γ sort} (p : List (LiveFiring s)) (a : LiveFiring s)
    (q : List (LiveFiring s)), p.length = n → FamilyClear s (p ++ a :: q) →
    ∀ {t t' : NativeState S O Γ sort}, Sequential s (p ++ a :: q) t → Sequential s (a :: (p ++ q)) t' →
      DeadEquiv t t'
  | _, _, [], _, _, _, _, t, _, first, second => by
      rw [first.unique second]
      exact DeadEquiv.refl _
  | 0, _, _ :: _, _, _, length, _, _, _, _, _ => absurd length (by simp)
  | n + 1, s, b :: p, a, q, length, clear, t, t', first, second => by
      rw [List.cons_append] at first clear second
      obtain ⟨ab, later⟩ := sequential_cons_iff.mp first
      have clearAfter := familyClear_residual clear ab
      rw [List.map_append, List.map_cons] at later clearAfter
      obtain ⟨t₁, bubbled⟩ := every_order_admitted clearAfter List.perm_middle.symm
      have agree₁ := bubble n (p.map (residualAfter ab)) (residualAfter ab a) (q.map (residualAfter ab))
        (by rw [List.length_map]; exact Nat.succ.inj length) clearAfter later bubbled
      have run : Sequential s (b :: a :: (p ++ q)) t₁ := by
        refine .cons b _ ab ?_
        rw [List.map_cons, List.map_append]
        exact bubbled
      have clears : Clears a b :=
        ((List.pairwise_cons.mp clear.pairwise).1 a (List.mem_append_right _ List.mem_cons_self)).symm
      exact agree₁.trans (swap_agree clears run second)

/-- **Every two orders of a clear family agree up to dead names.** -/
theorem orders_agree : ∀ (n : ℕ) {s : NativeState S O Γ sort} (l : List (LiveFiring s)), l.length = n →
    FamilyClear s l → ∀ {order : List (LiveFiring s)}, order.Perm l →
      ∀ {t t' : NativeState S O Γ sort}, Sequential s l t → Sequential s order t' → DeadEquiv t t'
  | _, _, [], _, _, order, perm, t, t', first, second => by
      have empty : order = [] := perm.eq_nil
      subst empty
      rw [sequential_nil_iff.mp first, sequential_nil_iff.mp second]
      exact DeadEquiv.refl _
  | 0, _, _ :: _, length, _, _, _, _, _, _, _ => absurd length (by simp)
  | n + 1, s, a :: rest, length, clear, order, perm, t, t', first, second => by
      obtain ⟨p, q, rfl⟩ := List.append_of_mem (perm.symm.subset List.mem_cons_self)
      have toFront : (a :: (p ++ q)).Perm (a :: rest) := List.perm_middle.symm.trans perm
      obtain ⟨t₁, middle⟩ := every_order_admitted clear toFront
      have agree₁ := bubble _ p a q rfl (clear.perm perm) second middle
      obtain ⟨admitted, firstLater⟩ := sequential_cons_iff.mp first
      obtain ⟨_, middleLater⟩ := sequential_cons_iff.mp middle
      have agree₂ := orders_agree n (rest.map (residualAfter admitted))
        (by rw [List.length_map]; exact Nat.succ.inj length) (familyClear_residual clear admitted)
        (((List.perm_cons a).mp toFront).map _) firstLater middleLater
      exact agree₂.trans agree₁.symm

/-- **Every order of a clear family is admitted and agrees, up to dead names, with the run of the
family as given.** -/
theorem every_order_agrees {fs : List (LiveFiring s)} (clear : FamilyClear s fs) :
    ∃ t₀, Sequential s fs t₀ ∧ ∀ order : List (LiveFiring s), order.Perm fs →
      ∃ t, Sequential s order t ∧ DeadEquiv t₀ t := by
  obtain ⟨t₀, run⟩ := every_order_admitted clear (List.Perm.refl fs)
  refine ⟨t₀, run, fun order perm => ?_⟩
  obtain ⟨t, other⟩ := every_order_admitted clear perm
  exact ⟨t, other, orders_agree _ fs rfl clear perm run other⟩

end Orders

end NativeIterated

#print axioms NativeIterated.carryAlong_comp
#print axioms NativeIterated.coreResidual_carried
#print axioms NativeIterated.coreResidual_coreCarried
#print axioms NativeIterated.sequential_along
#print axioms NativeIterated.cube
#print axioms NativeIterated.swap_agree
#print axioms NativeIterated.bubble
#print axioms NativeIterated.orders_agree
#print axioms NativeIterated.every_order_agrees

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
