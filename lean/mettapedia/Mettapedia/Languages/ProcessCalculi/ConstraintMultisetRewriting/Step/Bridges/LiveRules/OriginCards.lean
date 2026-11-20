import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.RunFibres
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Counting

/-!
# Finite held-origin counts and the ambient-overlap control

With no ambient program, the available origins above a fixed base firing are
exactly the held identities carrying its rule. With an ambient occurrence as
well, that origin is additional. The latter is why both conditions of `Once`
are necessary for the event bijection that forgets origins.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Origins

open RuleSyntax RuleSyntax.RuleOccurrences

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {R : Type uR} {Z : Type uZ}
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom) {Q : Program Tm}
  {ids : Finset R} {code : R → Rule Tm} (zone : R → Z)

def heldUsesEquiv (state : State Tm O)
    (firing : (baseEvents X E (P := ∅) (Q := Q)).Choice state) :
    Uses X E (P := ∅) (ids := ids) (code := code) zone state firing ≃
      {identity : R // identity ∈ ids ∧ code identity = firing.val.rule} where
  toFun origin := by
    obtain ⟨use, available, aligned⟩ := origin
    cases use with
    | ambient rule => exact False.elim (Set.notMem_empty rule available)
    | held identity => exact ⟨identity, available, aligned⟩
  invFun origin := ⟨.held origin.val, origin.property.1, origin.property.2⟩
  left_inv origin := by
    obtain ⟨use, available, aligned⟩ := origin
    cases use with
    | ambient rule => exact False.elim (Set.notMem_empty rule available)
    | held identity => rfl
  right_inv origin := by cases origin; rfl

theorem held_uses_card (state : State Tm O)
    (firing : (baseEvents X E (P := ∅) (Q := Q)).Choice state) :
    Nat.card (Uses X E (P := ∅) (ids := ids) (code := code) zone state firing) =
      Nat.card {identity : R // identity ∈ ids ∧ code identity = firing.val.rule} :=
  Nat.card_congr (heldUsesEquiv X E zone state firing)

theorem held_uses_finite (state : State Tm O)
    (firing : (baseEvents X E (P := ∅) (Q := Q)).Choice state) :
    Finite (Uses X E (P := ∅) (ids := ids) (code := code) zone state firing) := by
  let : Finite {identity : R // identity ∈ ids ∧ code identity = firing.val.rule} :=
    Finite.of_injective (fun value => (⟨value.val, value.property.1⟩ : {identity : R // identity ∈ ids}))
      (fun _ _ same => Subtype.ext (congrArg (fun value : {identity : R // identity ∈ ids} => value.val) same))
  exact Finite.of_equiv _ (heldUsesEquiv X E zone state firing).symm

variable {P : Program Tm}

def originCases (state : State Tm O)
    (firing : (baseEvents X E (P := P) (Q := Q)).Choice state) :
    Uses X E (ids := ids) (code := code) zone state firing ≃
      {_point : Unit // firing.val.rule ∈ P} ⊕
        {identity : R // identity ∈ ids ∧ code identity = firing.val.rule} where
  toFun origin := by
    obtain ⟨use, available, aligned⟩ := origin
    cases use with
    | ambient rule => exact .inl ⟨(), aligned ▸ available⟩
    | held identity => exact .inr ⟨identity, available, aligned⟩
  invFun
    | .inl available => ⟨.ambient firing.val.rule, available.property, rfl⟩
    | .inr available => ⟨.held available.val, available.property.1, available.property.2⟩
  left_inv origin := by
    obtain ⟨use, available, aligned⟩ := origin
    cases use with
    | ambient rule => exact Subtype.ext (congrArg Use.ambient aligned.symm)
    | held identity => rfl
  right_inv origin := by
    cases origin with
    | inl available => cases available with | mk point available => cases point; rfl
    | inr available => rfl

theorem uses_finite (state : State Tm O)
    (firing : (baseEvents X E (P := P) (Q := Q)).Choice state) :
    Finite (Uses X E (ids := ids) (code := code) zone state firing) := by
  let : Finite {identity : R // identity ∈ ids ∧ code identity = firing.val.rule} :=
    Finite.of_injective (fun value => (⟨value.val, value.property.1⟩ : {identity : R // identity ∈ ids}))
      (fun _ _ same => Subtype.ext (congrArg (fun value : {identity : R // identity ∈ ids} => value.val) same))
  exact Finite.of_equiv _ (originCases X E zone state firing).symm

theorem origin_count (state : State Tm O)
    (firing : (baseEvents X E (P := P) (Q := Q)).Choice state) :
    Nat.card (Uses X E (ids := ids) (code := code) zone state firing) =
      Nat.card {_point : Unit // firing.val.rule ∈ P} +
        Nat.card {identity : R // identity ∈ ids ∧ code identity = firing.val.rule} := by
  let : Finite {identity : R // identity ∈ ids ∧ code identity = firing.val.rule} :=
    Finite.of_injective (fun value => (⟨value.val, value.property.1⟩ : {identity : R // identity ∈ ids}))
      (fun _ _ same => Subtype.ext (congrArg (fun value : {identity : R // identity ∈ ids} => value.val) same))
  rw [Nat.card_congr (originCases X E zone state firing), Nat.card_sum]

theorem decorations_finite : ∀ {count : Nat} {state : State Tm O}
    (run : (baseEvents X E (P := P) (Q := Q)).Execution count state),
    Finite (Decorations X E (ids := ids) (code := code) zone run)
  | 0, _, _ => by
      change Finite PUnit
      infer_instance
  | _ + 1, state, ⟨firing, rest⟩ => by
      let : Finite (Uses X E (ids := ids) (code := code) zone state firing) := uses_finite X E zone state firing
      let : Finite (Decorations X E (ids := ids) (code := code) zone rest) := decorations_finite rest
      change Finite (Uses X E (ids := ids) (code := code) zone state firing ×
        Decorations X E (ids := ids) (code := code) zone rest)
      infer_instance

theorem run_fibre_finite [DecidableEq R] (offers : Offers Q ids code)
    (state : State Tm O) (count : Nat) (base : BaseRuns X E (P := P) (Q := Q) state count) :
    Finite {run : HeldRuns X E (P := P) (ids := ids) (code := code) zone state count //
      projectRun X E zone offers state count run = base} := by
  let path := ((step X O E (P ∪ Q)).toStep.countedExecutionRunEquiv
    (fun {_} firing => (firing.rule, firing.selection)) state count).symm base
  let : Finite (Decorations X E (ids := ids) (code := code) zone path) := decorations_finite X E zone path
  exact Finite.of_equiv _ (runFibreEquiv X E zone offers state count base).symm

theorem ways_constant (multiplicity : Nat)
    (each : ∀ (state : State Tm O) (firing : (baseEvents X E (P := P) (Q := Q)).Choice state),
      Nat.card (Uses X E (ids := ids) (code := code) zone state firing) = multiplicity) :
    ∀ {count : Nat} {state : State Tm O} (run : (baseEvents X E (P := P) (Q := Q)).Execution count state),
      ways X E (ids := ids) (code := code) zone run = multiplicity ^ count
  | 0, _, _ => by simp [ways]
  | count + 1, state, ⟨firing, rest⟩ => by
      change Nat.card (Uses X E zone state firing) * ways X E zone rest = _
      rw [each, ways_constant multiplicity each rest, pow_succ, Nat.mul_comm]

theorem ambient_and_held_origins {state : State Tm O}
    (firing : (baseEvents X E (P := P) (Q := Q)).Choice state) {identity : R}
    (ambient : firing.val.rule ∈ P) (held : identity ∈ ids) (label : code identity = firing.val.rule) :
    ∃ first second : Uses X E (ids := ids) (code := code) zone state firing,
      first.val = .ambient firing.val.rule ∧ second.val = .held identity ∧ first ≠ second := by
  refine ⟨⟨.ambient firing.val.rule, ambient, rfl⟩, ⟨.held identity, held, label⟩, rfl, rfl, ?_⟩
  intro same
  have uses := congrArg Subtype.val same
  cases uses

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Origins
