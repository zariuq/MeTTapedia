import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.Persistent

/-!
# Available rule origins retained over actual base events

Each decorated choice contains the old admitted firing and one available use
of its rule. The result is the old firing's result. This event presentation is
realized by the actual persistent rule store, with its `Use` label retained.
The canonical projection fixes the complete base firing, including its opening
and occurrence selection; irrelevant infinite opening choices cannot erase
the number of available origins above that firing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Origins

open RuleSyntax RuleSyntax.RuleOccurrences
open EventMultiplicity

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R] {Z : Type uZ}
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom) {P Q : Program Tm}
  {ids : Finset R} {code : R → Rule Tm} (offers : Offers Q ids code) (zone : R → Z)

abbrev baseEvents := (step X O E (P ∪ Q)).toStep.eventSystem
  (Action := Rule Tm × Selection O) (fun {_} firing => (firing.rule, firing.selection))

abbrev heldEvents := (rstep X O R E (ofRules Z) P).toStep.eventSystem
  (Action := Use (Rule Tm) R) (fun {_} firing => firing.use)

def Uses (state : State Tm O) (firing : (baseEvents X E (P := P) (Q := Q)).Choice state) :=
  {use : Use (Rule Tm) R //
    (holding state ids code zone).Available P use ∧
      (holding state ids code zone).codeOf use = firing.val.rule}

def decorated : EventMultiplicity.System (State Tm O) (Use (Rule Tm) R) where
  Choice state := (firing : (baseEvents X E (P := P) (Q := Q)).Choice state) × Uses X E (ids := ids) (code := code) zone state firing
  next state choice := (baseEvents X E (P := P) (Q := Q)).next state choice.1
  action _ choice := choice.2.val

def withOrigin (state : State Tm O) :
    (heldEvents X E (O := O) (R := R) (Z := Z) (P := P)).Choice (holding state ids code zone) →
      (decorated X E (P := P) (Q := Q) (ids := ids) (code := code) zone).Choice state :=
  fun choice => ⟨project X offers zone state choice,
    ⟨choice.val.use, choice.property.1.2.2.available, rfl⟩⟩

theorem withOrigin_injective (state : State Tm O) : Function.Injective (withOrigin X E (P := P) offers zone state) := by
  intro first second same
  have projected := congrArg Sigma.fst same
  have used := congrArg (fun choice : (decorated X E (P := P) (Q := Q) (ids := ids) (code := code) zone).Choice state => choice.2.val) same
  exact fibre_use_injective X offers zone projected used

theorem withOrigin_surjective (state : State Tm O) : Function.Surjective (withOrigin X E (P := P) offers zone state) := by
  rintro ⟨firing, ⟨use, available, aligned⟩⟩
  obtain ⟨lifted, projected, used⟩ := fibre_use_surjective X offers zone firing available aligned
  subst firing
  refine ⟨lifted, ?_⟩
  subst use
  rfl

noncomputable def choices (state : State Tm O) :
    (heldEvents X E (O := O) (R := R) (Z := Z) (P := P)).Choice (holding state ids code zone) ≃
      (decorated X E (P := P) (Q := Q) (ids := ids) (code := code) zone).Choice state :=
  Equiv.ofBijective (withOrigin X E offers zone state)
    ⟨withOrigin_injective X E offers zone state, withOrigin_surjective X E offers zone state⟩

noncomputable def realization :
    EventMultiplicity.Realization (decorated X E (O := O) (P := P) (Q := Q) (ids := ids) (code := code) zone) (heldEvents X E (O := O) (R := R) (Z := Z) (P := P)) where
  state state := holding state ids code zone
  choices state := (choices X E offers zone state).symm
  actions state choice := by
    have restored := (choices X E offers zone state).apply_symm_apply choice
    exact (congrArg (fun entry : (decorated X E (P := P) (Q := Q) (ids := ids) (code := code) zone).Choice state => entry.2.val) restored).symm
  successors state choice := by
    let lifted := (choices X E offers zone state).symm choice
    have restored : withOrigin X E offers zone state lifted = choice :=
      (choices X E offers zone state).apply_symm_apply choice
    have projected := congrArg Sigma.fst restored
    have member := member_of_admits X offers zone lifted.property
    have parts := (admits_toProgram_iff X lifted.val member P).mp lifted.property
    have endpoint := result_holding X lifted.val member parts.2.2.1 parts.2.2.2.2.1
    change holding (choice.1.val.result X state) ids code zone = lifted.val.result X
    rw [endpoint]
    exact congrArg (fun firing : (baseEvents X E (P := P) (Q := Q)).Choice state =>
      holding (firing.val.result X state) ids code zone) projected.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Origins
