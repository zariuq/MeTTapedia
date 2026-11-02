import Mettapedia.Languages.ProcessCalculi.PiCalculus.CongruenceSubstitution

/-!
# Early labelled transitions of the asynchronous π-calculus

Labels are a silent step, the input of a name on a channel, the output of a free name and the output of a restricted
name (`Label`). The transitions (`Transition`) are the early ones: an input receives any name; a replicated input
receives and stays; a parallel component moves beside the other when its bound name is fresh for it; an output meets
an input in a communication, and a bound output meets an input in a close, which keeps the extruded name restricted
around both; a restriction lets a transition through when its name is not involved, and opens an output of its own
name into a bound output.

- **Visible transitions have a shape** (`output_shape`, `input_shape`, `boundOutput_shape`): the output, the receiver
  (`receive` is what it becomes) or the opened output sits among parallel components under restrictions that avoid any
  finite set, and the target is what is left. Restrictions are renamed after the fact (`rename_under`), and receiving
  commutes with renaming (`receive_substitute`), a renamed payload included (`receive_renamed`).
- **Every silent transition is a reduction** (`reduces_of_tau`): a communication merges the two scopes and reduces
  inside them (`comm_exposed`); a close does the same under the extruded name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

/-- **Labels**: a silent step, an input of a name on a channel, an output of a free name, an output of a restricted
name. -/
inductive Label where
  | tau
  | input (channel payload : Name)
  | output (channel payload : Name)
  | boundOutput (channel payload : Name)
  deriving DecidableEq

/-- The name a label binds. -/
def Label.bound : Label → Finset Name
  | .boundOutput _ payload => {payload}
  | _ => ∅

/-- The names a label mentions. -/
def Label.names : Label → Finset Name
  | .tau => ∅
  | .input channel payload => {channel, payload}
  | .output channel payload => {channel, payload}
  | .boundOutput channel payload => {channel, payload}

/-- **Early transitions.** -/
inductive Transition : Process → Label → Process → Prop
  | output (x z : Name) : Transition (.output x z) (.output x z) .nil
  | input (x y z : Name) (body : Process) : Transition (.input x y body) (.input x z) (body.substitute y z)
  | replicate (x y z : Name) (body : Process) :
      Transition (.replicate x y body) (.input x z) (.par (body.substitute y z) (.replicate x y body))
  | parLeft {left left' : Process} {label : Label} (right : Process) :
      Transition left label left' → Disjoint label.bound right.freeNames →
        Transition (.par left right) label (.par left' right)
  | parRight {right right' : Process} {label : Label} (left : Process) :
      Transition right label right' → Disjoint label.bound left.freeNames →
        Transition (.par left right) label (.par left right')
  | commLeft {left left' right right' : Process} {x z : Name} :
      Transition left (.output x z) left' → Transition right (.input x z) right' →
        Transition (.par left right) .tau (.par left' right')
  | commRight {left left' right right' : Process} {x z : Name} :
      Transition left (.input x z) left' → Transition right (.output x z) right' →
        Transition (.par left right) .tau (.par left' right')
  | closeLeft {left left' right right' : Process} {x z : Name} :
      Transition left (.boundOutput x z) left' → Transition right (.input x z) right' → z ∉ right.freeNames →
        Transition (.par left right) .tau (.nu z (.par left' right'))
  | closeRight {left left' right right' : Process} {x z : Name} :
      Transition left (.input x z) left' → Transition right (.boundOutput x z) right' → z ∉ left.freeNames →
        Transition (.par left right) .tau (.nu z (.par left' right'))
  | res {body body' : Process} {label : Label} (name : Name) :
      Transition body label body' → name ∉ label.names → Transition (.nu name body) label (.nu name body')
  | «open» {body body' : Process} {x z : Name} :
      Transition body (.output x z) body' → z ≠ x → Transition (.nu z body) (.boundOutput x z) body'

/-! ## Receivers -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open PiCalcInstance (piToPattern piToPattern_substitute piToPattern_noExplicitSubst piToPattern_open_close_substitute)

/-- **What a receiver becomes on receiving a name**: an input, its body with the name received; a replicated input,
the same beside itself. -/
def receive : Process → Name → Process
  | .input _ binder body, payload => body.substitute binder payload
  | .replicate x binder body, payload => .par (body.substitute binder payload) (.replicate x binder body)
  | process, _ => process

theorem substitute_input_shape (x binder : Name) (body : Process) (old new : Name) :
    ∃ binder' body', (Process.input x binder body).substitute old new =
      .input (if x = old then new else x) binder' body' := by
  rw [Process.substitute]
  split_ifs <;> exact ⟨_, _, rfl⟩

theorem substitute_replicate_shape (x binder : Name) (body : Process) (old new : Name) :
    ∃ binder' body', (Process.replicate x binder body).substitute old new =
      .replicate (if x = old then new else x) binder' body' := by
  rw [Process.substitute]
  split_ifs <;> exact ⟨_, _, rfl⟩

/-- The continuation of a binder renamed by a substitution, received, is the substituted continuation. -/
theorem received_substitute {binder binder' : Name} {body body' : Process} {old new payload : Name}
    (images : closeFVar 0 binder' (piToPattern body') =
      applySubst [(old, .fvar new)] (closeFVar 0 binder (piToPattern body)))
    (notPayload : payload ≠ old) :
    Congruent (body'.substitute binder' payload) ((body.substitute binder payload).substitute old new) := by
  refine congruent_of_piToPattern_eq _ _ _ le_rfl ?_
  rw [← piToPattern_open_close_substitute, images, piToPattern_substitute, ← piToPattern_open_close_substitute]
  exact (applySubst_openBVar_comm notPayload (by rfl)
    (noExplicitSubst_closeFVar (piToPattern_noExplicitSubst body))).symm

/-- **Receiving commutes with renaming**, up to structural congruence. -/
theorem receive_substitute {x : Name} {receiver : Process} (receives : ReceivesOn x receiver) {old new payload : Name}
    (notPayload : payload ≠ old) :
    Congruent (receive (receiver.substitute old new) payload) ((receive receiver payload).substitute old new) := by
  rcases receives with ⟨binder, body, rfl⟩ | ⟨binder, body, rfl⟩
  · obtain ⟨binder', body', shape⟩ := substitute_input_shape x binder body old new
    have images := congrArg piToPattern shape
    rw [piToPattern_substitute] at images
    simp only [piToPattern, applySubst, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
      Pattern.lambda.injEq, true_and, and_true] at images
    rw [shape]
    exact received_substitute images.2.symm notPayload
  · obtain ⟨binder', body', shape⟩ := substitute_replicate_shape x binder body old new
    have images := congrArg piToPattern shape
    rw [piToPattern_substitute] at images
    simp only [piToPattern, applySubst, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
      Pattern.lambda.injEq, true_and, and_true] at images
    rw [shape]
    simp only [receive, Process.substitute_par]
    rw [shape]
    exact Congruent.par (received_substitute images.2.symm notPayload) (Congruent.refl _)

/-- The continuation of a binder renamed by a substitution, received at the renamed payload, is the substituted
continuation. -/
theorem received_renamed {binder binder' : Name} {body body' : Process} {old new payload : Name}
    (images : closeFVar 0 binder' (piToPattern body') =
      applySubst [(old, .fvar new)] (closeFVar 0 binder (piToPattern body))) :
    Congruent (body'.substitute binder' (if payload = old then new else payload))
      ((body.substitute binder payload).substitute old new) := by
  refine congruent_of_piToPattern_eq _ _ _ le_rfl ?_
  have closed := noExplicitSubst_closeFVar (k := 0) (x := binder) (piToPattern_noExplicitSubst body)
  rw [← piToPattern_open_close_substitute, images, piToPattern_substitute, ← piToPattern_open_close_substitute,
    applySubst_single_eq_mapFVars _ _ _ closed,
    applySubst_single_eq_mapFVars _ _ _ (noExplicitSubst_openBVar closed rfl), mapFVars_openBVar]

/-- **Receiving commutes with renaming**, the payload renamed too. -/
theorem receive_renamed {x : Name} {receiver : Process} (receives : ReceivesOn x receiver) (old new payload : Name) :
    Congruent (receive (receiver.substitute old new) (if payload = old then new else payload))
      ((receive receiver payload).substitute old new) := by
  rcases receives with ⟨binder, body, rfl⟩ | ⟨binder, body, rfl⟩
  · obtain ⟨binder', body', shape⟩ := substitute_input_shape x binder body old new
    have images := congrArg piToPattern shape
    rw [piToPattern_substitute] at images
    simp only [piToPattern, applySubst, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
      Pattern.lambda.injEq, true_and, and_true] at images
    rw [shape]
    exact received_renamed images.2.symm
  · obtain ⟨binder', body', shape⟩ := substitute_replicate_shape x binder body old new
    have images := congrArg piToPattern shape
    rw [piToPattern_substitute] at images
    simp only [piToPattern, applySubst, List.map_cons, List.map_nil, Pattern.apply.injEq, List.cons.injEq,
      Pattern.lambda.injEq, true_and, and_true] at images
    rw [shape]
    simp only [receive, Process.substitute_par]
    rw [shape]
    exact Congruent.par (received_renamed images.2.symm) (Congruent.refl _)

theorem freeNames_receive {x : Name} {receiver : Process} (receives : ReceivesOn x receiver) (payload : Name) :
    (receive receiver payload).freeNames ⊆ insert payload receiver.freeNames := by
  rcases receives with ⟨binder, body, rfl⟩ | ⟨binder, body, rfl⟩
  · intro name inside
    have := Process.substitute_freeNames body binder payload inside
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton, Process.freeNames] at this ⊢
    tauto
  · intro name inside
    simp only [receive, Process.freeNames, Finset.mem_union] at inside
    rcases inside with received | server
    · have := Process.substitute_freeNames body binder payload received
      simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton, Process.freeNames] at this ⊢
      tauto
    · exact Finset.mem_insert_of_mem server

/-- **A receiver beside an output on its channel reduces to what it receives.** -/
theorem receive_reduces {x : Name} {receiver : Process} (receives : ReceivesOn x receiver) (payload : Name) :
    Nonempty (Reduces (.par receiver (.output x payload)) (receive receiver payload)) := by
  rcases receives with ⟨binder, body, rfl⟩ | ⟨binder, body, rfl⟩
  · exact ⟨.comm x binder payload body⟩
  · have unfold : Congruent (Process.replicate x binder body ||| Process.output x payload)
        ((Process.input x binder body ||| Process.output x payload) ||| Process.replicate x binder body) :=
      (Congruent.par ⟨.replicate_unfold x binder body⟩ (Congruent.refl _)).trans ((Congruent.assoc _ _ _).trans
        ((Congruent.par (Congruent.refl _) (Congruent.comm _ _)).trans (Congruent.assoc _ _ _).symm))
    exact reduces_of_congruent unfold (reduces_parLeft _ ⟨.comm x binder payload body⟩) (Congruent.refl _)

/-! ## Visible transitions have a shape -/

/-- A restriction renamed to a fresh name, through the restrictions under it. -/
theorem rename_under {names : List Name} {name fresh : Name} {body : Process} (nameOut : name ∉ names)
    (freshOut : fresh ∉ names) (notFree : fresh ∉ (nuList names body).freeNames) :
    Congruent (.nu name (nuList names body)) (.nu fresh (nuList names (body.substitute name fresh))) := by
  rw [← substitute_nuList nameOut freshOut]
  exact ⟨.alpha_nu name fresh _ notFree⟩

/-- **An output transition** exposes the output among parallel components under restrictions that avoid any finite
set, and its target is the rest. -/
theorem output_shape {source target : Process} {label : Label} (step : Transition source label target) :
    ∀ {x z : Name}, label = .output x z → ∀ avoid : Finset Name, ∃ (names : List Name) (rest : Process),
      names.Nodup ∧ Disjoint names.toFinset avoid ∧ x ∉ names ∧ z ∉ names ∧
        Congruent source (nuList names (.par (.output x z) rest)) ∧ Congruent target (nuList names rest) := by
  induction step with
  | output x z =>
    intro x' z' same avoid
    cases same
    exact ⟨[], .nil, List.nodup_nil, by simp, by simp, by simp, (Congruent.nilRight _).symm, Congruent.refl _⟩
  | input => intro _ _ same; cases same
  | replicate => intro _ _ same; cases same
  | parLeft right _ _ holds =>
    intro x z same avoid
    obtain ⟨names, rest, nodup, away, notX, notZ, before, after⟩ := holds same (avoid ∪ right.freeNames)
    have fresh : Disjoint names.toFinset right.freeNames := away.mono_right Finset.subset_union_right
    refine ⟨names, .par rest right, nodup, away.mono_right Finset.subset_union_left, notX, notZ, ?_, ?_⟩
    · exact (Congruent.par before (Congruent.refl _)).trans
        ((nuList_extrude fresh).trans (nuList_congruent _ (Congruent.assoc _ _ _)))
    · exact (Congruent.par after (Congruent.refl _)).trans (nuList_extrude fresh)
  | parRight left _ _ holds =>
    intro x z same avoid
    obtain ⟨names, rest, nodup, away, notX, notZ, before, after⟩ := holds same (avoid ∪ left.freeNames)
    have fresh : Disjoint names.toFinset left.freeNames := away.mono_right Finset.subset_union_right
    refine ⟨names, .par rest left, nodup, away.mono_right Finset.subset_union_left, notX, notZ, ?_, ?_⟩
    · exact (Congruent.par (Congruent.refl _) before).trans ((Congruent.comm _ _).trans
        ((nuList_extrude fresh).trans (nuList_congruent _ (Congruent.assoc _ _ _))))
    · exact (Congruent.par (Congruent.refl _) after).trans ((Congruent.comm _ _).trans (nuList_extrude fresh))
  | commLeft => intro _ _ same; cases same
  | commRight => intro _ _ same; cases same
  | closeLeft => intro _ _ same; cases same
  | closeRight => intro _ _ same; cases same
  | res name _ notInvolved holds =>
    intro x z same avoid
    subst same
    obtain ⟨names, rest, nodup, away, notX, notZ, before, after⟩ := holds rfl (insert name avoid)
    have nameOut : name ∉ names := fun member =>
      Finset.disjoint_left.mp away (List.mem_toFinset.mpr member) (Finset.mem_insert_self _ _)
    simp only [Label.names, Finset.mem_insert, Finset.mem_singleton, not_or] at notInvolved
    obtain ⟨fresh, freshNot⟩ := exists_fresh (avoid ∪ names.toFinset ∪
      (nuList names (.par (.output x z) rest)).freeNames ∪ {x, z})
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at freshNot
    obtain ⟨⟨⟨freshAvoid, freshNames⟩, freshFree⟩, freshX, freshZ⟩ := freshNot
    have freshOut : fresh ∉ names := fun member => freshNames (List.mem_toFinset.mpr member)
    have freshRest : fresh ∉ (nuList names rest).freeNames := by
      intro inside
      apply freshFree
      rw [freeNames_nuList] at inside ⊢
      simp only [Finset.mem_sdiff, Process.freeNames, Finset.mem_union] at inside ⊢
      exact ⟨Or.inr inside.1, inside.2⟩
    refine ⟨fresh :: names, rest.substitute name fresh, List.nodup_cons.mpr ⟨freshOut, nodup⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.toFinset_cons]
      refine Finset.disjoint_insert_left.mpr ⟨freshAvoid, away.mono_right (Finset.subset_insert _ _)⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm freshX, notX⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm freshZ, notZ⟩
    · refine (Congruent.nu name before).trans ((rename_under nameOut freshOut freshFree).trans ?_)
      simp only [Process.substitute_par, Process.substitute_output, if_neg (Ne.symm notInvolved.1),
        if_neg (Ne.symm notInvolved.2)]
      exact Congruent.refl _
    · exact (Congruent.nu name after).trans (rename_under nameOut freshOut freshRest)
  | «open» => intro _ _ same; cases same

/-- **An input transition** exposes a receiver on the channel among parallel components under restrictions that avoid
any finite set, and its target is what the receiver receives beside the rest. -/
theorem input_shape {source target : Process} {label : Label} (step : Transition source label target) :
    ∀ {x z : Name}, label = .input x z → ∀ avoid : Finset Name, ∃ (names : List Name) (receiver rest : Process),
      names.Nodup ∧ Disjoint names.toFinset avoid ∧ x ∉ names ∧ z ∉ names ∧ ReceivesOn x receiver ∧
        Congruent source (nuList names (.par receiver rest)) ∧
        Congruent target (nuList names (.par (receive receiver z) rest)) := by
  induction step with
  | output => intro _ _ same; cases same
  | input x binder z body =>
    intro x' z' same avoid
    cases same
    exact ⟨[], .input x binder body, .nil, List.nodup_nil, by simp, by simp, by simp, Or.inl ⟨binder, body, rfl⟩,
      (Congruent.nilRight _).symm, (Congruent.nilRight _).symm⟩
  | replicate x binder z body =>
    intro x' z' same avoid
    cases same
    exact ⟨[], .replicate x binder body, .nil, List.nodup_nil, by simp, by simp, by simp, Or.inr ⟨binder, body, rfl⟩,
      (Congruent.nilRight _).symm, (Congruent.nilRight _).symm⟩
  | parLeft right _ _ holds =>
    intro x z same avoid
    obtain ⟨names, receiver, rest, nodup, away, notX, notZ, receives, before, after⟩ :=
      holds same (avoid ∪ right.freeNames)
    have fresh : Disjoint names.toFinset right.freeNames := away.mono_right Finset.subset_union_right
    refine ⟨names, receiver, .par rest right, nodup, away.mono_right Finset.subset_union_left, notX, notZ, receives,
      ?_, ?_⟩
    · exact (Congruent.par before (Congruent.refl _)).trans
        ((nuList_extrude fresh).trans (nuList_congruent _ (Congruent.assoc _ _ _)))
    · exact (Congruent.par after (Congruent.refl _)).trans
        ((nuList_extrude fresh).trans (nuList_congruent _ (Congruent.assoc _ _ _)))
  | parRight left _ _ holds =>
    intro x z same avoid
    obtain ⟨names, receiver, rest, nodup, away, notX, notZ, receives, before, after⟩ :=
      holds same (avoid ∪ left.freeNames)
    have fresh : Disjoint names.toFinset left.freeNames := away.mono_right Finset.subset_union_right
    refine ⟨names, receiver, .par rest left, nodup, away.mono_right Finset.subset_union_left, notX, notZ, receives,
      ?_, ?_⟩
    · exact (Congruent.par (Congruent.refl _) before).trans ((Congruent.comm _ _).trans
        ((nuList_extrude fresh).trans (nuList_congruent _ (Congruent.assoc _ _ _))))
    · exact (Congruent.par (Congruent.refl _) after).trans ((Congruent.comm _ _).trans
        ((nuList_extrude fresh).trans (nuList_congruent _ (Congruent.assoc _ _ _))))
  | commLeft => intro _ _ same; cases same
  | commRight => intro _ _ same; cases same
  | closeLeft => intro _ _ same; cases same
  | closeRight => intro _ _ same; cases same
  | res name _ notInvolved holds =>
    intro x z same avoid
    subst same
    obtain ⟨names, receiver, rest, nodup, away, notX, notZ, receives, before, after⟩ := holds rfl (insert name avoid)
    have nameOut : name ∉ names := fun member =>
      Finset.disjoint_left.mp away (List.mem_toFinset.mpr member) (Finset.mem_insert_self _ _)
    simp only [Label.names, Finset.mem_insert, Finset.mem_singleton, not_or] at notInvolved
    obtain ⟨fresh, freshNot⟩ := exists_fresh (avoid ∪ names.toFinset ∪
      (nuList names (.par receiver rest)).freeNames ∪ (nuList names (.par (receive receiver z) rest)).freeNames ∪
        {x, z})
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at freshNot
    obtain ⟨⟨⟨⟨freshAvoid, freshNames⟩, freshFree⟩, freshFree'⟩, freshX, freshZ⟩ := freshNot
    have freshOut : fresh ∉ names := fun member => freshNames (List.mem_toFinset.mpr member)
    refine ⟨fresh :: names, receiver.substitute name fresh, rest.substitute name fresh,
      List.nodup_cons.mpr ⟨freshOut, nodup⟩, ?_, ?_, ?_, receivesOn_substitute receives (Ne.symm notInvolved.1), ?_, ?_⟩
    · rw [List.toFinset_cons]
      exact Finset.disjoint_insert_left.mpr ⟨freshAvoid, away.mono_right (Finset.subset_insert _ _)⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm freshX, notX⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm freshZ, notZ⟩
    · refine (Congruent.nu name before).trans ((rename_under nameOut freshOut freshFree).trans ?_)
      rw [Process.substitute_par]
      exact Congruent.refl _
    · refine (Congruent.nu name after).trans ((rename_under nameOut freshOut freshFree').trans ?_)
      rw [Process.substitute_par]
      exact Congruent.nu fresh (nuList_congruent _ (Congruent.par
        (receive_substitute receives (Ne.symm notInvolved.2)).symm (Congruent.refl _)))
  | «open» => intro _ _ same; cases same

/-- **A bound output transition** exposes the output of its restricted name among parallel components under further
restrictions that avoid any finite set, and its target is the rest with the name now free. -/
theorem boundOutput_shape {source target : Process} {label : Label} (step : Transition source label target) :
    ∀ {x z : Name}, label = .boundOutput x z → ∀ avoid : Finset Name, ∃ (names : List Name) (rest : Process),
      names.Nodup ∧ Disjoint names.toFinset avoid ∧ x ∉ names ∧ z ∉ names ∧ z ≠ x ∧
        Congruent source (.nu z (nuList names (.par (.output x z) rest))) ∧ Congruent target (nuList names rest) := by
  induction step with
  | output => intro _ _ same; cases same
  | input => intro _ _ same; cases same
  | replicate => intro _ _ same; cases same
  | parLeft right _ bound holds =>
    intro x z same avoid
    subst same
    have zOut : z ∉ right.freeNames := Finset.disjoint_left.mp bound (by simp [Label.bound])
    obtain ⟨names, rest, nodup, away, notX, notZ, different, before, after⟩ := holds rfl (avoid ∪ right.freeNames)
    have fresh : Disjoint names.toFinset right.freeNames := away.mono_right Finset.subset_union_right
    refine ⟨names, .par rest right, nodup, away.mono_right Finset.subset_union_left, notX, notZ, different, ?_, ?_⟩
    · exact (Congruent.par before (Congruent.refl _)).trans (Congruent.trans (Congruent.symm ⟨.nu_par z _ _ zOut⟩)
        (Congruent.nu z ((nuList_extrude fresh).trans (nuList_congruent _ (Congruent.assoc _ _ _)))))
    · exact (Congruent.par after (Congruent.refl _)).trans (nuList_extrude fresh)
  | parRight left _ bound holds =>
    intro x z same avoid
    subst same
    have zOut : z ∉ left.freeNames := Finset.disjoint_left.mp bound (by simp [Label.bound])
    obtain ⟨names, rest, nodup, away, notX, notZ, different, before, after⟩ := holds rfl (avoid ∪ left.freeNames)
    have fresh : Disjoint names.toFinset left.freeNames := away.mono_right Finset.subset_union_right
    refine ⟨names, .par rest left, nodup, away.mono_right Finset.subset_union_left, notX, notZ, different, ?_, ?_⟩
    · exact (Congruent.par (Congruent.refl _) before).trans ((Congruent.comm _ _).trans
        (Congruent.trans (Congruent.symm ⟨.nu_par z _ _ zOut⟩)
          (Congruent.nu z ((nuList_extrude fresh).trans (nuList_congruent _ (Congruent.assoc _ _ _))))))
    · exact (Congruent.par (Congruent.refl _) after).trans ((Congruent.comm _ _).trans (nuList_extrude fresh))
  | commLeft => intro _ _ same; cases same
  | commRight => intro _ _ same; cases same
  | closeLeft => intro _ _ same; cases same
  | closeRight => intro _ _ same; cases same
  | res name _ notInvolved holds =>
    intro x z same avoid
    subst same
    obtain ⟨names, rest, nodup, away, notX, notZ, different, before, after⟩ := holds rfl (insert name avoid)
    have nameOut : name ∉ names := fun member =>
      Finset.disjoint_left.mp away (List.mem_toFinset.mpr member) (Finset.mem_insert_self _ _)
    simp only [Label.names, Finset.mem_insert, Finset.mem_singleton, not_or] at notInvolved
    obtain ⟨fresh, freshNot⟩ := exists_fresh (avoid ∪ names.toFinset ∪
      (nuList names (.par (.output x z) rest)).freeNames ∪ {x, z})
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at freshNot
    obtain ⟨⟨⟨freshAvoid, freshNames⟩, freshFree⟩, freshX, freshZ⟩ := freshNot
    have freshOut : fresh ∉ names := fun member => freshNames (List.mem_toFinset.mpr member)
    have freshRest : fresh ∉ (nuList names rest).freeNames := by
      intro inside
      apply freshFree
      rw [freeNames_nuList] at inside ⊢
      simp only [Finset.mem_sdiff, Process.freeNames, Finset.mem_union] at inside ⊢
      exact ⟨Or.inr inside.1, inside.2⟩
    refine ⟨fresh :: names, rest.substitute name fresh, List.nodup_cons.mpr ⟨freshOut, nodup⟩, ?_, ?_, ?_, different,
      ?_, ?_⟩
    · rw [List.toFinset_cons]
      exact Finset.disjoint_insert_left.mpr ⟨freshAvoid, away.mono_right (Finset.subset_insert _ _)⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm freshX, notX⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm freshZ, notZ⟩
    · refine (Congruent.nu name before).trans (Congruent.trans ⟨.nu_swap name z _⟩ (Congruent.nu z ?_))
      refine (rename_under nameOut freshOut freshFree).trans ?_
      simp only [Process.substitute_par, Process.substitute_output, if_neg (Ne.symm notInvolved.1),
        if_neg (Ne.symm notInvolved.2)]
      exact Congruent.refl _
    · exact (Congruent.nu name after).trans (rename_under nameOut freshOut freshRest)
  | @«open» body body' x z premise different _ =>
    intro x' z' same avoid
    cases same
    obtain ⟨names, rest, nodup, away, notX, notZ, before, after⟩ := output_shape premise rfl (insert z avoid)
    have zOut : z ∉ names := fun member =>
      Finset.disjoint_left.mp away (List.mem_toFinset.mpr member) (Finset.mem_insert_self _ _)
    exact ⟨names, rest, nodup, away.mono_right (Finset.subset_insert _ _), notX, zOut, different,
      Congruent.nu z before, after⟩

/-! ## Silent transitions are reductions -/

theorem par_medial (p q r t : Process) :
    Congruent (.par (.par p q) (.par r t)) (.par (.par p r) (.par q t)) :=
  (Congruent.assoc _ _ _).trans ((Congruent.par (Congruent.refl _) (Congruent.assoc _ _ _).symm).trans
    ((Congruent.par (Congruent.refl _) (Congruent.par (Congruent.comm _ _) (Congruent.refl _))).trans
      ((Congruent.par (Congruent.refl _) (Congruent.assoc _ _ _)).trans (Congruent.assoc _ _ _).symm)))

theorem par_rotate (p q r : Process) : Congruent (.par p (.par q r)) (.par q (.par p r)) :=
  (Congruent.assoc _ _ _).symm.trans ((Congruent.par (Congruent.comm _ _) (Congruent.refl _)).trans
    (Congruent.assoc _ _ _))

theorem mem_of_congruent_nuList {process body : Process} {names : List Name}
    (congruent : Congruent process (nuList names body)) {name : Name} (inside : name ∈ body.freeNames) :
    name ∈ names.toFinset ∨ name ∈ process.freeNames := by
  by_cases bound : name ∈ names.toFinset
  · exact Or.inl bound
  · refine Or.inr ?_
    rw [congruent.freeNames_eq, freeNames_nuList]
    exact Finset.mem_sdiff.mpr ⟨inside, bound⟩

theorem freeNames_received {receiver rest : Process} {names : List Name} {x payload : Name}
    (receives : ReceivesOn x receiver) {process : Process}
    (congruent : Congruent process (nuList names (.par receiver rest))) :
    (nuList names (.par (receive receiver payload) rest)).freeNames ⊆ insert payload process.freeNames := by
  intro name inside
  rw [freeNames_nuList] at inside
  obtain ⟨present, unbound⟩ := Finset.mem_sdiff.mp inside
  simp only [Process.freeNames, Finset.mem_union] at present
  rcases present with received | inRest
  · rcases Finset.mem_insert.mp (freeNames_receive receives payload received) with same | fromReceiver
    · exact Finset.mem_insert.mpr (Or.inl same)
    · refine Finset.mem_insert_of_mem ?_
      rw [congruent.freeNames_eq, freeNames_nuList]
      exact Finset.mem_sdiff.mpr ⟨by simp [Process.freeNames, fromReceiver], unbound⟩
  · refine Finset.mem_insert_of_mem ?_
    rw [congruent.freeNames_eq, freeNames_nuList]
    exact Finset.mem_sdiff.mpr ⟨by simp [Process.freeNames, inRest], unbound⟩

/-- The communication of an output and a receiver exposed under two lists of restrictions. -/
theorem comm_exposed {left right left' right' : Process} {sendNames receiveNames : List Name}
    {sendRest receiver receiveRest : Process} {x payload : Name} (receives : ReceivesOn x receiver)
    (sendBefore : Congruent left (nuList sendNames (.par (.output x payload) sendRest)))
    (sendAfter : Congruent left' (nuList sendNames sendRest))
    (receiveBefore : Congruent right (nuList receiveNames (.par receiver receiveRest)))
    (receiveAfter : Congruent right' (nuList receiveNames (.par (receive receiver payload) receiveRest)))
    (sendAway : Disjoint sendNames.toFinset (insert payload right.freeNames))
    (receiveAway : Disjoint receiveNames.toFinset (left.freeNames ∪ sendNames.toFinset)) :
    Nonempty (Reduces (.par left right) (.par left' right')) := by
  have sendFresh : Disjoint sendNames.toFinset (nuList receiveNames (.par receiver receiveRest)).freeNames := by
    rw [← receiveBefore.freeNames_eq]
    exact sendAway.mono_right (Finset.subset_insert _ _)
  have receiveFresh : ∀ {body : Process}, body.freeNames ⊆ (Process.par (.output x payload) sendRest).freeNames →
      Disjoint receiveNames.toFinset body.freeNames := fun {body} within => by
    refine Finset.disjoint_left.mpr fun name restricted inside => ?_
    rcases mem_of_congruent_nuList sendBefore (within inside) with bound | free
    · exact Finset.disjoint_left.mp receiveAway restricted (Finset.mem_union_right _ bound)
    · exact Finset.disjoint_left.mp receiveAway restricted (Finset.mem_union_left _ free)
  have before : Congruent (.par left right)
      (nuList (sendNames ++ receiveNames) (.par (.par receiver (.output x payload)) (.par sendRest receiveRest))) :=
    (Congruent.par sendBefore receiveBefore).trans ((nuList_merge sendFresh (receiveFresh le_rfl)).trans
      (nuList_congruent _ ((par_medial _ _ _ _).trans (Congruent.par (Congruent.comm _ _) (Congruent.refl _)))))
  have receivedFresh : Disjoint sendNames.toFinset
      (nuList receiveNames (.par (receive receiver payload) receiveRest)).freeNames :=
    sendAway.mono_right (freeNames_received receives receiveBefore)
  have after : Congruent
      (nuList (sendNames ++ receiveNames) (.par (receive receiver payload) (.par sendRest receiveRest)))
      (.par left' right') :=
    (nuList_congruent _ (par_rotate _ _ _)).trans ((nuList_merge receivedFresh
      (receiveFresh fun name inside => by simp [Process.freeNames, inside])).symm.trans
        (Congruent.par sendAfter.symm receiveAfter.symm))
  exact reduces_of_congruent before (reduces_nuList _ (reduces_parLeft _ (receive_reduces receives payload))) after

/-- **Every silent transition is a reduction.** -/
theorem reduces_of_tau {source target : Process} {label : Label} (step : Transition source label target) :
    label = .tau → Nonempty (Reduces source target) := by
  induction step with
  | output => intro same; cases same
  | input => intro same; cases same
  | replicate => intro same; cases same
  | parLeft right _ _ holds => intro same; exact (holds same).map fun inner => .par_left _ _ _ inner
  | parRight left _ _ holds => intro same; exact (holds same).map fun inner => .par_right _ _ _ inner
  | @commLeft left left' right right' x z sending receiving _ _ =>
    intro _
    obtain ⟨sendNames, sendRest, _, sendAway, _, sendZ, sendBefore, sendAfter⟩ :=
      output_shape sending rfl (insert z right.freeNames)
    obtain ⟨receiveNames, receiver, receiveRest, _, receiveAway, _, _, receives, receiveBefore, receiveAfter⟩ :=
      input_shape receiving rfl (left.freeNames ∪ sendNames.toFinset)
    exact comm_exposed receives sendBefore sendAfter receiveBefore receiveAfter sendAway receiveAway
  | @commRight left left' right right' x z receiving sending _ _ =>
    intro _
    obtain ⟨sendNames, sendRest, _, sendAway, _, sendZ, sendBefore, sendAfter⟩ :=
      output_shape sending rfl (insert z left.freeNames)
    obtain ⟨receiveNames, receiver, receiveRest, _, receiveAway, _, _, receives, receiveBefore, receiveAfter⟩ :=
      input_shape receiving rfl (right.freeNames ∪ sendNames.toFinset)
    exact reduces_of_congruent (Congruent.comm _ _)
      (comm_exposed receives sendBefore sendAfter receiveBefore receiveAfter sendAway receiveAway)
      (Congruent.comm _ _)
  | @closeLeft left left' right right' x z sending receiving outside _ _ =>
    intro _
    obtain ⟨sendNames, sendRest, _, sendAway, _, sendZ, _, sendBefore, sendAfter⟩ :=
      boundOutput_shape sending rfl (insert z right.freeNames)
    obtain ⟨receiveNames, receiver, receiveRest, _, receiveAway, _, receiveZ, receives, receiveBefore, receiveAfter⟩ :=
      input_shape receiving rfl (insert z left.freeNames ∪ sendNames.toFinset)
    have inner := comm_exposed (left := nuList sendNames (.par (.output x z) sendRest)) receives
      (Congruent.refl _) sendAfter receiveBefore receiveAfter sendAway ?_
    · exact reduces_of_congruent ((Congruent.par sendBefore (Congruent.refl _)).trans
        (Congruent.symm ⟨.nu_par z _ _ outside⟩)) (inner.map fun step => .res z _ _ step) (Congruent.refl _)
    · refine Finset.disjoint_left.mpr fun name restricted inside => ?_
      rcases Finset.mem_union.mp inside with free | bound
      · by_cases isZ : name = z
        · exact receiveZ (isZ ▸ List.mem_toFinset.mp restricted)
        · refine Finset.disjoint_left.mp receiveAway restricted (Finset.mem_union_left _ ?_)
          refine Finset.mem_insert_of_mem ?_
          rw [sendBefore.freeNames_eq]
          simp only [Process.freeNames, Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨free, isZ⟩
      · exact Finset.disjoint_left.mp receiveAway restricted (Finset.mem_union_right _ bound)
  | @closeRight left left' right right' x z receiving sending outside _ _ =>
    intro _
    obtain ⟨sendNames, sendRest, _, sendAway, _, sendZ, _, sendBefore, sendAfter⟩ :=
      boundOutput_shape sending rfl (insert z left.freeNames)
    obtain ⟨receiveNames, receiver, receiveRest, _, receiveAway, _, receiveZ, receives, receiveBefore, receiveAfter⟩ :=
      input_shape receiving rfl (insert z right.freeNames ∪ sendNames.toFinset)
    have inner := comm_exposed (left := nuList sendNames (.par (.output x z) sendRest)) receives
      (Congruent.refl _) sendAfter receiveBefore receiveAfter sendAway ?_
    · exact reduces_of_congruent ((Congruent.comm _ _).trans ((Congruent.par sendBefore (Congruent.refl _)).trans
        (Congruent.symm ⟨.nu_par z _ _ outside⟩))) (inner.map fun step => .res z _ _ step)
        (Congruent.nu z (Congruent.comm _ _))
    · refine Finset.disjoint_left.mpr fun name restricted inside => ?_
      rcases Finset.mem_union.mp inside with free | bound
      · by_cases isZ : name = z
        · exact receiveZ (isZ ▸ List.mem_toFinset.mp restricted)
        · refine Finset.disjoint_left.mp receiveAway restricted (Finset.mem_union_left _ ?_)
          refine Finset.mem_insert_of_mem ?_
          rw [sendBefore.freeNames_eq]
          simp only [Process.freeNames, Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨free, isZ⟩
      · exact Finset.disjoint_left.mp receiveAway restricted (Finset.mem_union_right _ bound)
  | res name _ _ holds => intro same; exact (holds same).map fun inner => .res name _ _ inner
  | «open» => intro same; cases same

end Mettapedia.Languages.ProcessCalculi.PiCalculus
