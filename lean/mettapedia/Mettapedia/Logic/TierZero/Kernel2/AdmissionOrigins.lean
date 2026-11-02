import Mettapedia.Logic.TierZero.Kernel2.Spaces

/-!
# Reducing promoted rules to their admitted origins

The basis contains occurrences of rules admitted by successful admission
steps. Its presentation retains the original rule instance operation; rule
names in the evolving board do not become additional axioms.

For claims without local dummy declarations, the existing promotion theorem
introduces only cited-term hypotheses. Composing it with cut removes promoted
rules from subsequent derivations. This concerns the existing kernel model;
soundness of the admitted presentation in a guest logic remains separate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins

variable {R : Type}

/-- Rules are identified by their admitted occurrence, retaining the source
name and the exact rule. This avoids imposing a second lookup policy. -/
abbrev basisPres (basis : List (R × Rule)) (fr : Frame) : Presentation.{0} where
  J := Tm
  R := Fin basis.length
  A := List Tm
  inst position arguments := basis[position].2.instance fr arguments
  side _ := false

theorem basis_mono {basis larger : List (R × Rule)} (included : basis ⊆ larger)
    {fr : Frame} {hyps : List Tm} {goal : Tm}
    (derivation : Derivable (basisPres basis fr) hyps goal) :
    Derivable (basisPres larger fr) hyps goal := by
  refine Derivable.rec (P := basisPres basis fr) (hyps := hyps)
    (motive := fun conclusion _ =>
    Derivable (basisPres larger fr) hyps conclusion) ?_ ?_ derivation
  · intro conclusion member
    exact .hyp member
  · intro position arguments premises conclusion instanceOf _ ih
    obtain ⟨index, within, selected⟩ := List.mem_iff_getElem.mp
      (included (List.getElem_mem position.isLt))
    have targetInstance : (basisPres larger fr).inst ⟨index, within⟩ arguments =
        some (premises, conclusion) := by
      change larger[index].2.instance fr arguments = some (premises, conclusion)
      rw [selected]
      exact instanceOf
    exact Derivable.rule (P := basisPres larger fr)
      (r := ⟨index, within⟩) targetInstance
      (fun premise member _ => ih premise member rfl)

/-- An independent interpretation of the hypotheses and admitted instances
extends to every derivation. The interpretation is not supplied by the
kernel or manufactured by admission permissions. -/
theorem basis_sound {basis : List (R × Rule)} {fr : Frame} {hyps : List Tm} {goal : Tm}
    (meaning : Tm → Prop)
    (rulesSound : ∀ (position : Fin basis.length) arguments premises conclusion,
      (basisPres basis fr).inst position arguments = some (premises, conclusion) →
        (∀ premise ∈ premises, meaning premise) → meaning conclusion)
    (hypothesesSound : ∀ hypothesis ∈ hyps, meaning hypothesis)
    (derivation : Derivable (basisPres basis fr) hyps goal) : meaning goal := by
  refine Derivable.rec (P := basisPres basis fr) (hyps := hyps)
    (motive := fun conclusion _ => meaning conclusion) ?_ ?_ derivation
  · intro conclusion member
    exact hypothesesSound conclusion member
  · intro position arguments premises conclusion instanceOf _ ih
    exact rulesSound position arguments premises conclusion instanceOf
      (fun premise member => ih premise member rfl)

/-- Eliminate an evolving rule table while retaining all cited terms. -/
def ReducesTo (env : Env R) (basis : List (R × Rule)) : Prop :=
  ∀ (fr : Frame) (hyps : List Tm) (goal : Tm),
    Derivable (presOf env fr) hyps goal →
      ∃ givens : List Tm, (∀ given ∈ givens, IsGiven given) ∧
        Derivable (basisPres basis fr) (hyps ++ givens) goal

theorem reduces_empty : ReducesTo (fun _ : R => none) [] := by
  intro fr hyps goal derivation
  refine Derivable.rec (P := presOf (fun _ : R => none) fr) (hyps := hyps)
    (motive := fun conclusion _ =>
    ∃ givens : List Tm, (∀ given ∈ givens, IsGiven given) ∧
      Derivable (basisPres ([] : List (R × Rule)) fr) (hyps ++ givens) conclusion)
    ?_ ?_ derivation
  · intro conclusion member
    exact ⟨[], by simp, .hyp (by simpa using member)⟩
  · intro name arguments premises conclusion instanceOf _ _
    cases instanceOf

/-- Rule-instance reductions lift to whole derivations by collecting their
finite cited-term hypotheses and applying the existing cut theorem. -/
theorem reduces_of_instances (env : Env R) (basis : List (R × Rule))
    (instances : ∀ (fr : Frame) (name : R) (arguments : List Tm)
      (premises : List Tm) (conclusion : Tm),
      (presOf env fr).inst name arguments = some (premises, conclusion) →
        ∃ givens : List Tm, (∀ given ∈ givens, IsGiven given) ∧
          Derivable (basisPres basis fr) (premises ++ givens) conclusion) :
    ReducesTo env basis := by
  intro fr hyps goal derivation
  refine Derivable.rec (P := presOf env fr) (hyps := hyps)
    (motive := fun conclusion _ =>
    ∃ givens : List Tm, (∀ given ∈ givens, IsGiven given) ∧
      Derivable (basisPres basis fr) (hyps ++ givens) conclusion) ?_ ?_ derivation
  · intro conclusion member
    exact ⟨[], by simp, .hyp (by simpa using member)⟩
  · intro name arguments premises conclusion instanceOf _ ih
    obtain ⟨ruleGivens, ruleGiven, ruleProof⟩ :=
      instances fr name arguments premises conclusion instanceOf
    obtain ⟨childGivens, childGiven, children⟩ :=
      collect_givens (P := basisPres basis fr) (G := IsGiven) premises
        (fun premise member => ih premise member rfl)
    refine ⟨childGivens ++ ruleGivens, ?_, ruleProof.cut ?_⟩
    · intro given member
      rcases List.mem_append.mp member with child | own
      · exact childGiven given child
      · exact ruleGiven given own
    · intro premise member
      rcases List.mem_append.mp member with child | own
      · exact derivable_mono (children premise child) (fun term present => by
          rcases List.mem_append.mp present with original | cited
          · exact List.mem_append_left _ original
          · exact List.mem_append_right _ (List.mem_append_left _ cited))
      · exact .hyp (List.mem_append_right _ (List.mem_append_right _ own))

variable [DecidableEq R]

omit [DecidableEq R] in
theorem derivable_env_mono {env larger : Env R}
    (included : ∀ name rule, env name = some rule → larger name = some rule)
    {fr : Frame} {hyps : List Tm} {goal : Tm}
    (derivation : Derivable (presOf env fr) hyps goal) :
    Derivable (presOf larger fr) hyps goal := by
  refine Derivable.rec (P := presOf env fr) (hyps := hyps)
    (motive := fun conclusion _ => Derivable (presOf larger fr) hyps conclusion)
    ?_ ?_ derivation
  · intro conclusion member
    exact .hyp member
  · intro name arguments premises conclusion instanceOf _ ih
    cases found : env name with
    | none => simp [presOf, found] at instanceOf
    | some rule =>
        have instanceThere : (presOf larger fr).inst name arguments = some (premises, conclusion) := by
          simpa only [presOf, included name rule found, found] using instanceOf
        exact .rule instanceThere (fun premise member _ => ih premise member rfl)

theorem derivable_rules_prefix {earlier later : List (R × Rule)} (prefixProof : earlier <+: later)
    {fr : Frame} {hyps : List Tm} {goal : Tm}
    (derivation : Derivable (presOf (envOf earlier) fr) hyps goal) :
    Derivable (presOf (envOf later) fr) hyps goal := by
  apply derivable_env_mono (env := envOf earlier) _ derivation
  intro name rule found
  obtain ⟨rest, rfl⟩ := prefixProof
  change earlier.lookup name = some rule at found
  change (earlier ++ rest).lookup name = some rule
  simp only [List.lookup_append, found, Option.some_or]

/-- An admitted rule extends the trusted basis. Instances of older rules
continue to reduce to the older basis; the new rule is an explicit root. -/
theorem reduces_add_rule {env : Env R} {basis : List (R × Rule)}
    (reduction : ReducesTo env basis) (name : R) (rule : Rule) :
    ReducesTo (extendEnv env name rule) (basis ++ [(name, rule)]) := by
  apply reduces_of_instances
  intro fr called arguments premises conclusion instanceOf
  by_cases same : called = name
  · subst called
    have rootInstance : rule.instance fr arguments = some (premises, conclusion) := by
      simpa [presOf, extendEnv] using instanceOf
    refine ⟨[], by simp, ?_⟩
    rw [List.append_nil]
    exact Derivable.rule (P := basisPres (basis ++ [(name, rule)]) fr)
      (r := ⟨basis.length, by simp⟩) (by simpa [basisPres] using rootInstance)
      (fun premise member _ => .hyp member)
  · have oldInstance : (presOf env fr).inst called arguments = some (premises, conclusion) := by
      simpa [presOf, extendEnv, same] using instanceOf
    obtain ⟨givens, given, derivation⟩ := reduction fr premises conclusion
      (.rule oldInstance (fun premise member _ => .hyp member))
    exact ⟨givens, given, basis_mono (fun _ member => List.mem_append_left _ member) derivation⟩

/-- Promotion extends the usable rule table but leaves the admitted basis
unchanged. Empty locals remove precisely the local-dummy alternative from
the existing conservativity theorem; cited terms remain explicit. -/
theorem reduces_promote {env : Env R} {basis : List (R × Rule)}
    (reduction : ReducesTo env basis) (determined : EnvDetermined env)
    (noNames : EnvNoFv env) {claim : Claim R}
    (accepted : claim.verdictT env = true) (discipline : claim.declaredB env = true)
    (closedNames : claim.noFvB = true) (noLocals : claim.locals = []) :
    ReducesTo (extendEnv env claim.id claim.toRule) basis := by
  intro fr hyps goal derivation
  obtain ⟨localGivens, localGiven, reduced⟩ :=
    derived_conservative env determined noNames accepted discipline closedNames derivation
  obtain ⟨priorGivens, priorGiven, priorProof⟩ := reduction fr (hyps ++ localGivens) goal reduced
  refine ⟨localGivens ++ priorGivens, ?_, ?_⟩
  · intro given member
    rcases List.mem_append.mp member with own | prior
    · rcases localGiven given own with cited | dummy
      · exact cited
      · simp [noLocals, IsLocalFact] at dummy
    · exact priorGiven given prior
  · simpa only [List.append_assoc] using priorProof

/-- Exactly the rule occurrence added by this admission, or no occurrence
when its name or declaration check refuses it. -/
def admittedBy (world : World R) : Admission R → List (R × Rule)
  | .rule name rule => if !world.used name && world.L.ruleOk rule then [(name, rule)] else []
  | _ => []

theorem reduces_admit {world : World R} {basis : List (R × Rule)}
    (reduction : ReducesTo world.env basis) (message : Admission R) :
    ReducesTo (admit world message).env (basis ++ admittedBy world message) := by
  cases message with
  | judgment head arity =>
      simp only [admit, admittedBy, List.append_nil]
      split <;> exact reduction
  | sort sort =>
      simp only [admit, admittedBy, List.append_nil]
      split <;> exact reduction
  | rule name rule =>
      simp only [admit, admittedBy]
      split
      · rename_i permitted
        have absent : world.L.rules.lookup name = none := by
          cases found : world.L.rules.lookup name with
          | none => rfl
          | some old => simp [World.used, found] at permitted
        change ReducesTo (envOf (world.L.rules ++ [(name, rule)])) (basis ++ [(name, rule)])
        rw [envOf_append_fresh absent]
        exact reduces_add_rule reduction name rule
      · simpa using reduction

theorem reduces_checkClaim {world : World R} {basis : List (R × Rule)}
    (reduction : ReducesTo world.env basis) (determined : EnvDetermined world.env)
    (noNames : EnvNoFv world.env) (claim : Claim R) (noLocals : claim.locals = []) :
    ReducesTo (checkClaim world claim).env basis := by
  rcases checkClaim_env world claim with same | ⟨extended, qualified, accepted, discipline⟩
  · rw [same]; exact reduction
  · rw [extended]
    rw [Claim.verdictR_eq_verdictT] at accepted
    exact reduces_promote reduction determined noNames accepted discipline
      (claimOk_noFv qualified) noLocals

/-- Pending claims have no local dummy declarations. Ordinary logical
hypotheses are still permitted and are retained by `ReducesTo`. -/
def NoLocalPending (world : World R) : Prop :=
  ∀ claim ∈ world.W ++ world.K, claim.locals = []

theorem noLocal_admit {world : World R} (pending : NoLocalPending world)
    (message : Admission R) : NoLocalPending (admit world message) := by
  cases message <;> simp only [admit] <;> split
  all_goals simp_all only [NoLocalPending, List.mem_append, List.append_nil]
  all_goals aesop

theorem noLocal_checkClaim {world : World R} (pending : NoLocalPending world)
    (claim : Claim R) (noLocals : claim.locals = []) :
    NoLocalPending (checkClaim world claim) := by
  unfold checkClaim
  split
  · exact pending
  · split
    · split
      all_goals simp_all only [NoLocalPending, List.mem_append, List.append_nil]
      all_goals aesop
    · split
      · exact pending
      · intro other member
        simp only [List.mem_append, List.mem_singleton] at member
        rcases member with old | old | same
        · exact pending other (List.mem_append_left _ old)
        · exact pending other (List.mem_append_right _ old)
        · simpa only [same] using noLocals

/-- The independent derivability invariant, together with reachability and
the structural condition used by the promotion reduction. -/
structure Accounted (basis : List (R × Rule)) (world : World R) : Prop where
  reachable : Reachable world
  reduction : ReducesTo world.env basis
  pending : NoLocalPending world

theorem accounted_empty : Accounted ([] : List (R × Rule)) World.empty := by
  refine ⟨Reachable.empty, ?_, ?_⟩
  · change ReducesTo (fun _ : R => none) []
    exact reduces_empty
  · simp [NoLocalPending, World.empty]

theorem accounted_client {basis : List (R × Rule)} {world : World R}
    (accounted : Accounted basis world) (action : ClientAct R)
    (noLocals : ∀ claim, action = .sendClaim claim → claim.locals = []) :
    Accounted basis (action.apply world) := by
  refine ⟨Reachable.client action accounted.reachable, ?_, ?_⟩
  · cases action <;> exact accounted.reduction
  · cases action with
    | sendAdmission message => exact accounted.pending
    | sendClaim claim =>
        intro other member
        simp only [ClientAct.apply, List.mem_append, List.mem_singleton] at member
        rcases member with (old | same) | old
        · exact accounted.pending other (List.mem_append_left _ old)
        · subst other
          exact noLocals claim rfl
        · exact accounted.pending other (List.mem_append_right _ old)

/-- The successful admission performed by the next kernel step. No claim
promotion contributes an entry to this list. -/
def admittedAt (world : World R) : List (R × Rule) :=
  match world.A with
  | message :: rest => admittedBy { world with A := rest } message
  | [] => []

theorem accounted_step {basis : List (R × Rule)} {world next : World R}
    (accounted : Accounted basis world) (step : kernelStep world = some next) :
    Accounted (basis ++ admittedAt world) next := by
  have nextReachable := Reachable.kernel accounted.reachable step
  unfold kernelStep at step
  cases admissions : world.A with
  | cons message rest =>
      rw [admissions] at step
      simp only [Option.some.injEq] at step
      subst next
      refine ⟨nextReachable, ?_, ?_⟩
      · simpa only [admittedAt, admissions] using
          (reduces_admit (world := { world with A := rest }) accounted.reduction message)
      · exact noLocal_admit (world := { world with A := rest }) accounted.pending message
  | nil =>
      rw [admissions] at step
      cases claims : world.W with
      | nil => rw [claims] at step; cases step
      | cons claim rest =>
          rw [claims] at step
          simp only [Option.some.injEq] at step
          subst next
          have noLocals : claim.locals = [] :=
            accounted.pending claim (by simp [claims])
          have remaining : NoLocalPending { world with A := [], W := rest } := by
            intro other member
            apply accounted.pending other
            simp only [List.mem_append] at member
            simp only [claims, List.mem_append, List.mem_cons]
            aesop
          refine ⟨nextReachable, ?_, noLocal_checkClaim remaining claim noLocals⟩
          simp only [admittedAt, admissions, List.append_nil]
          exact reduces_checkClaim (world := { world with A := [], W := rest }) accounted.reduction
            (reachable_rules_determined (w := world) accounted.reachable)
            (reachable_rules_noFv (w := world) accounted.reachable) claim noLocals

/-- Instrument the existing runner with its successful admission occurrences.
The world transition itself is exactly `kernelStep`. -/
def runObserved : ℕ → List (R × Rule) → World R → List (R × Rule) × World R
  | 0, basis, world => (basis, world)
  | fuel + 1, basis, world =>
      match kernelStep world with
      | none => (basis, world)
      | some next => runObserved fuel (basis ++ admittedAt world) next

theorem runObserved_world : ∀ (fuel : ℕ) (basis : List (R × Rule)) (world : World R),
    (runObserved fuel basis world).2 = runWorld fuel world
  | 0, _, _ => rfl
  | fuel + 1, basis, world => by
      simp only [runObserved, runWorld]
      cases step : kernelStep world with
      | none => rfl
      | some next => exact runObserved_world fuel (basis ++ admittedAt world) next

theorem runObserved_accounted : ∀ (fuel : ℕ) {basis : List (R × Rule)} {world : World R},
    Accounted basis world →
      Accounted (runObserved fuel basis world).1 (runObserved fuel basis world).2
  | 0, _, _, accounted => accounted
  | fuel + 1, basis, world, accounted => by
      simp only [runObserved]
      cases step : kernelStep world with
      | none => exact accounted
      | some next => exact runObserved_accounted fuel (accounted_step accounted step)

def observeAction (fuel : ℕ) (state : List (R × Rule) × World R) (action : ClientAct R) :
    List (R × Rule) × World R := runObserved fuel state.1 (action.apply state.2)

def observeProgram (fuel : ℕ) (actions : List (ClientAct R)) : List (R × Rule) × World R :=
  actions.foldl (observeAction fuel) ([], World.empty)

theorem foldObserved_world (fuel : ℕ) :
    ∀ (actions : List (ClientAct R)) (state : List (R × Rule) × World R),
      (actions.foldl (observeAction fuel) state).2 =
        actions.foldl (fun world action => runWorld fuel (action.apply world)) state.2
  | [], _ => rfl
  | action :: actions, state => by
      simp only [List.foldl_cons]
      rw [foldObserved_world fuel actions]
      simp only [observeAction, runObserved_world]

theorem foldObserved_accounted (fuel : ℕ) :
    ∀ (actions : List (ClientAct R)) (state : List (R × Rule) × World R),
      Accounted state.1 state.2 →
      (∀ claim, ClientAct.sendClaim claim ∈ actions → claim.locals = []) →
      Accounted (actions.foldl (observeAction fuel) state).1
        (actions.foldl (observeAction fuel) state).2
  | [], _, accounted, _ => accounted
  | action :: actions, state, accounted, noLocals => by
      simp only [List.foldl_cons]
      apply foldObserved_accounted fuel actions
      · exact runObserved_accounted fuel (accounted_client accounted action
          (fun claim same => noLocals claim (by simp [same])))
      · intro claim member
        exact noLocals claim (List.mem_cons_of_mem _ member)

/-- After an actual program run, every rule-table derivation reduces to the
successful admission occurrences. Promoted claims add no independent roots. -/
theorem observeProgram_accounted (fuel : ℕ) (actions : List (ClientAct R))
    (noLocals : ∀ claim, ClientAct.sendClaim claim ∈ actions → claim.locals = []) :
    Accounted (observeProgram fuel actions).1 (observeProgram fuel actions).2 :=
  foldObserved_accounted fuel actions ([], World.empty) accounted_empty noLocals

omit [DecidableEq R] in
/-- With no admitted rules, derivability contains exactly the supplied
hypotheses. A cycle of proposed claims cannot manufacture a root rule. -/
theorem empty_basis_iff {fr : Frame} {hyps : List Tm} {goal : Tm} :
    Derivable (basisPres ([] : List (R × Rule)) fr) hyps goal ↔ goal ∈ hyps := by
  constructor
  · intro derivation
    refine Derivable.rec (P := basisPres ([] : List (R × Rule)) fr) (hyps := hyps)
      (motive := fun conclusion _ => conclusion ∈ hyps) ?_ ?_ derivation
    · intro conclusion member
      exact member
    · intro position arguments premises conclusion _ _ _
      exact Fin.elim0 position
  · intro member
    exact .hyp member

end Mettapedia.Logic.TierZero.Kernel2.AdmissionOrigins
