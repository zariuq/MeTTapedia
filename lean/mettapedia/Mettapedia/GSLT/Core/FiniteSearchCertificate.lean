import Mettapedia.GSLT.Core.WellFoundedSearch

/-!
# Executable certificates for finite source observations

An unfolding certificate contains the actual source states and every physical
successor position. Its builder refuses an unfinished leaf. Failure to build
within a depth allowance says nothing about shortage or divergence.

The completed bag and work count are folds of that independently constructed
source tree. Their local unfolding laws are proved from the builder, including
at states reached after a pause. A source may have infinite computations at
other roots; it need not have a global normalization theorem.

The builder is a finite verification algorithm, not an eager prerequisite for
streaming evaluation. Live clients retain the original evaluator work.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.FiniteSearchCertificate

open BranchingTemporal

variable {Node Answer Value : Type*}

inductive Tree (Node : Type*) where
  | branch (root : Node) (children : List (Tree Node))

def Tree.root : Tree Node → Node
  | .branch root _ => root

def collect {Item Result : Type*} (f : Item → Option Result) :
    List Item → Option (List Result)
  | [] => some []
  | item :: rest => do
      let first ← f item
      let remaining ← collect f rest
      pure (first :: remaining)

theorem collect_iff {Item Result : Type*} (f : Item → Option Result)
    (items : List Item) (results : List Result) :
    collect f items = some results ↔
      List.Forall₂ (fun item result => f item = some result) items results := by
  induction items generalizing results with
  | nil => simp [collect, List.forall₂_nil_left_iff]
  | cons first rest ih =>
      cases found : f first with
      | none =>
          cases results <;> simp [collect, found, List.forall₂_cons, List.forall₂_nil_right_iff]
      | some result =>
          cases remaining : collect f rest with
          | none =>
              have noRest : ∀ ys, ¬ List.Forall₂ (fun x y => f x = some y) rest ys := by
                intro ys good
                have := (ih ys).mpr good
                simp [remaining] at this
              cases results <;> simp [collect, found, remaining,
                List.forall₂_cons, List.forall₂_nil_right_iff, noRest]
          | some tail =>
              have goodRest := (ih tail).mp remaining
              constructor
              · intro same
                have : result :: tail = results := by simpa [collect, found, remaining] using same
                subst results
                exact .cons found goodRest
              · intro matched
                cases matched with
                | cons same good =>
                    have := Option.some.inj (found.symm.trans same)
                    subst this
                    have := (ih _).mpr good
                    simp [collect, found, this]

def build (system : BranchingSystem Node Answer) : Nat → Node → Option (Tree Node)
  | 0, _ => none
  | depth + 1, node =>
      (collect (build system depth) (system.successors node)).map (.branch node)

theorem build_successors (system : BranchingSystem Node Answer) (depth : Nat)
    (node : Node) (tree : Tree Node) (built : build system (depth + 1) node = some tree) :
    ∃ children, tree = .branch node children ∧
      List.Forall₂ (fun child subtree => build system depth child = some subtree)
        (system.successors node) children := by
  simp only [build] at built
  obtain ⟨children, completed, same⟩ := Option.map_eq_some_iff.mp built
  exact ⟨children, same.symm, (collect_iff _ _ _).mp completed⟩

/-- Once a whole source tree has been certified, a larger allowance produces
that same tree, rather than adding spurious answers or rerunning a prefix. -/
theorem build_stable (system : BranchingSystem Node Answer) (depth extra : Nat)
    (node : Node) (tree : Tree Node) (built : build system depth node = some tree) :
    build system (depth + extra) node = some tree := by
  induction depth generalizing node tree with
  | zero => simp [build] at built
  | succ depth ih =>
      obtain ⟨children, rfl, matched⟩ := build_successors system depth node tree built
      have longer : List.Forall₂
          (fun child subtree => build system (depth + extra) child = some subtree)
          (system.successors node) children :=
        matched.imp (fun child subtree same => ih child subtree same)
      simp only [Nat.succ_add, build, (collect_iff _ _ _).mpr longer,
        Option.map_some]

def Certified (system : BranchingSystem Node Answer) (depth : Nat) (node : Node) : Prop :=
  ∃ tree, build system depth node = some tree

private theorem related_member_left {Item Result : Type*} {relation : Item → Result → Prop}
    {items : List Item} {results : List Result} (matched : List.Forall₂ relation items results)
    (item : Item) (member : item ∈ items) : ∃ result, relation item result := by
  induction matched with
  | nil => simp at member
  | @cons head result xs ys related rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst item; exact ⟨result, related⟩
      · exact ih later

theorem certified_children (system : BranchingSystem Node Answer) (depth : Nat)
    (node : Node) (certified : Certified system depth node) :
    ∀ child ∈ system.successors node, Certified system depth child := by
  obtain ⟨tree, built⟩ := certified
  cases depth with
  | zero => simp [build] at built
  | succ depth =>
      obtain ⟨children, _, matched⟩ := build_successors system depth node tree built
      intro child member
      obtain ⟨subtree, compiled⟩ := related_member_left matched child member
      exact ⟨subtree, by simpa using build_stable system depth 1 child subtree compiled⟩

theorem generated_certified (system : BranchingSystem Node Answer) (depth : Nat)
    (roots : List Node) (certified : ∀ root ∈ roots, Certified system depth root)
    (node : Node) (generated : Generated system roots node) : Certified system depth node := by
  induction generated with
  | root member => exact certified _ member
  | successor _ member ih => exact certified_children system depth _ ih _ member

def Tree.fold [AddCommMonoid Value] (output : Node → Value) : Tree Node → Value
  | .branch node children => output node + (children.map (Tree.fold output)).sum

def value [AddCommMonoid Value] (system : BranchingSystem Node Answer) (depth : Nat)
    (output : Node → Value) (node : Node) : Value :=
  ((build system depth node).map (Tree.fold output)).getD 0

theorem value_of_build [AddCommMonoid Value] (system : BranchingSystem Node Answer)
    (depth : Nat) (output : Node → Value) (node : Node) (tree : Tree Node)
    (built : build system depth node = some tree) :
    value system depth output node = Tree.fold output tree := by simp [value, built]

/-- The local additive law is a consequence of the actual source unfolding
certificate. It is not a required denotation supplied by a client. -/
theorem value_unfold [AddCommMonoid Value] (system : BranchingSystem Node Answer)
    (depth : Nat) (output : Node → Value) (node : Node)
    (certified : Certified system depth node) :
    value system depth output node = output node +
      ((system.successors node).map (value system depth output)).sum := by
  obtain ⟨tree, built⟩ := certified
  cases depth with
  | zero => simp [build] at built
  | succ depth =>
      obtain ⟨children, rfl, matched⟩ := build_successors system depth node tree built
      rw [value_of_build system (depth + 1) output node _ built, Tree.fold]
      congr 1
      apply congrArg List.sum
      have equalValues : List.Forall₂ (fun child subtree =>
          value system (depth + 1) output child = Tree.fold output subtree)
          (system.successors node) children := by
        apply matched.imp
        intro child subtree compiled
        exact value_of_build system (depth + 1) output child subtree
          (by simpa using build_stable system depth 1 child subtree compiled)
      have mapped : List.Forall₂ (· = ·)
          ((system.successors node).map (value system (depth + 1) output))
          (children.map (Tree.fold output)) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact equalValues
      have same : ((system.successors node).map (value system (depth + 1) output)) =
          children.map (Tree.fold output) := by simpa only [List.forall₂_eq_eq_eq] using mapped
      exact same.symm

def finiteBag (system : BranchingSystem Node Answer) (depth : Nat) : Node → Multiset Answer :=
  value system depth (fun node => optionBag (system.emit node))

def finiteWork (system : BranchingSystem Node Answer) (depth : Nat) : Node → Nat :=
  value system depth (fun _ => 1)

theorem bag_unfold (system : BranchingSystem Node Answer) (depth : Nat) (node : Node)
    (certified : Certified system depth node) :
    finiteBag system depth node = optionBag (system.emit node) +
      foldValues (finiteBag system depth) (system.successors node) := by
  simpa only [finiteBag, WellFoundedSearch.sum_eq_foldValues] using
    value_unfold system depth (fun node => optionBag (system.emit node)) node certified

theorem work_unfold (system : BranchingSystem Node Answer) (depth : Nat) (node : Node)
    (certified : Certified system depth node) :
    finiteWork system depth node = 1 +
      foldRanks (finiteWork system depth) (system.successors node) := by
  simpa only [finiteWork, WellFoundedSearch.sum_eq_foldRanks] using
    value_unfold system depth (fun _ => (1 : Nat)) node certified

def account (system : BranchingSystem Node Answer) (depth : Nat)
    (snapshot : BranchingTemporal.Snapshot Node Answer) : Multiset Answer :=
  eventBag snapshot.events + foldValues (finiteBag system depth) snapshot.frontier

/-- Reordering actual pending occurrences preserves the certificate-derived
residual meaning, including duplicates. -/
theorem reorder_account (system : BranchingSystem Node Answer) (depth : Nat)
    (events : List (Emission Node Answer)) (first second : List Node)
    (reordered : first.Perm second) :
    account system depth ⟨events, first⟩ = account system depth ⟨events, second⟩ := by
  exact congrArg (eventBag events + ·) (foldValues_perm _ reordered)

theorem account_tick (system : BranchingSystem Node Answer) (depth : Nat)
    (scheduler : Scheduler Node) (roots : List Node)
    (certified : ∀ root ∈ roots, Certified system depth root)
    (snapshot : BranchingTemporal.Snapshot Node Answer)
    (sound : snapshot.Sound system roots) :
    account system depth (BranchingTemporal.tick system scheduler snapshot) =
      account system depth snapshot := by
  cases ordered : scheduler.reorder snapshot.frontier with
  | nil => simp [BranchingTemporal.tick, ordered]
  | cons node pending =>
      have member : node ∈ snapshot.frontier :=
        scheduler.mem_reorder_iff.mp (by simp [ordered])
      have nodeCertified := generated_certified system depth roots certified node
        (sound.1 node member)
      have reorderValue := foldValues_perm (finiteBag system depth)
        (scheduler.reorder_complete snapshot.frontier)
      have integrateValue := foldValues_perm (finiteBag system depth)
        (scheduler.integrate_complete pending (system.successors node))
      unfold account
      rw [← reorderValue, ordered]
      simp only [BranchingTemporal.tick, ordered, eventBag_append, foldValues,
        integrateValue, foldValues_append]
      have emitted : eventBag
          (match system.emit node with | none => [] | some answer => [⟨node, answer⟩]) =
          optionBag (system.emit node) := by
        cases system.emit node <;> simp [eventBag, optionBag]
      change (eventBag snapshot.events + eventBag
        (match system.emit node with | none => [] | some answer => [⟨node, answer⟩])) +
          (foldValues (finiteBag system depth) pending +
            foldValues (finiteBag system depth) (system.successors node)) = _
      rw [emitted, bag_unfold system depth node nodeCertified]
      ac_rfl

/-- The native controller may change policy and memory at every turn. All
completed source trees remain accounted for by emitted and pending work. -/
theorem controlled_account (system : BranchingSystem Node Answer) (depth : Nat)
    {Memory : Type*} (controller : InferenceControl.Controller Node Answer Memory)
    (roots : List Node) (certified : ∀ root ∈ roots, Certified system depth root)
    (fuel : Nat) (snapshot : InferenceControl.Snapshot Node Answer Memory)
    (sound : snapshot.search.Sound system roots) :
    account system depth (InferenceControl.Snapshot.run system controller fuel snapshot).search =
      account system depth snapshot.search := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      exact (account_tick system depth
        (controller.scheduler (InferenceControl.Snapshot.run system controller fuel snapshot).memory)
        roots certified _ (InferenceControl.Snapshot.sound_run system controller sound fuel)).trans ih

/-- Completion exposes the independently unfolded source bag. Only the
requested roots need finite certificates; unrelated computations can diverge. -/
theorem completed_controller_observation (system : BranchingSystem Node Answer) (depth : Nat)
    {Memory : Type*} (controller : InferenceControl.Controller Node Answer Memory)
    (roots : List Node) (certified : ∀ root ∈ roots, Certified system depth root)
    (fuel : Nat) (closed : (InferenceControl.Snapshot.run system controller fuel
      (InferenceControl.Snapshot.initial controller roots)).search.frontier = []) :
    eventBag (InferenceControl.Snapshot.run system controller fuel
      (InferenceControl.Snapshot.initial controller roots)).search.events =
      foldValues (finiteBag system depth) roots := by
  have preserved := controlled_account system depth controller roots certified fuel
    (InferenceControl.Snapshot.initial controller roots) (initial_sound system roots)
  unfold account at preserved
  rw [closed] at preserved
  simpa [foldValues, InferenceControl.Snapshot.initial,
    BranchingTemporal.initial, eventBag] using preserved

/-- Pure completed observations agree without assuming a finite additive
denotation at every state of an open source language. Stream prefixes and
implementation costs are not observations of this theorem. -/
theorem completed_controllers_agree (system : BranchingSystem Node Answer) (depth : Nat)
    {FirstMemory SecondMemory : Type*}
    (first : InferenceControl.Controller Node Answer FirstMemory)
    (second : InferenceControl.Controller Node Answer SecondMemory)
    (roots : List Node) (certified : ∀ root ∈ roots, Certified system depth root)
    (firstFuel secondFuel : Nat)
    (firstClosed : (InferenceControl.Snapshot.run system first firstFuel
      (InferenceControl.Snapshot.initial first roots)).search.frontier = [])
    (secondClosed : (InferenceControl.Snapshot.run system second secondFuel
      (InferenceControl.Snapshot.initial second roots)).search.frontier = []) :
    eventBag (InferenceControl.Snapshot.run system first firstFuel
        (InferenceControl.Snapshot.initial first roots)).search.events =
      eventBag (InferenceControl.Snapshot.run system second secondFuel
        (InferenceControl.Snapshot.initial second roots)).search.events := by
  rw [completed_controller_observation system depth first roots certified firstFuel firstClosed,
    completed_controller_observation system depth second roots certified secondFuel secondClosed]

/-- A demanded prefix has the same independently reconstructed occurrence
bag plus the real retained frontier; no completed-answer cache replaces it. -/
theorem demanded_account (system : BranchingSystem Node Answer) (depth : Nat)
    {Memory : Type*} (controller : InferenceControl.Controller Node Answer Memory)
    (roots : List Node) (certified : ∀ root ∈ roots, Certified system depth root)
    (goal : List Answer → Bool) (fuel : Nat)
    (snapshot : InferenceControl.Snapshot Node Answer Memory)
    (sound : snapshot.search.Sound system roots) :
    account system depth (DemandExecution.run system controller goal fuel snapshot).search =
      account system depth snapshot.search := by
  obtain ⟨used, _, same⟩ := DemandExecution.run_prefix system controller goal fuel snapshot
  rw [same]
  exact controlled_account system depth controller roots certified used snapshot sound

theorem closed_observation (system : BranchingSystem Node Answer) (depth : Nat)
    {Memory : Type*} (controller : InferenceControl.Controller Node Answer Memory)
    (roots : List Node) (certified : ∀ root ∈ roots, Certified system depth root)
    (goal : List Answer → Bool) (fuel : Nat)
    (closed : (DemandExecution.run system controller goal fuel
      (InferenceControl.Snapshot.initial controller roots)).search.frontier = []) :
    eventBag (DemandExecution.run system controller goal fuel
      (InferenceControl.Snapshot.initial controller roots)).search.events =
      foldValues (finiteBag system depth) roots := by
  obtain ⟨used, _, same⟩ := DemandExecution.run_prefix system controller goal fuel
    (InferenceControl.Snapshot.initial controller roots)
  rw [same] at closed ⊢
  exact completed_controller_observation system depth controller roots certified used closed

theorem work_tick (system : BranchingSystem Node Answer) (depth : Nat)
    (scheduler : Scheduler Node) (roots : List Node)
    (certified : ∀ root ∈ roots, Certified system depth root)
    (snapshot : BranchingTemporal.Snapshot Node Answer)
    (sound : snapshot.Sound system roots) :
    foldRanks (finiteWork system depth) (BranchingTemporal.tick system scheduler snapshot).frontier =
      foldRanks (finiteWork system depth) snapshot.frontier - 1 := by
  cases ordered : scheduler.reorder snapshot.frontier with
  | nil =>
      have empty : snapshot.frontier = [] :=
        List.perm_nil.mp ((scheduler.reorder_complete _).symm.trans (by simp [ordered]))
      rw [BranchingTemporal.tick, ordered]
      simp [empty, foldRanks]
  | cons node pending =>
      have member : node ∈ snapshot.frontier :=
        scheduler.mem_reorder_iff.mp (by simp [ordered])
      have nodeCertified := generated_certified system depth roots certified node
        (sound.1 node member)
      have reorderValue := foldRanks_perm (finiteWork system depth)
        (scheduler.reorder_complete snapshot.frontier)
      have integrateValue := foldRanks_perm (finiteWork system depth)
        (scheduler.integrate_complete pending (system.successors node))
      rw [← reorderValue, ordered]
      simp only [BranchingTemporal.tick, ordered, integrateValue, foldRanks_append, foldRanks]
      rw [work_unfold system depth node nodeCertified]
      omega

theorem controlled_work (system : BranchingSystem Node Answer) (depth : Nat)
    {Memory : Type*} (controller : InferenceControl.Controller Node Answer Memory)
    (roots : List Node) (certified : ∀ root ∈ roots, Certified system depth root)
    (fuel : Nat) (snapshot : InferenceControl.Snapshot Node Answer Memory)
    (sound : snapshot.search.Sound system roots) :
    foldRanks (finiteWork system depth)
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.frontier =
      foldRanks (finiteWork system depth) snapshot.search.frontier - fuel := by
  induction fuel with
  | zero => simp [InferenceControl.Snapshot.run]
  | succ fuel ih =>
      change foldRanks (finiteWork system depth)
        (BranchingTemporal.tick system
          (controller.scheduler (InferenceControl.Snapshot.run system controller fuel snapshot).memory)
          (InferenceControl.Snapshot.run system controller fuel snapshot).search).frontier = _
      rw [work_tick system depth _ roots certified _
        (InferenceControl.Snapshot.sound_run system controller sound fuel), ih]
      omega

/-- The certificate constructs a sufficient exhaustion allowance. This is
independent of priority policy, ties, controller memory and stream order. -/
theorem completes_at_work (system : BranchingSystem Node Answer) (depth : Nat)
    {Memory : Type*} (controller : InferenceControl.Controller Node Answer Memory)
    (roots : List Node) (certified : ∀ root ∈ roots, Certified system depth root) :
    (InferenceControl.Snapshot.run system controller
      (foldRanks (finiteWork system depth) roots)
      (InferenceControl.Snapshot.initial controller roots)).search.frontier = [] := by
  let final := InferenceControl.Snapshot.run system controller
    (foldRanks (finiteWork system depth) roots)
    (InferenceControl.Snapshot.initial controller roots)
  have sound := InferenceControl.Snapshot.sound_run system controller
    (snapshot := InferenceControl.Snapshot.initial controller roots) (roots := roots)
    (initial_sound system roots)
    (foldRanks (finiteWork system depth) roots)
  have zero : foldRanks (finiteWork system depth) final.search.frontier = 0 := by
    have counted := controlled_work system depth controller roots certified
      (foldRanks (finiteWork system depth) roots)
      (InferenceControl.Snapshot.initial controller roots) (initial_sound system roots)
    simpa [final, InferenceControl.Snapshot.initial, BranchingTemporal.initial] using counted
  cases found : final.search.frontier with
  | nil => rfl
  | cons node rest =>
      have nodeCertified := generated_certified system depth roots certified node
        (sound.1 node (by change node ∈ final.search.frontier; simp [found]))
      rw [found, foldRanks, work_unfold system depth node nodeCertified] at zero
      omega

/-- The independently constructed finite work allowance is sufficient both
for closure and for the complete source observation. -/
theorem observation_at_work (system : BranchingSystem Node Answer) (depth : Nat)
    {Memory : Type*} (controller : InferenceControl.Controller Node Answer Memory)
    (roots : List Node) (certified : ∀ root ∈ roots, Certified system depth root) :
    let result := InferenceControl.Snapshot.run system controller
      (foldRanks (finiteWork system depth) roots)
      (InferenceControl.Snapshot.initial controller roots)
    result.search.frontier = [] ∧ eventBag result.search.events =
      foldValues (finiteBag system depth) roots := by
  have closed := completes_at_work system depth controller roots certified
  exact ⟨closed, completed_controller_observation system depth controller roots certified _ closed⟩

namespace Controls

def duplicates : BranchingSystem Nat Nat where
  emit node := if node = 0 then some 9 else none
  successors node := if node = 0 then [] else [0, 0]

example : Certified duplicates 2 1 := by
  exact ⟨.branch 1 [.branch 0 [], .branch 0 []], rfl⟩

example : finiteBag duplicates 2 1 = {9, 9} := by
  simp [finiteBag, value, build, collect, Tree.fold, duplicates, optionBag]
example : finiteWork duplicates 2 1 = 3 := by
  simp [finiteWork, value, build, collect, Tree.fold, duplicates]

/-- An unfinished compilation refuses a certificate rather than declaring
the unvisited children empty. -/
example : build duplicates 1 1 = none := by decide

def barren : BranchingSystem Nat Nat where
  emit _ := none
  successors node := [node + 1]

theorem barren_no_certificate (depth node : Nat) : build barren depth node = none := by
  induction depth generalizing node with
  | zero => rfl
  | succ depth ih =>
      rw [build]
      change (collect (build barren depth) [node + 1]).map (Tree.branch node) = none
      simp [collect, ih]

end Controls

end Mettapedia.GSLT.Core.FiniteSearchCertificate
