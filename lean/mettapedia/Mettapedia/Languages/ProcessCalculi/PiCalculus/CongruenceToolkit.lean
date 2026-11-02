import Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduction

/-!
# A toolkit for π's structural congruence

- **Parallel composition and restriction of lists** (`parList`, `nuList`), with their free names.
- **Structural congruence as a proposition** (`Congruent`): an equivalence and a congruence, preserving free names.
- **Lists up to congruence**: permutations of components and of restrictions (`parList_perm`, `nuList_perm`),
  concatenation (`parList_append`), scope extrusion over a list of names (`nuList_extrude`) and two scopes merged (`nuList_merge`).
- **Substitution** through the lists (`substitute_parList`, `substitute_nuList`), the identity substitution
  (`substitute_self`) and its size (`nodeCount_substitute`).
- **Reduction** up to congruence, under restrictions and beside a component.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

/-! ## Sizes -/

theorem nodeCount_substitute : (P : Process) → (y z : Name) → (P.substitute y z).nodeCount = P.nodeCount
  | .nil, _, _ => by rw [Process.substitute]
  | .output _ _, _, _ => by rw [Process.substitute]; rfl
  | .par P Q, y, z => by
    rw [Process.substitute]
    simp only [Process.nodeCount, nodeCount_substitute P y z, nodeCount_substitute Q y z]
  | .input x w P, y, z => by
    rw [Process.substitute]
    split_ifs <;> simp only [Process.nodeCount, nodeCount_substitute (P.renameFree w (P.freshFor y z)) y z,
      nodeCount_substitute P y z, Process.nodeCount_renameFree]
  | .nu x P, y, z => by
    rw [Process.substitute]
    split_ifs <;> simp only [Process.nodeCount, nodeCount_substitute (P.renameFree x (P.freshFor y z)) y z,
      nodeCount_substitute P y z, Process.nodeCount_renameFree]
  | .replicate x w P, y, z => by
    rw [Process.substitute]
    split_ifs <;> simp only [Process.nodeCount, nodeCount_substitute (P.renameFree w (P.freshFor y z)) y z,
      nodeCount_substitute P y z, Process.nodeCount_renameFree]
termination_by P => P.nodeCount
decreasing_by all_goals simp only [Process.nodeCount, Process.nodeCount_renameFree]; all_goals omega

/-! ## Lists of processes and names -/

/-- Parallel composition of a list of processes. -/
def parList : List Process → Process
  | [] => .nil
  | process :: processes => process ||| parList processes

/-- Restriction of a list of names. -/
def nuList : List Name → Process → Process
  | [], process => process
  | name :: names, process => .nu name (nuList names process)

theorem nuList_append (first second : List Name) (process : Process) :
    nuList (first ++ second) process = nuList first (nuList second process) := by
  induction first with
  | nil => rfl
  | cons name names holds => simp only [List.cons_append, nuList, holds]

theorem freeNames_nuList (names : List Name) (process : Process) :
    (nuList names process).freeNames = process.freeNames \ names.toFinset := by
  induction names with
  | nil => simp [nuList]
  | cons name names holds =>
    simp only [nuList, Process.freeNames, holds, List.toFinset_cons]
    ext other
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    tauto

theorem mem_freeNames_parList {processes : List Process} {name : Name} :
    name ∈ (parList processes).freeNames ↔ ∃ process ∈ processes, name ∈ process.freeNames := by
  induction processes with
  | nil => simp [parList, Process.freeNames]
  | cons process processes holds => simp [parList, Process.freeNames, holds]

/-! ## Structural congruence as a proposition -/

/-- **Structural congruence**, as a proposition. -/
def Congruent (first second : Process) : Prop := Nonempty (first ≡ second)

namespace Congruent

variable {first second third first' second' : Process}

theorem refl (process : Process) : Congruent process process := ⟨.refl process⟩

theorem symm : Congruent first second → Congruent second first := fun ⟨congruence⟩ => ⟨.symm _ _ congruence⟩

theorem trans : Congruent first second → Congruent second third → Congruent first third :=
  fun ⟨left⟩ ⟨right⟩ => ⟨.trans _ _ _ left right⟩

theorem par : Congruent first first' → Congruent second second' → Congruent (first ||| second) (first' ||| second') :=
  fun ⟨left⟩ ⟨right⟩ => ⟨.par_cong _ _ _ _ left right⟩

theorem nu (name : Name) : Congruent first second → Congruent (.nu name first) (.nu name second) :=
  fun ⟨inner⟩ => ⟨.nu_cong _ _ _ inner⟩

theorem input (x y : Name) : Congruent first second → Congruent (.input x y first) (.input x y second) :=
  fun ⟨inner⟩ => ⟨.input_cong _ _ _ _ inner⟩

theorem replicate (x y : Name) : Congruent first second → Congruent (.replicate x y first) (.replicate x y second) :=
  fun ⟨inner⟩ => ⟨.replicate_cong _ _ _ _ inner⟩

theorem comm (first second : Process) : Congruent (first ||| second) (second ||| first) := ⟨.par_comm _ _⟩

theorem assoc (first second third : Process) : Congruent ((first ||| second) ||| third) (first ||| (second ||| third)) :=
  ⟨.par_assoc _ _ _⟩

theorem nilLeft (process : Process) : Congruent (Process.nil ||| process) process := ⟨.par_nil_left _⟩

theorem nilRight (process : Process) : Congruent (process ||| Process.nil) process := ⟨.par_nil_right _⟩

theorem freeNames_eq : Congruent first second → first.freeNames = second.freeNames :=
  fun ⟨congruence⟩ => StructuralCongruence.freeNames_eq congruence

end Congruent

theorem nuList_congruent (names : List Name) {first second : Process} (congruent : Congruent first second) :
    Congruent (nuList names first) (nuList names second) := by
  induction names with
  | nil => exact congruent
  | cons name names holds => exact Congruent.nu name holds

theorem parList_append (first second : List Process) :
    Congruent (parList (first ++ second)) (parList first ||| parList second) := by
  induction first with
  | nil => exact (Congruent.nilLeft _).symm
  | cons process processes holds =>
    exact (Congruent.par (Congruent.refl process) holds).trans (Congruent.assoc _ _ _).symm

theorem parList_perm {first second : List Process} (perm : first.Perm second) :
    Congruent (parList first) (parList second) := by
  induction perm with
  | nil => exact Congruent.refl _
  | cons process _ holds => exact Congruent.par (Congruent.refl process) holds
  | swap left right rest =>
    exact (Congruent.assoc _ _ _).symm.trans
      ((Congruent.par (Congruent.comm _ _) (Congruent.refl _)).trans (Congruent.assoc _ _ _))
  | trans _ _ first second => exact first.trans second

theorem nuList_perm {first second : List Name} (perm : first.Perm second) (process : Process) :
    Congruent (nuList first process) (nuList second process) := by
  induction perm with
  | nil => exact Congruent.refl _
  | cons name _ holds => exact Congruent.nu name holds
  | swap left right rest => exact ⟨.nu_swap _ _ _⟩
  | trans _ _ first second => exact first.trans second

/-- **Scope extrusion over a list of names**: restrictions absent from a parallel component reach over it. -/
theorem nuList_extrude {names : List Name} {process other : Process} (fresh : Disjoint names.toFinset other.freeNames) :
    Congruent (nuList names process ||| other) (nuList names (process ||| other)) := by
  induction names with
  | nil => exact Congruent.refl _
  | cons name names holds =>
    have absent : name ∉ other.freeNames := Finset.disjoint_left.mp fresh (by simp)
    have rest : Disjoint names.toFinset other.freeNames := fresh.mono_left (by simp)
    exact (Congruent.symm ⟨.nu_par name (nuList names process) other absent⟩).trans (Congruent.nu name (holds rest))

/-- **Two scopes merge** when neither's names occur free in the other. -/
theorem nuList_merge {first second : List Name} {left right : Process}
    (firstFresh : Disjoint first.toFinset (nuList second right).freeNames)
    (secondFresh : Disjoint second.toFinset left.freeNames) :
    Congruent (nuList first left ||| nuList second right) (nuList (first ++ second) (left ||| right)) := by
  rw [nuList_append]
  refine (nuList_extrude firstFresh).trans (nuList_congruent first ?_)
  exact (Congruent.comm _ _).trans ((nuList_extrude secondFresh).trans (nuList_congruent second (Congruent.comm _ _)))

/-! ## Substitution through the lists -/

theorem substitute_self (process : Process) (name : Name) : process.substitute name name = process := by
  induction process with
  | nil => rw [Process.substitute]
  | output x z => rw [Process.substitute]; split_ifs <;> simp_all
  | par left right leftHolds rightHolds => rw [Process.substitute]; rw [leftHolds, rightHolds]
  | input x w body holds => rw [Process.substitute]; split_ifs <;> simp_all
  | nu x body holds => rw [Process.substitute]; split_ifs <;> simp_all
  | replicate x w body holds => rw [Process.substitute]; split_ifs <;> simp_all

theorem substitute_parList (processes : List Process) (old new : Name) :
    (parList processes).substitute old new = parList (processes.map fun process => process.substitute old new) := by
  induction processes with
  | nil => simp [parList]
  | cons process processes holds => simp [parList, holds]

theorem substitute_nuList {names : List Name} {old new : Name} (notOld : old ∉ names) (notNew : new ∉ names)
    (process : Process) : (nuList names process).substitute old new = nuList names (process.substitute old new) := by
  induction names with
  | nil => rfl
  | cons name names holds =>
    simp only [List.mem_cons, not_or] at notOld notNew
    simp only [nuList]
    rw [Process.substitute, if_neg (Ne.symm notOld.1), if_neg (fun both => notNew.1 both.1.symm),
      holds notOld.2 notNew.2]


theorem parList_forall₂ {first second : List Process} (pointwise : List.Forall₂ Congruent first second) :
    Congruent (parList first) (parList second) := by
  induction pointwise with
  | nil => exact Congruent.refl _
  | cons head _ holds => exact Congruent.par head holds

/-! ## Receivers and senders -/

/-- A receiver on a channel: an input or a replicated input. -/
def ReceivesOn (channel : Name) (process : Process) : Prop :=
  (∃ bound body, process = .input channel bound body) ∨ ∃ bound body, process = .replicate channel bound body

/-- A sender on a channel. -/
def SendsOn (channel : Name) (process : Process) : Prop := ∃ payload, process = .output channel payload

theorem receivesOn_substitute {channel old new : Name} {process : Process} (receives : ReceivesOn channel process)
    (different : channel ≠ old) : ReceivesOn channel (process.substitute old new) := by
  rcases receives with ⟨bound, body, rfl⟩ | ⟨bound, body, rfl⟩
  · rw [Process.substitute]
    split_ifs <;> simp_all [ReceivesOn]
  · rw [Process.substitute]
    split_ifs <;> simp_all [ReceivesOn]

theorem sendsOn_substitute {channel old new : Name} {process : Process} (sends : SendsOn channel process)
    (different : channel ≠ old) : SendsOn channel (process.substitute old new) := by
  obtain ⟨payload, rfl⟩ := sends
  rw [Process.substitute]
  exact ⟨if payload = old then new else payload, by simp [different]⟩

/-! ## Reduction up to congruence -/

theorem reduces_of_congruent {first first' second' second : Process} (before : Congruent first first')
    (step : Nonempty (first' ⇝ second')) (after : Congruent second' second) : Nonempty (first ⇝ second) :=
  match before, step, after with
  | ⟨before⟩, ⟨step⟩, ⟨after⟩ => ⟨.struct _ _ _ _ before step after⟩

theorem reduces_nuList (names : List Name) {first second : Process} (step : Nonempty (first ⇝ second)) :
    Nonempty (nuList names first ⇝ nuList names second) := by
  induction names with
  | nil => exact step
  | cons name names holds => exact holds.map fun step => .res name _ _ step

theorem reduces_parLeft {first second : Process} (other : Process) (step : Nonempty (first ⇝ second)) :
    Nonempty ((first ||| other) ⇝ (second ||| other)) :=
  step.map fun step => .par_left _ _ _ step

end Mettapedia.Languages.ProcessCalculi.PiCalculus
