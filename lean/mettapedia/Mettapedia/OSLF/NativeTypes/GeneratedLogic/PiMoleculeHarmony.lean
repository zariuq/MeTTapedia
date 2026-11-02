import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiMoleculeSoundness
import Mettapedia.Languages.ProcessCalculi.PiCalculus.CongruenceSubstitution

/-!
# Harmony: π's reductions are the molecules' communications

Every reduction of π is realized by a communication inside one molecule (`reduces_realized`): a molecule denoting the
source, up to structural congruence, communicates to a molecule denoting the target. With soundness, a process reduces
to another exactly when some molecule denoting it communicates to one denoting the other (`reduces_iff_internal`).

The proof is by induction on the reduction, for every list of substitutions applied to both sides and every finite
set the restricted and lifted names must avoid (`Realized`):

- a communication is realized by the molecule of its receiver and sender, its binder renamed fresh for the
  substitutions (`substList_receive`);
- beside a parallel component, the component's lifting is merged in, renamed apart;
- under a restriction, the binder is renamed to a fresh name and joins the scope;
- structural congruence is absorbed, since it is closed under substitution (`congruent_substList`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners

open Mettapedia.Languages.ProcessCalculi.PiCalculus

/-! ## Names of lifted bodies and continuations -/

theorem bodyNames_of_congruent {scope : Finset Name} {primes : List Prime} {names : List Name} {process : Process}
    (congruent : Congruent process (nuList names (parList (primes.map Subtype.val)))) :
    (Molecule.mk scope primes).bodyNames ⊆ process.freeNames ∪ names.toFinset := by
  intro name member
  obtain ⟨prime, primeMem, present⟩ := Molecule.mem_bodyNames.mp member
  by_cases bound : name ∈ names.toFinset
  · exact Finset.mem_union_right _ bound
  · refine Finset.mem_union_left _ ?_
    rw [congruent.freeNames_eq, freeNames_nuList]
    refine Finset.mem_sdiff.mpr ⟨mem_freeNames_parList.mpr ⟨prime.1, ?_, present⟩, bound⟩
    exact List.mem_map.mpr ⟨prime, Multiset.mem_coe.mp primeMem, rfl⟩

/-- **A lifting's body names are the process's free names and the lifted ones.** -/
theorem lifts_bodyNames {process : Process} {scope : Finset Name} {body : Multiset Prime}
    (lifts : Lifts process scope body) : (Molecule.mk scope body).bodyNames ⊆ process.freeNames ∪ scope := by
  obtain ⟨names, primes, _, scopeEq, bodyEq, congruent⟩ := lifts_congruent lifts
  subst scopeEq bodyEq
  exact bodyNames_of_congruent congruent

/-- What a communication's continuation and kept server mention, the receiver and sender mention. -/
theorem fires_freeNames {receiver sender : Prime} {continuation : Process} {kept : Multiset Prime}
    (fires : Fires receiver sender continuation kept) :
    continuation.freeNames ⊆ receiver.1.freeNames ∪ sender.1.freeNames ∧
      ∀ prime ∈ kept, prime = receiver := by
  cases fires with
  | input x y z body =>
    refine ⟨fun name inside => ?_, by simp⟩
    have := Process.substitute_freeNames body y z inside
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at this
    simp only [Finset.mem_union, Process.freeNames, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    tauto
  | replicate x y z body =>
    refine ⟨fun name inside => ?_, fun prime member => Multiset.mem_singleton.mp member⟩
    have := Process.substitute_freeNames body y z inside
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton] at this
    simp only [Finset.mem_union, Process.freeNames, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    tauto

/-- **The body names after a communication** are the molecule's and the lifted ones. -/
theorem bodyNames_after {molecule : Molecule} {receiver sender : Prime} {continuation : Process}
    {kept : Multiset Prime} {lifted : Finset Name} {components : Multiset Prime}
    (contained : {receiver, sender} ≤ molecule.body) (fires : Fires receiver sender continuation kept)
    (lifts : Lifts continuation lifted components) (scope : Finset Name) :
    (Molecule.mk scope (molecule.body - {receiver, sender} + kept + components)).bodyNames ⊆
      molecule.bodyNames ∪ lifted := by
  obtain ⟨continuationNames, keptIsReceiver⟩ := fires_freeNames fires
  have receiverMem : receiver ∈ molecule.body := Multiset.subset_of_le contained (by simp)
  have senderMem : sender ∈ molecule.body := Multiset.subset_of_le contained (by simp)
  intro name member
  obtain ⟨prime, primeMem, present⟩ := Molecule.mem_bodyNames.mp member
  simp only [Multiset.mem_add] at primeMem
  rcases primeMem with (remaining | keptMem) | component
  · exact Finset.mem_union_left _
      (Molecule.mem_bodyNames.mpr ⟨prime, Multiset.mem_of_le (Multiset.sub_le_self _ _) remaining, present⟩)
  · obtain rfl := keptIsReceiver prime keptMem
    exact Finset.mem_union_left _ (Molecule.mem_bodyNames.mpr ⟨prime, receiverMem, present⟩)
  · rcases Finset.mem_union.mp (lifts_bodyNames lifts (Molecule.mem_bodyNames.mpr ⟨prime, component, present⟩)) with
      free | liftedName
    · rcases Finset.mem_union.mp (continuationNames free) with fromReceiver | fromSender
      · exact Finset.mem_union_left _ (Molecule.mem_bodyNames.mpr ⟨receiver, receiverMem, fromReceiver⟩)
      · exact Finset.mem_union_left _ (Molecule.mem_bodyNames.mpr ⟨sender, senderMem, fromSender⟩)
    · exact Finset.mem_union_right _ liftedName

/-! ## Realized reductions -/

/-- **A reduction realized by a molecule**: a molecule denoting the source, up to structural congruence, with a
communication inside it — receiver, sender, continuation and lifted names exposed — to a molecule denoting the target;
its restricted and lifted names avoid a given finite set. -/
def Realized (avoid : Finset Name) (source target : Process) : Prop :=
  ∃ (molecule : Molecule) (receiver sender : Prime) (continuation : Process) (kept : Multiset Prime)
    (lifted : Finset Name) (components : Multiset Prime),
    {receiver, sender} ≤ molecule.body ∧ Fires receiver sender continuation kept ∧
    Lifts continuation lifted components ∧ Disjoint lifted (molecule.scope ∪ molecule.bodyNames) ∧
    Disjoint molecule.scope avoid ∧ Disjoint lifted avoid ∧
    (∃ process, Denotes molecule process ∧ Congruent source process) ∧
    ∃ process, Denotes ⟨molecule.scope ∪ lifted, molecule.body - {receiver, sender} + kept + components⟩ process ∧
      Congruent target process

theorem Realized.congr {avoid : Finset Name} {source target source' target' : Process}
    (realized : Realized avoid source target) (sourceCongruent : Congruent source' source)
    (targetCongruent : Congruent target' target) : Realized avoid source' target' := by
  obtain ⟨molecule, receiver, sender, continuation, kept, lifted, components, contained, fires, lifts, fresh,
    scopeAvoids, liftedAvoids, ⟨process, denotes, congruent⟩, ⟨process', denotes', congruent'⟩⟩ := realized
  exact ⟨molecule, receiver, sender, continuation, kept, lifted, components, contained, fires, lifts, fresh,
    scopeAvoids, liftedAvoids, ⟨process, denotes, sourceCongruent.trans congruent⟩,
    ⟨process', denotes', targetCongruent.trans congruent'⟩⟩

theorem Realized.internal {avoid : Finset Name} {source target : Process} (realized : Realized avoid source target) :
    ∃ molecule result process process', Internal molecule result ∧ Denotes molecule process ∧
      Congruent source process ∧ Denotes result process' ∧ Congruent target process' := by
  obtain ⟨molecule, receiver, sender, continuation, kept, lifted, components, contained, fires, lifts, fresh,
    -, -, ⟨process, denotes, congruent⟩, ⟨process', denotes', congruent'⟩⟩ := realized
  exact ⟨molecule, _, process, process', .comm contained fires lifts fresh, denotes, congruent, denotes', congruent'⟩

theorem mem_bodyNames_add {scope : Finset Name} {left right : Multiset Prime} {name : Name} :
    name ∈ (Molecule.mk scope (left + right)).bodyNames ↔
      name ∈ (Molecule.mk ∅ left).bodyNames ∨ name ∈ (Molecule.mk ∅ right).bodyNames := by
  simp only [Molecule.mem_bodyNames, Multiset.mem_add]
  constructor
  · rintro ⟨prime, (inLeft | inRight), present⟩
    · exact Or.inl ⟨prime, inLeft, present⟩
    · exact Or.inr ⟨prime, inRight, present⟩
  · rintro (⟨prime, inLeft, present⟩ | ⟨prime, inRight, present⟩)
    · exact ⟨prime, Or.inl inLeft, present⟩
    · exact ⟨prime, Or.inr inRight, present⟩

theorem bodyNames_scope (scope scope' : Finset Name) (body : Multiset Prime) :
    (Molecule.mk scope body).bodyNames = (Molecule.mk scope' body).bodyNames := rfl

/-- **Beside a parallel component**: its lifting, renamed apart, merges into the realizing molecule. -/
theorem Realized.par {avoid : Finset Name} {source target : Process} (other : Process)
    (realized : Realized (avoid ∪ other.freeNames) source target) :
    Realized avoid (source ||| other) (target ||| other) := by
  obtain ⟨molecule, receiver, sender, continuation, kept, lifted, components, contained, fires, lifts, fresh,
    scopeAvoids, liftedAvoids, ⟨process, denotes, congruent⟩, ⟨process', denotes', congruent'⟩⟩ := realized
  obtain ⟨scope, body, otherLifts, otherAvoids⟩ :=
    lifts_exists _ other le_rfl (molecule.scope ∪ molecule.bodyNames ∪ lifted ∪ avoid)
  obtain ⟨names, primes, nodup, scopeEq, bodyEq, otherCongruent⟩ := lifts_congruent otherLifts
  have otherDenotes : Denotes ⟨scope, body⟩ (nuList names (parList (primes.map Subtype.val))) :=
    ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩
  have otherNames := lifts_bodyNames otherLifts
  have scopeOther : Disjoint molecule.scope other.freeNames := scopeAvoids.mono_right Finset.subset_union_right
  have liftedOther : Disjoint lifted other.freeNames := liftedAvoids.mono_right Finset.subset_union_right
  have away : ∀ name ∈ scope, name ∉ molecule.scope ∧ name ∉ molecule.bodyNames ∧ name ∉ lifted ∧ name ∉ avoid := by
    intro name member
    have := Finset.disjoint_left.mp otherAvoids member
    simp only [Finset.mem_union, not_or] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  have theirBody : ∀ name ∈ (Molecule.mk scope body).bodyNames, name ∈ other.freeNames ∨ name ∈ scope := fun name inside =>
    Finset.mem_union.mp (otherNames inside)
  have resultNames := bodyNames_after contained fires lifts (molecule.scope ∪ lifted)
  have apart : Apart molecule ⟨scope, body⟩ := by
    refine ⟨Finset.disjoint_left.mpr fun name restricted inside => ?_,
      Finset.disjoint_left.mpr fun name theirs inside => ?_⟩
    · rcases Finset.mem_union.mp inside with theirs | named
      · exact (away name theirs).1 restricted
      · rcases theirBody name named with free | theirs
        · exact Finset.disjoint_left.mp scopeOther restricted free
        · exact (away name theirs).1 restricted
    · rcases Finset.mem_union.mp inside with mine | named
      · exact (away name theirs).1 mine
      · exact (away name theirs).2.1 named
  have apart' : Apart ⟨molecule.scope ∪ lifted, molecule.body - {receiver, sender} + kept + components⟩
      ⟨scope, body⟩ := by
    refine ⟨Finset.disjoint_left.mpr fun name restricted inside => ?_,
      Finset.disjoint_left.mpr fun name theirs inside => ?_⟩
    · rcases Finset.mem_union.mp restricted with mine | liftedName
      · rcases Finset.mem_union.mp inside with theirs | named
        · exact (away name theirs).1 mine
        · rcases theirBody name named with free | theirs
          · exact Finset.disjoint_left.mp scopeOther mine free
          · exact (away name theirs).1 mine
      · rcases Finset.mem_union.mp inside with theirs | named
        · exact (away name theirs).2.2.1 liftedName
        · rcases theirBody name named with free | theirs
          · exact Finset.disjoint_left.mp liftedOther liftedName free
          · exact (away name theirs).2.2.1 liftedName
    · rcases Finset.mem_union.mp inside with ours | named
      · rcases Finset.mem_union.mp ours with mine | liftedName
        · exact (away name theirs).1 mine
        · exact (away name theirs).2.2.1 liftedName
      · rcases Finset.mem_union.mp (resultNames named) with mine | liftedName
        · exact (away name theirs).2.1 mine
        · exact (away name theirs).2.2.1 liftedName
  obtain ⟨merged, mergedDenotes, mergedCongruent⟩ := merge_denotes apart denotes otherDenotes
  obtain ⟨mergedResult, mergedResultDenotes, mergedResultCongruent⟩ := merge_denotes apart' denotes' otherDenotes
  refine ⟨⟨molecule.scope ∪ scope, molecule.body + body⟩, receiver, sender, continuation, kept, lifted, components,
    contained.trans (Multiset.le_add_right _ _), fires, lifts, ?_, ?_, liftedAvoids.mono_right Finset.subset_union_left,
    ⟨merged, mergedDenotes, (Congruent.par congruent otherCongruent).trans mergedCongruent⟩,
    ⟨mergedResult, ?_, (Congruent.par congruent' otherCongruent).trans mergedResultCongruent⟩⟩
  · refine Finset.disjoint_left.mpr fun name liftedName inside => ?_
    rcases Finset.mem_union.mp inside with restricted | named
    · rcases Finset.mem_union.mp restricted with mine | theirs
      · exact Finset.disjoint_left.mp fresh liftedName (Finset.mem_union_left _ mine)
      · exact (away name theirs).2.2.1 liftedName
    · rcases mem_bodyNames_add.mp named with mine | theirsNamed
      · exact Finset.disjoint_left.mp fresh liftedName (Finset.mem_union_right _ mine)
      · rcases theirBody name theirsNamed with free | theirs
        · exact Finset.disjoint_left.mp liftedOther liftedName free
        · exact (away name theirs).2.2.1 liftedName
  · refine Finset.disjoint_left.mpr fun name restricted inside => ?_
    rcases Finset.mem_union.mp restricted with mine | theirs
    · exact Finset.disjoint_left.mp scopeAvoids mine (Finset.mem_union_left _ inside)
    · exact (away name theirs).2.2.2 inside
  · have scopeEq' : molecule.scope ∪ lifted ∪ scope = molecule.scope ∪ scope ∪ lifted := by
      ext name
      simp only [Finset.mem_union]
      tauto
    have bodyEq' : molecule.body - {receiver, sender} + kept + components + body =
        molecule.body + body - {receiver, sender} + kept + components := by
      rw [← tsub_add_eq_add_tsub contained]
      ac_rfl
    simpa only [scopeEq', bodyEq'] using mergedResultDenotes

theorem denotes_insert {scope : Finset Name} {body : Multiset Prime} {process : Process} {fresh : Name}
    (denotes : Denotes ⟨scope, body⟩ process) (outside : fresh ∉ scope) :
    Denotes ⟨insert fresh scope, body⟩ (.nu fresh process) := by
  obtain ⟨names, primes, nodup, scopeEq, bodyEq, rfl⟩ := denotes
  exact ⟨fresh :: names, primes,
    List.nodup_cons.mpr ⟨fun member => outside (by have := List.mem_toFinset.mpr member; rw [scopeEq] at this; exact this),
      nodup⟩,
    by simp only [List.toFinset_cons]; exact congrArg _ scopeEq, bodyEq, rfl⟩

/-- **Under a restriction**: the binder joins the realizing molecule's scope. -/
theorem Realized.nu {avoid : Finset Name} {source target : Process} (fresh : Name)
    (realized : Realized (insert fresh avoid) source target) (outside : fresh ∉ avoid) :
    Realized avoid (.nu fresh source) (.nu fresh target) := by
  obtain ⟨molecule, receiver, sender, continuation, kept, lifted, components, contained, fires, lifts, freshLifted,
    scopeAvoids, liftedAvoids, ⟨process, denotes, congruent⟩, ⟨process', denotes', congruent'⟩⟩ := realized
  have notScope : fresh ∉ molecule.scope := fun inside =>
    Finset.disjoint_left.mp scopeAvoids inside (Finset.mem_insert_self _ _)
  have notLifted : fresh ∉ lifted := fun inside =>
    Finset.disjoint_left.mp liftedAvoids inside (Finset.mem_insert_self _ _)
  refine ⟨⟨insert fresh molecule.scope, molecule.body⟩, receiver, sender, continuation, kept, lifted, components,
    contained, fires, lifts, ?_, ?_, liftedAvoids.mono_right (Finset.subset_insert _ _),
    ⟨_, denotes_insert denotes notScope, Congruent.nu fresh congruent⟩, ⟨_, ?_, Congruent.nu fresh congruent'⟩⟩
  · refine Finset.disjoint_left.mpr fun name liftedName inside => ?_
    rcases Finset.mem_union.mp inside with restricted | named
    · rcases Finset.mem_insert.mp restricted with rfl | mine
      · exact notLifted liftedName
      · exact Finset.disjoint_left.mp freshLifted liftedName (Finset.mem_union_left _ mine)
    · exact Finset.disjoint_left.mp freshLifted liftedName (Finset.mem_union_right _ named)
  · refine Finset.disjoint_left.mpr fun name restricted inside => ?_
    rcases Finset.mem_insert.mp restricted with rfl | mine
    · exact outside inside
    · exact Finset.disjoint_left.mp scopeAvoids mine (Finset.mem_insert_of_mem inside)
  · have scopeEq : insert fresh molecule.scope ∪ lifted = insert fresh (molecule.scope ∪ lifted) := Finset.insert_union _ _ _
    rw [scopeEq]
    exact denotes_insert denotes' fun inside => (Finset.mem_union.mp inside).elim notScope notLifted

/-- **A communication** is realized by the molecule of its receiver and sender. -/
theorem realized_comm (substitutions : List (Name × Name)) (avoid : Finset Name) (x binder payload : Name)
    (body : Process) :
    Realized avoid (substList substitutions (Process.par (.input x binder body) (.output x payload)))
      (substList substitutions (body.substitute binder payload)) := by
  obtain ⟨fresh, freshNot⟩ := exists_fresh (body.freeNames ∪ substNames substitutions)
  simp only [Finset.mem_union, not_or] at freshNot
  obtain ⟨notBody, away⟩ := freshNot
  set receiver : Prime := ⟨.input (substName substitutions x) fresh (substList ((binder, fresh) :: substitutions) body),
    .input _ _ _⟩
  set sender : Prime := ⟨.output (substName substitutions x) (substName substitutions payload), .output _ _⟩
  have fires : Fires receiver sender
      ((substList ((binder, fresh) :: substitutions) body).substitute fresh (substName substitutions payload)) 0 :=
    .input _ _ _ _
  obtain ⟨lifted, components, lifts, liftedAvoids⟩ := lifts_exists _ _ le_rfl
    (avoid ∪ (Molecule.mk ∅ {receiver, sender}).bodyNames)
  obtain ⟨names, primes, nodup, scopeEq, bodyEq, liftedCongruent⟩ := lifts_congruent lifts
  refine ⟨⟨∅, {receiver, sender}⟩, receiver, sender, _, 0, lifted, components, le_rfl, fires, lifts, ?_,
    Finset.disjoint_empty_left _, liftedAvoids.mono_right Finset.subset_union_left,
    ⟨_, ⟨[], [receiver, sender], List.nodup_nil, rfl, rfl, rfl⟩, ?_⟩, ⟨_, ⟨names, primes, nodup, ?_, ?_, rfl⟩, ?_⟩⟩
  · refine liftedAvoids.mono_right fun name inside => ?_
    rcases Finset.mem_union.mp inside with impossible | named
    · simp at impossible
    · exact Finset.mem_union_right _ named
  · rw [substList_par, substList_output]
    exact Congruent.par (substList_input substitutions x binder fresh body notBody away)
      (Congruent.nilRight _).symm
  · rw [scopeEq]
    simp
  · rw [bodyEq]
    simp
  · exact (substList_receive substitutions body binder fresh payload notBody away).symm.trans liftedCongruent

/-! ## Harmony -/

/-- **Every reduction of π is realized by a communication inside a molecule**, under every list of substitutions and
avoiding every finite set of names. -/
theorem reduces_realized {source target : Process} (step : source ⇝ target) :
    ∀ (substitutions : List (Name × Name)) (avoid : Finset Name),
      Realized avoid (substList substitutions source) (substList substitutions target) := by
  induction step with
  | comm x binder payload body => exact fun substitutions avoid => realized_comm substitutions avoid x binder payload body
  | par_left left left' right _ holds =>
    intro substitutions avoid
    rw [substList_par, substList_par]
    exact Realized.par _ (holds substitutions (avoid ∪ (substList substitutions right).freeNames))
  | par_right left right right' _ holds =>
    intro substitutions avoid
    rw [substList_par, substList_par]
    exact (Realized.par _ (holds substitutions (avoid ∪ (substList substitutions left).freeNames))).congr
      (Congruent.comm _ _) (Congruent.comm _ _)
  | res binder body body' step holds =>
    intro substitutions avoid
    obtain ⟨fresh, freshNot⟩ := exists_fresh (body.freeNames ∪ substNames substitutions ∪ avoid)
    simp only [Finset.mem_union, not_or] at freshNot
    obtain ⟨⟨notBody, away⟩, outside⟩ := freshNot
    have notBody' : fresh ∉ body'.freeNames := fun inside => notBody (Reduces.freeNames_reduces step inside)
    exact (Realized.nu fresh (holds ((binder, fresh) :: substitutions) (insert fresh avoid)) outside).congr
      (substList_nu substitutions binder fresh body notBody away)
      (substList_nu substitutions binder fresh body' notBody' away)
  | struct first first' second' second before _ after holds =>
    exact fun substitutions avoid => (holds substitutions avoid).congr (congruent_substList before substitutions)
      (congruent_substList after substitutions).symm

/-- **Harmony**: a process reduces to another exactly when some molecule denoting it communicates internally to one
denoting the other, up to structural congruence. -/
theorem reduces_iff_internal {source target : Process} :
    Nonempty (source ⇝ target) ↔
      ∃ molecule result process process', Internal molecule result ∧ Denotes molecule process ∧
        Congruent source process ∧ Denotes result process' ∧ Congruent target process' := by
  constructor
  · rintro ⟨step⟩
    exact (reduces_realized step [] ∅).internal
  · rintro ⟨molecule, result, process, process', internal, denotes, congruent, denotes', congruent'⟩
    obtain ⟨reduct, reductDenotes, step⟩ := internal_reduces internal denotes
    exact reduces_of_congruent congruent step ((denotes_congruent reductDenotes denotes').trans congruent'.symm)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Pi.LeastPartners
