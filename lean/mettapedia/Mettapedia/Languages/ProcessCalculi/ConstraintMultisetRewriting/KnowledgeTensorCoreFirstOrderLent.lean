import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreFirstOrderIdentities

/-!
# What a run does not take may be lent

On occurrence identities the lent zone of the logical reading is a theorem about native runs.
Fix a set of present identities that a native run never takes. The run is then a run of the
zoned calculus that owns only the other identities and has the fixed ones lent: it may read
them, its checks see them, and it leaves them.

* `firesUnder_lent_of_valid`, `valid_of_firesUnder_lent`: one firing, in both directions.
* `lent_run_iff_zoned_proof`: **native runs that take nothing from a set of present identities
  and end in consistent knowledge are exactly the graded proofs under that set as lent zone**,
  from the remaining identities, with the same firings in the same order.
* `checks_gives_lent_proof`: **the context of a placement is a lent zone.** A local run whose
  grade admits a context is a graded proof that owns its own identities, has the other
  identities of the context lent, and starts from the meet of the two knowledges. Shared
  identities are allowed.
* `native_tensor_is_zoned_proof_on_identities`: the native tensor of two runs is a graded proof
  of the tensor sequent, with the firings of the first run and then those of the second.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic.LinearLogic
open _root_.CategoryTheory
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open GuardFreeProcessOrders (problem_eq added)
open FirstOrderNativeRuns
open KnowledgeTensorFirstOrder (knowledge)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- The identities a check reads: the taken ones, the rest of the owned ones and the lent ones
are all the present identities. -/
theorem lent_store {present taken lent : Finset O} (lentIn : lent ⊆ present)
    (takenIn : taken ⊆ present \ lent) :
    taken ∪ (((present \ lent) \ taken).val + lent.val).toFinset = present := by
  rw [Multiset.toFinset_add, Finset.val_toFinset, Finset.val_toFinset]
  ext occurrence
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (taken | ⟨⟨here, _⟩, _⟩ | lent)
    · exact (Finset.mem_sdiff.mp (takenIn taken)).1
    · exact here
    · exact lentIn lent
  · intro here
    by_cases lentHere : occurrence ∈ lent
    · exact Or.inr (Or.inr lentHere)
    · by_cases takenHere : occurrence ∈ taken
      · exact Or.inl takenHere
      · exact Or.inr (Or.inl ⟨⟨here, lentHere⟩, takenHere⟩)

/-- The rest of the owned identities and the lent ones, side by side. -/
theorem frame_lent_val (present taken lent : Finset O) :
    (((present \ lent) \ taken) ∪ lent).val = ((present \ lent) \ taken).val + lent.val := by
  have apart : Disjoint ((present \ lent) \ taken) lent :=
    Finset.disjoint_left.mpr fun _ member lentHere =>
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp member).1).2 lentHere
  rw [← Finset.disjUnion_eq_union _ _ apart]
  rfl

/-- The owned identities after a firing that takes nothing lent. -/
theorem owned_after {present taken made lent : Finset O} (fresh : Disjoint made present)
    (lentIn : lent ⊆ present) :
    ((present \ taken) ∪ made) \ lent = ((present \ lent) \ taken) ∪ made := by
  ext occurrence
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨here, untaken⟩ | made, unlent⟩
    · exact Or.inl ⟨⟨here, unlent⟩, untaken⟩
    · exact Or.inr made
  · rintro (⟨⟨here, unlent⟩, untaken⟩ | made)
    · exact ⟨Or.inl ⟨here, untaken⟩, unlent⟩
    · exact ⟨Or.inr made, fun lentHere => Finset.disjoint_left.mp fresh made (lentIn lentHere)⟩

variable (A : SubstitutionAction T S) (label : O → T)

/-- **An admitted firing that takes nothing from a set of present identities is a firing under
that set as lent zone.** -/
theorem firesUnder_lent_of_valid {J : Configuration T O} {f : Firing T S O} {lent : Finset O}
    (valid : f.Valid A label J) (lentIn : lent ⊆ J.present)
    (untaken : Disjoint f.selection.taken.toFinset lent) :
    (identityZoned A label).FiresUnder (a := ()) lent.val f (knowledge A J)
      (J.present \ lent).val (knowledge A (f.result label J))
      ((f.result label J).present \ lent).val := by
  have occurrences := valid.firing.occurrences
  have takenIn : f.selection.taken.toFinset ⊆ J.present \ lent := fun occurrence member =>
    Finset.mem_sdiff.mpr ⟨occurrences.taken_subset member,
      fun lentHere => Finset.disjoint_left.mp untaken member lentHere⟩
  have store := lent_store lentIn takenIn
  refine ⟨((J.present \ lent) \ f.selection.taken.toFinset).val, val_split takenIn, ?_, ?_, ?_,
    knowledge_result A label J f, ?_⟩
  · show f.selection.read.toFinset.val ≤
      ((J.present \ lent) \ f.selection.taken.toFinset).val + lent.val
    rw [← frame_lent_val]
    refine Finset.val_le_iff.mpr fun occurrence member => ?_
    by_cases lentHere : occurrence ∈ lent
    · exact Finset.mem_union_right _ lentHere
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨occurrences.kept_subset member, lentHere⟩,
          fun taken => Finset.disjoint_left.mp occurrences.apart taken member⟩)
  · exact ⟨valid.firing.take_distinct, valid.firing.output_distinct, valid.firing.take_length,
      valid.firing.read_length, valid.firing.outputs⟩
  · refine ⟨?_, ?_, ?_⟩
    · show Disjoint f.selection.made.toFinset (f.selection.taken.toFinset ∪
        (((J.present \ lent) \ f.selection.taken.toFinset).val + lent.val).toFinset)
      rw [store]
      exact occurrences.fresh
    · intro check member σ known
      have here := valid.firing.checks check member σ (models_problem_of_mem A label J f σ known)
      show check.Holds A σ label (f.selection.taken.toFinset ∪
        (((J.present \ lent) \ f.selection.taken.toFinset).val + lent.val).toFinset)
      rw [store]
      exact here
    · intro query member σ known
      have here := valid.observations query member σ (models_problem_of_mem A label J f σ known)
      show (query.atSolution σ).Holds label (f.selection.taken.toFinset ∪
        (((J.present \ lent) \ f.selection.taken.toFinset).val + lent.val).toFinset)
      rw [store]
      exact here
  · show (((J.present \ f.selection.taken.toFinset) ∪ f.selection.made.toFinset) \ lent).val =
      f.selection.made.toFinset.val +
        Multiset.map (fun atom : O => atom) ((J.present \ lent) \ f.selection.taken.toFinset).val
    have fresh : Disjoint f.selection.made.toFinset J.present := occurrences.fresh
    rw [owned_after fresh lentIn, Multiset.map_id']
    exact fire_val (fresh.mono_right Finset.sdiff_subset)

/-- **A firing under a lent zone that reaches consistent knowledge is an admitted firing that
takes nothing lent.** -/
theorem valid_of_firesUnder_lent (J : Configuration T O) (f : Firing T S O) {lent : Finset O}
    (lentIn : lent ⊆ J.present) {reached : Set S} {left : Multiset O}
    (fires : (identityZoned A label).FiresUnder (a := ()) lent.val f (knowledge A J)
      (J.present \ lent).val reached left)
    (consistent : reached.Nonempty) :
    f.Valid A label J ∧ Disjoint f.selection.taken.toFinset lent ∧
      reached = knowledge A (f.result label J) ∧
      left = ((f.result label J).present \ lent).val := by
  obtain ⟨frame, source, readable, shaped, checked, known, target⟩ := fires
  have sourced : (J.present \ lent).val = f.selection.taken.toFinset.val + frame := source
  have takenIn : f.selection.taken.toFinset ⊆ J.present \ lent :=
    Finset.val_le_iff.mp (sourced ▸ Multiset.le_add_right _ _)
  have whole : frame = ((J.present \ lent) \ f.selection.taken.toFinset).val := by
    rw [Finset.sdiff_val (J.present \ lent), sourced, add_tsub_cancel_left]
  subst whole
  have store := lent_store lentIn takenIn
  have untaken : Disjoint f.selection.taken.toFinset lent :=
    Finset.disjoint_left.mpr fun _ taken lentHere => (Finset.mem_sdiff.mp (takenIn taken)).2 lentHere
  have reads : f.selection.read.toFinset.val ≤
      ((J.present \ lent) \ f.selection.taken.toFinset).val + lent.val := readable
  rw [← frame_lent_val] at reads
  have readIn := Finset.val_le_iff.mp reads
  have shapes : f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
      f.rule.take.length = f.selection.taken.length ∧
      f.rule.read.length = f.selection.read.length ∧ f.selection.made.map label = f.rule.produce :=
    shaped
  have checks : Disjoint f.selection.made.toFinset (f.selection.taken.toFinset ∪
        (((J.present \ lent) \ f.selection.taken.toFinset).val + lent.val).toFinset) ∧
      (∀ check ∈ f.rule.checks,
        ∀ σ ∈ (knowledge A J ⊓ {σ | A.Models σ (added label f.rule f.selection)} : Set S),
          check.Holds A σ label (f.selection.taken.toFinset ∪
            (((J.present \ lent) \ f.selection.taken.toFinset).val + lent.val).toFinset)) ∧
      ∀ query ∈ f.queries,
        ∀ σ ∈ (knowledge A J ⊓ {σ | A.Models σ (added label f.rule f.selection)} : Set S),
          (query.atSolution σ).Holds label (f.selection.taken.toFinset ∪
            (((J.present \ lent) \ f.selection.taken.toFinset).val + lent.val).toFinset) := checked
  rw [store] at checks
  have reaches : reached = knowledge A (f.result label J) :=
    (show reached = knowledge A J ⊓ {σ | A.Models σ (added label f.rule f.selection)} from known).trans
      (knowledge_result A label J f).symm
  obtain ⟨witness, member⟩ := consistent
  have inResult : witness ∈ knowledge A (f.result label J) := reaches ▸ member
  have solved : A.Models witness (f.selection.problem label f.rule J) := inResult
  have keptIn : f.selection.read.toFinset ⊆ J.present := fun occurrence member => by
    rcases Finset.mem_union.mp (readIn member) with owned | lentHere
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp owned).1).1
    · exact lentIn lentHere
  have apart : Disjoint f.selection.taken.toFinset f.selection.read.toFinset :=
    Finset.disjoint_left.mpr fun occurrence taken read => by
      rcases Finset.mem_union.mp (readIn read) with owned | lentHere
      · exact (Finset.mem_sdiff.mp owned).2 taken
      · exact Finset.disjoint_left.mp untaken taken lentHere
  refine ⟨⟨⟨shapes.1, shapes.2.1, shapes.2.2.1, shapes.2.2.2.1, shapes.2.2.2.2,
    ⟨fun occurrence member => (Finset.mem_sdiff.mp (takenIn member)).1, keptIn, apart, checks.1, ?_⟩,
    ⟨witness, solved⟩,
    fun check member σ models => checks.2.1 check member σ (mem_of_models_problem A label J f σ models)⟩,
    fun query member σ models => checks.2.2 query member σ (mem_of_models_problem A label J f σ models)⟩,
    untaken, reaches, ?_⟩
  · intro query member
    simp [Selection.commit] at member
  · have made : left = f.selection.made.toFinset.val + Multiset.map (fun atom : O => atom)
        ((J.present \ lent) \ f.selection.taken.toFinset).val := target
    show left = (((J.present \ f.selection.taken.toFinset) ∪ f.selection.made.toFinset) \ lent).val
    rw [made, Multiset.map_id', owned_after checks.1 lentIn]
    exact (fire_val (checks.1.mono_right Finset.sdiff_subset)).symm

/-- A set of identities that a firing does not take stays present. -/
theorem lent_stays {J : Configuration T O} {f : Firing T S O} {lent : Finset O}
    (lentIn : lent ⊆ J.present) (untaken : Disjoint f.selection.taken.toFinset lent) :
    lent ⊆ (f.result label J).present := fun occurrence member => by
  show occurrence ∈ (J.present \ f.selection.taken.toFinset) ∪ f.selection.made.toFinset
  exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
    ⟨lentIn member, fun taken => Finset.disjoint_left.mp untaken taken member⟩)

/-- **A native run that takes nothing from a set of present identities is a run under that set
as lent zone.** -/
theorem runUnder_lent_of_native_run :
    ∀ {J : Configuration T O} (run : (firstOrder A label).toStep.Run J) (lent : Finset O),
      lent ⊆ J.present →
      (∀ f ∈ sites A label run, Disjoint f.selection.taken.toFinset lent) →
      ∃ along : (() : Unit) ⟶ (),
        (identityZoned A label).RunUnder () lent.val (knowledge A J) (J.present \ lent).val
          ((sites A label run).map (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) ()
          along (knowledge A run.last) (run.last.present \ lent).val
  | _, .nil J, _, _, _ => ⟨𝟙 (), KnowledgeTensor.ZonedSystem.RunUnder.done _ _ _ _⟩
  | J, .cons f allowed rest, lent, lentIn, untaken => by
      have here : Disjoint f.selection.taken.toFinset lent := untaken f List.mem_cons_self
      obtain ⟨along, later⟩ := runUnder_lent_of_native_run rest lent (lent_stays label lentIn here)
        (fun g member => untaken g (List.mem_cons_of_mem f member))
      have carried : Multiset.map (fun atom : O => atom) lent.val = lent.val := Multiset.map_id' _
      have later' : (identityZoned A label).RunUnder ()
          (Multiset.map (fun atom : O => atom) lent.val) (knowledge A (f.result label J))
          ((f.result label J).present \ lent).val
          ((sites A label rest).map (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) ()
          along (knowledge A rest.last) (rest.last.present \ lent).val := carried.symm ▸ later
      exact ⟨_, KnowledgeTensor.ZonedSystem.RunUnder.fire
        (firesUnder_lent_of_valid A label allowed lentIn here) later'⟩

/-- **A run under a lent zone that ends in consistent knowledge is a native run that takes
nothing lent.** -/
theorem native_run_of_runUnder_lent : ∀ (word : List (Firing T S O)) {J : Configuration T O}
    {lent : Finset O} {along : (() : Unit) ⟶ ()} {reached : Set S} {left : Multiset O},
    lent ⊆ J.present →
    (identityZoned A label).RunUnder () lent.val (knowledge A J) (J.present \ lent).val
      (word.map (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) () along reached left →
      reached.Nonempty →
      ∃ run : (firstOrder A label).toStep.Run J, sites A label run = word ∧
        (∀ f ∈ word, Disjoint f.selection.taken.toFinset lent) ∧ A.Consistent run.last.equations
  | [], J, _, _, _, _, _, zoned, consistent => by
      have refined := KnowledgeTensor.ZonedSystem.RunUnder.refines zoned
      obtain ⟨witness, member⟩ := consistent
      exact ⟨.nil J, rfl, fun _ member => (List.not_mem_nil member).elim, ⟨witness, refined member⟩⟩
  | f :: rest, J, lent, _, _, _, lentIn, zoned, consistent => by
      obtain ⟨declaration, middle, held, onward, same, _, fires, later⟩ :=
        KnowledgeTensor.ZonedSystem.RunUnder.cons_inv zoned
      have which : f = declaration := eq_of_heq (Sigma.mk.inj same).2
      subst which
      have refined := KnowledgeTensor.ZonedSystem.RunUnder.refines later
      have between : Set.Nonempty middle := consistent.mono refined
      obtain ⟨valid, untaken, reaches, holds⟩ :=
        valid_of_firesUnder_lent A label J f lentIn fires between
      subst reaches
      subst holds
      have carried : (identityZoned A label).carried ((identityZoned A label).extend (a := ()) f)
          lent.val = lent.val := Multiset.map_id' _
      have later' : (identityZoned A label).RunUnder () lent.val (knowledge A (f.result label J))
          ((f.result label J).present \ lent).val
          (rest.map (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) () onward _ _ :=
        carried ▸ later
      obtain ⟨run, word, others, solvable⟩ :=
        native_run_of_runUnder_lent rest (lent_stays label lentIn untaken) later' consistent
      refine ⟨.cons f valid run, congrArg (List.cons f) word, ?_, solvable⟩
      intro g member
      rcases List.mem_cons.mp member with rfl | later
      · exact untaken
      · exact others g later

/-- **What a run does not take may be lent.** Native runs with given firings that take nothing
from a set of present identities and end in consistent knowledge are exactly the graded proofs
under that set as lent zone, from the remaining identities, whose grade admits the empty extra
context and whose final knowledge is consistent. -/
theorem lent_run_iff_zoned_proof (J : Configuration T O) (lent : Finset O)
    (lentIn : lent ⊆ J.present) (word : List (Firing T S O)) :
    (∃ run : (firstOrder A label).toStep.Run J, sites A label run = word ∧
        (∀ f ∈ word, Disjoint f.selection.taken.toFinset lent) ∧
        A.Consistent run.last.equations) ↔
      ∃ (along : (() : Unit) ⟶ ()) (reached : Set S) (left : Multiset O)
        (grade : Multiset O → Prop), grade 0 ∧
          (identityZoned A label).Proves () lent.val (knowledge A J) (J.present \ lent).val grade
            (word.map (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) () along
            reached left ∧ reached.Nonempty := by
  constructor
  · rintro ⟨run, rfl, untaken, consistent⟩
    obtain ⟨along, zoned⟩ := runUnder_lent_of_native_run A label run lent lentIn untaken
    obtain ⟨grade, atZero, proof⟩ := KnowledgeTensor.ZonedSystem.RunUnder.proves zoned
    exact ⟨along, _, _, grade, atZero, proof, consistent⟩
  · rintro ⟨along, reached, left, grade, atZero, proof, consistent⟩
    have zoned := KnowledgeTensor.ZonedSystem.Proves.run proof 0 atZero
    rw [add_zero] at zoned
    exact native_run_of_runUnder_lent A label word lentIn zoned consistent

/-- The firings of a local run in the grade of a context take nothing from the context. -/
theorem untaken_of_checks : ∀ {left right : Configuration T O}
    (run : (firstOrder A label).toStep.Run left),
    (contextualRunInterpretation A label).Checks (left := left) (right := right) PUnit.unit run →
      ∀ f ∈ sites A label run, Disjoint f.selection.taken.toFinset right.present
  | _, _, .nil _, _, _, member => (List.not_mem_nil member).elim
  | _, _, .cons f _ rest, checked, g, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact checked.1.1
      · exact untaken_of_checks rest checked.2 g later

/-- **The context of a placement is a lent zone.** A local run whose grade admits a context is a
graded proof that owns the identities of its own configuration, has the other identities of the
context lent, and starts from the meet of the two knowledges. The two configurations may share
identities: a shared identity is owned by the run and is not taken by it. -/
theorem checks_gives_lent_proof {left right : Configuration T O}
    (run : (firstOrder A label).toStep.Run left)
    (checked : (contextualRunInterpretation A label).Checks (left := left) (right := right)
      PUnit.unit run) :
    ∃ (along : (() : Unit) ⟶ ()) (reached : Set S) (left' : Multiset O)
      (grade : Multiset O → Prop), grade 0 ∧
        (identityZoned A label).Proves () (right.present \ left.present).val
          (knowledge A left ⊓ knowledge A right) left.present.val grade
          ((sites A label run).map (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) ()
          along reached left' := by
  let plan := ContextualRunInterpretation.Plan.ofChecks (contextualRunInterpretation A label)
    (left := left) (right := right) PUnit.unit run checked
  have word := plan_sites A label PUnit.unit run plan
  have owned : (AnnotatedRuns.tensor left right).present \ (right.present \ left.present) =
      left.present := by
    show (left.present ∪ right.present) \ (right.present \ left.present) = left.present
    ext occurrence
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨here | there, outside⟩
      · exact here
      · by_contra absent
        exact outside ⟨there, absent⟩
    · intro here
      exact ⟨Or.inl here, fun both => both.2 here⟩
  obtain ⟨along, zoned⟩ := runUnder_lent_of_native_run A label
    (plan.realize (contextualRunInterpretation A label) PUnit.unit run).execution
    (right.present \ left.present)
    (fun occurrence member => Finset.mem_union_right _ (Finset.mem_sdiff.mp member).1)
    (fun f member => (untaken_of_checks A label run checked f (word ▸ member)).mono_right
      Finset.sdiff_subset)
  rw [word, owned, knowledge_tensor] at zoned
  obtain ⟨grade, atZero, proof⟩ := KnowledgeTensor.ZonedSystem.RunUnder.proves zoned
  exact ⟨along, _, _, grade, atZero, proof⟩

/-- **The native tensor of two runs is a graded proof of the tensor sequent, on identities.** It
starts from the meet of the two knowledges and the identities of both configurations, and its
firings are those of the first run, then those of the second. No restriction on checks or
predicate queries, and no supply of occurrences. -/
theorem native_tensor_is_zoned_proof_on_identities {left right : Configuration T O}
    {first : (firstOrder A label).toStep.Run left} {second : (firstOrder A label).toStep.Run right}
    (plan : (contextualRunInterpretation A label).TensorPlan (contextualFlip A label) PUnit.unit
      first second)
    (consistent : A.Consistent
      (plan.realize (contextualRunInterpretation A label) (contextualFlip A label)).execution.last.equations) :
    ∃ (along : (() : Unit) ⟶ ()) (reached : Set S) (left' : Multiset O)
      (grade : Multiset O → Prop), grade 0 ∧
        (identityZoned A label).Proves () 0 (knowledge A left ⊓ knowledge A right)
          (left.present ∪ right.present).val grade
          ((sites A label first ++ sites A label second).map
            (Sigma.mk (β := KnowledgeTensor.Const (Firing T S O)) ())) () along reached left' ∧
        reached.Nonempty := by
  have proof := (native_run_iff_zoned_proof_on_identities A label (AnnotatedRuns.tensor left right)
    (sites A label first ++ sites A label second)).mp
    ⟨(plan.realize (contextualRunInterpretation A label) (contextualFlip A label)).execution,
      tensor_sites A label plan, consistent⟩
  rw [knowledge_tensor] at proof
  exact proof

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder
