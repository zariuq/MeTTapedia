import Mettapedia.GSLT.Contexts.ImageObservation

/-!
# The trace collapse

Bisimilarity as a probe sees it compares how two terms branch.  The coarsest
comparison the same probe supports forgets the branching: two terms are trace
equivalent when they can move along the same finite sequences of observers.

* Bisimilar terms are trace equivalent, for every probe.  The converse fails
  (a control is in the module of branching controls).
* For the probe whose only observers are the holes, a trace is a number of
  steps, and trace equivalence says the two terms can run for the same
  lengths.
* A map that preserves and reflects transitions neither adds nor loses trace
  equivalence, as it neither adds nor loses bisimilarity.
* Under an exhausting map the contexts of the target see the traces that the
  images of the source's contexts see.
* Trace comparison uses the same strong hosting and exhausting obligations.
  These force both comparisons to have the same embedding preorder, even
  though trace equivalence between terms is strictly coarser than bisimilarity.

Preservation of bisimilarity is a statement about the pairs that the finer
relation identifies.  It does not give preservation of trace equivalence,
which concerns more pairs: a morphism that adds a run out of one state of its
source preserves what every probe finds bisimilar and separates two terms
with the same traces (the control on transition tables extended at one
state).  Both preservations hold of the maps that preserve and reflect
transitions, and the two preorders are compared through those maps.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

namespace ContextTheory

variable {theory : ContextTheory.{u}}

namespace Probe

/-- A finite sequence of observers, each starting where the last ended. -/
inductive Path (probe : theory.Probe) : probe.Index → probe.Index → Type u where
  | nil (index : probe.Index) : Path probe index index
  | cons {source middle target : probe.Index} (observer : probe.Observer source middle)
      (rest : Path probe middle target) : Path probe source target

variable (probe : theory.Probe)

/-- The number of observers on a path. -/
def Path.length : {source target : probe.Index} → probe.Path source target → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ rest => rest.length + 1

/-- The term moves along the path: placed in the first observer it steps, and
the result moves along the rest. -/
def HasTrace : {source target : probe.Index} → probe.Path source target →
    theory.Term (probe.interface source) → Prop
  | _, _, .nil _, _ => True
  | _, _, .cons observer rest, term =>
      ∃ next, theory.Transition term (probe.label observer) next ∧ HasTrace rest next

/-- Traces respect the static equivalence. -/
theorem hasTrace_of_equations {source target : probe.Index} (path : probe.Path source target)
    {left right : theory.Term (probe.interface source)}
    (equivalent : (theory.equations (probe.interface source)).r left right)
    (trace : probe.HasTrace path left) : probe.HasTrace path right := by
  induction path with
  | nil index => trivial
  | cons observer rest recurse =>
      obtain ⟨next, step, more⟩ := trace
      obtain ⟨next', step', nextEquivalent⟩ :=
        theory.rewrites_resp_left (theory.apply_resp _ equivalent) step
      exact ⟨next', step', recurse nextEquivalent more⟩

variable {probe}

/-- A trace of a term is a trace of every term bisimilar to it. -/
theorem Bisimilar.hasTrace {source target : probe.Index} (path : probe.Path source target)
    {left right : theory.Term (probe.interface source)}
    (bisimilar : probe.Bisimilar left right) (trace : probe.HasTrace path left) :
    probe.HasTrace path right := by
  induction path with
  | nil index => trivial
  | cons observer rest recurse =>
      obtain ⟨relation, ⟨forward, backward⟩, related⟩ := bisimilar
      obtain ⟨next, step, more⟩ := trace
      obtain ⟨next', step', nextRelated⟩ := forward related observer step
      exact ⟨next', step', recurse ⟨relation, ⟨forward, backward⟩, nextRelated⟩ more⟩

variable (probe)

/-- **Trace equivalence as a probe sees it**: the two terms move along the
same sequences of observers. -/
def TraceEquivalent {index : probe.Index}
    (left right : theory.Term (probe.interface index)) : Prop :=
  ∀ {target : probe.Index} (path : probe.Path index target),
    probe.HasTrace path left ↔ probe.HasTrace path right

variable {probe}

/-- **Bisimilar terms are trace equivalent.** -/
theorem Bisimilar.traceEquivalent {index : probe.Index}
    {left right : theory.Term (probe.interface index)}
    (bisimilar : probe.Bisimilar left right) : probe.TraceEquivalent left right :=
  fun path => ⟨bisimilar.hasTrace path, (bisimilar_symm bisimilar).hasTrace path⟩

theorem traceEquivalent_refl {index : probe.Index}
    (term : theory.Term (probe.interface index)) : probe.TraceEquivalent term term :=
  fun _ => Iff.rfl

theorem traceEquivalent_symm {index : probe.Index}
    {left right : theory.Term (probe.interface index)}
    (equivalent : probe.TraceEquivalent left right) : probe.TraceEquivalent right left :=
  fun path => (equivalent path).symm

theorem traceEquivalent_trans {index : probe.Index}
    {left middle right : theory.Term (probe.interface index)}
    (first : probe.TraceEquivalent left middle) (second : probe.TraceEquivalent middle right) :
    probe.TraceEquivalent left right :=
  fun path => (first path).trans (second path)

/-- Statically equivalent terms are trace equivalent. -/
theorem traceEquivalent_of_equations {index : probe.Index}
    {left right : theory.Term (probe.interface index)}
    (equivalent : (theory.equations (probe.interface index)).r left right) :
    probe.TraceEquivalent left right :=
  (probe.bisimilar_of_equations equivalent).traceEquivalent

end Probe

/-! ## The probe that sees reduction only -/

variable (theory)

/-- The term can make this many steps. -/
def RunsFor {interface : theory.Interface} : ℕ → theory.Term interface → Prop
  | 0, _ => True
  | count + 1, term => ∃ next, theory.rewrites term next ∧ RunsFor count next

/-- The path of the reduction probe that looks at a term this many times. -/
def reductionPath (interface : theory.reductionProbe.Index) :
    (count : ℕ) → theory.reductionProbe.Path interface interface
  | 0 => .nil (probe := theory.reductionProbe) interface
  | count + 1 =>
      .cons (probe := theory.reductionProbe) ⟨⟨rfl⟩⟩ (reductionPath interface count)

variable {theory}

/-- For the reduction probe, a trace is a number of steps. -/
theorem hasTrace_reductionProbe_iff {source target : theory.reductionProbe.Index}
    (path : theory.reductionProbe.Path source target)
    (term : theory.Term (theory.reductionProbe.interface source)) :
    theory.reductionProbe.HasTrace path term ↔ theory.RunsFor path.length term := by
  induction path with
  | nil index => exact Iff.rfl
  | cons observer rest recurse =>
      obtain ⟨⟨same⟩⟩ := observer
      cases same
      constructor
      · rintro ⟨next, step, more⟩
        exact ⟨next, (theory.transition_identity_iff).mp step, (recurse next).mp more⟩
      · rintro ⟨next, step, more⟩
        exact ⟨next, (theory.transition_identity_iff).mpr step, (recurse next).mpr more⟩

theorem length_reductionPath (interface : theory.Interface) (count : ℕ) :
    (theory.reductionPath interface count).length = count := by
  induction count with
  | zero => rfl
  | succ count recurse => exact congrArg (· + 1) recurse

/-- The reduction probe sees a term run for a number of steps along the path
of that length. -/
theorem hasTrace_reductionPath_iff {interface : theory.Interface} (count : ℕ)
    (term : theory.Term interface) :
    theory.reductionProbe.HasTrace (theory.reductionPath interface count) term ↔
      theory.RunsFor count term := by
  have traces := hasTrace_reductionProbe_iff (theory.reductionPath interface count) term
  rwa [length_reductionPath] at traces

/-- **Trace equivalence as the reduction probe sees it**: the two terms can
run for the same numbers of steps. -/
theorem reductionProbe_traceEquivalent_iff {interface : theory.Interface}
    {left right : theory.Term interface} :
    theory.reductionProbe.TraceEquivalent (index := interface) left right ↔
      ∀ count, theory.RunsFor count left ↔ theory.RunsFor count right := by
  constructor
  · intro equivalent count
    exact ((hasTrace_reductionPath_iff count left).symm.trans
      (equivalent (theory.reductionPath interface count))).trans
        (hasTrace_reductionPath_iff count right)
  · intro runs target path
    exact ((hasTrace_reductionProbe_iff path left).trans (runs path.length)).trans
      (hasTrace_reductionProbe_iff path right).symm

end ContextTheory

/-! ## Traces along a map -/

namespace ContextMap

variable {source middle target : ContextTheory.{u}} (map : ContextMap source target)

/-- Carry a path along the map. -/
def pushPath (probe : source.Probe) : {origin result : probe.Index} →
    probe.Path origin result → (map.push probe).Path origin result
  | _, _, .nil index => .nil (probe := map.push probe) index
  | _, _, .cons observer rest => .cons (probe := map.push probe) observer (pushPath probe rest)

/-- A path of the carried probe, as a path of the probe. -/
def pullPath (probe : source.Probe) : {origin result : (map.push probe).Index} →
    (map.push probe).Path origin result → probe.Path origin result
  | _, _, .nil index => .nil (probe := probe) index
  | _, _, .cons observer rest => .cons (probe := probe) observer (pullPath probe rest)

/-- Every path of the carried probe is a carried path. -/
theorem pushPath_pullPath (probe : source.Probe) {origin result : (map.push probe).Index}
    (path : (map.push probe).Path origin result) :
    map.pushPath probe (map.pullPath probe path) = path := by
  induction path with
  | nil index => rfl
  | cons observer rest recurse =>
      exact congrArg (ContextTheory.Probe.Path.cons (probe := map.push probe) observer) recurse

/-- A trace is carried to a trace of the image along the carried path. -/
theorem hasTrace_push_of_transitions (preserves : map.PreservesTransitions)
    (probe : source.Probe) {origin result : probe.Index} (path : probe.Path origin result)
    {term : source.Term (probe.interface origin)} (trace : probe.HasTrace path term) :
    (map.push probe).HasTrace (map.pushPath probe path) (map.term term) := by
  induction path with
  | nil index => exact True.intro
  | cons observer rest recurse =>
      obtain ⟨next, step, more⟩ := trace
      exact ⟨map.term next, preserves _ step, recurse more⟩

/-- A trace of the image along a carried path comes from a trace. -/
theorem hasTrace_of_push_of_transitions (reflects : map.ReflectsTransitions)
    (probe : source.Probe) {origin result : probe.Index} (path : probe.Path origin result)
    {term : source.Term (probe.interface origin)}
    (trace : (map.push probe).HasTrace (map.pushPath probe path) (map.term term)) :
    probe.HasTrace path term := by
  induction path with
  | nil index => exact True.intro
  | cons observer rest recurse =>
      obtain ⟨imageNext, imageStep, more⟩ := trace
      obtain ⟨next, step, equivalent⟩ := reflects _ imageStep
      exact ⟨next, step,
        recurse ((map.push probe).hasTrace_of_equations _ equivalent more)⟩

/-- **A map that preserves and reflects transitions neither adds nor loses
trace equivalence**, as any probe sees it. -/
theorem traceEquivalent_push_iff_of_transitions (preserves : map.PreservesTransitions)
    (reflects : map.ReflectsTransitions) (probe : source.Probe) {index : probe.Index}
    {left right : source.Term (probe.interface index)} :
    (map.push probe).TraceEquivalent (index := index) (map.term left) (map.term right) ↔
      probe.TraceEquivalent left right := by
  constructor
  · intro equivalent result path
    exact ⟨fun trace => map.hasTrace_of_push_of_transitions reflects probe path
        ((equivalent (map.pushPath probe path)).mp
          (map.hasTrace_push_of_transitions preserves probe path trace)),
      fun trace => map.hasTrace_of_push_of_transitions reflects probe path
        ((equivalent (map.pushPath probe path)).mpr
          (map.hasTrace_push_of_transitions preserves probe path trace))⟩
  · intro equivalent result path
    rw [← map.pushPath_pullPath probe path]
    exact ⟨fun trace => map.hasTrace_push_of_transitions preserves probe _
        ((equivalent _).mp (map.hasTrace_of_push_of_transitions reflects probe _ trace)),
      fun trace => map.hasTrace_push_of_transitions preserves probe _
        ((equivalent _).mpr (map.hasTrace_of_push_of_transitions reflects probe _ trace))⟩

/-- **When the image of every hole acts as the identity, the carried
reduction probe sees the runs of the target.** -/
theorem hasTrace_push_reductionPath_iff
    (identity : ∀ (origin : source.Interface) (term : target.Term (map.interface origin)),
      target.apply (map.context (source.identity origin)) term = term)
    {origin : source.Interface} (count : ℕ) (term : target.Term (map.interface origin)) :
    (map.push source.reductionProbe).HasTrace
        (map.pushPath source.reductionProbe (source.reductionPath origin count)) term ↔
      target.RunsFor count term := by
  induction count generalizing term with
  | zero => exact Iff.rfl
  | succ count recurse =>
      constructor
      · rintro ⟨next, step, more⟩
        have moved : target.rewrites term next := by
          have raw : target.rewrites
              (target.apply (map.context (source.identity origin)) term) next := step
          rwa [identity origin term] at raw
        exact ⟨next, moved, (recurse next).mp more⟩
      · rintro ⟨next, step, more⟩
        have raw : target.rewrites
            (target.apply (map.context (source.identity origin)) term) next := by
          rw [identity origin term]
          exact step
        exact ⟨next, raw, (recurse next).mpr more⟩

/-! ## Exhausting maps and traces -/

/-- Under an exhausting map every path of contexts of the target is matched,
on every term, by the image of a path of contexts of the source. -/
theorem Exhausting.path_on_terms (exhausting : map.Exhausting)
    {origin result : map.targetProbe.Index} (path : map.targetProbe.Path origin result) :
    ∃ image : (map.push source.fullProbe).Path origin result,
      ∀ term : target.Term (map.targetProbe.interface origin),
        map.targetProbe.HasTrace path term ↔ (map.push source.fullProbe).HasTrace image term := by
  induction path with
  | nil index =>
      exact ⟨.nil (probe := map.push source.fullProbe) index, fun _ => Iff.rfl⟩
  | @cons origin between result observer rest recurse =>
      obtain ⟨image, agrees⟩ := recurse
      obtain ⟨label, acts⟩ := Exhausting.label_on_terms map exhausting observer
      refine ⟨.cons (probe := map.push source.fullProbe) label image, fun term => ⟨?_, ?_⟩⟩
      · rintro ⟨next, step, more⟩
        obtain ⟨next', step', equivalent⟩ :=
          target.rewrites_resp_left ((target.equations _).iseqv.symm (acts term)) step
        exact ⟨next', step',
          (agrees next').mp (map.targetProbe.hasTrace_of_equations rest equivalent more)⟩
      · rintro ⟨next, step, more⟩
        obtain ⟨next', step', equivalent⟩ := target.rewrites_resp_left (acts term) step
        exact ⟨next', step',
          map.targetProbe.hasTrace_of_equations rest equivalent ((agrees next).mpr more)⟩

/-- The image of a path of contexts of the source is a path of contexts of
the target with the same traces. -/
theorem path_of_image {origin result : (map.push source.fullProbe).Index}
    (image : (map.push source.fullProbe).Path origin result) :
    ∃ path : map.targetProbe.Path origin result,
      ∀ term : target.Term (map.targetProbe.interface origin),
        map.targetProbe.HasTrace path term ↔ (map.push source.fullProbe).HasTrace image term := by
  induction image with
  | nil index => exact ⟨.nil (probe := map.targetProbe) index, fun _ => Iff.rfl⟩
  | @cons origin between result observer rest recurse =>
      obtain ⟨path, agrees⟩ := recurse
      refine ⟨.cons (probe := map.targetProbe) (map.context observer) path,
        fun term => ⟨?_, ?_⟩⟩
      · rintro ⟨next, step, more⟩
        exact ⟨next, step, (agrees next).mp more⟩
      · rintro ⟨next, step, more⟩
        exact ⟨next, step, (agrees next).mpr more⟩

/-- **Exhausting: trace equivalence over the image of the source's contexts
is trace equivalence over the contexts of the target.** -/
theorem Exhausting.traceEquivalent_targetProbe_iff (exhausting : map.Exhausting)
    {origin : source.Interface} {left right : target.Term (map.interface origin)} :
    map.targetProbe.TraceEquivalent (index := origin) left right ↔
      (map.push source.fullProbe).TraceEquivalent (index := origin) left right := by
  constructor
  · intro equivalent result image
    obtain ⟨path, agrees⟩ := map.path_of_image image
    exact ((agrees left).symm.trans (equivalent path)).trans (agrees right)
  · intro equivalent result path
    obtain ⟨image, agrees⟩ := Exhausting.path_on_terms map exhausting path
    exact ((agrees left).trans (equivalent image)).trans (agrees right).symm

/-! ## The comparison of theories up to traces -/

/-- The map preserves trace equivalence, as every probe sees it. -/
def PreservesTraces : Prop :=
  ∀ (probe : source.Probe) {index : probe.Index}
    {left right : source.Term (probe.interface index)},
    probe.TraceEquivalent left right →
      (map.push probe).TraceEquivalent (index := index) (map.term left) (map.term right)

/-- A map that preserves and reflects transitions preserves trace
equivalence. -/
theorem preservesTraces_of_transitions (preserves : map.PreservesTransitions)
    (reflects : map.ReflectsTransitions) : map.PreservesTraces :=
  fun probe _ _ _ equivalent =>
    (map.traceEquivalent_push_iff_of_transitions preserves reflects probe).mpr equivalent

/-- Hosting supplies both operational laws needed for trace transport. -/
theorem Hosting.preservesTraces (hosting : map.Hosting) : map.PreservesTraces :=
  map.preservesTraces_of_transitions hosting.preserves hosting.reflects

theorem preservesTraces_id (theory : ContextTheory.{u}) :
    (ContextMap.id theory).PreservesTraces := by
  intro probe index left right equivalent result path
  have carried := equivalent ((ContextMap.id theory).pullPath probe path)
  have moves : ∀ {origin result : ((ContextMap.id theory).push probe).Index}
      (path : ((ContextMap.id theory).push probe).Path origin result)
      (term : theory.Term (probe.interface origin)),
      ((ContextMap.id theory).push probe).HasTrace path term ↔
        probe.HasTrace ((ContextMap.id theory).pullPath probe path) term := by
    intro origin result path
    induction path with
    | nil index => exact fun _ => Iff.rfl
    | cons observer rest recurse =>
        intro term
        constructor
        · rintro ⟨next, step, more⟩
          exact ⟨next, step, (recurse next).mp more⟩
        · rintro ⟨next, step, more⟩
          exact ⟨next, step, (recurse next).mpr more⟩
  exact ((moves path left).trans carried).trans (moves path right).symm

theorem PreservesTraces.comp {second : ContextMap middle target}
    {first : ContextMap source middle} (secondPreserves : second.PreservesTraces)
    (firstPreserves : first.PreservesTraces) : (second.comp first).PreservesTraces :=
  fun probe _ _ _ equivalent => secondPreserves (first.push probe) (firstPreserves probe equivalent)

end ContextMap

/-- **The comparison of theories up to traces**: some map between them
preserves trace equivalence and is hosting and exhausting. -/
def ContextTheory.TraceEmbeds (source target : ContextTheory.{u}) : Prop :=
  ∃ map : ContextMap source target, map.PreservesTraces ∧ map.Hosting ∧ map.Exhausting

theorem ContextTheory.traceEmbeds_refl (theory : ContextTheory.{u}) :
    theory.TraceEmbeds theory :=
  ⟨ContextMap.id theory, ContextMap.preservesTraces_id theory, ContextMap.hosting_id theory,
    ContextMap.exhausting_id theory⟩

theorem ContextTheory.traceEmbeds_trans {first second third : ContextTheory.{u}}
    (firstSecond : first.TraceEmbeds second) (secondThird : second.TraceEmbeds third) :
    first.TraceEmbeds third := by
  obtain ⟨lower, lowerTraces, lowerHosting, lowerExhausting⟩ := firstSecond
  obtain ⟨upper, upperTraces, upperHosting, upperExhausting⟩ := secondThird
  exact ⟨upper.comp lower, upperTraces.comp lowerTraces, upperHosting.comp lowerHosting,
    upperExhausting.comp lowerExhausting⟩

/-- With the same strong hosting contract on both sides, replacing
bisimilarity by traces does not change which theories embed. This concerns
admissible maps, not equality of the two observation relations on terms. -/
theorem ContextTheory.traceEmbeds_iff_embeds {source target : ContextTheory.{u}} :
    source.TraceEmbeds target ↔ source.Embeds target := by
  constructor
  · rintro ⟨map, _, hosting, exhausting⟩
    exact ⟨ContextMorphism.ofTransitions map hosting.preserves hosting.reflects,
      hosting, exhausting⟩
  · rintro ⟨morphism, hosting, exhausting⟩
    exact ⟨morphism.toContextMap, hosting.preservesTraces, hosting, exhausting⟩

/-- **A hosting and exhausting map compares the two theories at both
resolutions**: by bisimilarity and by traces. -/
theorem ContextTheory.embeds_and_traceEmbeds_of_hosting
    {source target : ContextTheory.{u}} (map : ContextMap source target)
    (hosting : map.Hosting) (exhausting : map.Exhausting) :
    source.Embeds target ∧ source.TraceEmbeds target :=
  ⟨⟨ContextMorphism.ofTransitions map hosting.preserves hosting.reflects, hosting, exhausting⟩,
    ⟨map, hosting.preservesTraces, hosting, exhausting⟩⟩

end Mettapedia.GSLT
