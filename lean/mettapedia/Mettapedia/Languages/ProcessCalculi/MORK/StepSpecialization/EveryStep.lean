import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Step
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Patterns
import Mettapedia.Languages.ProcessCalculi.MORK.StepSpecialization.Streaming
import Mettapedia.Languages.MeTTa.TransformQuantifiers

/-!
# An MM2 exec firing is an instance of the step

An MM2 exec `(exec LOC (, p₁ … pₙ) (O s₁ … sₖ))` in a set space `M` fires as MORK's kernel runs it
(`space.rs`: `metta_calculus`, `transform_multi_multi_io`; `sinks.rs`):

1. the exec leaves the space it writes (`btm.remove`);
2. its sources are matched against a copy of the space with the exec put back (`read_copy`), so an
   exec can read itself;
3. each match, in the order the query finds them, gives every sink its instance: an add is
   written at once into the space being written, any other sink stages it;
4. when the matches are done, the sinks other than adds publish, in their written order.

This file states that firing over any term layer (`morkFire`), and **the step's `every`**: all the
rows of the sources over the snapshot, each sink publishing what the rows give it
(`everyStep`). Its results:

* `step_of_everyRow`, `everyRow_of_step`: **a row of the `every` is exactly a step of the Prime
  calculus** (`GuardedMultisetRewriting.Step`, the two-line law) of the rule that reads the sources and
  produces the templates, over the snapshot. So the `every` over the snapshot fires every step of
  that rule at once.
* `morkFire_eq_everyStep`: **MORK's firing is the step's `every`** with the exec taken, the
  sources read over the snapshot (the exec included), and the sinks as its produce, publishing
  adds first, for **every** order and multiplicity in which the query enumerates the matches
  (`morkFire_enum_irrelevant`). The query's enumeration is a hypothesis: the matcher's own
  soundness and completeness are proved elsewhere (for trees, `Thinnings.treeMatcher_sound`,
  `treeMatcher_complete`).
* `leftToRight_eq_addsFirst`: the profile's declared publication law (each sink in its written
  order) agrees with the kernel's (adds first) when no removal meets an add written after it;
  `leftToRight_ne_addsFirst`: otherwise they differ, as `(O (- a) (+ a))` shows.
* `rowMajor_observes_order`: publishing each row's sinks as the row is taken (the row-major
  profile) depends on the order of the rows, so it is not a function of the step's rows.
* `morkStage_eq_of_mem_iff`: MORK's stages are union stages of `Streaming`, blind to the order
  and the repetitions of the matches.
* `everyStep_adds_eq_footprints`: when every sink is an add, the step's `every` is the existing
  bag meaning `TransformQuantifiers.Footprints.EveryStep` (the kernel row taking the exec), read
  as a set.
* `treeLayer_morkFire_eq_everyStep`: the same over the binding-tree term layer of thinnings.

Example: in `{(edge a b), (edge b c), X}` with `X = (exec 0 (, (edge $x $y) (edge $y $z))
(, (trans $x $z)))`, the one row is `{x ↦ a, y ↦ b, z ↦ c}`, a step of the rule reading the two
edges and producing `(trans a c)`; the firing leaves `{(edge a b), (edge b c), (trans a c)}`.

A template whose variables the sources do not bind writes nothing here (its instantiation is
undefined), where MORK writes it with fresh variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.StepSpecialization

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting

universe uV uT uP

variable {V : Type uV} {T : Type uT} {P : Type uP}

/-! ## The rows of `every` over the snapshot are steps -/

/-- The rule of an exec's sources: it takes nothing, reads the sources, checks nothing, and
produces the templates. -/
def readRule (sources templates : List P) : Rule V T P := ⟨[], sources, [], templates⟩

/-- **A row of `every` over a snapshot**: `σ` binds the sources' variables and nothing else, and
each source matches an atom of the snapshot. -/
def EveryRow (L : TermLayer V T P) (sources : List P) (snapshot : Finset T) (σ : Subst V T) :
    Prop :=
  (∀ v, (∀ p ∈ sources, v ∉ L.vars p) → σ v = none) ∧ ∀ p ∈ sources, ∃ t ∈ snapshot, L.Solves σ p t

theorem exists_forall₂_of_forall {α β : Type*} {R : α → β → Prop} {s : Finset β} :
    ∀ ps : List α, (∀ p ∈ ps, ∃ t ∈ s, R p t) → ∃ ts : List β, List.Forall₂ R ps ts ∧ ∀ t ∈ ts, t ∈ s
  | [], _ => ⟨[], .nil, by simp⟩
  | p :: ps, h => by
      obtain ⟨t, ts', rel⟩ := h p (by simp)
      obtain ⟨ts, rels, inS⟩ := exists_forall₂_of_forall ps fun q m => h q (by simp [m])
      refine ⟨t :: ts, .cons rel rels, fun u m => ?_⟩
      rcases List.mem_cons.mp m with rfl | m
      · exact ts'
      · exact inS u m

theorem exists_of_forall₂_of_mem {α β : Type*} {R : α → β → Prop} :
    ∀ {ps : List α} {ts : List β}, List.Forall₂ R ps ts → ∀ p ∈ ps, ∃ t ∈ ts, R p t
  | [], [], .nil, _, m => by simp at m
  | _ :: _, _ :: _, .cons rel rels, p, m => by
      rcases List.mem_cons.mp m with rfl | m
      · exact ⟨_, by simp, rel⟩
      · obtain ⟨t, tm, r⟩ := exists_of_forall₂_of_mem rels p m
        exact ⟨t, by simp [tm], r⟩

/-- **Every row of the `every` is a step of the read rule over the snapshot**: it adds the
instances of the templates and keeps everything. -/
theorem step_of_everyRow [DecidableEq T] {L : TermLayer V T P} {sources templates : List P}
    {M : Finset T} {σ : Subst V T} {made : List T} (row : EveryRow L sources M σ)
    (inst : instTemplate L σ templates = some made) :
    Step L (readRule sources templates) M.val (M.val + (made : Multiset T)) := by
  obtain ⟨only, solves⟩ := row
  obtain ⟨ts, rels, inM⟩ := exists_forall₂_of_forall sources solves
  have keptLe : ((ts.dedup : List T) : Multiset T) ≤ M.val := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (List.nodup_dedup ts))]
    intro t m
    exact inM t (List.mem_dedup.mp (Multiset.mem_coe.mp m))
  refine ⟨σ, M.val - (ts.dedup : Multiset T), 0, (ts.dedup : Multiset T), made, ?_, ?_, ?_, ?_, ?_,
    inst, ?_⟩
  · intro v notIn
    exact only v fun p m => notIn p (by simpa [readRule] using m)
  · exact ⟨[], .nil, rfl⟩
  · refine ⟨ts, rels, ?_, fun t m => Multiset.mem_coe.mpr (List.mem_dedup.mpr m)⟩
    exact Multiset.coe_le.mpr (List.dedup_sublist ts).subperm
  · rw [add_zero, tsub_add_cancel_of_le keptLe]
  · intro c m
    simp [readRule] at m
  · rw [tsub_add_cancel_of_le keptLe]

/-- **Every step of the read rule over the snapshot is a row of the `every`**: its substitution
is a row, and it adds exactly the instances of the templates. -/
theorem everyRow_of_step [DecidableEq T] {L : TermLayer V T P} {sources templates : List P}
    {M : Finset T} {N : Multiset T} (step : Step L (readRule sources templates) M.val N) :
    ∃ (σ : Subst V T) (made : List T), EveryRow L sources M σ ∧
      instTemplate L σ templates = some made ∧ N = M.val + (made : Multiset T) := by
  obtain ⟨σ, S, taken, kept, made, only, ⟨ts₀, rel₀, hts₀⟩, ⟨ts, rels, -, support⟩, hM, -, inst,
    hN⟩ := step
  cases rel₀
  simp only [Multiset.coe_nil] at hts₀
  subst hts₀
  rw [add_zero] at hM
  refine ⟨σ, made, ⟨fun v notIn => only v fun p m => notIn p (by simpa [readRule] using m),
    fun p m => ?_⟩, inst, by rw [hN, hM]⟩
  obtain ⟨t, tm, solves⟩ := exists_of_forall₂_of_mem rels p (by simpa [readRule] using m)
  refine ⟨t, ?_, solves⟩
  have inKept : t ∈ kept := support t tm
  have inVal : t ∈ M.val := by rw [hM]; exact Multiset.mem_add.mpr (Or.inr inKept)
  exact Finset.mem_val.mp inVal

/-! ## MM2 sinks as the step's produce -/

/-- **An MM2 sink**, read over a term layer.

* `add t`: `(+ t)`, or a template of `(, …)`;
* `remove t`: `(- t)`;
* `fold key value write`: `count`, `fmin`, `fmax`, `sum`, `fsum`, `fprod` and `pure`. Each row
  contributes the instance of `key` (the template with its hole marked) and of `value`; for each
  key, `write` makes the atom from the key and the distinct values it met. -/
inductive MSink (T : Type uT) (P : Type uP) where
  | add (template : P)
  | remove (template : P)
  | fold (key value : P) (write : T → Finset T → Option T)

namespace MSink

variable [DecidableEq T] (L : TermLayer V T P)

def isAdd : MSink T P → Bool
  | .add _ => true
  | _ => false

/-- What one row contributes to a sink's stage: the pair (key, value); an add or a removal
contributes its instance twice. -/
def contrib (σ : Subst V T) : MSink T P → Finset (T × T)
  | .add t => match L.inst σ t with
    | some u => {(u, u)}
    | none => ∅
  | .remove t => match L.inst σ t with
    | some u => {(u, u)}
    | none => ∅
  | .fold key value _ => match L.inst σ key, L.inst σ value with
    | some k, some v => {(k, v)}
    | _, _ => ∅

/-- What a fold writes from its stage: for each key, the atom `write` makes of it and the
distinct values staged with it. -/
def foldWrites (write : T → Finset T → Option T) (stage : Finset (T × T)) : Finset T :=
  (stage.image Prod.fst).biUnion fun k =>
    (write k ((stage.filter fun x => x.1 = k).image Prod.snd)).toFinset

/-- **A sink's publication**: an add joins its stage, a removal subtracts it, a fold joins what
it writes. -/
def publish (stage : Finset (T × T)) (s : Finset T) : MSink T P → Finset T
  | .add _ => s ∪ stage.image Prod.fst
  | .remove _ => s \ stage.image Prod.fst
  | .fold _ _ write => s ∪ foldWrites write stage

end MSink

variable [DecidableEq T] (L : TermLayer V T P)

/-! ### MORK's firing -/

/-- MORK's stage of one sink: the matches in the order the query enumerates them, each joined as
it arrives. -/
def morkStage (enum : List (Subst V T)) (k : MSink T P) : Finset (T × T) :=
  enum.foldl (fun st σ => st ∪ k.contrib L σ) ∅

/-- The space MORK writes while matching: each add's instance written as its match arrives. -/
def morkAdds (sinks : List (MSink T P)) (enum : List (Subst V T)) (live : Finset T) : Finset T :=
  enum.foldl (fun b σ => (sinks.filter (·.isAdd)).foldl
    (fun b k => b ∪ (k.contrib L σ).image Prod.fst) b) live

/-- MORK's finalization: the sinks other than adds, in index order, each from its stage. -/
def morkFinalize (enum : List (Subst V T)) : List (MSink T P) → Finset T → Finset T
  | [], s => s
  | k :: ks, s => morkFinalize enum ks (if k.isAdd then s else k.publish (morkStage L enum k) s)

/-- **MORK's firing of an exec** whose matches (over the read copy) the query enumerates as
`enum`: the exec leaves the space written, adds are written as matches arrive, the other sinks
are finalized in order. -/
def morkFire (exec : T) (sinks : List (MSink T P)) (enum : List (Subst V T)) (M : Finset T) :
    Finset T :=
  morkFinalize L enum sinks (morkAdds L sinks enum (M.erase exec))

/-- **What MORK matches against**: the space with the exec removed and put back. -/
def readCopy (exec : T) (M : Finset T) : Finset T := insert exec (M.erase exec)

theorem readCopy_eq {exec : T} {M : Finset T} (selected : exec ∈ M) : readCopy exec M = M :=
  Finset.insert_erase selected

/-! ### The step's `every` -/

/-- A sink's stage over a set of rows: the union of what each row contributes. -/
def stageOf (R : Finset (Subst V T)) (k : MSink T P) : Finset (T × T) :=
  R.biUnion fun σ => k.contrib L σ

/-- Publish sinks in order, each from its stage over the rows. -/
def publishSeq (R : Finset (Subst V T)) : List (MSink T P) → Finset T → Finset T
  | [], s => s
  | k :: ks, s => publishSeq R ks (k.publish (stageOf L R k) s)

/-- **Publication policies**: the GSLT profile declares each sink in its written order; MORK's
kernel writes every add first. -/
inductive Policy where
  | leftToRight
  | addsFirst
  deriving DecidableEq, Repr

/-- **The step's `every` with sinks as its produce**: the kernel takes `exec`; the rows `R` are
fired at once; the sinks publish what the rows give them, in the order of the policy. -/
def everyStep : Policy → T → List (MSink T P) → Finset (Subst V T) → Finset T → Finset T
  | .leftToRight, exec, sinks, R, M => publishSeq L R sinks (M.erase exec)
  | .addsFirst, exec, sinks, R, M =>
      publishSeq L R (sinks.filter fun k => !k.isAdd) (publishSeq L R (sinks.filter (·.isAdd))
        (M.erase exec))

/-! ### MORK's firing is the step's `every` -/

variable {L}

theorem mem_morkStage {enum : List (Subst V T)} {k : MSink T P} {y : T × T} :
    y ∈ morkStage L enum k ↔ ∃ σ ∈ enum, y ∈ k.contrib L σ := by
  unfold morkStage
  suffices h : ∀ (l : List (Subst V T)) (acc : Finset (T × T)),
      y ∈ l.foldl (fun st σ => st ∪ k.contrib L σ) acc ↔ y ∈ acc ∨ ∃ σ ∈ l, y ∈ k.contrib L σ by
    rw [h]; simp
  intro l
  induction l with
  | nil => intro acc; simp
  | cons σ l ih =>
      intro acc
      rw [List.foldl_cons, ih, Finset.mem_union]
      simp only [List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨τ, m, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨σ, Or.inl rfl, h⟩
        · exact Or.inr ⟨τ, Or.inr m, h⟩
      · rintro (h | ⟨τ, (rfl | m), h⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨τ, m, h⟩

theorem mem_stageOf {R : Finset (Subst V T)} {k : MSink T P} {y : T × T} :
    y ∈ stageOf L R k ↔ ∃ σ ∈ R, y ∈ k.contrib L σ := by
  simp [stageOf]

/-- **A streamed stage is the batch stage** when the enumeration holds exactly the rows, in any
order, with any repetitions. -/
theorem morkStage_eq_stageOf {enum : List (Subst V T)} {R : Finset (Subst V T)}
    (same : ∀ σ, σ ∈ enum ↔ σ ∈ R) (k : MSink T P) : morkStage L enum k = stageOf L R k := by
  ext y
  rw [mem_morkStage, mem_stageOf]
  exact ⟨fun ⟨σ, m, h⟩ => ⟨σ, (same σ).mp m, h⟩, fun ⟨σ, m, h⟩ => ⟨σ, (same σ).mpr m, h⟩⟩

theorem mem_foldl_adds {ks : List (MSink T P)} {σ : Subst V T} {x : T} :
    ∀ b : Finset T, x ∈ ks.foldl (fun b k => b ∪ (k.contrib L σ).image Prod.fst) b ↔
      x ∈ b ∨ ∃ k ∈ ks, x ∈ (k.contrib L σ).image Prod.fst := by
  induction ks with
  | nil => intro b; simp
  | cons k ks ih =>
      intro b
      rw [List.foldl_cons, ih, Finset.mem_union]
      simp only [List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨k', m, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨k, Or.inl rfl, h⟩
        · exact Or.inr ⟨k', Or.inr m, h⟩
      · rintro (h | ⟨k', (rfl | m), h⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨k', m, h⟩

theorem mem_morkAdds {sinks : List (MSink T P)} {enum : List (Subst V T)} {live : Finset T} {x : T} :
    x ∈ morkAdds L sinks enum live ↔
      x ∈ live ∨ ∃ σ ∈ enum, ∃ k ∈ sinks.filter (·.isAdd), x ∈ (k.contrib L σ).image Prod.fst := by
  unfold morkAdds
  suffices h : ∀ (l : List (Subst V T)) (b : Finset T),
      x ∈ l.foldl (fun b σ => (sinks.filter (·.isAdd)).foldl
        (fun b k => b ∪ (k.contrib L σ).image Prod.fst) b) b ↔
        x ∈ b ∨ ∃ σ ∈ l, ∃ k ∈ sinks.filter (·.isAdd), x ∈ (k.contrib L σ).image Prod.fst by
    exact h enum live
  intro l
  induction l with
  | nil => intro b; simp
  | cons σ l ih =>
      intro b
      rw [List.foldl_cons, ih, mem_foldl_adds]
      simp only [List.mem_cons]
      constructor
      · rintro ((h | ⟨k, km, h⟩) | ⟨τ, m, k, km, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨σ, Or.inl rfl, k, km, h⟩
        · exact Or.inr ⟨τ, Or.inr m, k, km, h⟩
      · rintro (h | ⟨τ, (rfl | m), k, km, h⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨k, km, h⟩)
        · exact Or.inr ⟨τ, m, k, km, h⟩

theorem mem_publishSeq_adds {R : Finset (Subst V T)} :
    ∀ (ks : List (MSink T P)), (∀ k ∈ ks, k.isAdd = true) → ∀ (s : Finset T) (x : T),
      x ∈ publishSeq L R ks s ↔ x ∈ s ∨ ∃ k ∈ ks, x ∈ (stageOf L R k).image Prod.fst
  | [], _, s, x => by simp [publishSeq]
  | k :: ks, adds, s, x => by
      have kAdd := adds k (by simp)
      have rest := mem_publishSeq_adds (R := R) ks (fun k' m => adds k' (by simp [m]))
      cases k with
      | add t =>
          simp only [publishSeq, MSink.publish]
          rw [rest, Finset.mem_union]
          simp only [List.mem_cons]
          constructor
          · rintro ((h | h) | ⟨k', m, h⟩)
            · exact Or.inl h
            · exact Or.inr ⟨.add t, Or.inl rfl, h⟩
            · exact Or.inr ⟨k', Or.inr m, h⟩
          · rintro (h | ⟨k', (rfl | m), h⟩)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr ⟨k', m, h⟩
      | remove t => simp [MSink.isAdd] at kAdd
      | fold key value write => simp [MSink.isAdd] at kAdd

theorem morkFinalize_eq {enum : List (Subst V T)} {R : Finset (Subst V T)}
    (same : ∀ σ, σ ∈ enum ↔ σ ∈ R) :
    ∀ (ks : List (MSink T P)) (s : Finset T),
      morkFinalize L enum ks s = publishSeq L R (ks.filter fun k => !k.isAdd) s
  | [], s => rfl
  | k :: ks, s => by
      by_cases h : k.isAdd = true
      · simp only [morkFinalize, h, if_true, List.filter_cons, Bool.not_true, Bool.false_eq_true,
          if_false]
        exact morkFinalize_eq same ks s
      · have h' : k.isAdd = false := by simpa using h
        simp only [morkFinalize, h', Bool.false_eq_true, if_false, List.filter_cons, Bool.not_false,
          if_true, publishSeq]
        rw [morkStage_eq_stageOf same]
        exact morkFinalize_eq same ks _

/-- **MORK's firing is the step's `every`.** Let the exec be selected from the space, `R` be the
rows of the sources over the snapshot (the exec included), and `enum` list the matches the query
finds over MORK's read copy, in any order and with any repetitions. Then MORK's firing (adds
written as matches arrive, the other sinks finalized in order) is the step's `every` publishing
adds first. -/
theorem morkFire_eq_everyStep {exec : T} {M : Finset T} (selected : exec ∈ M)
    {sources : List P} {sinks : List (MSink T P)} {enum : List (Subst V T)} {R : Finset (Subst V T)}
    (enumerates : ∀ σ, σ ∈ enum ↔ EveryRow L sources (readCopy exec M) σ)
    (rows : ∀ σ, σ ∈ R ↔ EveryRow L sources M σ) :
    morkFire L exec sinks enum M = everyStep L .addsFirst exec sinks R M := by
  have same : ∀ σ, σ ∈ enum ↔ σ ∈ R := fun σ => by
    rw [enumerates, rows, readCopy_eq selected]
  unfold morkFire everyStep
  rw [morkFinalize_eq same]
  congr 1
  ext x
  rw [mem_morkAdds, mem_publishSeq_adds _ (fun k m => (List.mem_filter.mp m).2)]
  constructor
  · rintro (h | ⟨σ, m, k, km, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨k, km, ?_⟩
      obtain ⟨y, ym, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨y, mem_stageOf.mpr ⟨σ, (same σ).mp m, ym⟩, rfl⟩
  · rintro (h | ⟨k, km, h⟩)
    · exact Or.inl h
    · obtain ⟨y, ym, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨σ, m, yc⟩ := mem_stageOf.mp ym
      exact Or.inr ⟨σ, (same σ).mpr m, k, km, Finset.mem_image.mpr ⟨y, yc, rfl⟩⟩

/-- **The order of the matches cannot be observed**: two enumerations of the matches give the
same firing. -/
theorem morkFire_enum_irrelevant {exec : T} {M : Finset T} (selected : exec ∈ M)
    {sources : List P} {sinks : List (MSink T P)} {enum enum' : List (Subst V T)}
    (enumerates : ∀ σ, σ ∈ enum ↔ EveryRow L sources (readCopy exec M) σ)
    (enumerates' : ∀ σ, σ ∈ enum' ↔ EveryRow L sources (readCopy exec M) σ)
    (R : Finset (Subst V T)) (rows : ∀ σ, σ ∈ R ↔ EveryRow L sources M σ) :
    morkFire L exec sinks enum M = morkFire L exec sinks enum' M := by
  rw [morkFire_eq_everyStep selected enumerates rows, morkFire_eq_everyStep selected enumerates' rows]

/-! ## The two publication laws -/

variable (L)

/-- No removal meets an add written after it: each removal's stage is disjoint from the stage of
every later add. -/
def NoRemovalMeetsLaterAdd (R : Finset (Subst V T)) : List (MSink T P) → Prop
  | [] => True
  | k :: ks => (∀ t, k = .remove t → ∀ a ∈ ks, a.isAdd = true →
      Disjoint ((stageOf L R k).image Prod.fst) ((stageOf L R a).image Prod.fst)) ∧
      NoRemovalMeetsLaterAdd R ks


/-- Publishing adds first into a space with more in it: a fold or an add commutes with adding,
and so does a removal disjoint from what is added. -/
theorem publish_union_comm {R : Finset (Subst V T)} {k : MSink T P} {s B : Finset T}
    (disjoint : ∀ t, k = .remove t → Disjoint ((stageOf L R k).image Prod.fst) B) :
    k.publish (stageOf L R k) (s ∪ B) = k.publish (stageOf L R k) s ∪ B := by
  cases k with
  | add t =>
      simp only [MSink.publish]
      rw [Finset.union_right_comm]
  | remove t =>
      simp only [MSink.publish]
      have d := disjoint t rfl
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, notIn⟩
        · exact Or.inl ⟨h, notIn⟩
        · exact Or.inr h
      · rintro (⟨h, notIn⟩ | h)
        · exact ⟨Or.inl h, notIn⟩
        · exact ⟨Or.inr h, Finset.disjoint_right.mp d h⟩
  | fold key value write =>
      simp only [MSink.publish]
      rw [Finset.union_right_comm]

theorem publishSeq_adds_union {R : Finset (Subst V T)} :
    ∀ (adds : List (MSink T P)) (s B : Finset T), (∀ k ∈ adds, k.isAdd = true) →
      publishSeq L R adds (s ∪ B) = publishSeq L R adds s ∪ B
  | [], s, B, _ => rfl
  | k :: ks, s, B, allAdds => by
      simp only [publishSeq]
      rw [publish_union_comm L (fun t h => by
        have := allAdds k (by simp); rw [h] at this; simp [MSink.isAdd] at this)]
      exact publishSeq_adds_union ks _ B fun k' m => allAdds k' (by simp [m])

/-- A non-add sink commutes with the adds written after it, unless it is a removal meeting one. -/
theorem publish_publishSeq_adds_comm {R : Finset (Subst V T)} {k : MSink T P} (notAdd : k.isAdd = false) :
    ∀ (adds : List (MSink T P)), (∀ a ∈ adds, a.isAdd = true) →
      (∀ t, k = .remove t → ∀ a ∈ adds, a.isAdd = true →
        Disjoint ((stageOf L R k).image Prod.fst) ((stageOf L R a).image Prod.fst)) →
      ∀ s, k.publish (stageOf L R k) (publishSeq L R adds s) =
        publishSeq L R adds (k.publish (stageOf L R k) s)
  | [], _, _, s => rfl
  | a :: as, allAdds, disjoint, s => by
      have aAdd := allAdds a (by simp)
      cases a with
      | add t =>
          have addPub : ∀ (st : Finset (T × T)) (s' : Finset T),
              (MSink.add t : MSink T P).publish st s' = s' ∪ st.image Prod.fst := fun _ _ => rfl
          simp only [publishSeq]
          rw [addPub, addPub]
          rw [publishSeq_adds_union L as _ _ (fun a' m => allAdds a' (by simp [m])),
            publishSeq_adds_union L as _ _ (fun a' m => allAdds a' (by simp [m]))]
          rw [publish_union_comm L (fun t' h => disjoint t' h (.add t) (by simp) rfl)]
          rw [publish_publishSeq_adds_comm notAdd as (fun a' m => allAdds a' (by simp [m]))
            (fun t' h a' m ha => disjoint t' h a' (by simp [m]) ha)]
      | remove t => simp [MSink.isAdd] at aAdd
      | fold key value write => simp [MSink.isAdd] at aAdd

/-- **The profile's law and the kernel's agree when no removal meets a later add**: publishing
each sink in its written order is publishing adds first. -/
theorem leftToRight_eq_addsFirst {R : Finset (Subst V T)} :
    ∀ (sinks : List (MSink T P)), NoRemovalMeetsLaterAdd L R sinks → ∀ s : Finset T,
      publishSeq L R sinks s =
        publishSeq L R (sinks.filter fun k => !k.isAdd) (publishSeq L R (sinks.filter (·.isAdd)) s)
  | [], _, s => rfl
  | k :: ks, ⟨here, rest⟩, s => by
      by_cases h : k.isAdd = true
      · simp only [publishSeq, List.filter_cons, h, Bool.not_true, Bool.false_eq_true, if_false,
          if_true]
        exact leftToRight_eq_addsFirst ks rest _
      · have h' : k.isAdd = false := by simpa using h
        simp only [publishSeq, List.filter_cons, h', Bool.not_false, if_true, Bool.false_eq_true,
          if_false]
        rw [publish_publishSeq_adds_comm L h' (ks.filter (·.isAdd))
          (fun a m => (List.mem_filter.mp m).2)
          (fun t hk a m ha => here t hk a (List.mem_filter.mp m).1 ha)]
        exact leftToRight_eq_addsFirst ks rest _

theorem everyStep_leftToRight_eq_addsFirst {exec : T} {sinks : List (MSink T P)}
    {R : Finset (Subst V T)} (noMeet : NoRemovalMeetsLaterAdd L R sinks) (M : Finset T) :
    everyStep L .leftToRight exec sinks R M = everyStep L .addsFirst exec sinks R M :=
  leftToRight_eq_addsFirst L sinks noMeet (M.erase exec)

/-- **The two laws differ when a removal meets a later add**: `(O (- t) (+ t))` over one row
instantiating `t` to an atom `u` of the space keeps `u` under the profile's law and removes it
under the kernel's. -/
theorem leftToRight_ne_addsFirst {exec u : T} {t : P} {M : Finset T} {σ : Subst V T}
    (inst : L.inst σ t = some u) :
    u ∈ everyStep L .leftToRight exec [.remove t, .add t] {σ} M ∧
      u ∉ everyStep L .addsFirst exec [.remove t, .add t] {σ} M := by
  have stage : ∀ k : MSink T P, (k = .remove t ∨ k = .add t) →
      (stageOf L {σ} k).image Prod.fst = {u} := by
    rintro k (rfl | rfl) <;> simp [stageOf, MSink.contrib, inst]
  constructor
  · simp only [everyStep, publishSeq, MSink.publish]
    rw [stage (.add t) (Or.inr rfl)]
    simp
  · simp only [everyStep, List.filter, MSink.isAdd, Bool.not_true, Bool.not_false, publishSeq,
      MSink.publish]
    rw [stage (.remove t) (Or.inl rfl)]
    simp

/-! ### Publishing row by row observes the order of the rows -/

/-- **Row-major publication** (`ProgrammableSpaceMM2RowMajorWrites.rows`): each row's sinks
publish, in their written order, as the row is taken. -/
def rowMajor (sinks : List (MSink T P)) (enum : List (Subst V T)) (s : Finset T) : Finset T :=
  enum.foldl (fun s σ => sinks.foldl (fun s k => k.publish (k.contrib L σ) s) s) s

/-- **Row-major publication observes the order of the rows**, so it is not a function of a step's
rows: with the sinks `(O (- t) (+ t'))`, a row `σ₁` removing `a` and adding `b`, and a row `σ₂`
removing `b` and adding `c`, the order `[σ₁, σ₂]` leaves `b` out and `[σ₂, σ₁]` leaves it in.
(This is the existing profile's own example `(O (+ $x) (- $y))` over `(edge a b)`, `(edge b c)`,
with its two rows taken in the other order.) -/
theorem rowMajor_observes_order {t t' : P} {σ₁ σ₂ : Subst V T} {a b c : T}
    (h₁ : L.inst σ₁ t = some a) (h₁' : L.inst σ₁ t' = some b)
    (h₂ : L.inst σ₂ t = some b) (h₂' : L.inst σ₂ t' = some c) (bc : b ≠ c) :
    b ∉ rowMajor L [.remove t, .add t'] [σ₁, σ₂] ∅ ∧
      b ∈ rowMajor L [.remove t, .add t'] [σ₂, σ₁] ∅ := by
  constructor
  · simp [rowMajor, MSink.publish, MSink.contrib, h₁, h₁', h₂, h₂', bc]
  · simp [rowMajor, MSink.publish, MSink.contrib, h₁, h₁', h₂, h₂']

/-! ## Bridges: the streaming results and the existing `every` -/

/-- A sink's stage as a union sink of `Streaming`. -/
def MSink.unionSink (k : MSink T P) : Sink (Subst V T) (Finset T) (Finset (T × T)) :=
  ⟨finsetUnion, fun σ => k.contrib L σ, fun _ s => s⟩

/-- **MORK's stage of a sink is a streamed union stage**, so the results of `Streaming` apply. -/
theorem morkStage_eq_stream (enum : List (Subst V T)) (k : MSink T P) :
    morkStage L enum k = (k.unionSink L).stream enum := rfl

/-- **The stage cannot see the order or the repetitions of the matches.** -/
theorem morkStage_eq_of_mem_iff [DecidableEq (Subst V T)] {enum enum' : List (Subst V T)}
    (same : ∀ σ, σ ∈ enum ↔ σ ∈ enum') (k : MSink T P) :
    morkStage L enum k = morkStage L enum' k := by
  rw [morkStage_eq_stream, morkStage_eq_stream]
  exact Sink.stream_eq_of_mem_iff finsetUnion_commutative finsetUnion_idempotent same

theorem forall₂_of_mapM_some {α β : Type*} {f : α → Option β} :
    ∀ {ts : List α} {us : List β}, ts.mapM f = some us → List.Forall₂ (fun a b => f a = some b) ts us
  | [], us, h => by
      simp only [List.mapM_nil] at h
      cases h
      exact .nil
  | t :: ts, us, h => by
      rw [List.mapM_cons] at h
      cases ht : f t with
      | none => simp [ht] at h
      | some u =>
          cases hts : ts.mapM f with
          | none => simp [ht, hts] at h
          | some us' =>
              rw [ht, hts] at h
              have h' : some (u :: us') = some us := h
              cases h'
              exact .cons ht (forall₂_of_mapM_some hts)

theorem mem_of_forall₂_some {α β : Type*} {f : α → Option β} :
    ∀ {ts : List α} {us : List β}, List.Forall₂ (fun a b => f a = some b) ts us →
      ∀ x, x ∈ us ↔ ∃ t ∈ ts, f t = some x
  | [], [], .nil, x => by simp
  | t :: ts, u :: us, .cons h rest, x => by
      rw [List.mem_cons, mem_of_forall₂_some rest x]
      constructor
      · rintro (rfl | ⟨t', m, h'⟩)
        · exact ⟨t, by simp, h⟩
        · exact ⟨t', by simp [m], h'⟩
      · rintro ⟨t', m, h'⟩
        rcases List.mem_cons.mp m with rfl | m
        · rw [h] at h'; exact Or.inl (Option.some.inj h').symm
        · exact Or.inr ⟨t', m, h'⟩

open Mettapedia.Languages.MeTTa.TransformQuantifiers in
/-- The footprints of an exec's `every` in the existing bag meaning (`Footprints.EveryStep`): the
kernel row takes the exec, and each row `σ` writes the instances of the templates. -/
def addFootprints (exec : T) (made : Subst V T → List T) : Footprints (Option (Subst V T)) T :=
  ⟨fun r => match r with
    | none => {exec}
    | some _ => 0,
   fun r => match r with
    | none => 0
    | some σ => (made σ : Multiset T)⟩

open Mettapedia.Languages.MeTTa.TransformQuantifiers in
/-- **An exec whose templates are adds fires the existing `every`, read as a set**: the bag the
`every` of the kernel row and the rows `R` leaves, read as a set, is the step's `every`. -/
theorem everyStep_adds_eq_footprints {exec : T} {M : Finset T} {templates : List P}
    {R : Finset (Subst V T)} {made : Subst V T → List T}
    (inst : ∀ σ ∈ R, instTemplate L σ templates = some (made σ)) {N : Multiset T}
    (step : (addFootprints exec made).EveryStep (none ::ₘ R.val.map some) M.val N) :
    N.toFinset = everyStep L .addsFirst exec (templates.map .add) R M := by
  have hN : N = M.val - {exec} + (R.val.map fun σ => (made σ : Multiset T)).sum := by
    rw [step.2]
    simp [Footprints.totalTake, Footprints.totalWrite, addFootprints, Multiset.map_map]
  have adds : (templates.map MSink.add : List (MSink T P)).filter (·.isAdd) = templates.map .add := by
    rw [List.filter_eq_self]; intro k m; obtain ⟨t, -, rfl⟩ := List.mem_map.mp m; rfl
  have others : (templates.map MSink.add : List (MSink T P)).filter (fun k => !k.isAdd) = [] := by
    rw [List.filter_eq_nil_iff]; intro k m; obtain ⟨t, -, rfl⟩ := List.mem_map.mp m; simp [MSink.isAdd]
  ext x
  simp only [everyStep, adds, others, publishSeq]
  rw [Multiset.mem_toFinset, hN, mem_publishSeq_adds _ (fun k m => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp m; rfl)]
  rw [Multiset.mem_add, Multiset.sub_singleton, ← Finset.erase_val, Finset.mem_val,
    show ∀ S : Multiset (Multiset T), x ∈ S.sum ↔ ∃ s ∈ S, x ∈ s from fun S => Multiset.mem_join]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨w, wm, xw⟩
    obtain ⟨σ, σm, rfl⟩ := Multiset.mem_map.mp wm
    have rel := forall₂_of_mapM_some (inst σ σm)
    obtain ⟨t, tm, ht⟩ := (mem_of_forall₂_some rel x).mp (Multiset.mem_coe.mp xw)
    refine ⟨.add t, List.mem_map.mpr ⟨t, tm, rfl⟩, Finset.mem_image.mpr ⟨(x, x), ?_, rfl⟩⟩
    exact mem_stageOf.mpr ⟨σ, σm, by simp [MSink.contrib, ht]⟩
  · rintro ⟨k, km, xk⟩
    obtain ⟨t, tm, rfl⟩ := List.mem_map.mp km
    obtain ⟨y, ym, rfl⟩ := Finset.mem_image.mp xk
    obtain ⟨σ, σm, yc⟩ := mem_stageOf.mp ym
    have rel := forall₂_of_mapM_some (inst σ σm)
    simp only [MSink.contrib] at yc
    split at yc
    · rename_i u hu
      rw [Finset.mem_singleton] at yc
      subst yc
      refine ⟨(made σ : Multiset T), Multiset.mem_map.mpr ⟨σ, σm, rfl⟩, ?_⟩
      exact Multiset.mem_coe.mpr ((mem_of_forall₂_some rel u).mpr ⟨t, tm, hu⟩)
    · simp at yc

/-! ## Over the binding-tree term layer of thinnings -/

open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings in
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT in
/-- **MORK's firing is the step's `every` over the thinnings term layer**: binding trees compared
up to alpha-equivalence, patterns with pattern variables. -/
theorem treeLayer_morkFire_eq_everyStep {Head Var : Type} [DecidableEq Head] [DecidableEq Var]
    [DecidableEq (Term Head)] {exec : Term Head} {M : Finset (Term Head)} (selected : exec ∈ M)
    {sources : List (TreePat Head Var)} {sinks : List (MSink (Term Head) (TreePat Head Var))}
    {enum : List (Subst Var (Term Head))} {R : Finset (Subst Var (Term Head))}
    (enumerates : ∀ σ, σ ∈ enum ↔ EveryRow treeLayer sources (readCopy exec M) σ)
    (rows : ∀ σ, σ ∈ R ↔ EveryRow treeLayer sources M σ) :
    morkFire treeLayer exec sinks enum M = everyStep treeLayer .addsFirst exec sinks R M :=
  morkFire_eq_everyStep selected enumerates rows

end Mettapedia.Languages.ProcessCalculi.MORK.StepSpecialization
