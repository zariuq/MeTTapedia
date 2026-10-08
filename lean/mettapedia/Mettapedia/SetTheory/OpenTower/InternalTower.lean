import Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts
import Mathlib.SetTheory.Ordinal.Family

/-!
# The internal tower: closed sets inside one level of `ZFSet`

"Open tower" has at least four meanings, kept apart here: (a) an internal tower of set
models inside one host level under a named supply of inaccessibles (this module); (b) the
external schema of embeddings between Lean's universe levels (`ExternalTower`); (c) a
generated enclosure tower, the closure of declared codes under declared operations, which is
weaker than closure under every small family; (d) a proof-theoretic progression of consistency
or reflection extensions. Only (a) and (b) are built in this directory.

Inside one fixed level `ZFSet.{u}`, a *stage* is a closed set in the sense of
`ZFSetUniverseClosure.Closed`: transitive and closed under union, power set and
replacement by arbitrary functions of the host. Under the named hypothesis
`CofinalInaccessibles.{u}` (cofinally many inaccessible cardinals at this level; a
parameter of every theorem that needs it, never an axiom) every set lies in a least
closed set, and the stages form an open tower.

**The ω-tower.** `stage h N n` starts from the least closed set around `N` and takes the
least closed set around the previous stage. Stages are strictly increasing for membership
and for inclusion (`stage_mem_of_lt`, `stage_ssubset_of_lt`), each is the least closed set
around its predecessor (`stage_succ_least`), and no stage is terminal.

`Closed` is not by itself a Grothendieck universe with infinity: the empty set is closed
(`closed_empty`), and the least closed set around `∅` need not contain `ω`. Every stage after
the first does contain `ω` (`omega_mem_stage_succ`).

**The class of stages.** Every set lies in a stage (`exists_stage_containing`); two sets lie
in a common stage (`stages_directed`); every set-indexed family of sets lies inside one stage
(`small_family_bounded`); no stage is greatest (`not_exists_greatest_stage`); and no
set-indexed family of sets is cofinal among the stages (`no_small_cofinal_family`). The law
"every set lies in a closed set" holds of the whole level under the hypothesis, but inside no
least closed set (`no_closed_member_around`). So the
stages form a directed class without a top that no set exhausts.

**Limits.** The union of the ω-tower is a set (`towerUnion`) but not a stage
(`towerUnion_not_closed`): replacement along the natural numbers collects all the stages into
one member, which would have to lie in some stage and then in itself. The tower continues by
closing again (`limitStage`). Indexed by all ordinals of the level, closing each set-sized
initial segment gives an ordinal-indexed tower (`ordinalStage`) whose stages are strictly
increasing (`ordinalStage_mem_of_lt`) and are not all members of any one set
(`ordinalStage_unbounded`): its length is a proper class.

**Where choice enters.** Three separate places, none of them the construction of the least
closed set:
* `ZFSetHenkinInterpretation.replacement` forms the image of a set under an arbitrary host
  function with `Classical.allZFSetDefinable`; the predicate `Closed` mentions it, so every
  statement about `Closed`, `hull` and `univOf` depends on `Classical.choice`.
* Mathlib's cardinal arithmetic behind `inaccessible_closed` is classical.
* `univOf` picks an enclosing universe with `Classical.choose`; its value does not depend on
  the pick (`univOf_independent`).

Stating replacement relationally (`ClosedRel`: a set that is an image of a member and lies
inside the stage is a member) removes the first dependency, and supplying enclosures as data
(`Enclosures`) removes the third: the least closed set (`hullRel`), its minimality and
independence of the enclosure, and the whole ω-tower (`relStage`) are then free of choice.
The two notions of closure agree (`closedRel_iff_closed`), and with an enclosure operator
extracted from `CofinalInaccessibles` the two towers coincide (`relStage_enclosuresOf`); that
extraction is the only remaining use of choice.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.InternalTower

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation

universe u v

/-! ## Elementary facts about closed sets -/

theorem closed_subset_of_mem {U V : ZFSet.{u}} (hV : Closed V) (h : U ∈ V) : U ⊆ V :=
  hV.transitive U h

/-- The empty set is closed: closure alone forces neither nonemptiness nor infinity. -/
theorem closed_empty : Closed (∅ : ZFSet.{u}) where
  transitive y hy := absurd hy (ZFSet.notMem_empty y)
  union_mem ha := absurd ha (ZFSet.notMem_empty _)
  power_mem ha := absurd ha (ZFSet.notMem_empty _)
  replacement_mem ha := absurd ha (ZFSet.notMem_empty _)

/-- A closed set is closed under `insert`, hence under the successor `x ∪ {x}`. -/
theorem closed_insert_mem {U a b : ZFSet.{u}} (hU : Closed U) (ha : a ∈ U) (hb : b ∈ U) :
    insert a b ∈ U := by
  have hunion := hU.union_mem (hU.unorderedPair_mem (hU.singleton_mem ha) hb)
  have heq : ZFSet.sUnion {{a}, b} = insert a b := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sUnion, ZFSet.mem_insert_iff]
    constructor
    · rintro ⟨z, hz, hy⟩
      rcases ZFSet.mem_pair.mp hz with rfl | rfl
      · exact Or.inl (ZFSet.mem_singleton.mp hy)
      · exact Or.inr hy
    · rintro (rfl | hy)
      · exact ⟨{y}, ZFSet.mem_pair.mpr (Or.inl rfl), ZFSet.mem_singleton.mpr rfl⟩
      · exact ⟨b, ZFSet.mem_pair.mpr (Or.inr rfl), hy⟩
  rwa [heq] at hunion

/-! ## The finite von Neumann ordinals -/

/-- The finite von Neumann ordinals, `0 = ∅` and `n + 1 = n ∪ {n}`. -/
def natCode : ℕ → ZFSet.{u}
  | 0 => ∅
  | n + 1 => insert (natCode n) (natCode n)

theorem natCode_mem_of_lt {m n : ℕ} (hmn : m < n) : natCode.{u} m ∈ natCode.{u} n := by
  induction n with
  | zero => exact absurd hmn (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | rfl
    · exact ZFSet.mem_insert_of_mem _ (ih hlt)
    · exact ZFSet.mem_insert _ _

theorem natCode_injective : Function.Injective natCode.{u} := by
  intro m n equal
  rcases lt_trichotomy m n with hlt | same | hgt
  · have member := natCode_mem_of_lt.{u} hlt
    rw [← equal] at member
    exact absurd member (ZFSet.mem_irrefl _)
  · exact same
  · have member := natCode_mem_of_lt.{u} hgt
    rw [equal] at member
    exact absurd member (ZFSet.mem_irrefl _)

/-- A closed set containing `∅` contains every finite ordinal. -/
theorem closed_natCode_mem {U : ZFSet.{u}} (hU : Closed U) (hempty : (∅ : ZFSet.{u}) ∈ U)
    (n : ℕ) : natCode.{u} n ∈ U := by
  induction n with
  | zero => exact hempty
  | succ n ih => exact closed_insert_mem hU ih ih

/-- The finite ordinals are Mathlib's von Neumann naturals. -/
theorem mk_ofNat (n : ℕ) : ZFSet.mk (PSet.ofNat.{u} n) = natCode.{u} n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ZFSet.mk (insert (PSet.ofNat.{u} n) (PSet.ofNat.{u} n)) =
      insert (natCode.{u} n) (natCode.{u} n)
    rw [← ih]
    rfl

/-- The members of `ω` are exactly the finite ordinals. -/
theorem mem_omega_iff {x : ZFSet.{u}} : x ∈ ZFSet.omega ↔ ∃ n, natCode.{u} n = x := by
  induction x using Quotient.inductionOn with
  | _ p =>
    constructor
    · rintro ⟨⟨n⟩, hn⟩
      exact ⟨n, (mk_ofNat n).symm.trans (ZFSet.sound hn).symm⟩
    · rintro ⟨n, hn⟩
      rw [← mk_ofNat] at hn
      exact ⟨⟨n⟩, (ZFSet.exact hn).symm⟩

/-- A closed set containing `∅` includes `ω`. -/
theorem omega_subset_of_closed {U : ZFSet.{u}} (hU : Closed U)
    (hempty : (∅ : ZFSet.{u}) ∈ U) : ZFSet.omega ⊆ U := by
  intro x hx
  obtain ⟨n, rfl⟩ := mem_omega_iff.mp hx
  exact closed_natCode_mem hU hempty n

/-! ## The ω-tower -/

section Tower

variable (h : CofinalInaccessibles.{u}) (N : ZFSet.{u})

/-- The ω-tower over `N`: the least closed set around `N`, then the least closed set around
the previous stage. -/
noncomputable def stage : ℕ → ZFSet.{u}
  | 0 => univOf h N
  | n + 1 => univOf h (stage n)

theorem stage_zero : stage h N 0 = univOf h N := rfl

theorem stage_succ (n : ℕ) : stage h N (n + 1) = univOf h (stage h N n) := rfl

theorem stage_closed (n : ℕ) : Closed (stage h N n) := by
  cases n with
  | zero => exact univOf_closed h N
  | succ n => exact univOf_closed h _

theorem base_mem_stage_zero : N ∈ stage h N 0 := mem_univOf h N

theorem stage_mem_succ (n : ℕ) : stage h N n ∈ stage h N (n + 1) := mem_univOf h _

/-- Each stage is the least closed set containing its predecessor. -/
theorem stage_succ_least (n : ℕ) {V : ZFSet.{u}} (hn : stage h N n ∈ V) (hV : Closed V) :
    stage h N (n + 1) ⊆ V :=
  univOf_minimal h hn hV

theorem stage_mem_of_lt {m n : ℕ} (hmn : m < n) : stage h N m ∈ stage h N n := by
  induction n with
  | zero => exact absurd hmn (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | rfl
    · exact (stage_closed h N (n + 1)).transitive _ (stage_mem_succ h N n) (ih hlt)
    · exact stage_mem_succ h N m

theorem stage_subset_of_le {m n : ℕ} (hmn : m ≤ n) : stage h N m ⊆ stage h N n := by
  rcases Nat.lt_or_eq_of_le hmn with hlt | rfl
  · exact closed_subset_of_mem (stage_closed h N n) (stage_mem_of_lt h N hlt)
  · exact fun _ hx => hx

theorem stage_ne_of_lt {m n : ℕ} (hmn : m < n) : stage h N m ≠ stage h N n := by
  intro equal
  have member := stage_mem_of_lt h N hmn
  rw [equal] at member
  exact ZFSet.mem_irrefl _ member

/-- **Strictly increasing.** An earlier stage is a member and a proper subset of a later one. -/
theorem stage_ssubset_of_lt {m n : ℕ} (hmn : m < n) :
    stage h N m ∈ stage h N n ∧ stage h N m ⊆ stage h N n ∧ stage h N m ≠ stage h N n :=
  ⟨stage_mem_of_lt h N hmn, stage_subset_of_le h N hmn.le, stage_ne_of_lt h N hmn⟩

theorem stage_injective : Function.Injective (stage h N) := by
  intro m n equal
  rcases lt_trichotomy m n with hlt | same | hgt
  · exact absurd equal (stage_ne_of_lt h N hlt)
  · exact same
  · exact absurd equal.symm (stage_ne_of_lt h N hgt)

theorem base_mem_stage (n : ℕ) : N ∈ stage h N n :=
  stage_subset_of_le h N (Nat.zero_le n) (base_mem_stage_zero h N)

theorem empty_mem_stage (n : ℕ) : (∅ : ZFSet.{u}) ∈ stage h N n :=
  (stage_closed h N n).empty_mem (base_mem_stage h N n)

/-- Every stage after the first contains `ω`. -/
theorem omega_mem_stage_succ (n : ℕ) : ZFSet.omega ∈ stage h N (n + 1) :=
  (stage_closed h N (n + 1)).subset_mem (stage_mem_succ h N n)
    (omega_subset_of_closed (stage_closed h N n) (empty_mem_stage h N n))

/-- **No terminal stage of the ω-tower.** -/
theorem stage_no_terminal (n : ℕ) :
    ∃ m, stage h N n ∈ stage h N m ∧ stage h N n ≠ stage h N m :=
  ⟨n + 1, stage_mem_succ h N n, stage_ne_of_lt h N (Nat.lt_succ_self n)⟩

end Tower

/-! ## The class of stages: directed, cofinal, without a top -/

section ClassOfStages

variable (h : CofinalInaccessibles.{u})
include h

/-- Every set lies in a stage. -/
theorem exists_stage_containing (x : ZFSet.{u}) : ∃ U, Closed U ∧ x ∈ U :=
  ⟨univOf h x, univOf_closed h x, mem_univOf h x⟩

/-- **No terminal stage.** Every set, in particular every stage, is a member and a proper
subset of a later stage. -/
theorem no_terminal_stage (U : ZFSet.{u}) :
    ∃ V, Closed V ∧ U ∈ V ∧ U ⊆ V ∧ U ≠ V := by
  refine ⟨univOf h U, univOf_closed h U, mem_univOf h U,
    closed_subset_of_mem (univOf_closed h U) (mem_univOf h U), ?_⟩
  intro equal
  have member := mem_univOf h U
  rw [← equal] at member
  exact ZFSet.mem_irrefl _ member

/-- **No greatest stage.** No closed set includes every closed set. -/
theorem not_exists_greatest_stage : ¬ ∃ W : ZFSet.{u}, Closed W ∧ ∀ U, Closed U → U ⊆ W := by
  rintro ⟨W, hW, greatest⟩
  have above := greatest (univOf h W) (univOf_closed h W)
  exact ZFSet.mem_irrefl W (above (mem_univOf h W))

/-- **A successor stage has no stage around its generator.** No member of the least closed
set around `N` is a closed set containing `N`; the next stage has one, namely this stage.
So the law "every set lies in a closed set" fails inside every least closed set. -/
theorem no_closed_member_around (N : ZFSet.{u}) :
    ¬ ∃ V ∈ univOf h N, N ∈ V ∧ Closed V := by
  rintro ⟨V, hV, hNV, hVclosed⟩
  exact ZFSet.mem_irrefl V (univOf_minimal h hNV hVclosed hV)

/-- **Directed.** Any two sets are members of one stage. -/
theorem stages_directed (x y : ZFSet.{u}) : ∃ W, Closed W ∧ x ∈ W ∧ y ∈ W := by
  refine ⟨univOf h {x, y}, univOf_closed h _, ?_, ?_⟩
  · exact (univOf_closed h _).transitive _ (mem_univOf h _) (ZFSet.mem_pair.mpr (Or.inl rfl))
  · exact (univOf_closed h _).transitive _ (mem_univOf h _) (ZFSet.mem_pair.mpr (Or.inr rfl))

/-- **Set-sized families are bounded.** Every family of sets indexed by a small type consists
of members of one stage. -/
theorem small_family_bounded {ι : Type v} [Small.{u} ι] (S : ι → ZFSet.{u}) :
    ∃ W, Closed W ∧ ∀ i, S i ∈ W := by
  refine ⟨univOf h (ZFSet.range S), univOf_closed h _, fun i => ?_⟩
  exact (univOf_closed h _).transitive _ (mem_univOf h _) (ZFSet.mem_range_self i)

/-- **No set-sized family is cofinal.** For every small-indexed family of sets there is a stage
included in none of them. -/
theorem no_small_cofinal_family {ι : Type v} [Small.{u} ι] (S : ι → ZFSet.{u}) :
    ∃ W, Closed W ∧ ∀ i, ¬ W ⊆ S i := by
  obtain ⟨W, hW, bound⟩ := small_family_bounded h S
  refine ⟨W, hW, fun i below => ?_⟩
  exact ZFSet.mem_irrefl (S i) (below (bound i))

end ClassOfStages

/-! ## The union of the ω-tower is a set but not a stage -/

section Limit

variable (h : CofinalInaccessibles.{u}) (N : ZFSet.{u})

/-- The union of the ω-tower. -/
noncomputable def towerUnion : ZFSet.{u} :=
  ZFSet.iUnion fun n : ℕ => stage h N n

theorem mem_towerUnion {x : ZFSet.{u}} : x ∈ towerUnion h N ↔ ∃ n, x ∈ stage h N n :=
  ZFSet.mem_iUnion

theorem stage_mem_towerUnion (n : ℕ) : stage h N n ∈ towerUnion h N :=
  (mem_towerUnion h N).mpr ⟨n + 1, stage_mem_succ h N n⟩

/-- **The union of the ω-tower is not a stage.** Replacement along the finite ordinals of the
first stage would collect every stage into one member of the union, hence into a member of
some stage, which would then contain itself. -/
theorem towerUnion_not_closed : ¬ Closed (towerUnion h N) := by
  classical
  intro hW
  let index : ZFSet.{u} → ℕ := fun x =>
    if hx : ∃ n, natCode.{u} n = x then Classical.choose hx else 0
  have hindex : ∀ n, index (natCode.{u} n) = n := by
    intro n
    have hx : ∃ m, natCode.{u} m = natCode.{u} n := ⟨n, rfl⟩
    simp only [index, dif_pos hx]
    exact natCode_injective (Classical.choose_spec hx)
  let f : ZFSet.{u} → ZFSet.{u} := fun x => stage h N (index x)
  have hrep := hW.replacement_mem (stage_mem_towerUnion h N 0) f
    (fun x _ => stage_mem_towerUnion h N (index x))
  obtain ⟨k, hk⟩ := (mem_towerUnion h N).mp hrep
  have hmem : stage h N k ∈ replacement (stage h N 0) f :=
    mem_replacement.mpr ⟨natCode.{u} k,
      closed_natCode_mem (stage_closed h N 0) (empty_mem_stage h N 0) k,
      by simp only [f, hindex]⟩
  exact ZFSet.mem_irrefl _ ((stage_closed h N k).transitive _ hk hmem)

/-- The ω-th stage: the least closed set around the union of the ω-tower. -/
noncomputable def limitStage : ZFSet.{u} := univOf h (towerUnion h N)

theorem limitStage_closed : Closed (limitStage h N) := univOf_closed h _

theorem stage_mem_limitStage (n : ℕ) : stage h N n ∈ limitStage h N :=
  (limitStage_closed h N).transitive _ (mem_univOf h _) (stage_mem_towerUnion h N n)

/-- The union of the stages is strictly below the ω-th stage. -/
theorem towerUnion_ne_limitStage : towerUnion h N ≠ limitStage h N := by
  intro equal
  apply towerUnion_not_closed h N
  rw [equal]
  exact limitStage_closed h N

end Limit

/-! ## The ordinal-indexed tower -/

section Ordinals

variable (h : CofinalInaccessibles.{u}) (N : ZFSet.{u})

/-- The ordinal-indexed tower: the stage at `α` is the least closed set around `N` and all
earlier stages. The earlier stages form a set because each initial segment of the ordinals of
this level is small. -/
noncomputable def ordinalStage : Ordinal.{u} → ZFSet.{u} :=
  WellFoundedLT.fix fun α previous =>
    univOf h (insert N (ZFSet.range fun β : Set.Iio α => previous β.1 β.2))

theorem ordinalStage_eq (α : Ordinal.{u}) :
    ordinalStage h N α =
      univOf h (insert N (ZFSet.range fun β : Set.Iio α => ordinalStage h N β.1)) :=
  WellFoundedLT.fix_eq _ α

theorem ordinalStage_closed (α : Ordinal.{u}) : Closed (ordinalStage h N α) := by
  rw [ordinalStage_eq]
  exact univOf_closed h _

theorem base_mem_ordinalStage (α : Ordinal.{u}) : N ∈ ordinalStage h N α := by
  rw [ordinalStage_eq]
  exact (univOf_closed h _).transitive _ (mem_univOf h _) (ZFSet.mem_insert _ _)

theorem ordinalStage_mem_of_lt {β α : Ordinal.{u}} (hβα : β < α) :
    ordinalStage h N β ∈ ordinalStage h N α := by
  rw [ordinalStage_eq h N α]
  have member : ordinalStage h N β ∈
      insert N (ZFSet.range fun γ : Set.Iio α => ordinalStage h N γ.1) :=
    ZFSet.mem_insert_of_mem _ (ZFSet.mem_range.mpr ⟨⟨β, hβα⟩, rfl⟩)
  exact (univOf_closed h _).transitive _ (mem_univOf h _) member

theorem ordinalStage_injective : Function.Injective (ordinalStage h N) := by
  intro β α equal
  rcases lt_trichotomy β α with hlt | same | hgt
  · have member := ordinalStage_mem_of_lt h N hlt
    rw [equal] at member
    exact absurd member (ZFSet.mem_irrefl _)
  · exact same
  · have member := ordinalStage_mem_of_lt h N hgt
    rw [equal] at member
    exact absurd member (ZFSet.mem_irrefl _)

/-- **The ordinal-indexed tower is a proper class.** No set has all its stages as members:
otherwise the ordinals of this level would inject into the members of one set. -/
theorem ordinalStage_unbounded : ¬ ∃ s : ZFSet.{u}, ∀ α, ordinalStage h N α ∈ s := by
  rintro ⟨s, hs⟩
  let code : Ordinal.{u} → s := fun α => ⟨ordinalStage h N α, hs α⟩
  have injective : Function.Injective code := by
    intro β α equal
    exact ordinalStage_injective h N (congrArg Subtype.val equal)
  have : Small.{u} Ordinal.{u} := small_of_injective injective
  exact not_small_ordinal.{u, u} this

end Ordinals

/-! ## Where choice enters, and a choice-free least closure -/

/-- Closure with replacement stated relationally: a set that is the image of a member under a
host function, and whose members are in the stage, is in the stage. It does not form images,
so it does not need the host's choice. -/
structure ClosedRel (U : ZFSet.{u}) : Prop where
  transitive : ZFSet.IsTransitive U
  union_mem : ∀ {a : ZFSet.{u}}, a ∈ U → ZFSet.sUnion a ∈ U
  power_mem : ∀ {a : ZFSet.{u}}, a ∈ U → ZFSet.powerset a ∈ U
  image_mem : ∀ {a b : ZFSet.{u}}, a ∈ U → b ⊆ U →
    (∃ f : ZFSet.{u} → ZFSet.{u}, ∀ y, y ∈ b ↔ ∃ x ∈ a, f x = y) → b ∈ U

/-- The relational and the operational closure agree. -/
theorem closedRel_iff_closed (U : ZFSet.{u}) : ClosedRel U ↔ Closed U := by
  constructor
  · intro hU
    refine ⟨hU.transitive, hU.union_mem, hU.power_mem, ?_⟩
    intro a ha f hf
    refine hU.image_mem ha ?_ ⟨f, fun y => mem_replacement⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_replacement.mp hy
    exact hf x hx
  · intro hU
    refine ⟨hU.transitive, hU.union_mem, hU.power_mem, ?_⟩
    rintro a b ha hbU ⟨f, hb⟩
    have equal : b = replacement a f := by
      apply ZFSet.ext
      intro y
      rw [hb y, mem_replacement]
    have values : ∀ x ∈ a, f x ∈ U := fun x hx => hbU ((hb (f x)).mpr ⟨x, hx, rfl⟩)
    rw [equal]
    exact hU.replacement_mem ha f values

/-- The least closed set around `N`, cut out of a given relationally closed enclosure by
separation. Choice-free: it uses neither images nor a chosen enclosure. -/
noncomputable def hullRel (N bound : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∀ U : ZFSet.{u}, N ∈ U → ClosedRel U → x ∈ U) bound

theorem mem_hullRel {N bound x : ZFSet.{u}} :
    x ∈ hullRel N bound ↔ x ∈ bound ∧ ∀ U : ZFSet.{u}, N ∈ U → ClosedRel U → x ∈ U :=
  ZFSet.mem_sep

theorem contains_hullRel {N bound : ZFSet.{u}} (hN : N ∈ bound) : N ∈ hullRel N bound :=
  mem_hullRel.mpr ⟨hN, fun _ hU _ => hU⟩

theorem hullRel_minimal {N bound U : ZFSet.{u}} (hN : N ∈ U) (hU : ClosedRel U) :
    hullRel N bound ⊆ U :=
  fun _ hx => (mem_hullRel.mp hx).2 U hN hU

theorem hullRel_closedRel {N bound : ZFSet.{u}} (hbound : ClosedRel bound) :
    ClosedRel (hullRel N bound) where
  transitive y hy x hxy := by
    obtain ⟨hyb, hyall⟩ := mem_hullRel.mp hy
    exact mem_hullRel.mpr ⟨hbound.transitive y hyb hxy,
      fun U hNU hU => hU.transitive y (hyall U hNU hU) hxy⟩
  union_mem ha := by
    obtain ⟨hab, haall⟩ := mem_hullRel.mp ha
    exact mem_hullRel.mpr ⟨hbound.union_mem hab,
      fun U hNU hU => hU.union_mem (haall U hNU hU)⟩
  power_mem ha := by
    obtain ⟨hab, haall⟩ := mem_hullRel.mp ha
    exact mem_hullRel.mpr ⟨hbound.power_mem hab,
      fun U hNU hU => hU.power_mem (haall U hNU hU)⟩
  image_mem ha hb himage := by
    obtain ⟨hab, haall⟩ := mem_hullRel.mp ha
    refine mem_hullRel.mpr ⟨hbound.image_mem hab (fun y hy => (mem_hullRel.mp (hb hy)).1)
      himage, fun U hNU hU => ?_⟩
    exact hU.image_mem (haall U hNU hU) (fun y hy => (mem_hullRel.mp (hb hy)).2 U hNU hU) himage

/-- The least relationally closed set does not depend on the enclosure it is cut from. -/
theorem hullRel_independent {N left right : ZFSet.{u}}
    (hleft : ClosedRel left) (hNleft : N ∈ left)
    (hright : ClosedRel right) (hNright : N ∈ right) :
    hullRel N left = hullRel N right :=
  ZFSet.ext fun _ =>
    ⟨fun hx => hullRel_minimal (contains_hullRel hNright) (hullRel_closedRel hright) hx,
      fun hx => hullRel_minimal (contains_hullRel hNleft) (hullRel_closedRel hleft) hx⟩

/-- Enclosures supplied as data: an operation giving every set a relationally closed set that
contains it. -/
structure Enclosures : Type (u + 1) where
  enclose : ZFSet.{u} → ZFSet.{u}
  mem_enclose : ∀ N, N ∈ enclose N
  enclose_closed : ∀ N, ClosedRel (enclose N)

namespace Enclosures

variable (E : Enclosures.{u}) (N : ZFSet.{u})

/-- The least closed set around `N`, without choice. -/
noncomputable def least : ZFSet.{u} := hullRel N (E.enclose N)

theorem mem_least : N ∈ E.least N := contains_hullRel (E.mem_enclose N)

theorem least_closedRel : ClosedRel (E.least N) := hullRel_closedRel (E.enclose_closed N)

theorem least_minimal {U : ZFSet.{u}} (hN : N ∈ U) (hU : ClosedRel U) : E.least N ⊆ U :=
  hullRel_minimal hN hU

/-- Two enclosure operations give the same least closed sets. -/
theorem least_independent (F : Enclosures.{u}) : E.least N = F.least N :=
  hullRel_independent (E.enclose_closed N) (E.mem_enclose N)
    (F.enclose_closed N) (F.mem_enclose N)

/-- The ω-tower built from supplied enclosures. -/
noncomputable def relStage : ℕ → ZFSet.{u}
  | 0 => E.least N
  | n + 1 => E.least (relStage n)

theorem relStage_closedRel (n : ℕ) : ClosedRel (E.relStage N n) := by
  cases n with
  | zero => exact E.least_closedRel N
  | succ n => exact E.least_closedRel _

theorem relStage_mem_succ (n : ℕ) : E.relStage N n ∈ E.relStage N (n + 1) :=
  E.mem_least _

theorem relStage_succ_least (n : ℕ) {V : ZFSet.{u}} (hn : E.relStage N n ∈ V)
    (hV : ClosedRel V) : E.relStage N (n + 1) ⊆ V :=
  E.least_minimal _ hn hV

theorem relStage_mem_of_lt {m n : ℕ} (hmn : m < n) : E.relStage N m ∈ E.relStage N n := by
  induction n with
  | zero => exact absurd hmn (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | rfl
    · exact (E.relStage_closedRel N (n + 1)).transitive _ (E.relStage_mem_succ N n) (ih hlt)
    · exact E.relStage_mem_succ N m

/-- Every stage has a later one, without choice. -/
theorem relStage_no_terminal (n : ℕ) :
    ∃ m, E.relStage N n ∈ E.relStage N m ∧ E.relStage N n ≠ E.relStage N m := by
  refine ⟨n + 1, E.relStage_mem_succ N n, fun equal => ?_⟩
  have member := E.relStage_mem_succ N n
  rw [← equal] at member
  exact ZFSet.mem_irrefl _ member

/-- The tower does not depend on the enclosure operation. -/
theorem relStage_independent (F : Enclosures.{u}) (n : ℕ) :
    E.relStage N n = F.relStage N n := by
  induction n with
  | zero => exact E.least_independent N F
  | succ n ih =>
    change E.least (E.relStage N n) = F.least (F.relStage N n)
    rw [ih]
    exact E.least_independent _ F

end Enclosures

/-- **The one remaining use of choice:** the hypothesis only says that enclosures exist, and
an operation is extracted from it. -/
noncomputable def enclosuresOf (h : CofinalInaccessibles.{u}) : Enclosures.{u} where
  enclose N := univOf h N
  mem_enclose N := mem_univOf h N
  enclose_closed N := (closedRel_iff_closed _).mpr (univOf_closed h N)

theorem least_enclosuresOf (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    (enclosuresOf h).least N = univOf h N := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    exact (mem_hullRel.mp hx).1
  · intro hx
    refine mem_hullRel.mpr ⟨hx, fun U hNU hU => ?_⟩
    exact univOf_minimal h hNU ((closedRel_iff_closed U).mp hU) hx

/-- With enclosures extracted from the hypothesis, the choice-free tower is the tower of
least universes. -/
theorem relStage_enclosuresOf (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) (n : ℕ) :
    (enclosuresOf h).relStage N n = stage h N n := by
  induction n with
  | zero => exact least_enclosuresOf h N
  | succ n ih =>
    change (enclosuresOf h).least ((enclosuresOf h).relStage N n) = univOf h (stage h N n)
    rw [ih]
    exact least_enclosuresOf h _

#print axioms closed_natCode_mem
#print axioms mem_omega_iff
#print axioms omega_mem_stage_succ
#print axioms stage_ssubset_of_lt
#print axioms stage_succ_least
#print axioms stage_no_terminal
#print axioms no_terminal_stage
#print axioms not_exists_greatest_stage
#print axioms no_closed_member_around
#print axioms stages_directed
#print axioms small_family_bounded
#print axioms no_small_cofinal_family
#print axioms towerUnion_not_closed
#print axioms towerUnion_ne_limitStage
#print axioms ordinalStage_mem_of_lt
#print axioms ordinalStage_unbounded
#print axioms closedRel_iff_closed
#print axioms hullRel_closedRel
#print axioms hullRel_minimal
#print axioms hullRel_independent
#print axioms Enclosures.least_closedRel
#print axioms Enclosures.least_independent
#print axioms Enclosures.relStage_mem_of_lt
#print axioms Enclosures.relStage_succ_least
#print axioms Enclosures.relStage_no_terminal
#print axioms Enclosures.relStage_independent
#print axioms enclosuresOf
#print axioms relStage_enclosuresOf

end Mettapedia.SetTheory.OpenTower.InternalTower
