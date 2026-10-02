import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSetUniverses
import Mettapedia.TypeTheory.UniverseLevel.Offsets
import Mettapedia.TypeTheory.UniverseLevel.Notation

/-!
# The tower of closed universes over a level order

A closed universe is a transitive set closed under union, power set and replacement. The
least closed universe *around* a set is the least one that has the set as a member; it
exists relative to cofinally many inaccessible cardinals, and so does everything here.

Over a level order, the *tower* `universeSet` assigns a closed universe to every level by
well-founded recursion: the stage at a level is the least closed universe around the set of
the seed and all the earlier stages. Each stage is therefore an enclosing universe of the
stages before it. The tower and its laws are declared in the namespace of the set
interpretation of universe levels, whose codes are the members of the stages.

Every stage is closed and has the seed as a member. An earlier stage is a member and a
subset of every later one: membership and inclusion of stages are the strict and the weak
order of levels, and the tower is injective.

At the least level the stage is the least closed universe around the seed, and at a
successor level it is the least closed universe around the previous stage. Over the
natural numbers these two equations are the whole recursion. The tower commutes with
initial embeddings of level orders, so the finite stages of the tower over any level order
are the stages of the tower over the natural numbers.

At every level the set of the earlier stages is a member of the stage and of no earlier
stage. The union of the earlier stages is then a member and a proper subset of the stage,
and at a positive level the stage is the least closed universe around that union. The
union is itself a stage exactly at a successor level, where it is the previous stage. At a
limit level it is no stage, and the stage is not the least closed universe around any
single stage.

At a level with countably many predecessors the stage is, moreover, the least closed
universe that has the seed and every earlier stage as members, and at a limit level the
union of the earlier stages is then not a closed universe. The ordinal notations below ε₀
are countable, so both hold at all of their levels.

The tower is monotone in the seed.

These are the laws of a tower of universes of well-founded hypersets, for the least-universe
operation carried along the equivalence between the well-founded hypersets and `ZFSet`
(`MaterialSets.Hypersets.WellFoundedPart.IsUniverseTower`). The carried stages satisfy the
tower equation (`isUniverseTower_universeSet`), and their earlier stages are collected by
the carried set of the earlier stages (`collectsEarlierStages_universeSet`): a range of a
family of sets, which `ZFSet` forms with choice. Every tower of the carried operation over
the carried seed has the same stages (`universeSet_eq_of_isUniverseTower`): over the natural
numbers the stages built by insertion (`natStage_eq_universeSet`), and over every level order
the stages built as graphs from a presentation of the hypersets
(`picture_stageGraph_eq_universeSet`).

Positive example: over the ordinal notations below ε₀, every finite stage is a member of
the stage at `ω`, and the stage at `ω` is the least closed universe with these members.
Negative example: the union of the stages below `ω` is not a closed universe, and the
stage at `ω` is not the least closed universe around any single stage.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure
open MaterialSets.Hypersets
open LevelOrder

universe u

/-- The equivalence of the well-founded hypersets with `ZFSet`. -/
local notation "toZF" => HSet.wellFoundedPartEquivZFSet

/-- Its inverse. -/
local notation "ofZF" => HSet.wellFoundedPartEquivZFSet.symm

/-! ## Sets of subsets of a member -/

/-- A set whose members are all subsets of one member of a closed universe is a member of
that universe: it is a subset of a power set. -/
theorem _root_.Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.Closed.mem_of_forall_subset
    {U a b : ZFSet.{u}} (closed : Closed U) (ha : a ∈ U) (hb : ∀ y ∈ b, y ⊆ a) : b ∈ U :=
  closed.subset_mem (closed.power_mem ha) fun y hy => ZFSet.mem_powerset.mpr (hb y hy)

/-! ## The tower -/

section Tower

variable {L : Type} [LevelOrder L] (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})

/-- The tower of closed universes over a level order. The stage at a level is the least
closed universe around the set of the seed and all the earlier stages. -/
noncomputable def universeSet : L → ZFSet.{u} :=
  LevelOrder.wf.fix fun α stage =>
    univOf h (insert seed (ZFSet.range fun β : {β : L // β < α} => stage β.1 β.2))

/-- The stages of the tower below a level, collected into one set. -/
noncomputable def earlierStages (α : L) : ZFSet.{u} :=
  ZFSet.range fun β : {β : L // β < α} => universeSet h seed β.1

/-- The tower's equation: the stage at a level is the least closed universe around the set
of the seed and the earlier stages. -/
theorem universeSet_eq (α : L) :
    universeSet h seed α = univOf h (insert seed (earlierStages h seed α)) :=
  LevelOrder.wf.fix_eq _ α

section

variable {h seed}

/-- The members of the set of earlier stages are the stages at the lower levels. -/
theorem mem_earlierStages {α : L} {x : ZFSet.{u}} :
    x ∈ earlierStages h seed α ↔ ∃ β < α, universeSet h seed β = x := by
  rw [earlierStages, ZFSet.mem_range]
  exact ⟨fun ⟨β, hx⟩ => ⟨β.1, β.2, hx⟩, fun ⟨β, hβ, hx⟩ => ⟨⟨β, hβ⟩, hx⟩⟩

/-- The members of the union of the earlier stages are the members of the stages at the
lower levels. -/
theorem mem_sUnion_earlierStages {α : L} {x : ZFSet.{u}} :
    x ∈ ZFSet.sUnion (earlierStages h seed α) ↔ ∃ β < α, x ∈ universeSet h seed β := by
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨z, hz, hx⟩
    obtain ⟨β, hβ, rfl⟩ := mem_earlierStages.mp hz
    exact ⟨β, hβ, hx⟩
  · rintro ⟨β, hβ, hx⟩
    exact ⟨_, mem_earlierStages.mpr ⟨β, hβ, rfl⟩, hx⟩

end

/-! ## The tower among the well-founded hypersets

Carried along the equivalence between the well-founded hypersets and `ZFSet`, the stages
satisfy the tower equation of the carried least-universe operation, and their earlier stages
are collected. The laws of towers of universes then apply to them. -/

/-- The set of the earlier stages, carried to the well-founded hypersets, is the set of the
carried earlier stages. -/
theorem isEarlierStages_universeSet (α : L) :
    WellFoundedPart.IsEarlierStages (fun β : L => ofZF (universeSet h seed β)) α
      (ofZF (earlierStages h seed α)) := fun z => by
  change z ∈ HSet.ofZFSet (earlierStages h seed α) ↔ _
  rw [HSet.mem_ofZFSet_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨β, hβ, rfl⟩ := mem_earlierStages.mp hx
    exact ⟨β, hβ, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨_, mem_earlierStages.mpr ⟨β, hβ, rfl⟩, rfl⟩

/-- The set of the seed and the earlier stages, carried to the well-founded hypersets, is
the set of the carried seed and the carried earlier stages. -/
theorem isGeneratingSet_universeSet (α : L) :
    WellFoundedPart.IsGeneratingSet (ofZF seed) (fun β : L => ofZF (universeSet h seed β)) α
      (ofZF (insert seed (earlierStages h seed α))) := fun z => by
  change z ∈ HSet.ofZFSet (insert seed (earlierStages h seed α)) ↔ _
  rw [HSet.ofZFSet_insert, HSet.mem_insert_iff]
  exact or_congr Iff.rfl (isEarlierStages_universeSet h seed α z)

/-- The tower equation: the carried stages are a tower of universes of well-founded
hypersets, for the carried least-universe operation and the carried seed. -/
theorem isUniverseTower_universeSet :
    WellFoundedPart.IsUniverseTower (WellFoundedPart.univOf h) (ofZF seed)
      fun α : L => ofZF (universeSet h seed α) := fun α N hN => by
  rw [hN.unique (isGeneratingSet_universeSet h seed α), WellFoundedPart.univOf_symm,
    ← universeSet_eq]

/-- The collection hypothesis: the earlier carried stages are collected, by the carried set
of the earlier stages. That set is the range of a family of sets, which `ZFSet` forms with
choice. -/
theorem collectsEarlierStages_universeSet :
    WellFoundedPart.CollectsEarlierStages fun α : L => ofZF (universeSet h seed α) :=
  fun α => ⟨ofZF (earlierStages h seed α), fun β =>
    HSet.mem_wellFoundedPartEquivZFSet_symm_iff.mpr (mem_earlierStages.mpr ⟨β.1, β.2, rfl⟩)⟩

/-- Every tower of the carried least-universe operation over the carried seed has the
carried stages: its stages are the stages of the tower of sets. -/
theorem universeSet_eq_of_isUniverseTower {stage : L → WellFoundedPart.{u}}
    (t : WellFoundedPart.IsUniverseTower (WellFoundedPart.univOf h) (ofZF seed) stage)
    (α : L) : toZF (stage α) = universeSet h seed α :=
  (congrArg toZF (congrFun ((isUniverseTower_universeSet h seed).unique
    (collectsEarlierStages_universeSet h seed) t) α).symm).trans (Equiv.apply_symm_apply _ _)

/-- Over the natural numbers, the stages built by insertion for the carried least-universe
operation are the stages of the tower of sets. -/
theorem natStage_eq_universeSet (n : Nat) :
    toZF (WellFoundedPart.natStage (WellFoundedPart.univOf h) (ofZF seed) n) =
      universeSet h seed n :=
  universeSet_eq_of_isUniverseTower h seed (WellFoundedPart.isUniverseTower_natStage _ _) n

/-- Given a presentation of the hypersets by graphs, the stages built as graphs for the
carried least-universe operation picture the stages of the tower of sets. -/
theorem picture_stageGraph_eq_universeSet (p : HSet.Presentation.{u})
    (S : WellFoundedPart.Graph.{u}) (α : L) :
    toZF (WellFoundedPart.stageGraph
        (WellFoundedPart.Graph.ofPresentation p (WellFoundedPart.univOf h)) S α).picture =
      universeSet h (toZF S.picture) α :=
  universeSet_eq_of_isUniverseTower h (toZF S.picture) (by
    rw [Equiv.symm_apply_apply]
    exact WellFoundedPart.isUniverseTower_stageGraph S
      (WellFoundedPart.presents_ofPresentation p _)) α

/-- The universe laws of the carried least-universe operation. -/
local notation "𝒪" => WellFoundedPart.isUniverseOperator_univOf h

/-- The tower equation of the carried stages. -/
local notation "𝒯" => isUniverseTower_universeSet h seed

/-- The collection hypothesis of the carried stages. -/
local notation "𝒞" => collectsEarlierStages_universeSet h seed

/-! ## Basic laws -/

/-- Every stage is a closed universe. -/
theorem universeSet_closed (α : L) : Closed (universeSet h seed α) :=
  WellFoundedPart.isGrothendieckUniverse_symm_iff.mp ((𝒯).isGrothendieckUniverse 𝒪 𝒞 α)

/-- The set of the seed and the earlier stages is a member of the stage. -/
theorem insert_seed_earlierStages_mem (α : L) :
    insert seed (earlierStages h seed α) ∈ universeSet h seed α :=
  HSet.mem_wellFoundedPartEquivZFSet_symm_iff.mp
    ((𝒯).generatingSet_mem 𝒪 (isGeneratingSet_universeSet h seed α))

/-- The seed is a member of every stage. -/
theorem seed_mem_universeSet (α : L) : seed ∈ universeSet h seed α :=
  HSet.mem_wellFoundedPartEquivZFSet_symm_iff.mp ((𝒯).seed_mem 𝒪 𝒞 α)

/-- An earlier stage is a member of every later stage. -/
theorem universeSet_mem_of_lt {α β : L} (hβα : β < α) :
    universeSet h seed β ∈ universeSet h seed α :=
  HSet.mem_wellFoundedPartEquivZFSet_symm_iff.mp ((𝒯).mem_of_lt 𝒪 𝒞 hβα)

/-- The tower is monotone: a stage is a subset of every stage at a level above. -/
theorem universeSet_mono {α β : L} (hβα : β ≤ α) :
    universeSet h seed β ⊆ universeSet h seed α :=
  WellFoundedPart.subset_symm_iff.mp ((𝒯).subset_of_le 𝒪 𝒞 hβα)

/-- Membership of stages is the strict order of levels. -/
theorem universeSet_mem_iff {α β : L} :
    universeSet h seed β ∈ universeSet h seed α ↔ β < α :=
  HSet.mem_wellFoundedPartEquivZFSet_symm_iff.symm.trans ((𝒯).mem_iff 𝒪 𝒞)

/-- Inclusion of stages is the order of levels. -/
theorem universeSet_subset_iff {α β : L} :
    universeSet h seed β ⊆ universeSet h seed α ↔ β ≤ α :=
  WellFoundedPart.subset_symm_iff.symm.trans ((𝒯).subset_iff 𝒪 𝒞)

/-- The tower is injective: distinct levels have distinct stages. -/
theorem universeSet_injective :
    Function.Injective (universeSet h seed : L → ZFSet.{u}) := fun _ _ heq =>
  (𝒯).injective 𝒪 𝒞 (congrArg ofZF heq)

/-- An earlier stage differs from every later stage. -/
theorem universeSet_ne_of_lt {α β : L} (hβα : β < α) :
    universeSet h seed β ≠ universeSet h seed α := fun heq =>
  ne_of_lt hβα (universeSet_injective h seed heq)

/-! ## The least level and successor levels -/

/-- A stage is the least closed universe around any of its members that includes the seed
and every earlier stage. -/
theorem universeSet_eq_univOf {α : L} {N : ZFSet.{u}} (hN : N ∈ universeSet h seed α)
    (hseed : seed ⊆ N) (hstages : ∀ β < α, universeSet h seed β ⊆ N) :
    universeSet h seed α = univOf h N :=
  Equiv.injective ofZF (((𝒯).eq_univOf 𝒪 𝒞 (HSet.mem_wellFoundedPartEquivZFSet_symm_iff.mpr hN)
    (WellFoundedPart.subset_symm_iff.mpr hseed)
    fun β hβ => WellFoundedPart.subset_symm_iff.mpr (hstages β hβ)).trans
    (WellFoundedPart.univOf_symm h N))

/-- The stage at the least level is the least closed universe around the seed. -/
theorem universeSet_bot : universeSet h seed (bot : L) = univOf h seed :=
  Equiv.injective ofZF (((𝒯).stage_bot 𝒪 𝒞).trans (WellFoundedPart.univOf_symm h seed))

/-- The stage at a successor level is the least closed universe around the previous
stage. -/
theorem universeSet_succ (l : L) :
    universeSet h seed (succ l) = univOf h (universeSet h seed l) :=
  Equiv.injective ofZF (((𝒯).stage_succ 𝒪 𝒞 l).trans (WellFoundedPart.univOf_symm h _))

/-- A stage is the least closed universe around another stage exactly when its level is the
successor of the other's. -/
theorem universeSet_eq_univOf_universeSet_iff {α β : L} :
    universeSet h seed α = univOf h (universeSet h seed β) ↔ α = succ β := by
  rw [← universeSet_succ]
  exact (universeSet_injective h seed).eq_iff

/-! ## Every stage encloses the earlier ones -/

/-- The set of the earlier stages is a member of the stage. -/
theorem earlierStages_mem (α : L) : earlierStages h seed α ∈ universeSet h seed α :=
  HSet.mem_wellFoundedPartEquivZFSet_symm_iff.mp
    ((𝒯).earlierStages_mem 𝒪 𝒞 (isEarlierStages_universeSet h seed α))

/-- The set of the earlier stages is a member of no earlier stage. -/
theorem earlierStages_notMem_of_lt {α β : L} (hβα : β < α) :
    earlierStages h seed α ∉ universeSet h seed β :=
  ZFSet.mem_asymm (mem_earlierStages.mpr ⟨β, hβα, rfl⟩)

/-- The set of the earlier stages is not a member of their union. -/
theorem earlierStages_notMem_sUnion (α : L) :
    earlierStages h seed α ∉ ZFSet.sUnion (earlierStages h seed α) := fun hmem =>
  let ⟨_, hβ, hx⟩ := mem_sUnion_earlierStages.mp hmem
  earlierStages_notMem_of_lt h seed hβ hx

/-- The union of the earlier stages is a member of the stage: the stage encloses it. -/
theorem sUnion_earlierStages_mem (α : L) :
    ZFSet.sUnion (earlierStages h seed α) ∈ universeSet h seed α :=
  (universeSet_closed h seed α).union_mem (earlierStages_mem h seed α)

/-- The union of the earlier stages is a proper subset of the stage. -/
theorem sUnion_earlierStages_ssubset (α : L) :
    ZFSet.sUnion (earlierStages h seed α) ⊂ universeSet h seed α :=
  ssubset_of_subset_not_superset
    ((universeSet_closed h seed α).transitive _ (sUnion_earlierStages_mem h seed α))
    fun hsub => earlierStages_notMem_sUnion h seed α (hsub (earlierStages_mem h seed α))

/-- At a positive level the stage is the least closed universe around the union of the
earlier stages. -/
theorem universeSet_eq_univOf_sUnion {α : L} (hα : bot < α) :
    universeSet h seed α = univOf h (ZFSet.sUnion (earlierStages h seed α)) :=
  universeSet_eq_univOf h seed (sUnion_earlierStages_mem h seed α)
    (fun _ hx => mem_sUnion_earlierStages.mpr ⟨bot, hα,
      (universeSet_closed h seed bot).transitive _ (seed_mem_universeSet h seed bot) hx⟩)
    fun β hβ _ hx => mem_sUnion_earlierStages.mpr ⟨β, hβ, hx⟩

/-- At a successor level the union of the earlier stages is the previous stage. -/
theorem sUnion_earlierStages_succ (l : L) :
    ZFSet.sUnion (earlierStages h seed (succ l)) = universeSet h seed l :=
  ZFSet.ext fun _ => mem_sUnion_earlierStages.trans
    ⟨fun ⟨_, hβ, hx⟩ => universeSet_mono h seed (le_of_lt_succ hβ) hx,
      fun hx => ⟨l, lt_succ l, hx⟩⟩

/-- The union of the earlier stages is a stage exactly at a successor level, where it is
the previous stage. -/
theorem sUnion_earlierStages_eq_universeSet_iff {α β : L} :
    ZFSet.sUnion (earlierStages h seed α) = universeSet h seed β ↔ α = succ β := by
  rw [← (𝒯).sUnion_earlierStages_eq_stage_iff 𝒪 𝒞 (isEarlierStages_universeSet h seed α),
    WellFoundedPart.sUnion_symm, Equiv.apply_eq_iff_eq]

/-! ## The least closed universe with the earlier stages as members -/

/-- A closed universe that has the stages along a sequence of levels as members includes
the stage at every level whose lower levels all lie at or below members of the sequence. -/
theorem universeSet_subset_of_sequence_mem {α : L} (c : Nat → L)
    (hcof : ∀ β < α, ∃ n, β ≤ c n) {V : ZFSet.{u}}
    (hV : ∀ n, universeSet h seed (c n) ∈ V) (closed : Closed V) :
    universeSet h seed α ⊆ V :=
  WellFoundedPart.subset_symm_iff.mp ((𝒯).subset_of_sequence_mem 𝒪 𝒞 c hcof
    (fun n => HSet.mem_wellFoundedPartEquivZFSet_symm_iff.mpr (hV n))
    (WellFoundedPart.isGrothendieckUniverse_symm_iff.mpr closed))

/-- At a level with countably many predecessors, the stage is the least closed universe
that has the seed and every earlier stage as members: it is included in every closed
universe with these members. -/
theorem universeSet_subset_of_forall_mem {α : L} [Countable {β : L // β < α}]
    {V : ZFSet.{u}} (hseed : seed ∈ V) (hV : ∀ β < α, universeSet h seed β ∈ V)
    (closed : Closed V) : universeSet h seed α ⊆ V :=
  WellFoundedPart.subset_symm_iff.mp ((𝒯).subset_of_forall_mem 𝒪 𝒞
    (HSet.mem_wellFoundedPartEquivZFSet_symm_iff.mpr hseed)
    (fun β hβ => HSet.mem_wellFoundedPartEquivZFSet_symm_iff.mpr (hV β hβ))
    (WellFoundedPart.isGrothendieckUniverse_symm_iff.mpr closed))

/-! ## Limit levels -/

/-- Below a limit level the union of the stages is not a stage. -/
theorem sUnion_earlierStages_ne_universeSet_of_isLimit {α : L} (hα : IsLimit α) (β : L) :
    ZFSet.sUnion (earlierStages h seed α) ≠ universeSet h seed β := fun heq =>
  hα.2 β ((sUnion_earlierStages_eq_universeSet_iff h seed).mp heq).symm

/-- The stage at a limit level is not the least closed universe around any single stage. -/
theorem universeSet_ne_univOf_universeSet_of_isLimit {α : L} (hα : IsLimit α) (β : L) :
    universeSet h seed α ≠ univOf h (universeSet h seed β) := fun heq =>
  hα.2 β ((universeSet_eq_univOf_universeSet_iff h seed).mp heq).symm

/-- At a limit level with countably many predecessors, the union of the earlier stages is
not a closed universe: it has the seed and every earlier stage as members, so if it were
closed it would include the stage itself. -/
theorem sUnion_earlierStages_not_closed {α : L} [Countable {β : L // β < α}]
    (hα : IsLimit α) : ¬ Closed (ZFSet.sUnion (earlierStages h seed α)) := fun closed =>
  (𝒯).sUnion_earlierStages_not_isGrothendieckUniverse 𝒪 𝒞
    (isEarlierStages_universeSet h seed α) hα (by
      rw [WellFoundedPart.sUnion_symm]
      exact WellFoundedPart.isGrothendieckUniverse_symm_iff.mpr closed)

/-! ## Initial embeddings of level orders -/

/-- The tower commutes with initial embeddings of level orders: the stage at the image of a
level is the stage at that level. -/
theorem universeSet_map {L' : Type} [LevelOrder L'] (f : Embedding L L')
    (initial : f.Initial) (α : L) : universeSet h seed (f α) = universeSet h seed α :=
  Equiv.injective ofZF ((𝒯).map_eq 𝒞 (isUniverseTower_universeSet h seed) f initial α)

/-- The finite stages of the tower over any level order are the stages of the tower over
the natural numbers. -/
theorem universeSet_ofNat (n : Nat) :
    universeSet h seed (ofNat n : L) = universeSet h seed n :=
  universeSet_map h seed (Embedding.ofNat L) (Embedding.ofNat_initial L) n

end Tower

/-! ## The seed -/

section Seed

variable {L : Type} [LevelOrder L] (h : CofinalInaccessibles.{u})

/-- The tower is monotone in the seed. -/
theorem universeSet_seed_mono {small large : ZFSet.{u}} (below : small ⊆ large) (α : L) :
    universeSet h small α ⊆ universeSet h large α :=
  WellFoundedPart.subset_symm_iff.mp (WellFoundedPart.IsUniverseTower.seed_mono
    (WellFoundedPart.isUniverseOperator_univOf h)
    (isUniverseTower_universeSet h small) (collectsEarlierStages_universeSet h small)
    (isUniverseTower_universeSet h large) (collectsEarlierStages_universeSet h large)
    (WellFoundedPart.subset_symm_iff.mpr below) α)

end Seed

/-! ## The ordinal notations below ε₀ -/

-- The notation trees are countable. The instance is stated here, with the sets, because
-- its derivation uses choice, which the notations themselves do not.
deriving instance Countable for Cnf

/-- The ordinal notations below ε₀ are countable, so every level has countably many
predecessors. -/
instance : Countable Level := inferInstanceAs (Countable {x : Cnf // x.NF})

/-! ## Examples -/

section Examples

variable (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})

/-- The tower's equation with the set of the earlier stages written out. -/
example {L : Type} [LevelOrder L] (α : L) :
    universeSet h seed α =
      univOf h (insert seed (ZFSet.range fun β : {β : L // β < α} => universeSet h seed β.1)) :=
  universeSet_eq h seed α

/-- Over the natural numbers the stage at zero is the least closed universe around the
seed. -/
theorem universeSet_nat_zero : universeSet h seed (0 : Nat) = univOf h seed :=
  universeSet_bot h seed

/-- Over the natural numbers the stage at `n + 1` is the least closed universe around the
stage at `n`. -/
theorem universeSet_nat_succ (n : Nat) :
    universeSet h seed (n + 1) = univOf h (universeSet h seed n) :=
  universeSet_succ h seed n

/-- Over the ordinal notations below ε₀, every finite stage is a member of the stage at
`ω`. -/
theorem universeSet_ofNat_mem_omega (n : Nat) :
    universeSet h seed (Level.ofNat n) ∈ universeSet h seed Level.omega :=
  universeSet_mem_of_lt h seed (Level.ofNat_lt_omega n)

/-- The finite stages over the ordinal notations are the stages over the natural
numbers. -/
theorem universeSet_level_ofNat (n : Nat) :
    universeSet h seed (Level.ofNat n) = universeSet h seed n := by
  rw [← Level.levelOrder_ofNat]
  exact universeSet_ofNat h seed n

/-- The stage at `ω` is the least closed universe around the union of the stages below
`ω`. -/
theorem universeSet_omega :
    universeSet h seed Level.omega =
      univOf h (ZFSet.sUnion (earlierStages h seed Level.omega)) :=
  universeSet_eq_univOf_sUnion h seed Level.isLimit_omega.1

/-- No stage is a member of itself. -/
example {L : Type} [LevelOrder L] (α : L) :
    universeSet h seed α ∉ universeSet h seed α :=
  ZFSet.mem_irrefl _

/-- The stage at `ω` is included in every closed universe that has every finite stage as a
member: it is the least such universe. -/
theorem universeSet_omega_subset {V : ZFSet.{u}}
    (hV : ∀ n, universeSet h seed (Level.ofNat n) ∈ V) (closed : Closed V) :
    universeSet h seed Level.omega ⊆ V :=
  universeSet_subset_of_sequence_mem h seed Level.ofNat
    (fun _ hβ => (Level.exists_lt_ofNat_of_lt_omega hβ).imp fun _ => le_of_lt) hV closed

/-- Over the ordinal notations below ε₀, every stage is the least closed universe that has
the seed and every earlier stage as members. -/
example {α : Level} {V : ZFSet.{u}} (hseed : seed ∈ V)
    (hV : ∀ β < α, universeSet h seed β ∈ V) (closed : Closed V) :
    universeSet h seed α ⊆ V :=
  universeSet_subset_of_forall_mem h seed hseed hV closed

/-- Over the ordinal notations below ε₀, the union of the earlier stages is a closed
universe at no limit level. -/
example {α : Level} (hα : IsLimit α) :
    ¬ Closed (ZFSet.sUnion (earlierStages h seed α)) :=
  sUnion_earlierStages_not_closed h seed hα

/-- The union of the stages below `ω` is not a closed universe. -/
theorem sUnion_earlierStages_omega_not_closed :
    ¬ Closed (ZFSet.sUnion (earlierStages h seed Level.omega)) :=
  sUnion_earlierStages_not_closed h seed Level.isLimit_omega

/-- The stage at `ω` is not the least closed universe around any single stage: `ω` has no
predecessor. -/
theorem universeSet_omega_ne_univOf_universeSet (β : Level) :
    universeSet h seed Level.omega ≠ univOf h (universeSet h seed β) :=
  universeSet_ne_univOf_universeSet_of_isLimit h seed Level.isLimit_omega β

end Examples

end Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation
