import Mettapedia.Machines.Cursor.TailSummary

/-!
# Sharing across generations

A term is a tree whose nodes live at homes: arenas, or storage that is never
released.  An arena may name one older generation, whose storage outlives its
own: the older generation is released only together with the younger.

A node is closed when every child is closed and lives in the node's own
arena, in that arena's older generation, or in storage that is never
released.  Closure is folded from the children, one bit per node.  Every
descendant of a closed node then lives in the node's arena, along its chain of
older generations, or in storage that is never released
(`closed_descendant_home`).  A release that follows the generation order
therefore never releases a descendant of a node it keeps
(`kept_descendants_survive`).

A transfer into a destination arena copies exactly the nodes that are not
settled there, and shares the others.  A node is settled when it is closed
and lives in the destination, in its older generation, or in storage that is
never released.  The result is closed and lives there too
(`transfer_closed`, `transfer_settled`), so releasing the arena the value came
from, which is on no chain the destination reaches, leaves the result whole
(`transfer_survives_source_release`).

The transfer takes a sharing policy: an implementation may share fewer settled
nodes than it could, and every result holds for every policy.  The runtime
shares only nodes in an arena, never ones in storage that is never released
(`arena_policy_copies_global`).

A suffix view may share its parent's storage when that storage is in the
view's arena or in its older generation (`older_storage_outlives`).  With one
level of generations, where an older generation has none of its own, the view
is closed whenever its parent is (`suffix_view_closed`).

Releasing part of an arena, everything allocated after a mark, is safe for a
kept node when nothing outside that arena was allocated since the mark: every
child is allocated before its parent (`quiescent_mark_release_safe`).

The controls show that each hypothesis carries weight: releasing an older
generation alone strands a kept node's child, sharing a node from an arena the
destination does not reach strands the result, and a child two generations
older is not admitted by the one-link test, which is conservative: such a
child is copied, not lost.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.GenerationalSharing

open Mettapedia.Machines.Cursor.TailSummary (Home)

/-! ## Terms and generations -/

/-- A term node: its home and its children. -/
inductive Node
  | mk (home : Home) (children : List Node)

namespace Node

/-- The home of a node. -/
def home : Node → Home
  | mk h _ => h

/-- The children of a node. -/
def children : Node → List Node
  | mk _ cs => cs

end Node

/-- The generations: each arena may name its older generation. -/
structure Generations where
  older : ℕ → Option ℕ

/-- One step along the generation order: `g` is the older generation of `a`. -/
def Generations.Older (G : Generations) (a g : ℕ) : Prop := G.older a = some g

/-- Whether a child at home `there` may be referenced from an arena `here`: it
is never released, lives in `here`, or lives in `here`'s older generation. -/
def Generations.admits (G : Generations) (here : ℕ) : Home → Bool
  | .global => true
  | .arena there => there == here || G.older here == some there

/-- A node's own arena, for the closure test: storage that is never released
admits only children that are never released either. -/
def Generations.admitsFrom (G : Generations) : Home → Home → Bool
  | .arena here, there => G.admits here there
  | .global, .global => true
  | .global, .arena _ => false

mutual
/-- The closure bit, folded from the children. -/
def closed (G : Generations) : Node → Bool
  | .mk h cs => closedAll G h cs

/-- Every child is closed and admitted from `h`. -/
def closedAll (G : Generations) (h : Home) : List Node → Bool
  | [] => true
  | c :: cs => (closed G c && G.admitsFrom h c.home) && closedAll G h cs
end

theorem closedAll_iff (G : Generations) (h : Home) (cs : List Node) :
    closedAll G h cs = true ↔
      ∀ c ∈ cs, closed G c = true ∧ G.admitsFrom h c.home = true := by
  induction cs with
  | nil => simp [closedAll]
  | cons c cs ih =>
      simp only [closedAll, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, ih]

theorem closed_mk (G : Generations) (h : Home) (cs : List Node) :
    closed G (.mk h cs) = true ↔
      ∀ c ∈ cs, closed G c = true ∧ G.admitsFrom h c.home = true := by
  rw [closed, closedAll_iff]

/-! ## Linking a generation later -/

/-- Generations `G'` extend `G` when every older generation `G` names, `G'`
names too. -/
def Extends (G G' : Generations) : Prop := ∀ a g, G.Older a g → G'.Older a g

theorem admits_mono (G G' : Generations) (ext : Extends G G') (h there : Home)
    (admitted : G.admitsFrom h there = true) : G'.admitsFrom h there = true := by
  cases h with
  | global =>
      cases there with
      | global => rfl
      | arena _ => simp [Generations.admitsFrom] at admitted
  | arena here =>
      cases there with
      | global => rfl
      | arena t =>
          simp only [Generations.admitsFrom, Generations.admits, Bool.or_eq_true,
            beq_iff_eq] at admitted ⊢
          rcases admitted with same | older
          · exact Or.inl same
          · exact Or.inr (ext here t older)

/-- **Closure survives linking a generation later**: a node closed before an
arena named its older generation stays closed after.  So an arena may take
its older generation once there is something to share, and the bits its atoms
folded before stay sound. -/
theorem closed_mono (G G' : Generations) (ext : Extends G G') (n : Node)
    (isClosed : closed G n = true) : closed G' n = true := by
  refine Node.rec
    (motive_1 := fun n => closed G n = true → closed G' n = true)
    (motive_2 := fun cs => ∀ c ∈ cs, closed G c = true → closed G' c = true)
    ?mk ?nil ?cons n isClosed
  case mk =>
    intro h cs ih closedBefore
    rw [closed_mk] at closedBefore ⊢
    intro c mem
    have facts := closedBefore c mem
    exact ⟨ih c mem facts.1, admits_mono G G' ext h c.home facts.2⟩
  case nil =>
    intro c mem
    exact absurd mem List.not_mem_nil
  case cons =>
    intro c cs ihc ihcs x mem
    rcases List.mem_cons.mp mem with same | rest
    · subst same; exact ihc
    · exact ihcs x rest

/-- No generations at all, and the machine's once its tenured arena `2`
holds something, linked to its nursery `1`: the second extends the first. -/
def unlinked : Generations := ⟨fun _ => none⟩

def linkedMachine : Generations := ⟨fun a => if a = 1 then some 2 else none⟩

theorem machine_extends_unlinked : Extends unlinked linkedMachine := by
  intro a g older
  simp [Generations.Older, unlinked] at older

/-! ## Descendants of a closed node -/

/-- `d` is `n` or lies below it. -/
inductive Below : Node → Node → Prop
  | refl (n : Node) : Below n n
  | child {h : Home} {cs : List Node} {c d : Node} :
      c ∈ cs → Below c d → Below (.mk h cs) d

/-- The homes a node at `h` may reach: storage that is never released, or an
arena along the chain of older generations from `h`. -/
def Reaches (G : Generations) : Home → Home → Prop
  | .global, there => there = .global
  | .arena here, there =>
      there = .global ∨ ∃ g, Relation.ReflTransGen G.Older here g ∧ there = .arena g

theorem reaches_self (G : Generations) (h : Home) : Reaches G h h := by
  cases h with
  | global => rfl
  | arena here => exact Or.inr ⟨here, Relation.ReflTransGen.refl, rfl⟩

/-- An admitted child's home is reached from the parent's. -/
theorem reaches_of_admits (G : Generations) (h there : Home)
    (admitted : G.admitsFrom h there = true) : Reaches G h there := by
  cases h with
  | global =>
      cases there with
      | global => rfl
      | arena _ => simp [Generations.admitsFrom] at admitted
  | arena here =>
      cases there with
      | global => exact Or.inl rfl
      | arena t =>
          simp only [Generations.admitsFrom, Generations.admits, Bool.or_eq_true,
            beq_iff_eq] at admitted
          rcases admitted with same | older
          · subst same
            exact Or.inr ⟨t, Relation.ReflTransGen.refl, rfl⟩
          · exact Or.inr ⟨t, Relation.ReflTransGen.single older, rfl⟩

/-- Reaching composes along the generation order. -/
theorem reaches_trans (G : Generations) (a b c : Home)
    (ab : Reaches G a b) (bc : Reaches G b c) : Reaches G a c := by
  cases a with
  | global =>
      have : b = .global := ab
      subst this
      exact bc
  | arena x =>
      rcases ab with bGlobal | ⟨g, xg, bEq⟩
      · subst bGlobal
        have : c = .global := bc
        subst this
        exact Or.inl rfl
      · subst bEq
        rcases bc with cGlobal | ⟨g', gg', cEq⟩
        · exact Or.inl cGlobal
        · exact Or.inr ⟨g', xg.trans gg', cEq⟩

/-- **Every descendant of a closed node lives where the node reaches.** -/
theorem closed_descendant_home (G : Generations) (n d : Node)
    (below : Below n d) (isClosed : closed G n = true) :
    Reaches G n.home d.home ∧ closed G d = true := by
  induction below with
  | refl n => exact ⟨reaches_self G n.home, isClosed⟩
  | @child h cs c d mem _ ih =>
      have facts := (closed_mk G h cs).mp isClosed c mem
      have step := ih facts.1
      exact ⟨reaches_trans G h c.home d.home
        (reaches_of_admits G h c.home facts.2) step.1, step.2⟩

/-! ## Releases that follow the generation order -/

/-- A release: the arenas it frees.  It follows the generation order when
freeing an older generation frees the younger too. -/
def FollowsGenerations (G : Generations) (released : ℕ → Prop) : Prop :=
  ∀ a g, G.Older a g → released g → released a

/-- Whether a release frees storage at a home. -/
def Frees (released : ℕ → Prop) : Home → Prop
  | .global => False
  | .arena id => released id

/-- Along the generation order, a freed older arena frees the arena it was
reached from. -/
theorem freed_along_chain (G : Generations) (released : ℕ → Prop)
    (order : FollowsGenerations G released) (a g : ℕ)
    (chain : Relation.ReflTransGen G.Older a g) (freed : released g) :
    released a := by
  induction chain using Relation.ReflTransGen.head_induction_on with
  | refl => exact freed
  | head step _ ih => exact order _ _ step ih

/-- **A release that follows the generation order frees no descendant of a
closed node it keeps.** -/
theorem kept_descendants_survive (G : Generations) (released : ℕ → Prop)
    (order : FollowsGenerations G released) (n d : Node)
    (isClosed : closed G n = true) (kept : ¬ Frees released n.home)
    (below : Below n d) : ¬ Frees released d.home := by
  have reach := (closed_descendant_home G n d below isClosed).1
  intro freedD
  revert reach kept freedD
  cases n.home with
  | global =>
      intro _ reach freedD
      have : d.home = .global := reach
      rw [this] at freedD
      exact freedD
  | arena here =>
      intro kept reach freedD
      rcases reach with isGlobal | ⟨g, chain, dEq⟩
      · rw [isGlobal] at freedD
        exact freedD
      · rw [dEq] at freedD
        exact kept (freed_along_chain G released order here g chain freedD)

/-! ## Transfers copy what is not settled -/

/-- A node is settled at `dst` when it is closed and admitted from `dst`. -/
def settled (G : Generations) (dst : ℕ) (n : Node) : Bool :=
  closed G n && G.admits dst n.home

/-- Admission from an arena, as the closure test reads it. -/
theorem reaches_admits_home (G : Generations) (dst : ℕ) (there : Home)
    (admitted : G.admits dst there = true) :
    G.admitsFrom (.arena dst) there = true := admitted

mutual
/-- The transfer into `dst` under a sharing policy: a settled node the policy
shares is shared; any other node is copied into `dst`, over the transfers of
its children.  An implementation may share fewer settled nodes than it could:
every theorem below holds for every policy. -/
def transfer (G : Generations) (dst : ℕ) (share : Node → Bool) : Node → Node
  | .mk h cs =>
      if settled G dst (.mk h cs) && share (.mk h cs) then .mk h cs
      else .mk (.arena dst) (transferAll G dst share cs)

/-- The transfers of a list of children. -/
def transferAll (G : Generations) (dst : ℕ) (share : Node → Bool) :
    List Node → List Node
  | [] => []
  | c :: cs => transfer G dst share c :: transferAll G dst share cs
end

theorem transferAll_eq_map (G : Generations) (dst : ℕ) (share : Node → Bool)
    (cs : List Node) :
    transferAll G dst share cs = cs.map (transfer G dst share) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [transferAll, ih, List.map_cons]

theorem transfer_mk (G : Generations) (dst : ℕ) (share : Node → Bool)
    (h : Home) (cs : List Node) :
    transfer G dst share (.mk h cs) =
      if settled G dst (.mk h cs) && share (.mk h cs) then .mk h cs
      else .mk (.arena dst) (cs.map (transfer G dst share)) := by
  rw [transfer, transferAll_eq_map]

/-- **The transfer's result is settled at the destination**: closed, and at the
destination, its older generation, or storage never released. -/
theorem transfer_settled (G : Generations) (dst : ℕ) (share : Node → Bool)
    (n : Node) : settled G dst (transfer G dst share n) = true := by
  refine Node.rec
    (motive_1 := fun n => settled G dst (transfer G dst share n) = true)
    (motive_2 := fun cs => ∀ c ∈ cs, settled G dst (transfer G dst share c) = true)
    ?mk ?nil ?cons n
  case mk =>
    intro h cs ih
    rw [transfer_mk]
    split
    · rename_i sharedIt
      simp only [Bool.and_eq_true] at sharedIt
      exact sharedIt.1
    · simp only [settled, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [closed_mk]
        intro c mem
        rcases List.mem_map.mp mem with ⟨c0, mem0, rfl⟩
        have s := ih c0 mem0
        simp only [settled, Bool.and_eq_true] at s
        exact ⟨s.1, reaches_admits_home G dst _ s.2⟩
      · simp [Node.home, Generations.admits]
  case nil =>
    intro c mem
    exact absurd mem List.not_mem_nil
  case cons =>
    intro c cs ihc ihcs x mem
    rcases List.mem_cons.mp mem with same | rest
    · subst same; exact ihc
    · exact ihcs x rest

theorem transfer_closed (G : Generations) (dst : ℕ) (share : Node → Bool)
    (n : Node) : closed G (transfer G dst share n) = true := by
  have s := transfer_settled G dst share n
  simp only [settled, Bool.and_eq_true] at s
  exact s.1

/-- A settled node at `dst` is reached from `dst`. -/
theorem reaches_of_settled (G : Generations) (dst : ℕ) (n : Node)
    (s : settled G dst n = true) : Reaches G (.arena dst) n.home := by
  simp only [settled, Bool.and_eq_true] at s
  exact reaches_of_admits G (.arena dst) n.home s.2

/-- **Releasing where a value came from leaves its transfer whole.**  Any
release that follows the generation order and keeps the destination frees
no descendant of the result: in particular a scratch arena that is nobody's
older generation, released alone. -/
theorem transfer_survives_source_release (G : Generations)
    (released : ℕ → Prop) (order : FollowsGenerations G released) (dst : ℕ)
    (share : Node → Bool) (keepsDst : ¬ released dst) (n d : Node)
    (below : Below (transfer G dst share n) d) : ¬ Frees released d.home := by
  have s := transfer_settled G dst share n
  have reach :=
    (closed_descendant_home G _ d below (transfer_closed G dst share n)).1
  have dstReach := reaches_of_settled G dst _ s
  have total := reaches_trans G _ _ _ dstReach reach
  intro freedD
  rcases total with isGlobal | ⟨g, chain, dEq⟩
  · rw [isGlobal] at freedD
    exact freedD
  · rw [dEq] at freedD
    exact keepsDst (freed_along_chain G released order dst g chain freedD)

/-- Releasing one arena that is nobody's older generation follows the order. -/
theorem single_release_follows (G : Generations) (s : ℕ)
    (young : ∀ a, ¬ G.Older a s) : FollowsGenerations G (fun r => r = s) := by
  intro a g older freed
  subst freed
  exact absurd older (young a)

/-- Releasing a younger arena together with its older generation follows the
order when nothing else names either as its older generation. -/
theorem pair_release_follows (G : Generations) (young old : ℕ)
    (link : G.Older young old)
    (onlyYoung : ∀ a, G.Older a old → a = young)
    (noneOlderYoung : ∀ a, ¬ G.Older a young) :
    FollowsGenerations G (fun r => r = young ∨ r = old) := by
  intro a g older freed
  rcases freed with isYoung | isOld
  · subst isYoung; exact absurd older (noneOlderYoung a)
  · subst isOld; exact Or.inl (onlyYoung a older)

/-! ## Views over older storage -/

/-- A view allocated in `young` over storage of `young`'s older generation is
released no later than the storage: releasing the storage releases the view's
arena too. -/
theorem older_storage_outlives (G : Generations) (released : ℕ → Prop)
    (order : FollowsGenerations G released) (young old : ℕ)
    (link : G.Older young old) (freed : released old) : released young :=
  order young old link freed

/-- One level of generations: an older generation has no older generation of
its own.  The machine's tenured storage is such a generation. -/
def OneLevel (G : Generations) : Prop := ∀ a g, G.Older a g → G.older g = none

/-- **A suffix view is closed in the view's arena** when its parent is closed in
that arena, or in that arena's older generation under one level: every child
the view keeps was admitted from the parent's arena, and so is admitted from
the view's. -/
theorem suffix_view_closed (G : Generations) (young : ℕ) (h : Home)
    (cs : List Node) (k : ℕ) (parent : closed G (.mk h cs) = true)
    (placed : h = .arena young ∨
      (∃ g, h = .arena g ∧ G.Older young g ∧ OneLevel G)) :
    closed G (.mk (.arena young) (cs.drop k)) = true := by
  rw [closed_mk] at parent ⊢
  intro c mem
  have facts := parent c (List.mem_of_mem_drop mem)
  refine ⟨facts.1, ?_⟩
  rcases placed with same | ⟨g, hg, link, oneLevel⟩
  · subst same; exact facts.2
  · subst hg
    have none := oneLevel young g link
    have admitted := facts.2
    cases home : c.home with
    | global => simp [Generations.admitsFrom, Generations.admits]
    | arena there =>
        rw [home] at admitted
        simp only [Generations.admitsFrom, Generations.admits, Bool.or_eq_true,
          beq_iff_eq, none, reduceCtorEq, or_false] at admitted
        subst admitted
        simp only [Generations.admitsFrom, Generations.admits, Bool.or_eq_true, beq_iff_eq]
        exact Or.inr link

/-! ## Releasing part of an arena -/

/-- Allocation positions: each node has one, and children precede parents. -/
structure Allocation where
  pos : Node → ℕ
  children_first : ∀ h cs c, c ∈ cs → pos c < pos (.mk h cs)

/-- Descendants were allocated no later than their ancestor. -/
theorem below_pos_le (A : Allocation) (n d : Node) (below : Below n d) :
    A.pos d ≤ A.pos n := by
  induction below with
  | refl => exact le_refl _
  | @child h cs c d mem _ ih =>
      exact le_trans ih (le_of_lt (A.children_first h cs c mem))

/-- Releasing everything arena `a` allocated at or after mark `m`. -/
def FreedAfter (A : Allocation) (a m : ℕ) (n : Node) : Prop :=
  n.home = .arena a ∧ m ≤ A.pos n

/-- **A quiescent mark release is safe.**  When every node allocated at or
after the mark lives in the released arena, a node that is not freed was
allocated before the mark, and so was every descendant: none is freed. -/
theorem quiescent_mark_release_safe (A : Allocation) (a m : ℕ) (n d : Node)
    (quiescent : ∀ x, m ≤ A.pos x → x.home = .arena a)
    (kept : ¬ FreedAfter A a m n) (below : Below n d) :
    ¬ FreedAfter A a m d := by
  have early : A.pos n < m := by
    by_contra late
    exact kept ⟨quiescent n (Nat.le_of_not_lt late), Nat.le_of_not_lt late⟩
  intro freed
  have late := freed.2
  have := below_pos_le A n d below
  omega

/-! ## A tenured store shared by the machine and a cursor -/

/-- The machine's nursery `1` and a cursor's region `3` both name the tenured
arena `2` as their older generation. -/
def shared : Generations :=
  ⟨fun a => if a = 1 then some 2 else if a = 3 then some 2 else none⟩

theorem shared_older_iff (a g : ℕ) : shared.Older a g ↔ (a = 1 ∨ a = 3) ∧ g = 2 := by
  simp only [Generations.Older, shared]
  split_ifs with h1 h3 <;> simp_all [eq_comm]

theorem shared_oneLevel : OneLevel shared := by
  intro a g older
  rw [((shared_older_iff a g).mp older).2]
  decide

/-- Releasing the nursery alone, at a collection or a reset, follows the
order, as does releasing the region alone at its own collection. -/
theorem nursery_release_follows : FollowsGenerations shared (fun r => r = 1) := by
  apply single_release_follows
  intro a older
  exact absurd ((shared_older_iff a 1).mp older).2 (by decide)

theorem region_release_follows : FollowsGenerations shared (fun r => r = 3) := by
  apply single_release_follows
  intro a older
  exact absurd ((shared_older_iff a 3).mp older).2 (by decide)

/-- Releasing tenured storage follows the order only together with every
arena that names it: the nursery and the region. -/
theorem tenured_release_follows :
    FollowsGenerations shared (fun r => r = 1 ∨ r = 2 ∨ r = 3) := by
  intro a g older freed
  rcases (shared_older_iff a g).mp older with ⟨young, _⟩
  rcases young with one | three
  · exact Or.inl one
  · exact Or.inr (Or.inr three)

/-- While a cursor lives, tenured storage may not be released: releasing it
with the nursery but not the region breaks the order. -/
theorem tenured_with_live_cursor_breaks :
    ¬ FollowsGenerations shared (fun r => r = 1 ∨ r = 2) := by
  intro order
  rcases order 3 2 ((shared_older_iff 3 2).mpr ⟨Or.inr rfl, rfl⟩) (Or.inr rfl) with bad | bad
  · exact absurd bad (by decide)
  · exact absurd bad (by decide)

/-- **Detaching before the nursery is released.**  A region value borrowed
from the nursery is transferred into tenured storage before the nursery is
released; the transfer then has no descendant the release frees. -/
theorem detach_into_tenured_survives (share : Node → Bool) (n d : Node)
    (below : Below (transfer shared 2 share n) d) :
    ¬ Frees (fun r => r = 1) d.home :=
  transfer_survives_source_release shared (fun r => r = 1)
    nursery_release_follows 2 share (by decide) n d below

/-- A region value over tenured structure survives the nursery's release
and the region's own collection alike. -/
theorem region_over_tenured_survives :
    let v : Node := .mk (.arena 3) [.mk (.arena 2) [], .mk .global []]
    closed shared v = true ∧
      (∀ d, Below v d → ¬ Frees (fun r => r = 1) d.home) := by
  refine ⟨by decide, ?_⟩
  intro d below
  exact kept_descendants_survive shared (fun r => r = 1) nursery_release_follows
    _ d (by decide) (by intro freed; exact absurd (show (3 : ℕ) = 1 from freed) (by decide))
    below

/-! ## Controls -/

namespace Controls

/-- The machine's shape: nursery `1` names tenured `2` as its older
generation. -/
def machine : Generations := ⟨fun a => if a = 1 then some 2 else none⟩

/-- A nursery node over a tenured child is closed. -/
theorem nursery_over_tenured_closed :
    closed machine (.mk (.arena 1) [.mk (.arena 2) []]) = true := by
  decide

/-- Releasing the older generation alone strands the kept node's child. -/
theorem older_alone_strands_child :
    let n : Node := .mk (.arena 1) [.mk (.arena 2) []]
    closed machine n = true ∧ ¬ Frees (fun r => r = 2) n.home ∧
      Below n (.mk (.arena 2) []) ∧ Frees (fun r => r = 2) (Home.arena 2) := by
  refine ⟨by decide, ?_, Below.child (List.mem_singleton.mpr rfl) (Below.refl _), rfl⟩
  intro freed
  exact absurd (show (1 : ℕ) = 2 from freed) (by decide)

/-- That release does not follow the generation order. -/
theorem older_alone_breaks_order : ¬ FollowsGenerations machine (fun r => r = 2) := by
  intro order
  have := order 1 2 (by simp [Generations.Older, machine]) rfl
  exact absurd this (by decide)

/-- A child in scratch arena `3` is not settled at the nursery, so the transfer
copies it; sharing it instead would strand the result once the scratch arena
is released. -/
theorem scratch_child_not_settled :
    settled machine 1 (.mk (.arena 3) []) = false := by
  decide

theorem sharing_scratch_strands :
    let shared : Node := .mk (.arena 1) [.mk (.arena 3) []]
    Below shared (.mk (.arena 3) []) ∧ Frees (fun r => r = 3) (Home.arena 3) ∧
      ¬ Frees (fun r => r = 3) shared.home := by
  refine ⟨Below.child (List.mem_singleton.mpr rfl) (Below.refl _), rfl, ?_⟩
  intro freed
  exact absurd (show (1 : ℕ) = 3 from freed) (by decide)

/-- The transfer copies the scratch child into the nursery. -/
theorem transfer_copies_scratch :
    transfer machine 1 (fun _ => true) (.mk (.arena 1) [.mk (.arena 3) []]) =
      .mk (.arena 1) [.mk (.arena 1) []] := by
  rfl

/-- The runtime's policy shares only nodes in an arena: a node in storage never
released is copied, which costs a copy and loses nothing. -/
def arenaOnly (n : Node) : Bool := n.home != .global

theorem arena_policy_copies_global :
    transfer machine 1 arenaOnly (.mk .global []) = .mk (.arena 1) [] ∧
      settled machine 1 (transfer machine 1 arenaOnly (.mk .global [])) = true := by
  refine ⟨rfl, transfer_settled machine 1 arenaOnly _⟩

/-- The tenured child is shared by the nursery transfer, under either policy. -/
theorem transfer_shares_tenured :
    transfer machine 1 arenaOnly (.mk (.arena 3) [.mk (.arena 2) []]) =
      .mk (.arena 1) [.mk (.arena 2) []] := by
  rfl

/-- A child two generations older is not admitted by the one-link test: the
parent is not closed, and the transfer copies rather than shares. -/
def threeGenerations : Generations :=
  ⟨fun a => if a = 1 then some 2 else if a = 2 then some 4 else none⟩

theorem two_generations_older_not_admitted :
    closed threeGenerations (.mk (.arena 1) [.mk (.arena 4) []]) = false ∧
      closed threeGenerations (.mk (.arena 2) [.mk (.arena 4) []]) = true := by
  decide

end Controls

#print axioms closed_descendant_home
#print axioms kept_descendants_survive
#print axioms transfer_settled
#print axioms transfer_survives_source_release
#print axioms quiescent_mark_release_safe
#print axioms suffix_view_closed
#print axioms closed_mono
#print axioms tenured_release_follows
#print axioms detach_into_tenured_survives

end Mettapedia.Machines.Cursor.GenerationalSharing
