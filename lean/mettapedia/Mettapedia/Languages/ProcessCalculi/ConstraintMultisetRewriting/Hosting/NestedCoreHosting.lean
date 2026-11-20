import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.WellFormedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NestedCore

/-!
# The nested-calls core, embedded in the source language, on the step

The nested-calls core (`ProgramNested`: held data, pairs evaluated left to right, calls by value,
leftmost-innermost) is embedded in the source language by `NestedCore`: a pair or a call becomes
arrows (`let_`) at slot sites and an `apply`. This module shows that the embedding of every program
(of one version) and of every query whose held data are ground falls under the run theorems with
arrows, so the step runs it.

* `rowNodes`: the row signature (numerals and one cell) has nodes: `(tag . (a₁ . (… . 0)))`.
* `trEquation_clauses`: every embedded equation is scoped, its site and its slot sites are distinct
  (`epatSlots`: the slots are tree addresses below the equation's path), and it is of the fragment
  with arrows; the same for the strict program's failing equation and for ground queries.
* `nested_runs_forward`, `nested_answers`, `nested_runs_reflected` (and the strict program's
  `nestedStrict_answers`, `nestedStrict_runs_reflected`): the run theorems for the embedding.

What this gives: calls by value with nested evaluation, **as the source language runs them**, are
run by the step, answers agreeing as bags. What it does not give: the correspondence between the
core's own reference semantics (`CStep`) and the source semantics of the embedding, which is the
open part of `NestedCore` (a solved-form relation between the core's rows and the language's stores,
a most general unifier of the core giving an idempotent most general solution, and the core's
evaluation contexts read as `let` frames). Queries with variables are not covered: the embedding
reads a core variable as an already opened name, which the source's query rule does not allow.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.NestedCoreHosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.NestedCore
open Mettapedia.Logic.LP
open ProgramRows ProgramNested

/-! ## The row signature has nodes -/

section RowNodes

variable {V : Type} {target : V → MetaArity RSig}

/-- The cell `(a . b)` over any family. -/
def cellAt (a b : Term (signature RSig target) [] ()) : Term (signature RSig target) [] () :=
  .op (.inl .cell) (.cons a (.cons b .nil))

/-- The numeral `k` over any family. -/
def constAt (k : ℕ) : Term (signature RSig target) [] () := .op (.inl (.const k)) .nil

/-- The data of a node, as cells ending in `0`. -/
def cellsOf : (n : ℕ) → (Fin n → Term (signature RSig target) [] ()) → Term (signature RSig target) [] ()
  | 0, _ => constAt 0
  | n + 1, f => cellAt (f 0) (cellsOf n fun i => f i.succ)

/-- A numeral for each former. -/
def tagCode : Tag → ℕ
  | .ret => 0
  | .apply => 1
  | .bind => 2
  | .choice => 3
  | .fail => 4
  | .outside => 5
  | .eval => 6
  | .value => 7
  | .empty => 8
  | .push => 9
  | .alt => 10
  | .eqn => 11
  | .query => 12
  | .fact => 13
  | .revision => 14

theorem tagCode_injective : Function.Injective tagCode := by
  intro a b same
  cases a <;> cases b <;> first | rfl | (simp [tagCode] at same)

/-- **The node** `(tag . (a₁ . (… . 0)))`. -/
def rowNode (k : Tag) (args : Fin k.arity → Term (signature RSig target) [] ()) :
    Term (signature RSig target) [] () :=
  cellAt (constAt (tagCode k)) (cellsOf k.arity args)

theorem instantiate_cellsOf {W : Type} {next : W → MetaArity RSig} (σ : Assignment target next) :
    ∀ (n : ℕ) (f : Fin n → Term (signature RSig target) [] ()),
      instantiate σ (cellsOf n f) = cellsOf n (fun i => instantiate σ (f i))
  | 0, _ => rfl
  | n + 1, f => by
      show cellAt (instantiate σ (f 0)) (instantiate σ (cellsOf n fun i => f i.succ)) = _
      rw [instantiate_cellsOf σ n]
      rfl

theorem rop_inj {o : ROp ()} {a b : Args (signature RSig target) (ROp.arity o) []}
    (same : (Term.op (Sum.inl o) a : Term (signature RSig target) [] ()) = Term.op (Sum.inl o) b) :
    a = b := by
  injection same

theorem cellAt_inj {a b a' b' : Term (signature RSig target) [] ()} (same : cellAt a b = cellAt a' b') :
    a = a' ∧ b = b' := by
  obtain ⟨first, rest⟩ := Args.cons.inj (rop_inj same)
  exact ⟨first, (Args.cons.inj rest).1⟩

theorem cellsOf_injective :
    ∀ (n : ℕ) {f g : Fin n → Term (signature RSig target) [] ()}, cellsOf n f = cellsOf n g → f = g
  | 0, _, _, _ => funext fun i => i.elim0
  | n + 1, f, g, same => by
      obtain ⟨first, rest⟩ := cellAt_inj same
      have tail := cellsOf_injective n rest
      funext i
      refine Fin.cases first (fun j => ?_) i
      exact congrFun tail j

/-- The numeral a cell starts with, if any. -/
def firstNumeral : {as : List (List Unit × Unit)} → Args (signature RSig target) as [] → Option ℕ
  | _, .nil => none
  | _, .cons (.op (.inl (.const k)) _) _ => some k
  | _, .cons _ _ => none

def headNumeral : Term (signature RSig target) [] () → Option ℕ
  | .op (.inl _) args => firstNumeral args
  | _ => none

theorem headNumeral_rowNode (k : Tag) (args : Fin k.arity → Term (signature RSig target) [] ()) :
    headNumeral (rowNode k args) = some (tagCode k) :=
  rfl

end RowNodes

/-- **The row signature has nodes.** -/
def rowNodes : Nodes RSig [] () where
  node k args := rowNode k args
  instantiate_node σ k args := by
    show cellAt (instantiate σ (constAt (tagCode k))) (instantiate σ (cellsOf k.arity args)) = _
    rw [instantiate_cellsOf]
    rfl
  tag_eq {_ _ k k' args args'} same := by
    have heads := congrArg headNumeral same
    rw [headNumeral_rowNode, headNumeral_rowNode] at heads
    exact tagCode_injective (Option.some.inj heads)
  args_eq {_ _ k args args'} same := cellsOf_injective k.arity (cellAt_inj same).2

/-! ## The slots of the embedding -/

/-- The slots that the embedding of an expression pattern binds, as addresses below its path. -/
def epatSlots : EPat → List (List ℕ)
  | .val _ => []
  | .pair a b => [0] :: ((epatSlots a).map (0 :: ·) ++ [1] :: (epatSlots b).map (1 :: ·))
  | .call a => [0] :: (epatSlots a).map (0 :: ·)

/-- The slots that the embedding of an expression binds, as addresses below its path. -/
def exSlots : Ex → List (List ℕ)
  | .val _ => []
  | .pair a b => [0] :: ((exSlots a).map (0 :: ·) ++ [1] :: (exSlots b).map (1 :: ·))
  | .call a => [0] :: (exSlots a).map (0 :: ·)

/-- The site of the slot at an address below a path. -/
def slotSite (path : List ℕ) (r : List ℕ) : rkeys.Site := .inr (.inl (path ++ r))

theorem slotSite_injective (path : List ℕ) : Function.Injective (slotSite path) := by
  intro r r' same
  simp only [slotSite, Sum.inr.injEq, Sum.inl.injEq, List.append_cancel_left_eq] at same
  exact same

theorem slotSite_cons (path : List ℕ) (b : ℕ) (r : List ℕ) :
    slotSite (path ++ [b]) r = slotSite path (b :: r) := by
  simp [slotSite]

variable {Ty : Type}

/-- The slots below a path's child are the child's addresses below the path. -/
theorem map_slotSite_snoc (path : List ℕ) (b : ℕ) (A : List (List ℕ)) :
    A.map (slotSite (path ++ [b])) = (A.map (b :: ·)).map (slotSite path) := by
  rw [List.map_map]
  exact List.map_congr_left fun r _ => slotSite_cons path b r

theorem trEPat_sites (j : ℕ) : ∀ (e : EPat) (path : List ℕ),
    (trEPat (Ty := Ty) j path e).sites = (epatSlots e).map (slotSite path)
  | .val _, _ => rfl
  | .pair a b, path => by
      have unfolded : (trEPat (Ty := Ty) j path (.pair a b)).sites =
          slotSite path [0] :: ((trEPat (Ty := Ty) j (path ++ [0]) a).sites ++
            slotSite path [1] :: (trEPat (Ty := Ty) j (path ++ [1]) b).sites) := by
        simp [trEPat, Comp.sites, slotSite]
      rw [unfolded, trEPat_sites j a, trEPat_sites j b, map_slotSite_snoc, map_slotSite_snoc]
      simp only [epatSlots, List.map_cons, List.map_append]
  | .call a, path => by
      have unfolded : (trEPat (Ty := Ty) j path (.call a)).sites =
          slotSite path [0] :: (trEPat (Ty := Ty) j (path ++ [0]) a).sites := by
        simp [trEPat, Comp.sites, slotSite]
      rw [unfolded, trEPat_sites j a, map_slotSite_snoc]
      simp only [epatSlots, List.map_cons]

theorem trEx_sites (eqAt : ℕ → ℕ) : ∀ (ex : Ex) (path : List ℕ),
    (trEx (Ty := Ty) eqAt path ex).sites = (exSlots ex).map (slotSite path)
  | .val _, _ => rfl
  | .pair a b, path => by
      have unfolded : (trEx (Ty := Ty) eqAt path (.pair a b)).sites =
          slotSite path [0] :: ((trEx (Ty := Ty) eqAt (path ++ [0]) a).sites ++
            slotSite path [1] :: (trEx (Ty := Ty) eqAt (path ++ [1]) b).sites) := by
        simp [trEx, Comp.sites, slotSite]
      rw [unfolded, trEx_sites eqAt a, trEx_sites eqAt b, map_slotSite_snoc, map_slotSite_snoc]
      simp only [exSlots, List.map_cons, List.map_append]
  | .call a, path => by
      have unfolded : (trEx (Ty := Ty) eqAt path (.call a)).sites =
          slotSite path [0] :: (trEx (Ty := Ty) eqAt (path ++ [0]) a).sites := by
        simp [trEx, Comp.sites, slotSite]
      rw [unfolded, trEx_sites eqAt a, map_slotSite_snoc]
      simp only [exSlots, List.map_cons]

/-- Addresses below two different first steps are different. -/
theorem slots_apart {A B : List (List ℕ)} {b b' : ℕ} (different : b ≠ b') :
    ∀ x ∈ A.map (b :: ·), ∀ y ∈ B.map (b' :: ·), x ≠ y := by
  intro x xMember y yMember same
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp xMember
  obtain ⟨r', _, rfl⟩ := List.mem_map.mp yMember
  exact different (List.cons.inj same).1

/-- **The slots of a tree are distinct addresses, none of them empty.** -/
theorem slots_nodup_of {A B : List (List ℕ)} (nodupA : A.Nodup) (emptyA : [] ∉ A) (nodupB : B.Nodup)
    (emptyB : [] ∉ B) :
    ([0] :: (A.map (0 :: ·) ++ [1] :: B.map (1 :: ·))).Nodup ∧
      [] ∉ [0] :: (A.map (0 :: ·) ++ [1] :: B.map (1 :: ·)) := by
  have mapA : (A.map (0 :: ·)).Nodup := nodupA.map (fun _ _ same => List.cons_injective same)
  have mapB : (B.map (1 :: ·)).Nodup := nodupB.map (fun _ _ same => List.cons_injective same)
  have notZeroA : [0] ∉ A.map (0 :: ·) := by
    intro member
    obtain ⟨r, inside, same⟩ := List.mem_map.mp member
    exact emptyA ((List.cons.inj same).2 ▸ inside)
  have notOneB : [1] ∉ B.map (1 :: ·) := by
    intro member
    obtain ⟨r, inside, same⟩ := List.mem_map.mp member
    exact emptyB ((List.cons.inj same).2 ▸ inside)
  have notZeroB : [0] ∉ B.map (1 :: ·) := by
    intro member
    obtain ⟨r, _, same⟩ := List.mem_map.mp member
    exact absurd (List.cons.inj same).1 (by decide)
  refine ⟨List.nodup_cons.mpr ⟨?_, ?_⟩, ?_⟩
  · intro member
    rcases List.mem_append.mp member with inA | inRest
    · exact notZeroA inA
    · rcases List.mem_cons.mp inRest with same | inB
      · exact absurd same (by decide)
      · exact notZeroB inB
  · refine List.nodup_append.mpr ⟨mapA, List.nodup_cons.mpr ⟨notOneB, mapB⟩, ?_⟩
    intro x xMember y yMember
    rcases List.mem_cons.mp yMember with rfl | inB
    · intro same
      subst same
      obtain ⟨r, _, same⟩ := List.mem_map.mp xMember
      exact absurd (List.cons.inj same).1 (by decide)
    · exact slots_apart (by decide) x xMember y inB
  · intro member
    rcases List.mem_cons.mp member with same | inRest
    · exact absurd same (by decide)
    · rcases List.mem_append.mp inRest with inA | inRest'
      · obtain ⟨r, _, same⟩ := List.mem_map.mp inA
        exact absurd same (List.cons_ne_nil _ _)
      · rcases List.mem_cons.mp inRest' with same | inB
        · exact absurd same (by decide)
        · obtain ⟨r, _, same⟩ := List.mem_map.mp inB
          exact absurd same (List.cons_ne_nil _ _)

theorem call_slots_nodup_of {A : List (List ℕ)} (nodupA : A.Nodup) (emptyA : [] ∉ A) :
    ([0] :: A.map (0 :: ·)).Nodup ∧ [] ∉ [0] :: A.map (0 :: ·) := by
  refine ⟨List.nodup_cons.mpr ⟨?_, nodupA.map (fun _ _ same => List.cons_injective same)⟩, ?_⟩
  · intro member
    obtain ⟨r, inside, same⟩ := List.mem_map.mp member
    exact emptyA ((List.cons.inj same).2 ▸ inside)
  · intro member
    rcases List.mem_cons.mp member with same | inA
    · exact absurd same (by decide)
    · obtain ⟨r, _, same⟩ := List.mem_map.mp inA
      exact absurd same (List.cons_ne_nil _ _)

theorem epatSlots_nodup : ∀ e : EPat, (epatSlots e).Nodup ∧ [] ∉ epatSlots e
  | .val _ => ⟨List.nodup_nil, List.not_mem_nil⟩
  | .pair a b =>
      slots_nodup_of (epatSlots_nodup a).1 (epatSlots_nodup a).2 (epatSlots_nodup b).1
        (epatSlots_nodup b).2
  | .call a => call_slots_nodup_of (epatSlots_nodup a).1 (epatSlots_nodup a).2

theorem exSlots_nodup : ∀ ex : Ex, (exSlots ex).Nodup ∧ [] ∉ exSlots ex
  | .val _ => ⟨List.nodup_nil, List.not_mem_nil⟩
  | .pair a b =>
      slots_nodup_of (exSlots_nodup a).1 (exSlots_nodup a).2 (exSlots_nodup b).1 (exSlots_nodup b).2
  | .call a => call_slots_nodup_of (exSlots_nodup a).1 (exSlots_nodup a).2

/-! ## Scope -/

theorem namesIn_slotD {allowed : List rkeys.Site} {path : List ℕ}
    (member : (.inr (.inl path) : rkeys.Site) ∈ allowed) : NamesIn allowed (slotD path) := by
  intro x inside
  have same : x = ⟨[], .slot path⟩ := List.mem_singleton.mp inside
  subst same
  exact ⟨rfl, member⟩

theorem namesIn_cellD {allowed : List rkeys.Site} {a b : RData} (inA : NamesIn allowed a)
    (inB : NamesIn allowed b) : NamesIn allowed (cellD a b) := by
  intro x inside
  change x ∈ support a ++ (support b ++ []) at inside
  rcases List.mem_append.mp inside with fromA | fromB
  · exact inA x fromA
  · exact inB x (by simpa using fromB)

theorem namesIn_trPat (j : ℕ) {allowed : List rkeys.Site} (member : (.inl j : rkeys.Site) ∈ allowed) :
    ∀ p : Pat, NamesIn allowed (trPat j p)
  | .var x => by
      intro y inside
      have same : y = ⟨[], .var j x⟩ := List.mem_singleton.mp inside
      subst same
      exact ⟨rfl, member⟩
  | .sym _ => fun _ inside => nomatch inside
  | .cell a b => namesIn_cellD (namesIn_trPat j member a) (namesIn_trPat j member b)

/-- A term of the core with no variables is embedded with no names. -/
theorem support_trTm_ground (eqAt : ℕ → ℕ) : ∀ t : Tm, t.isGround → support (trTm eqAt t) = []
  | .var _, ground => ground.elim
  | .const _, _ => rfl
  | .app () ts, ground => by
      change support (trTm eqAt (ts 0)) ++ (support (trTm eqAt (ts 1)) ++ []) = []
      rw [support_trTm_ground eqAt (ts 0) (ground 0), support_trTm_ground eqAt (ts 1) (ground 1)]
      rfl

/-- **A query of the core whose held data are ground.** -/
def GroundQuery : Ex → Prop
  | .val t => t.isGround
  | .pair a b => GroundQuery a ∧ GroundQuery b
  | .call a => GroundQuery a

theorem trEPat_scoped (j : ℕ) : ∀ (e : EPat) (path : List ℕ) {allowed : List rkeys.Site},
    (.inl j : rkeys.Site) ∈ allowed → (trEPat (Ty := Ty) j path e).Scoped allowed
  | .val p, _, _, member => namesIn_trPat j member p
  | .pair a b, path, _, member =>
      ⟨trEPat_scoped j a (path ++ [0]) member, namesIn_slotD (List.mem_cons_self ..),
        trEPat_scoped j b (path ++ [1]) (List.mem_cons_of_mem _ member),
        namesIn_slotD (List.mem_cons_self ..),
        namesIn_cellD (namesIn_slotD (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          (namesIn_slotD (List.mem_cons_self ..))⟩
  | .call a, path, _, member =>
      ⟨trEPat_scoped j a (path ++ [0]) member, namesIn_slotD (List.mem_cons_self ..),
        namesIn_slotD (List.mem_cons_self ..)⟩

theorem trEx_scoped (eqAt : ℕ → ℕ) : ∀ (ex : Ex) (path : List ℕ) {allowed : List rkeys.Site},
    GroundQuery ex → (trEx (Ty := Ty) eqAt path ex).Scoped allowed
  | .val t, _, _, ground => by
      intro x inside
      rw [support_trTm_ground eqAt t ground] at inside
      exact absurd inside List.not_mem_nil
  | .pair a b, path, _, ⟨groundA, groundB⟩ =>
      ⟨trEx_scoped eqAt a (path ++ [0]) groundA, namesIn_slotD (List.mem_cons_self ..),
        trEx_scoped eqAt b (path ++ [1]) groundB, namesIn_slotD (List.mem_cons_self ..),
        namesIn_cellD (namesIn_slotD (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          (namesIn_slotD (List.mem_cons_self ..))⟩
  | .call a, path, _, ground =>
      ⟨trEx_scoped eqAt a (path ++ [0]) ground, namesIn_slotD (List.mem_cons_self ..),
        namesIn_slotD (List.mem_cons_self ..)⟩

/-! ## The fragment with arrows -/

theorem trEPat_arrow (j : ℕ) : ∀ (e : EPat) (path : List ℕ), ArrowComp (trEPat (Ty := Ty) j path e)
  | .val _, _ => trivial
  | .pair a b, path => ⟨trEPat_arrow j a (path ++ [0]), trEPat_arrow j b (path ++ [1]), trivial⟩
  | .call a, path => ⟨trEPat_arrow j a (path ++ [0]), trivial⟩

theorem trEx_arrow (eqAt : ℕ → ℕ) : ∀ (ex : Ex) (path : List ℕ), ArrowComp (trEx (Ty := Ty) eqAt path ex)
  | .val _, _ => trivial
  | .pair a b, path => ⟨trEx_arrow eqAt a (path ++ [0]), trEx_arrow eqAt b (path ++ [1]), trivial⟩
  | .call a, path => ⟨trEx_arrow eqAt a (path ++ [0]), trivial⟩

/-! ## The clauses of the run theorems, for the embedding -/

/-- **Every embedded equation satisfies the clauses of the run theorems.** -/
theorem trEquation_clauses (j : ℕ) (e : NEquation) :
    (trEquation (Ty := Ty) j e).Scoped ∧
      ((trEquation (Ty := Ty) j e).site :: (trEquation (Ty := Ty) j e).rhs.sites).Nodup ∧
      ArrowComp (trEquation (Ty := Ty) j e).rhs := by
  refine ⟨⟨namesIn_trPat j (List.mem_singleton_self _) e.lhs,
    trEPat_scoped j e.rhs [j] (List.mem_singleton_self _)⟩, ?_, trEPat_arrow j e.rhs [j]⟩
  show ((.inl j : rkeys.Site) :: (trEPat (Ty := Ty) j [j] e.rhs).sites).Nodup
  rw [trEPat_sites]
  refine List.nodup_cons.mpr ⟨?_, (epatSlots_nodup e.rhs).1.map (slotSite_injective [j])⟩
  intro member
  obtain ⟨r, _, same⟩ := List.mem_map.mp member
  exact Sum.inr_ne_inl same

theorem program_clauses (eqs : List NEquation) :
    ∀ e ∈ (program (Ty := Ty) eqs).equations, e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs := by
  intro e member
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
  exact trEquation_clauses p.2 p.1

theorem programStrict_clauses (eqs : List NEquation) :
    ∀ e ∈ (programStrict (Ty := Ty) eqs).equations,
      e.Scoped ∧ (e.site :: e.rhs.sites).Nodup ∧ ArrowComp e.rhs := by
  intro e member
  rcases List.mem_append.mp member with embedded | last
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp embedded
    exact trEquation_clauses p.2 p.1
  · rw [List.mem_singleton.mp last]
    refine ⟨⟨?_, trivial⟩, List.nodup_singleton _, trivial⟩
    intro y inside
    have same : y = ⟨[], .var eqs.length 0⟩ := List.mem_singleton.mp inside
    subst same
    exact ⟨rfl, List.mem_singleton_self _⟩

/-- The site of a query: a site no slot of the embedding uses (the query has no names of its own). -/
def querySite : rkeys.Site := .inr (.inr 0)

theorem query_scoped (eqAt : ℕ → ℕ) {ex : Ex} (ground : GroundQuery ex) :
    (trEx (Ty := Ty) eqAt [] ex).Scoped [querySite] :=
  trEx_scoped eqAt ex [] ground

theorem query_distinctSites (eqAt : ℕ → ℕ) (ex : Ex) :
    (querySite :: (trEx (Ty := Ty) eqAt [] ex).sites).Nodup := by
  rw [trEx_sites]
  refine List.nodup_cons.mpr ⟨?_, (exSlots_nodup ex).1.map (slotSite_injective [])⟩
  intro member
  obtain ⟨r, _, same⟩ := List.mem_map.mp member
  simp [slotSite, querySite] at same

/-! ## The run theorems for the embedding -/

variable (N : Nodes RSig [] ()) {D : Discipline RSig [] ()} {supply : ℕ → Term RSig [] ()}
  (spaces : Term RSig [] () → Multiset (Row rkeys [] ()))

/-- **Every source run of an embedded nested-calls program from a ground query is followed by runs of
the step.** The frontier is one represented state per live alternative; the step does not count
alternatives by itself. -/
theorem nested_runs_forward (eqs : List NEquation) (eqAt : ℕ → ℕ) {ex : Ex} (ground : GroundQuery ex)
    {C : Config rkeys [] () D.Ty}
    (runs : Runs D (program eqs) supply (Config.initial spaces (trEx eqAt [] ex)) C) :
    ∃ L, ArrowFrontier N (program eqs) C L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N (program (Ty := D.Ty) eqs))
        (start N (program (Ty := D.Ty) eqs) (trEx eqAt [] ex)) x.2.1 :=
  arrow_runs_forward_of_scoped N spaces _ (program_clauses eqs) (query_scoped eqAt ground)
    (query_distinctSites eqAt ex) (trEx_arrow eqAt ex []) runs

/-- **The answers of an embedded nested-calls program, as a bag, are those of a frontier reached by
the step.** The frontier is one represented state per live alternative; the step does not count
alternatives by itself. -/
theorem nested_answers (eqs : List NEquation) (eqAt : ℕ → ℕ) {ex : Ex} (ground : GroundQuery ex)
    {C : Config rkeys [] () D.Ty}
    (runs : Runs D (program eqs) supply (Config.initial spaces (trEx eqAt [] ex)) C) :
    ∃ L : Multiset (Branch rkeys [] () D.Ty × HostState RSig × ℕ),
      C.answers (D := D) = frontierAnswers N L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N (program (Ty := D.Ty) eqs))
        (start N (program (Ty := D.Ty) eqs) (trEx eqAt [] ex)) x.2.1 :=
  arrow_answers_of_scoped N spaces _ (program_clauses eqs) (query_scoped eqAt ground)
    (query_distinctSites eqAt ex) (trEx_arrow eqAt ex []) runs

/-- **Every run of the step of an embedded nested-calls program from a ground query is a source run.** -/
theorem nested_runs_reflected (eqs : List NEquation) (eqAt : ℕ → ℕ) {ex : Ex} (ground : GroundQuery ex)
    {s : HostState RSig}
    (run : Relation.ReflTransGen (Fires N (program (Ty := D.Ty) eqs))
      (start N (program (Ty := D.Ty) eqs) (trEx (Ty := D.Ty) eqAt [] ex)) s) :
    ∃ (C : Config rkeys [] () D.Ty) (b : Branch rkeys [] () D.Ty) (a : ℕ),
      Runs D (program eqs) supply (Config.initial spaces (trEx eqAt [] ex)) C ∧ b ∈ C.branches ∧
        Represents N (program eqs) C.world.scope b s a ∧ ArrowBranch b :=
  arrow_runs_reflected_of_scoped N spaces _ (program_clauses eqs) (query_scoped eqAt ground)
    (query_distinctSites eqAt ex) (trEx_arrow eqAt ex []) run

/-- The same for the strict program (a call that no equation answers fails, as in the core). -/
theorem nestedStrict_answers (eqs : List NEquation) (eqAt : ℕ → ℕ) {ex : Ex} (ground : GroundQuery ex)
    {C : Config rkeys [] () D.Ty}
    (runs : Runs D (programStrict eqs) supply (Config.initial spaces (trEx eqAt [] ex)) C) :
    ∃ L : Multiset (Branch rkeys [] () D.Ty × HostState RSig × ℕ),
      C.answers (D := D) = frontierAnswers N L ∧
      ∀ x ∈ L, Relation.ReflTransGen (Fires N (programStrict (Ty := D.Ty) eqs))
        (start N (programStrict (Ty := D.Ty) eqs) (trEx eqAt [] ex)) x.2.1 :=
  arrow_answers_of_scoped N spaces _ (programStrict_clauses eqs) (query_scoped eqAt ground)
    (query_distinctSites eqAt ex) (trEx_arrow eqAt ex []) runs

theorem nestedStrict_runs_reflected (eqs : List NEquation) (eqAt : ℕ → ℕ) {ex : Ex}
    (ground : GroundQuery ex) {s : HostState RSig}
    (run : Relation.ReflTransGen (Fires N (programStrict (Ty := D.Ty) eqs))
      (start N (programStrict (Ty := D.Ty) eqs) (trEx (Ty := D.Ty) eqAt [] ex)) s) :
    ∃ (C : Config rkeys [] () D.Ty) (b : Branch rkeys [] () D.Ty) (a : ℕ),
      Runs D (programStrict eqs) supply (Config.initial spaces (trEx eqAt [] ex)) C ∧ b ∈ C.branches ∧
        Represents N (programStrict eqs) C.world.scope b s a ∧ ArrowBranch b :=
  arrow_runs_reflected_of_scoped N spaces _ (programStrict_clauses eqs) (query_scoped eqAt ground)
    (query_distinctSites eqAt ex) (trEx_arrow eqAt ex []) run

#print axioms rowNodes
#print axioms trEquation_clauses
#print axioms nested_runs_forward
#print axioms nested_answers
#print axioms nested_runs_reflected
#print axioms nestedStrict_answers
#print axioms nestedStrict_runs_reflected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.NestedCoreHosting
