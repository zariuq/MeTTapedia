import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.BinderCore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# The binder core at the level of answers: the reachability theorem does not lift

`BinderCore.execution_iff` relates the terms the binder core reaches to the terms some alternative of
some configuration of some run shows. At the level of final answers it fails, in this direction: a
normal form the core reaches can be no answer of the language.

The binder-core program (over MeTTa text)

```
(= a (s $X))        ; the right-hand side leaves the hole $X free
(= (s b) c)
```

rewrites the call `a` to `(s z)` (taking `$X = z`), a normal form of the core (`core_reaches`,
`core_normal`). In the language, the alternative of the first equation calls `(s $X)` with `$X`
unknown; the second equation matches an instance of that open call, so the call commits to it: the
only answer is `c` (`answers_only_c`; a run ends with it, `answers_c`), and no configuration of any
run answers `(s z)` (`answers_differ`), although an intermediate alternative shows it
(`shows_open_call`), as the
reachability theorem says.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.BinderCoreAnswers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ProgramBinders (Rewrites Answers Matches ground ClosedTerms)
open BinderCore Elaboration Toolkit

/-! ## The binder-core program -/

/-- `(= a (s $X))`: one hole, free in the right-hand side. -/
def e1 : ProgramBinders.Equation MSig [] () where
  Holes := Unit
  holesEq := inferInstance
  arity := fun _ => ([], ())
  lhs := symAt "a"
  rhs := tupleAt [symAt "s", .op (.inr (.mk ())) .nil]

/-- `(= (s b) c)`: no hole. -/
def e2 : ProgramBinders.Equation MSig [] () where
  Holes := Empty
  holesEq := inferInstance
  arity := fun impossible => nomatch impossible
  lhs := tupleAt [symAt "s", symAt "b"]
  rhs := symAt "c"

def l : List (ProgramBinders.Equation MSig [] ()) := [e1, e2]

def sz : MClosed := ctuple [csym "s", csym "z"]

/-- **The core rewrites `a` to `(s z)`.** -/
theorem core_reaches : Relation.ReflTransGen (Rewrites l.get) (csym "a") sz :=
  .single ⟨⟨0, by decide⟩, fun _ => csym "z", by unfold Matches; rfl, by rfl⟩

/-- The head symbol of a pair, if any. -/
def secondSym : Term MSig [] () → String
  | .op (.tup 2) (.cons _ (.cons (.op (.sym name) _) .nil)) => name
  | _ => ""

/-- **`(s z)` is a normal form of the core.** -/
theorem core_normal : ¬ ∃ y, Rewrites l.get sz y := by
  rintro ⟨y, ⟨i, hi⟩, θ, matched', -⟩
  match i, hi with
  | 0, _ =>
      have same : (csym "a" : Term MSig [] ()) = sz :=
        Rigid.include_injective (ground MSig) _ _ matched'
      cases same
  | 1, _ =>
      have same : (ctuple [csym "s", csym "b"] : Term MSig [] ()) = sz :=
        Rigid.include_injective (ground MSig) _ _ matched'
      have parts := congrArg secondSym same
      exact absurd parts (by decide)
  | n + 2, hn => exact absurd hn (by simp [l])

/-! ## The language's runs -/

variable (D : Discipline MSig [] ()) (supply : ℕ → MClosed)

abbrev κ := keys l
abbrev A : Data κ [] () := Rigid.includeTerm (fam κ) (csym "a")

def i0 : Fin l.length := ⟨0, by decide⟩
def i1 : Fin l.length := ⟨1, by decide⟩

def t1 : Data κ [] () := instantiate (stamp l 0 i0) (l.get i0).rhs
def K1 : List (Constraint κ [] ()) := [] ++ [(instantiate (stamp l 0 i0) (l.get i0).lhs, A)]
def t2 : Data κ [] () := instantiate (stamp l 1 i1) (l.get i1).rhs
def K2 : List (Constraint κ [] ()) := K1 ++ [(instantiate (stamp l 1 i1) (l.get i1).lhs, t1)]

def B0 : Branch κ [] () D.Ty := ⟨[], .eval (.apply A), [], []⟩
def B1 : Branch κ [] () D.Ty := ⟨K1, .eval (.apply t1), [], []⟩
def B2 : Branch κ [] () D.Ty := ⟨K2, .eval (.apply t2), [], []⟩
def B3 : Branch κ [] () D.Ty := ⟨K2, .value t2, [], []⟩

/-- Every name of the embedded program is a copy of the first equation's hole; send each to `b`. -/
def allB : Assignment (fam κ) (ground MSig) := fun x =>
  match x with
  | ⟨_, ⟨⟨0, _⟩, ()⟩⟩ => Rigid.includeTerm (ground MSig) (csym "b")
  | ⟨_, ⟨⟨1, _⟩, h⟩⟩ => nomatch h
  | ⟨_, ⟨⟨n + 2, hn⟩, _⟩⟩ => absurd hn (by simp [l])

theorem K2_live : Solvable K2 := by
  refine ⟨Empty, ground MSig, allB, fun e member => ?_⟩
  simp only [K2, K1, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem K1_live : Solvable K1 := solvable_of_append K2_live

theorem sym_ne_tup {X : Type} {target : X → MetaArity MSig} (name : String) (n : ℕ)
    (args : Args (signature MSig target) (MOp.arity (MOp.tup n)) []) :
    (symAt name : Term (signature MSig target) [] ()) ≠ Term.op (Sum.inl (MOp.tup n)) args := by
  intro same
  injection same with _ _ hop _
  injection hop with hop'
  cases hop'

/-- The alternatives each apply makes. -/
theorem apply_moves {w w' : World κ [] ()} {K : List (Constraint κ [] ())} {t : Data κ [] ()}
    {bs : Multiset (Branch κ [] () D.Ty)} (moved : Move D (program l) supply w ⟨K, .eval (.apply t), [], []⟩ w' bs) :
    (w' = w.fresh ∧ bs = ↑((program l (Ty := D.Ty)).equations.map (callBranch D w.scope K t [] [])) ∧
        ∃ e ∈ (program l (Ty := D.Ty)).equations, Solvable (K ++ [(instantiate (copyAt κ w.scope) e.lhs, t)])) ∨
      (w' = w ∧ bs = {⟨K, .value t, [], []⟩} ∧
        ∀ e ∈ (program l (Ty := D.Ty)).equations, ¬ Solvable (K ++ [(instantiate (copyAt κ w.scope) e.lhs, t)])) := by
  cases moved
  case apply =>
    rename_i matched
    exact .inl ⟨rfl, rfl, matched⟩
  case unmatched =>
    rename_i none
    exact .inr ⟨rfl, rfl, none⟩

/-- The equations of the embedded program, as two copies. -/
theorem copies (n : ℕ) (K : List (Constraint κ [] ())) (t : Data κ [] ()) :
    ((program l (Ty := D.Ty)).equations.map (callBranch D n K t [] [])) =
      [⟨K ++ [(instantiate (stamp l n i0) (l.get i0).lhs, t)], .eval (.apply (instantiate (stamp l n i0) (l.get i0).rhs)), [], []⟩,
        ⟨K ++ [(instantiate (stamp l n i1) (l.get i1).lhs, t)], .eval (.apply (instantiate (stamp l n i1) (l.get i1).rhs)), [], []⟩] := by
  simp only [program, List.map_map, Function.comp_def, callBranch_embed]
  rfl

open Classical in
/-- The configurations a run reaches: one live alternative, at a known scope. -/
def Good (C : Config κ [] () D.Ty) : Prop :=
  (C.branches.filter fun b => Solvable b.store) = {B0 D} ∧ C.world.scope = 0 ∨
  (C.branches.filter fun b => Solvable b.store) = {B1 D} ∧ C.world.scope = 1 ∨
  (C.branches.filter fun b => Solvable b.store) = {B2 D} ∧ C.world.scope = 2 ∨
  (C.branches.filter fun b => Solvable b.store) = {B3 D}

theorem dead_of_heads {K : List (Constraint κ [] ())} {u v : Data κ [] ()} (member : (u, v) ∈ K)
    (apart : ∀ {X : Type} (target : X → MetaArity MSig) (σ : Assignment (fam κ) target),
      instantiate σ u ≠ instantiate σ v) : ¬ Solvable K := by
  rintro ⟨X, target, σ, solved⟩
  exact apart target σ (solved _ member)

open Classical in
theorem filter_first {x y : Branch κ [] () D.Ty} (hx : Solvable x.store) (hy : ¬ Solvable y.store) :
    ((x ::ₘ y ::ₘ 0).filter fun b => Solvable b.store) = {x} := by
  rw [Multiset.filter_cons_of_pos (p := fun b : Branch κ [] () D.Ty => Solvable b.store) _ hx,
    Multiset.filter_cons_of_neg (p := fun b : Branch κ [] () D.Ty => Solvable b.store) _ hy, Multiset.filter_zero]
  rfl

open Classical in
theorem filter_second {x y : Branch κ [] () D.Ty} (hx : ¬ Solvable x.store) (hy : Solvable y.store) :
    ((x ::ₘ y ::ₘ 0).filter fun b => Solvable b.store) = {y} := by
  rw [Multiset.filter_cons_of_neg (p := fun b : Branch κ [] () D.Ty => Solvable b.store) _ hx,
    Multiset.filter_cons_of_pos (p := fun b : Branch κ [] () D.Ty => Solvable b.store) _ hy, Multiset.filter_zero]
  rfl

open Classical in
theorem filter_split {b : Branch κ [] () D.Ty} {rest : Multiset (Branch κ [] () D.Ty)} (live : Solvable b.store)
    {B : Branch κ [] () D.Ty} (same : ((b ::ₘ rest).filter fun b => Solvable b.store) = {B}) :
    b = B ∧ (rest.filter fun b => Solvable b.store) = 0 := by
  rw [Multiset.filter_cons_of_pos (p := fun b : Branch κ [] () D.Ty => Solvable b.store) _ live] at same
  obtain ⟨one, two⟩ := (Multiset.singleton_eq_cons_iff _).mp same.symm
  exact ⟨one.symm, two⟩

open Classical in
theorem filter_join {bs rest : Multiset (Branch κ [] () D.Ty)} {B : Branch κ [] () D.Ty}
    (none : (rest.filter fun b => Solvable b.store) = 0) (made : (bs.filter fun b => Solvable b.store) = {B}) :
    ((bs + rest).filter fun b => Solvable b.store) = {B} := by
  rw [Multiset.filter_add, none, made, add_zero]

/-- **A step keeps a run among the four alternatives.** -/
theorem good_step {C C' : Config κ [] () D.Ty} (step : Step D (program l) supply C C') (good : Good D C) :
    Good D C' := by
  cases step with
  | move w w' b rest bs live moved =>
      rcases good with ⟨filtered, scope⟩ | ⟨filtered, scope⟩ | ⟨filtered, scope⟩ | filtered
      · obtain ⟨rfl, none⟩ := filter_split D live filtered
        have scope' : w.scope = 0 := scope
        rcases apply_moves D supply moved with ⟨rfl, rfl, _⟩ | ⟨_, _, unmatched⟩
        · refine .inr (.inl ⟨filter_join D none ?_, show w.scope + 1 = 1 by rw [scope']⟩)
          rw [copies, scope']
          exact filter_first D K1_live (dead_of_heads (List.mem_append_right _ (List.mem_singleton_self _))
            fun target σ same => sym_ne_tup "a" 2 _ same.symm)
        · exact absurd (by rw [scope']; exact K1_live) (unmatched _ (List.mem_map.mpr ⟨i0, List.mem_finRange _, rfl⟩))
      · obtain ⟨rfl, none⟩ := filter_split D live filtered
        have scope' : w.scope = 1 := scope
        rcases apply_moves D supply moved with ⟨rfl, rfl, _⟩ | ⟨_, _, unmatched⟩
        · refine .inr (.inr (.inl ⟨filter_join D none ?_, show w.scope + 1 = 2 by rw [scope']⟩))
          rw [copies, scope']
          exact filter_second D (dead_of_heads (List.mem_append_right _ (List.mem_singleton_self _))
            fun target σ same => sym_ne_tup "a" 2 _ same) K2_live
        · exact absurd (by rw [scope']; exact K2_live) (unmatched _ (List.mem_map.mpr ⟨i1, List.mem_finRange _, rfl⟩))
      · obtain ⟨rfl, none⟩ := filter_split D live filtered
        rcases apply_moves D supply moved with ⟨_, _, ⟨e, member, solvable⟩⟩ | ⟨rfl, rfl, _⟩
        · exfalso
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
          match i with
          | ⟨0, _⟩ =>
              exact dead_of_heads (List.mem_append_right _ (List.mem_singleton_self _)) (fun target σ same => by
                injection same with _ _ hop _
                injection hop with hsym
                injection hsym with hname
                exact absurd hname (by decide)) solvable
          | ⟨1, _⟩ =>
              exact dead_of_heads (List.mem_append_right _ (List.mem_singleton_self _))
                (fun target σ same => by exact sym_ne_tup "c" 2 _ same.symm) solvable
          | ⟨n + 2, hn⟩ => exact absurd hn (by simp [l])
        · exact .inr (.inr (.inr (filter_join D none (by
            classical
            rw [Multiset.filter_singleton, if_pos K2_live]
            rfl))))
      · obtain ⟨rfl, _⟩ := filter_split D live filtered
        exact absurd moved Move.value_still

theorem B0_live : Solvable (B0 D).store := ⟨Empty, ground MSig, allB, fun _ h => by cases h⟩

theorem good_start : Good D (start l (Ty := D.Ty) (csym "a")) := by
  classical
  refine .inl ⟨?_, rfl⟩
  show Multiset.filter _ {B0 D} = _
  rw [Multiset.filter_singleton, if_pos (B0_live D)]

theorem good_runs {C : Config κ [] () D.Ty} (runs : Runs D (program l) supply (start l (csym "a")) C) :
    Good D C := by
  induction runs with
  | refl => exact good_start D
  | tail _ step ih => exact good_step D supply step ih

/-- **The only answer is `c`**: every reading set of every finished live alternative of every
configuration a run reaches is the set of readings of `c`. -/
theorem answers_only_c {C : Config κ [] () D.Ty} (runs : Runs D (program l) supply (start l (csym "a")) C) :
    ∀ ans ∈ C.answers, ans = {csym "c"} := by
  classical
  intro ans member
  obtain ⟨b, inside, rfl⟩ := Multiset.mem_map.mp member
  have ⟨finished, alive⟩ := (Multiset.mem_filter.mp inside).2
  have liveMember : b ∈ C.branches.filter fun b => Solvable b.store :=
    Multiset.mem_filter.mpr ⟨Multiset.mem_of_mem_filter inside, alive⟩
  rcases good_runs D supply runs with ⟨filtered, _⟩ | ⟨filtered, _⟩ | ⟨filtered, _⟩ | filtered <;>
    rw [filtered, Multiset.mem_singleton] at liveMember <;> subst liveMember
  · obtain ⟨_, t, focus⟩ := finished; cases focus
  · obtain ⟨_, t, focus⟩ := finished; cases focus
  · obtain ⟨_, t, focus⟩ := finished; cases focus
  · exact Branch.answer_of_determines rfl ⟨K2_live, fun target σ _ => rfl⟩

/-- The alternative the second equation makes for the call `a`: dead. -/
def X1 : Branch κ [] () D.Ty :=
  ⟨[] ++ [(instantiate (stamp l 0 i1) (l.get i1).lhs, A)],
    .eval (.apply (instantiate (stamp l 0 i1) (l.get i1).rhs)), [], []⟩

/-- The alternative the first equation makes for the call `(s $X)`: dead. -/
def Y2 : Branch κ [] () D.Ty :=
  ⟨K1 ++ [(instantiate (stamp l 1 i0) (l.get i0).lhs, t1)],
    .eval (.apply (instantiate (stamp l 1 i0) (l.get i0).rhs)), [], []⟩

theorem X1_dead : ¬ Solvable (X1 D).store :=
  dead_of_heads (List.mem_append_right _ (List.mem_singleton_self _))
    fun _ _ same => sym_ne_tup "a" 2 _ same.symm

theorem Y2_dead : ¬ Solvable (Y2 D).store :=
  dead_of_heads (List.mem_append_right _ (List.mem_singleton_self _))
    fun _ _ same => sym_ne_tup "a" 2 _ same

/-- **And `c` is answered**: a run ends, quiescent, with `c` among its answers. So the statement that
every answer is `c` is about a language that does answer. -/
theorem answers_c :
    ∃ C, Runs D (program l) supply (start l (csym "a")) C ∧ Config.Quiescent (D := D) (program l) supply C ∧
      ({csym "c"} : Set MClosed) ∈ C.answers := by
  have step1 : Step D (program l) supply (start l (csym "a"))
      ⟨⟨1, 0, fun _ => 0⟩, ↑((program l (Ty := D.Ty)).equations.map (callBranch D 0 [] A [] []))⟩ :=
    Step.single (B0_live D) (.apply ⟨0, 0, fun _ => 0⟩ [] A [] []
      ⟨_, List.mem_map.mpr ⟨i0, List.mem_finRange _, rfl⟩, ⟨Empty, ground MSig, allB, fun e h => by
        rw [List.nil_append, List.mem_singleton] at h
        subst h
        rfl⟩⟩)
  have step2 : Step D (program l) supply
      ⟨⟨1, 0, fun _ => 0⟩, ↑((program l (Ty := D.Ty)).equations.map (callBranch D 0 [] A [] []))⟩
      ⟨⟨2, 0, fun _ => 0⟩,
        ↑((program l (Ty := D.Ty)).equations.map (callBranch D 1 K1 t1 [] [])) + {X1 D}⟩ :=
    Step.of_eq (b := B1 D) (rest := {X1 D}) (by rw [copies]; rfl) rfl K1_live
      (.apply ⟨1, 0, fun _ => 0⟩ K1 t1 [] []
        ⟨_, List.mem_map.mpr ⟨i1, List.mem_finRange _, rfl⟩, K2_live⟩)
  have step3 : Step D (program l) supply
      ⟨⟨2, 0, fun _ => 0⟩,
        ↑((program l (Ty := D.Ty)).equations.map (callBranch D 1 K1 t1 [] [])) + {X1 D}⟩
      ⟨⟨2, 0, fun _ => 0⟩, {B3 D} + (Y2 D ::ₘ {X1 D})⟩ :=
    Step.of_eq (b := B2 D) (rest := Y2 D ::ₘ {X1 D})
      (by
        rw [copies]
        show Y2 D ::ₘ B2 D ::ₘ {X1 D} = B2 D ::ₘ Y2 D ::ₘ {X1 D}
        exact Multiset.cons_swap _ _ _)
      rfl K2_live
      (.unmatched ⟨2, 0, fun _ => 0⟩ K2 t2 [] [] fun e member solvable => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
        match i with
        | ⟨0, _⟩ =>
            exact dead_of_heads (List.mem_append_right _ (List.mem_singleton_self _)) (fun target σ same => by
              injection same with _ _ hop _
              injection hop with hsym
              injection hsym with hname
              exact absurd hname (by decide)) solvable
        | ⟨1, _⟩ =>
            exact dead_of_heads (List.mem_append_right _ (List.mem_singleton_self _))
              (fun target σ same => by exact sym_ne_tup "c" 2 _ same.symm) solvable
        | ⟨n + 2, hn⟩ => exact absurd hn (by simp [l]))
  refine ⟨_, ((Relation.ReflTransGen.single step1).tail step2).tail step3, ?_, ?_⟩
  · intro b member alive w' bs moved
    have member' : b ∈ {B3 D} + (Y2 D ::ₘ {X1 D}) := member
    simp only [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_cons] at member'
    rcases member' with rfl | rfl | rfl
    · exact Move.value_still moved
    · exact Y2_dead D alive
    · exact X1_dead D alive
  · classical
    unfold Config.answers
    exact Multiset.mem_map.mpr ⟨B3 D, Multiset.mem_filter.mpr
      ⟨Multiset.mem_add.mpr (.inl (Multiset.mem_singleton_self _)), ⟨rfl, _, rfl⟩, K2_live⟩,
      Branch.answer_of_determines rfl ⟨K2_live, fun target σ _ => rfl⟩⟩

/-- Every name sent to `z`. -/
def allZ : Assignment (fam κ) (ground MSig) := fun x =>
  match x with
  | ⟨_, ⟨⟨0, _⟩, ()⟩⟩ => Rigid.includeTerm (ground MSig) (csym "z")
  | ⟨_, ⟨⟨1, _⟩, h⟩⟩ => nomatch h
  | ⟨_, ⟨⟨n + 2, hn⟩, _⟩⟩ => absurd hn (by simp [l])

/-- **An intermediate alternative shows `(s z)`**, as the reachability theorem says: the open call
`(s $X)` reads as `(s z)`. -/
theorem shows_open_call :
    ∃ C, Runs D (program l) supply (start l (csym "a")) C ∧ ∃ b ∈ C.branches, Shows l b sz := by
  refine ⟨⟨⟨1, 0, fun _ => 0⟩, ↑((program l (Ty := D.Ty)).equations.map (callBranch D 0 [] A [] []))⟩,
    .single (Step.single (B0_live D) (.apply ⟨0, 0, fun _ => 0⟩ [] A [] []
      ⟨_, List.mem_map.mpr ⟨i0, List.mem_finRange _, rfl⟩, ⟨Empty, ground MSig, allB, fun e h => by
        rw [List.nil_append, List.mem_singleton] at h
        subst h
        rfl⟩⟩)), B1 D, ?_, t1, .inl rfl, ⟨Empty, ground MSig, allZ, fun e h => ?_, rfl⟩⟩
  · rw [copies]
    exact Multiset.mem_coe.mpr List.mem_cons_self
  · have h' : e ∈ K1 := h
    simp only [K1, List.nil_append, List.mem_singleton] at h'
    subst h'
    rfl

/-- **The answer-level form fails**: the core reaches the normal form `(s z)` from `a`, and no
configuration of any run of the embedded program answers it. -/
theorem answers_differ :
    Relation.ReflTransGen (Rewrites l.get) (csym "a") sz ∧ (¬ ∃ y, Rewrites l.get sz y) ∧
      ∀ C, Runs D (program l) supply (start l (csym "a")) C → ∀ ans ∈ C.answers, sz ∉ ans := by
  refine ⟨core_reaches, core_normal, fun C runs ans member inAns => ?_⟩
  rw [answers_only_c D supply runs ans member] at inAns
  have := Set.mem_singleton_iff.mp inAns
  cases this

#print axioms core_reaches
#print axioms core_normal
#print axioms answers_only_c
#print axioms answers_c
#print axioms shows_open_call
#print axioms answers_differ

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.BinderCoreAnswers
