import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Laws

/-!
# Renaming bound names changes no answer

A **renaming of bound names** of MeTTa programs permutes the keys of each binder site
(`KeyRenaming`): the equations `(= (f $x) $x)` and `(= (f $y) $y)` at one site differ by one. It acts
on every name with its scopes kept (`KeyRenaming.asg`), hence on data, computations, equations,
programs, stores, alternatives, spaces and configurations (`rConfig`); a program's reading of text as
code is conjugated (`rProg`).

* **Renaming commutes with fresh copies and with opening a site** (`copy_comm`, `open_comm`), and
  keeps solvability, readings, determination, entailment and most general solutions
  (`Laws.solvable_rename`, `Laws.reads_rename`, `determines_rename`, `entails_rename`,
  `principal_rename`).
* **Every move of a program is a move of the renamed program** between the renamed configurations
  (`move_rename`); hence every step and every run (`step_rename`, `runs_rename`).
* **A renamed configuration has the same bag of answers** (`answers_rConfig`).
* **The law** (`runs_rename_answers`): every run of a program from a query over spaces is matched by a
  run of the renamed program from the renamed query over the renamed spaces, ending with the same bag
  of answers. The converse is the same theorem for the inverse renaming (`rConfig_inv`, `rProg_inv`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Renaming

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Laws

/-! ## Knowledge under a renaming with an inverse, for any key system -/

section
variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  {ρ ρ' : Assignment (fam κ) (fam κ)}

theorem determines_rename (inverse : Assignment.compose ρ' ρ = generator (fam κ))
    (K : List (Constraint κ Γ star)) (t : Data κ Γ star) (g : Term S Γ star) :
    Determines (renameStore ρ K) (instantiate ρ t) g ↔ Determines K t g := by
  constructor
  · rintro ⟨live, all⟩
    refine ⟨(solvable_rename inverse K).mp live, fun target σ solved => ?_⟩
    have back : Assignment.compose (Assignment.compose σ ρ') ρ = σ := by
      rw [← Assignment.compose_associative, inverse, Assignment.compose_identity_right]
    have solved' : Models (Assignment.compose σ ρ') (renameStore ρ K) := by
      rw [models_renameStore, back]
      exact solved
    have read := all target _ solved'
    rw [← Assignment.instantiate_compose, back] at read
    exact read
  · rintro ⟨live, all⟩
    refine ⟨(solvable_rename inverse K).mpr live, fun target σ solved => ?_⟩
    rw [← Assignment.instantiate_compose]
    exact all target _ ((models_renameStore σ ρ K).mp solved)

theorem entails_rename (inverse : Assignment.compose ρ' ρ = generator (fam κ))
    (K : List (Constraint κ Γ star)) (a b : Data κ Γ star) :
    EntailsEq (renameStore ρ K) (instantiate ρ a) (instantiate ρ b) ↔ EntailsEq K a b := by
  constructor
  · intro all X target σ solved
    have back : Assignment.compose (Assignment.compose σ ρ') ρ = σ := by
      rw [← Assignment.compose_associative, inverse, Assignment.compose_identity_right]
    have solved' : Models (Assignment.compose σ ρ') (renameStore ρ K) := by
      rw [models_renameStore, back]
      exact solved
    have same := all target _ solved'
    rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, back] at same
    exact same
  · intro all X target σ solved
    rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
    exact all target _ ((models_renameStore σ ρ K).mp solved)

/-- **Most general solutions are conjugated.** -/
theorem principal_rename (inverse : Assignment.compose ρ' ρ = generator (fam κ))
    (inverse' : Assignment.compose ρ ρ' = generator (fam κ))
    {K : List (Constraint κ Γ star)} {θ : Assignment (fam κ) (fam κ)} (principal : Principal K θ) :
    Principal (renameStore ρ K) (Assignment.compose ρ (Assignment.compose θ ρ')) := by
  have fold : Assignment.compose (Assignment.compose ρ (Assignment.compose θ ρ')) ρ =
      Assignment.compose ρ θ := by
    rw [← Assignment.compose_associative, ← Assignment.compose_associative, inverse,
      Assignment.compose_identity_right]
  refine ⟨?_, fun target σ solved name => ?_⟩
  · rw [models_renameStore, fold]
    intro e member
    rw [Assignment.instantiate_compose, Assignment.instantiate_compose, principal.1 e member]
  · have solvedK := (models_renameStore σ ρ K).mp solved
    have general := principal.2 target (Assignment.compose σ ρ) solvedK
    show instantiate σ (Assignment.compose ρ (Assignment.compose θ ρ') name) = σ name
    have unfold : instantiate σ (Assignment.compose ρ (Assignment.compose θ ρ') name) =
        instantiate (Assignment.compose σ ρ) (instantiate θ (ρ' name)) := by
      show instantiate σ (instantiate ρ (instantiate θ (ρ' name))) = _
      rw [← Assignment.instantiate_compose σ ρ]
    -- every solution of the store is unchanged by `θ`
    have absorbs : Assignment.compose (Assignment.compose σ ρ) θ = Assignment.compose σ ρ := by
      funext x
      exact general x
    rw [unfold, ← Assignment.instantiate_compose (Assignment.compose σ ρ) θ, absorbs,
      Assignment.instantiate_compose]
    have rr : instantiate ρ (ρ' name) = generator (fam κ) name := congrFun inverse' name
    rw [rr, instantiate_generator]
end

/-! ## Renamings of the keys of each site of MeTTa programs -/

/-- **A renaming of bound names**: a permutation of the key indices of each site. -/
structure KeyRenaming where
  fwd : List ℕ → ℕ → ℕ
  bwd : List ℕ → ℕ → ℕ
  bwd_fwd : ∀ s i, bwd s (fwd s i) = i
  fwd_bwd : ∀ s i, fwd s (bwd s i) = i

namespace KeyRenaming

variable (π : KeyRenaming)

/-- The inverse renaming. -/
def inv : KeyRenaming := ⟨π.bwd, π.fwd, π.fwd_bwd, π.bwd_fwd⟩

/-- A name renamed: its scopes, site and arity kept. -/
def name (x : Name mkeys) : Name mkeys := ⟨x.scopes, ⟨x.key.site, π.fwd x.key.site x.key.index, x.key.arity⟩⟩

/-- The renaming as an assignment. -/
def asg : Assignment (fam mkeys) (fam mkeys) := fun x => generator (fam mkeys) (π.name x)

theorem compose_inv : Assignment.compose π.inv.asg π.asg = generator (fam mkeys) := by
  funext x
  rcases x with ⟨scopes, ⟨s, i, arity⟩⟩
  show instantiate π.inv.asg (generator (fam mkeys) (π.name ⟨scopes, ⟨s, i, arity⟩⟩)) = _
  rw [instantiate_generator]
  show generator (fam mkeys) ⟨scopes, ⟨s, π.bwd s (π.fwd s i), arity⟩⟩ = generator (fam mkeys) ⟨scopes, ⟨s, i, arity⟩⟩
  rw [π.bwd_fwd s i]

theorem inv_compose : Assignment.compose π.asg π.inv.asg = generator (fam mkeys) := by
  funext x
  rcases x with ⟨scopes, ⟨s, i, arity⟩⟩
  show instantiate π.asg (generator (fam mkeys) (π.inv.name ⟨scopes, ⟨s, i, arity⟩⟩)) = _
  rw [instantiate_generator]
  show generator (fam mkeys) ⟨scopes, ⟨s, π.fwd s (π.bwd s i), arity⟩⟩ = generator (fam mkeys) ⟨scopes, ⟨s, i, arity⟩⟩
  rw [π.fwd_bwd s i]

/-- **Renaming commutes with a fresh copy.** -/
theorem copy_comm (n : ℕ) :
    Assignment.compose π.asg (copyAt mkeys n) = Assignment.compose (copyAt mkeys n) π.asg := by
  funext x
  rcases x with ⟨scopes, ⟨s, i, arity⟩⟩
  show instantiate π.asg (generator (fam mkeys) ⟨n :: scopes, ⟨s, i, arity⟩⟩) =
    instantiate (copyAt mkeys n) (generator (fam mkeys) ⟨scopes, ⟨s, π.fwd s i, arity⟩⟩)
  rw [instantiate_generator, instantiate_generator]
  rfl

/-- **Renaming commutes with opening a site.** -/
theorem open_comm (s' : List ℕ) (n : ℕ) :
    Assignment.compose π.asg (openAt mkeys s' n) = Assignment.compose (openAt mkeys s' n) π.asg := by
  funext x
  rcases x with ⟨scopes, ⟨s, i, arity⟩⟩
  show instantiate π.asg (generator (fam mkeys) ⟨if s = s' then n :: scopes else scopes, ⟨s, i, arity⟩⟩) =
    instantiate (openAt mkeys s' n) (generator (fam mkeys) ⟨scopes, ⟨s, π.fwd s i, arity⟩⟩)
  rw [instantiate_generator, instantiate_generator]
  rfl

/-! ### The renaming on syntax and configurations -/

variable {Ty : Type}

def rD (t : MData) : MData := instantiate π.asg t
def rC (c : Comp mkeys [] () Ty) : Comp mkeys [] () Ty := c.inst π.asg
def rStore (K : List (Constraint mkeys [] ())) : List (Constraint mkeys [] ()) := renameStore π.asg K
def rEq (e : Equation mkeys [] () Ty) : Equation mkeys [] () Ty := ⟨e.site, π.rD e.lhs, π.rC e.rhs⟩
def rPend (entry : MData × Comp mkeys [] () Ty) : MData × Comp mkeys [] () Ty := (π.rD entry.1, π.rC entry.2)

/-- A renamed program: renamed equations, and the reading of text conjugated. -/
def rProg (P : Program mkeys [] () Ty) : Program mkeys [] () Ty :=
  ⟨P.equations.map π.rEq, fun t => π.rC (P.reflect (π.inv.rD t))⟩

def rFrame : Frame mkeys [] () Ty → Frame mkeys [] () Ty
  | .bindTo s p k => .bindTo s (π.rD p) (π.rC k)
  | .checkAt T => .checkAt T
  | .memo x => .memo (π.rD x)

def rFocus : Focus mkeys [] () Ty → Focus mkeys [] () Ty
  | .eval c => .eval (π.rC c)
  | .value t => .value (π.rD t)
  | .refused t T => .refused (π.rD t) T

def rBranch (b : Branch mkeys [] () Ty) : Branch mkeys [] () Ty :=
  ⟨π.rStore b.store, π.rFocus b.focus, b.frames.map π.rFrame, b.pending.map π.rPend⟩

def rRow (r : Row mkeys [] ()) : Row mkeys [] () := ⟨π.rD r.atom, π.rStore r.store⟩

def rSpaces (spaces : MClosed → Multiset (Row mkeys [] ())) : MClosed → Multiset (Row mkeys [] ()) :=
  fun h => (spaces h).map π.rRow

def rWorld (w : World mkeys [] ()) : World mkeys [] () := ⟨w.scope, w.handles, π.rSpaces w.spaces⟩

def rConfig (C : Config mkeys [] () Ty) : Config mkeys [] () Ty :=
  ⟨π.rWorld C.world, C.branches.map π.rBranch⟩

/-! ### Commutations -/

theorem rD_copy (n : ℕ) (t : MData) : π.rD (instantiate (copyAt mkeys n) t) = instantiate (copyAt mkeys n) (π.rD t) := by
  rw [rD, rD, ← Assignment.instantiate_compose, ← Assignment.instantiate_compose, copy_comm]

theorem rD_open (s : List ℕ) (n : ℕ) (t : MData) :
    π.rD (instantiate (openAt mkeys s n) t) = instantiate (openAt mkeys s n) (π.rD t) := by
  rw [rD, rD, ← Assignment.instantiate_compose, ← Assignment.instantiate_compose, open_comm]

theorem comp_inst (σ τ : Assignment (fam mkeys) (fam mkeys)) (c : Comp mkeys [] () Ty) :
    (c.inst σ).inst τ = c.inst (Assignment.compose τ σ) := by
  simp only [Comp.inst, Comp.mapData_comp]
  congr 1
  funext t
  exact (Assignment.instantiate_compose τ σ t).symm

theorem rC_copy (n : ℕ) (c : Comp mkeys [] () Ty) :
    π.rC (c.inst (copyAt mkeys n)) = (π.rC c).inst (copyAt mkeys n) := by
  rw [rC, rC, comp_inst, comp_inst, copy_comm]

theorem rC_open (s : List ℕ) (n : ℕ) (c : Comp mkeys [] () Ty) :
    π.rC (c.inst (openAt mkeys s n)) = (π.rC c).inst (openAt mkeys s n) := by
  rw [rC, rC, comp_inst, comp_inst, open_comm]

theorem rStore_append (K L : List (Constraint mkeys [] ())) : π.rStore (K ++ L) = π.rStore K ++ π.rStore L :=
  List.map_append

theorem rStore_single (a b : MData) : π.rStore [(a, b)] = [(π.rD a, π.rD b)] := rfl

theorem rStore_copy (n : ℕ) (K : List (Constraint mkeys [] ())) :
    π.rStore (copyStore n K) = copyStore n (π.rStore K) := by
  simp only [rStore, renameStore, copyStore, List.map_map]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp]
  rw [← rD, ← rD, π.rD_copy, π.rD_copy]
  rfl

theorem rStore_rowUse (n : ℕ) (r : Row mkeys [] ()) (t : MData) :
    π.rStore (rowUse n r t) = rowUse n (π.rRow r) (π.rD t) := by
  rw [rowUse, rowUse, rStore_append, rStore_copy, rStore_single, rD_copy]
  rfl

theorem rD_include (g : MClosed) : π.rD (Rigid.includeTerm (fam mkeys) g) = Rigid.includeTerm (fam mkeys) g :=
  Rigid.instantiate_include _ g

theorem rD_inv (t : MData) : π.inv.rD (π.rD t) = t := by
  rw [rD, rD, ← Assignment.instantiate_compose, compose_inv, instantiate_identity]

theorem rBranch_callBranch {D : Discipline MSig [] ()} (n : ℕ) (K : List (Constraint mkeys [] ())) (t : MData)
    (fs : List (Frame mkeys [] () D.Ty)) (ps : List (MData × Comp mkeys [] () D.Ty)) (e : Equation mkeys [] () D.Ty) :
    π.rBranch (callBranch D n K t fs ps e) =
      callBranch D n (π.rStore K) (π.rD t) (fs.map π.rFrame) (ps.map π.rPend) (π.rEq e) := by
  show (⟨π.rStore (K ++ [(instantiate (copyAt mkeys n) e.lhs, t)]), .eval (π.rC (e.rhs.inst (copyAt mkeys n))),
      fs.map π.rFrame, ps.map π.rPend⟩ : Branch mkeys [] () D.Ty) =
    ⟨π.rStore K ++ [(instantiate (copyAt mkeys n) (π.rD e.lhs), π.rD t)], .eval ((π.rC e.rhs).inst (copyAt mkeys n)),
      fs.map π.rFrame, ps.map π.rPend⟩
  rw [rStore_append, rStore_single, rD_copy, rC_copy]

theorem rWorld_setSpace (w : World mkeys [] ()) (h : MClosed) (bag : Multiset (Row mkeys [] ())) (scope handles : ℕ) :
    π.rWorld ⟨scope, handles, setSpace w.spaces h bag⟩ =
      ⟨scope, handles, setSpace (π.rWorld w).spaces h (bag.map π.rRow)⟩ := by
  show (⟨scope, handles, π.rSpaces (setSpace w.spaces h bag)⟩ : World mkeys [] ()) = _
  congr 1
  funext h'
  by_cases same : h' = h
  · subst same
    simp only [rSpaces, setSpace_same]
  · simp only [rSpaces, rWorld, setSpace_other _ _ same]

/-! ### Moves, steps and runs -/

variable {D : Discipline MSig [] ()} {P : Program mkeys [] () D.Ty} {supply : ℕ → MClosed}

/-- **A move of a program is a move of the renamed program between the renamed configurations.** -/
theorem move_rename {w w' : World mkeys [] ()} {b : Branch mkeys [] () D.Ty} {bs : Multiset (Branch mkeys [] () D.Ty)}
    (moved : Move D P supply w b w' bs) :
    Move D (π.rProg P) supply (π.rWorld w) (π.rBranch b) (π.rWorld w') (bs.map π.rBranch) := by
  have inverse := π.compose_inv
  have inverse' := π.inv_compose
  cases moved with
  | ret K t fs ps => exact .ret _ _ _ _ _
  | apply K t fs ps matched =>
      have bag : (((P.equations.map (callBranch D w.scope K t fs ps) : List (Branch mkeys [] () D.Ty)) :
          Multiset (Branch mkeys [] () D.Ty)).map π.rBranch) =
          (((π.rProg P).equations.map (callBranch D w.scope (π.rStore K) (π.rD t) (fs.map π.rFrame)
            (ps.map π.rPend)) : List (Branch mkeys [] () D.Ty)) : Multiset (Branch mkeys [] () D.Ty)) := by
        rw [Multiset.map_coe, List.map_map]
        simp only [rProg, List.map_map]
        congr 1
        apply List.map_congr_left
        intro e _
        exact π.rBranch_callBranch w.scope K t fs ps e
      rw [bag]
      obtain ⟨e, member, live⟩ := matched
      refine .apply _ _ _ _ _ ⟨π.rEq e, List.mem_map_of_mem member, ?_⟩
      have := (solvable_rename inverse (K ++ [(instantiate (copyAt mkeys w.scope) e.lhs, t)])).mpr live
      rw [← rStore, rStore_append, rStore_single, rD_copy] at this
      exact this
  | unmatched K t fs ps none =>
      refine .unmatched _ _ _ _ _ fun e' member live => ?_
      obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
      apply none e inside
      have live' : Solvable (π.rStore K ++ π.rStore [(instantiate (copyAt mkeys w.scope) e.lhs, t)]) := by
        rw [rStore_single, rD_copy]
        exact live
      rw [← rStore_append] at live'
      exact (solvable_rename inverse _).mp live'
  | run K t fs ps θ principal =>
      have principal' := principal_rename inverse inverse' principal
      have inner : Assignment.compose (Assignment.compose θ π.inv.asg) π.asg = θ := by
        rw [← Assignment.compose_associative, compose_inv, Assignment.compose_identity_right]
      have outer : Assignment.compose π.inv.asg (Assignment.compose π.asg θ) = θ := by
        rw [Assignment.compose_associative, compose_inv, Assignment.compose_identity_left]
      have key : Assignment.compose π.inv.asg (Assignment.compose
          (Assignment.compose π.asg (Assignment.compose θ π.inv.asg)) π.asg) = θ := by
        rw [← Assignment.compose_associative π.asg (Assignment.compose θ π.inv.asg) π.asg, inner, outer]
      have read : (π.rProg P).reflect (instantiate (Assignment.compose π.asg (Assignment.compose θ π.inv.asg))
          (π.rD t)) = π.rC (P.reflect (instantiate θ t)) := by
        have arg : π.inv.rD (instantiate (Assignment.compose π.asg (Assignment.compose θ π.inv.asg)) (π.rD t)) =
            instantiate θ t := by
          simp only [rD]
          rw [← Assignment.instantiate_compose (Assignment.compose π.asg (Assignment.compose θ π.inv.asg)) π.asg t,
            ← Assignment.instantiate_compose π.inv.asg _ t, key]
        show π.rC (P.reflect (π.inv.rD _)) = _
        rw [arg]
      have moved := Move.run (D := D) (P := π.rProg P) (supply := supply) (π.rWorld w) (π.rStore K) (π.rD t)
        (fs.map π.rFrame) (ps.map π.rPend) _ principal'
      rw [read] at moved
      exact moved
  | letStart K s p c k fs ps => exact .letStart _ _ _ _ _ _ _ _
  | letBind K v s p k fs ps =>
      have moved := Move.letBind (D := D) (P := π.rProg P) (supply := supply) (π.rWorld w) (π.rStore K) (π.rD v) s
        (π.rD p) (π.rC k) (fs.map π.rFrame) (ps.map π.rPend)
      rw [← rD_open, ← rC_open, ← rStore_single, ← rStore_append] at moved
      exact moved
  | choice K c d fs ps => exact .choice _ _ _ _ _ _
  | fail K fs ps => exact .fail _ _ _ _
  | query K sp p k fs ps h addressed =>
      have addressed' := (determines_rename inverse K sp h).mpr addressed
      have moved := Move.query (D := D) (P := π.rProg P) (supply := supply) (π.rWorld w) (π.rStore K) (π.rD sp)
        (π.rD p) (π.rC k) (fs.map π.rFrame) (ps.map π.rPend) h addressed'
      have bag : ((w.spaces h).map fun r => (⟨K ++ rowUse w.scope r p, .eval k, fs, ps⟩ : Branch mkeys [] () D.Ty)).map
          π.rBranch = ((π.rWorld w).spaces h).map fun r =>
            (⟨π.rStore K ++ rowUse (π.rWorld w).scope r (π.rD p), .eval (π.rC k), fs.map π.rFrame, ps.map π.rPend⟩ :
              Branch mkeys [] () D.Ty) := by
        show _ = ((w.spaces h).map π.rRow).map _
        rw [Multiset.map_map, Multiset.map_map]
        apply Multiset.map_congr rfl
        intro r _
        show (⟨π.rStore (K ++ rowUse w.scope r p), .eval (π.rC k), fs.map π.rFrame, ps.map π.rPend⟩ :
          Branch mkeys [] () D.Ty) = ⟨π.rStore K ++ rowUse w.scope (π.rRow r) (π.rD p), .eval (π.rC k),
            fs.map π.rFrame, ps.map π.rPend⟩
        rw [rStore_append, rStore_rowUse]
      rw [bag]
      exact moved
  | add K sp t k fs ps h addressed =>
      have addressed' := (determines_rename inverse K sp h).mpr addressed
      have moved := Move.add (D := D) (P := π.rProg P) (supply := supply) (π.rWorld w) (π.rStore K) (π.rD sp)
        (π.rD t) (π.rC k) (fs.map π.rFrame) (ps.map π.rPend) h addressed'
      rw [π.rWorld_setSpace w h (w.spaces h + {⟨t, K⟩}) w.scope w.handles]
      have bag : (w.spaces h + {⟨t, K⟩}).map π.rRow = (π.rWorld w).spaces h + {⟨π.rD t, π.rStore K⟩} := by
        rw [Multiset.map_add, Multiset.map_singleton]
        rfl
      rw [bag]
      exact moved
  | remove K sp t k fs ps h addressed r rest split fits =>
      have addressed' := (determines_rename inverse K sp h).mpr addressed
      have split' : (π.rWorld w).spaces h = π.rRow r ::ₘ rest.map π.rRow := by
        show (w.spaces h).map π.rRow = _
        rw [split, Multiset.map_cons]
      have fits' : Solvable (π.rStore K ++ rowUse w.scope (π.rRow r) (π.rD t)) := by
        rw [← rStore_rowUse, ← rStore_append]
        exact (solvable_rename inverse _).mpr fits
      have moved := Move.remove (D := D) (P := π.rProg P) (supply := supply) (π.rWorld w) (π.rStore K) (π.rD sp)
        (π.rD t) (π.rC k) (fs.map π.rFrame) (ps.map π.rPend) h addressed' (π.rRow r) (rest.map π.rRow) split' fits'
      rw [π.rWorld_setSpace w h rest (w.scope + 1) w.handles]
      rw [← rStore_rowUse, ← rStore_append] at moved
      exact moved
  | removeMissing K sp t k fs ps h addressed none =>
      have addressed' := (determines_rename inverse K sp h).mpr addressed
      refine .removeMissing _ _ _ _ _ _ _ h addressed' fun r' member live => ?_
      have member' : r' ∈ (w.spaces h).map π.rRow := member
      obtain ⟨r, inside, rfl⟩ := Multiset.mem_map.mp member'
      apply none r inside
      have live' : Solvable (π.rStore K ++ rowUse w.scope (π.rRow r) (π.rD t)) := live
      rw [← rStore_rowUse, ← rStore_append] at live'
      exact (solvable_rename inverse _).mp live'
  | new K s x k fs ps =>
      have moved := Move.new (D := D) (P := π.rProg P) (supply := supply) (π.rWorld w) (π.rStore K) s (π.rD x)
        (π.rC k) (fs.map π.rFrame) (ps.map π.rPend)
      rw [← rD_open, ← rC_open, ← π.rD_include, ← rStore_single, ← rStore_append] at moved
      exact moved
  | checkStart K T c fs ps => exact .checkStart _ _ _ _ _ _
  | admitted K v T fs ps all =>
      exact .admitted _ _ _ _ _ _ fun g reads => all g ((reads_rename inverse K v g).mp reads)
  | refused K v T fs ps none =>
      exact .refused _ _ _ _ _ _ fun g reads => none g ((reads_rename inverse K v g).mp reads)
  | delay K s x c k fs ps =>
      have moved := Move.delay (D := D) (P := π.rProg P) (supply := supply) (π.rWorld w) (π.rStore K) s (π.rD x)
        (π.rC c) (π.rC k) (fs.map π.rFrame) (ps.map π.rPend)
      rw [← rD_open, ← rC_open] at moved
      exact moved
  | forcePending K x cell c fs before after bound =>
      have bound' : EntailsEq (π.rStore K) (π.rD x) (π.rD cell) := (entails_rename inverse K x cell).mpr bound
      have moved := Move.forcePending (D := D) (P := π.rProg P) (supply := supply) (π.rWorld w) (π.rStore K)
        (π.rD x) (π.rD cell) (π.rC c) (fs.map π.rFrame) (before.map π.rPend) (after.map π.rPend) bound'
      have pend : (before ++ (cell, c) :: after).map π.rPend =
          before.map π.rPend ++ (π.rD cell, π.rC c) :: after.map π.rPend := by
        rw [List.map_append, List.map_cons]
        rfl
      have pend' : (before ++ after).map π.rPend = before.map π.rPend ++ after.map π.rPend := List.map_append
      show Move D (π.rProg P) supply (π.rWorld w)
        ⟨π.rStore K, .eval (.force (π.rD x)), fs.map π.rFrame, (before ++ (cell, c) :: after).map π.rPend⟩
        (π.rWorld w) {⟨π.rStore K, .eval (π.rC c), .memo (π.rD cell) :: fs.map π.rFrame, (before ++ after).map π.rPend⟩}
      rw [pend, pend']
      exact moved
  | forceDone K x fs ps none =>
      refine .forceDone _ _ _ _ _ fun entry member entails => ?_
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      exact none original inside ((entails_rename inverse K x original.1).mp entails)
  | memo K v x fs ps =>
      have moved := Move.memo (D := D) (P := π.rProg P) (supply := supply) (π.rWorld w) (π.rStore K) (π.rD v)
        (π.rD x) (fs.map π.rFrame) (ps.map π.rPend)
      rw [← rStore_single, ← rStore_append] at moved
      exact moved

theorem step_rename {C C' : Config mkeys [] () D.Ty} (step : Step D P supply C C') :
    Step D (π.rProg P) supply (π.rConfig C) (π.rConfig C') := by
  cases step with
  | move w w' b rest bs live moved =>
      refine Step.of_eq (b := π.rBranch b) (rest := rest.map π.rBranch) (bs := bs.map π.rBranch)
        (Multiset.map_cons _ _ _) (Multiset.map_add _ _ _) ?_ (π.move_rename moved)
      exact (solvable_rename π.compose_inv b.store).mpr live

/-- **Every run of a program is a run of the renamed program** between the renamed configurations. -/
theorem runs_rename {C C' : Config mkeys [] () D.Ty} (runs : Runs D P supply C C') :
    Runs D (π.rProg P) supply (π.rConfig C) (π.rConfig C') := by
  induction runs with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (π.step_rename step)

/-! ### Answers -/

/-- **A renamed configuration has the same bag of answers.** -/
theorem answers_rConfig (C : Config mkeys [] () D.Ty) : (π.rConfig C).answers = C.answers := by
  classical
  simp only [Config.answers, rConfig]
  rw [Multiset.filter_map, Multiset.map_map]
  have samePred : Multiset.filter ((fun b : Branch mkeys [] () D.Ty => b.Finished ∧ Solvable b.store) ∘
      π.rBranch) C.branches = Multiset.filter (fun b => b.Finished ∧ Solvable b.store) C.branches := by
    apply Multiset.filter_congr
    intro b _
    rcases b with ⟨K, focus, frames, pending⟩
    simp only [Function.comp, rBranch, Branch.Finished, List.map_eq_nil_iff]
    rw [show Solvable (π.rStore K) ↔ Solvable K from solvable_rename π.compose_inv K]
    cases focus <;> simp [rFocus]
  rw [samePred]
  apply Multiset.map_congr rfl
  intro b _
  rcases b with ⟨K, focus, frames, pending⟩
  ext g
  cases focus with
  | value t =>
      simp only [Function.comp, rBranch, rFocus, Branch.answer, Set.mem_ofPred_eq, Focus.value.injEq,
        exists_eq_left']
      exact reads_rename π.compose_inv K t g
  | eval c => simp [Function.comp, rBranch, rFocus, Branch.answer]
  | refused t T => simp [Function.comp, rBranch, rFocus, Branch.answer]

theorem rConfig_initial (spaces : MClosed → Multiset (Row mkeys [] ())) (q : Comp mkeys [] () D.Ty) :
    π.rConfig (Config.initial spaces q) = Config.initial (π.rSpaces spaces) (π.rC q) := rfl

/-- **The law**: a run of a program from a query over spaces is matched by a run of the renamed
program from the renamed query over the renamed spaces, which ends with the same bag of answers. -/
theorem runs_rename_answers {spaces : MClosed → Multiset (Row mkeys [] ())} {q : Comp mkeys [] () D.Ty}
    {C : Config mkeys [] () D.Ty} (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ C', Runs D (π.rProg P) supply (Config.initial (π.rSpaces spaces) (π.rC q)) C' ∧ C'.answers = C.answers :=
  ⟨π.rConfig C, π.rConfig_initial spaces q ▸ π.runs_rename runs, π.answers_rConfig C⟩

/-! ### The inverse renaming undoes the renaming -/

theorem rC_inv (c : Comp mkeys [] () Ty) : π.inv.rC (π.rC c) = c := by
  rw [rC, rC, comp_inst, compose_inv]
  have identity : (instantiate (generator (fam mkeys)) : MData → MData) = id := funext instantiate_identity
  show c.mapData (instantiate (generator (fam mkeys))) = c
  rw [identity, Comp.mapData_id]

theorem rProg_inv (Q : Program mkeys [] () Ty) : π.inv.rProg (π.rProg Q) = Q := by
  cases Q with
  | mk equations reflect =>
      simp only [rProg, List.map_map]
      congr 1
      · conv_rhs => rw [← List.map_id equations]
        apply List.map_congr_left
        intro e _
        cases e with
        | mk site lhs rhs =>
            show (⟨site, π.inv.rD (π.rD lhs), π.inv.rC (π.rC rhs)⟩ : Equation mkeys [] () Ty) = ⟨site, lhs, rhs⟩
            rw [rD_inv, rC_inv]
      · funext t
        show π.inv.rC (π.rC (reflect (π.inv.rD (π.inv.inv.rD t)))) = reflect t
        rw [rC_inv]
        congr 1
        exact π.rD_inv t

end KeyRenaming

#print axioms determines_rename
#print axioms entails_rename
#print axioms principal_rename
#print axioms KeyRenaming.move_rename
#print axioms KeyRenaming.runs_rename
#print axioms KeyRenaming.answers_rConfig
#print axioms KeyRenaming.runs_rename_answers
#print axioms KeyRenaming.rProg_inv

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Renaming
