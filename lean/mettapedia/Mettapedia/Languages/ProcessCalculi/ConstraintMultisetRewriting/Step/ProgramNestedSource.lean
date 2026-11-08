import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramEquationsVersions

/-!
# Nested calls: evaluation contexts, and the frame-stack machine that implements them

The equation core of `ProgramEquations` rewrites a call only at the root of a thread. Here calls
occur inside arguments and inside right-hand sides, and are evaluated under one stated strategy.

**Expressions** (`Ex`): held data `val t` (an open term, never evaluated), a pair `pair a b` whose
sides are evaluated left to right and then built into the data cell, and a call `call a`, which
evaluates `a` to data `w` and then matches `w` against the installed version's equations by two-way
unification. Right-hand sides of equations are expression patterns (`EPat`); a pattern variable
stands for data, in `val` positions.

**The strategy is call by value, leftmost-innermost**: the arguments of a call are evaluated before
the call, left to right, and the instantiated right-hand side is evaluated in the call's place.
This is the interpretation of tuples in the MeTTa specification (`interpret_tuple`,
`interpret_args`: every element is evaluated, left to right, with the product of the results, then
`metta_call` queries `(= atom $X)` and evaluates each result again). Positions declared `Atom` are
not evaluated there; here they are `val` positions. So the core keeps evaluation explicit, and a
surface inserts `call` and `pair` by position and declared type.

* **Reference semantics** (`CStep`): reduction in evaluation contexts. The contexts (`ECtx`) are
  the grammar `E ::= [] | (E b) | (v E) | call E`; a step rewrites the redex in the hole: a pair of
  data is built, or a call of data is answered by an equation renamed into a fresh scope `m`, with a
  most general unifier `θ` applied to the whole configuration (so the caller's variables are bound
  in every row).
* **The frame-stack machine** (`KStep`): a thread is `ev e K`, `ret v K` or `ap w K`, for a stack
  of frames `K` (the evaluation context, innermost first, as in Pitts's frame stacks). Six
  administrative rules decompose and rebuild; one rule per equation answers a call.
* **The machine implements the strategy** (`kstep_unload`, `kruns_unload`): plugging every thread's
  focus back into its frames (`SRow.unload`) maps each machine step to no step or to one reference
  step, and every machine run to a reference run whose scopes stay below the machine's.
* **The two decompositions agree** (`plug_ctxOf`): a frame stack plugs as the evaluation context it
  denotes.

The machine's translation into firings of the ordinary step, with adequacy both ways, is in
`ProgramNested`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations.Versions

/-! ## Expressions and expression patterns -/

/-- Expressions: held data, a pair evaluated left to right, and a call. -/
inductive Ex where
  | val (t : Tm)
  | pair (a b : Ex)
  | call (a : Ex)

/-- Apply a substitution to the data of an expression. -/
def Ex.subst (θ : Subst rows) : Ex → Ex
  | .val t => .val (θ.applyTerm t)
  | .pair a b => .pair (a.subst θ) (b.subst θ)
  | .call a => .call (a.subst θ)

/-- Expression patterns: the right-hand sides of equations. -/
inductive EPat where
  | val (p : Pat)
  | pair (a b : EPat)
  | call (a : EPat)

/-- Copy an expression pattern into the scope `n`. -/
def EPat.at (n : ℕ) : EPat → Ex
  | .val p => .val (p.at n)
  | .pair a b => .pair (EPat.at n a) (EPat.at n b)
  | .call a => .call (EPat.at n a)

/-- The pattern variables of an expression pattern. -/
def EPat.vars : EPat → List ℕ
  | .val p => p.vars
  | .pair a b => EPat.vars a ++ EPat.vars b
  | .call a => EPat.vars a

/-- An equation `(= lhs rhs)`: a data pattern and an expression pattern. -/
structure NEquation where
  lhs : Pat
  rhs : EPat

/-- Versioned programs: the equations installed at each version. -/
abbrev Defs := ℕ → List NEquation

/-! ## Frames and evaluation contexts -/

/-- Evaluation frames: the hole on the left of a pair, on the right of a pair whose left side is
data, or in the argument of a call. -/
inductive Frame where
  | left (b : Ex)
  | right (v : Tm)
  | arg

def Frame.subst (θ : Subst rows) : Frame → Frame
  | .left b => .left (b.subst θ)
  | .right v => .right (θ.applyTerm v)
  | .arg => .arg

/-- Plug an expression into a frame stack, innermost frame first. -/
def plug : List Frame → Ex → Ex
  | [], e => e
  | .left b :: K, e => plug K (.pair e b)
  | .right v :: K, e => plug K (.pair (.val v) e)
  | .arg :: K, e => plug K (.call e)

theorem plug_subst (θ : Subst rows) : ∀ (K : List Frame) (e : Ex),
    (plug K e).subst θ = plug (K.map (Frame.subst θ)) (e.subst θ)
  | [], _ => rfl
  | .left b :: K, e => by
      simp only [plug, List.map_cons, Frame.subst]
      rw [plug_subst θ K]
      rfl
  | .right v :: K, e => by
      simp only [plug, List.map_cons, Frame.subst]
      rw [plug_subst θ K]
      rfl
  | .arg :: K, e => by
      simp only [plug, List.map_cons, Frame.subst]
      rw [plug_subst θ K]
      rfl

/-- **Evaluation contexts** of the strategy: `E ::= [] | (E b) | (v E) | call E`. -/
inductive ECtx where
  | hole
  | pairL (E : ECtx) (b : Ex)
  | pairR (v : Tm) (E : ECtx)
  | arg (E : ECtx)

/-- Fill the hole of an evaluation context. -/
def ECtx.fill : ECtx → Ex → Ex
  | .hole, e => e
  | .pairL E b, e => .pair (E.fill e) b
  | .pairR v E, e => .pair (.val v) (E.fill e)
  | .arg E, e => .call (E.fill e)

/-- Put a context into the hole of another. -/
def ECtx.comp : ECtx → ECtx → ECtx
  | .hole, E' => E'
  | .pairL E b, E' => .pairL (E.comp E') b
  | .pairR v E, E' => .pairR v (E.comp E')
  | .arg E, E' => .arg (E.comp E')

theorem ECtx.fill_comp : ∀ (E E' : ECtx) (e : Ex), (E.comp E').fill e = E.fill (E'.fill e)
  | .hole, _, _ => rfl
  | .pairL E b, E', e => by simp only [comp, fill, fill_comp E E' e]
  | .pairR v E, E', e => by simp only [comp, fill, fill_comp E E' e]
  | .arg E, E', e => by simp only [comp, fill, fill_comp E E' e]

/-- The context of one frame. -/
def Frame.ctx : Frame → ECtx
  | .left b => .pairL .hole b
  | .right v => .pairR v .hole
  | .arg => .arg .hole

/-- **The evaluation context a frame stack denotes.** -/
def ctxOf : List Frame → ECtx
  | [] => .hole
  | f :: K => (ctxOf K).comp f.ctx

/-- **A frame stack plugs as the evaluation context it denotes.** -/
theorem plug_ctxOf : ∀ (K : List Frame) (e : Ex), plug K e = (ctxOf K).fill e
  | [], _ => rfl
  | .left b :: K, e => by rw [plug, plug_ctxOf K, ctxOf, ECtx.fill_comp]; rfl
  | .right v :: K, e => by rw [plug, plug_ctxOf K, ctxOf, ECtx.fill_comp]; rfl
  | .arg :: K, e => by rw [plug, plug_ctxOf K, ctxOf, ECtx.fill_comp]; rfl

/-! ## Encodings into rows -/

/-- Expressions as step terms. -/
def encE : Ex → Tm
  | .val t => tagged 130 t
  | .pair a b => tagged 131 (node (encE a) (encE b))
  | .call a => tagged 132 (encE a)

/-- Expression patterns as patterns. -/
def EPat.enc : EPat → Pat
  | .val p => ptag 130 p
  | .pair a b => ptag 131 (.cell (EPat.enc a) (EPat.enc b))
  | .call a => ptag 132 (EPat.enc a)

theorem EPat.enc_at (n : ℕ) : ∀ e : EPat, (EPat.enc e).at n = encE (e.at n)
  | .val _ => rfl
  | .pair a b => by
      show tagged 131 (node ((EPat.enc a).at n) ((EPat.enc b).at n)) = _
      rw [EPat.enc_at n a, EPat.enc_at n b]
      rfl
  | .call a => by
      show tagged 132 ((EPat.enc a).at n) = _
      rw [EPat.enc_at n a]
      rfl

theorem EPat.enc_vars : ∀ e : EPat, (EPat.enc e).vars = e.vars
  | .val _ => rfl
  | .pair a b => by
      show [] ++ ((EPat.enc a).vars ++ (EPat.enc b).vars) = _
      rw [EPat.enc_vars a, EPat.enc_vars b]
      rfl
  | .call a => by
      show [] ++ (EPat.enc a).vars = _
      rw [EPat.enc_vars a]
      rfl

theorem encE_subst (θ : Subst rows) : ∀ e : Ex, encE (e.subst θ) = θ.applyTerm (encE e)
  | .val _ => by simp only [Ex.subst, encE, apply_tagged]
  | .pair a b => by
      simp only [Ex.subst, encE, apply_tagged, apply_node, encE_subst θ a, encE_subst θ b]
  | .call a => by simp only [Ex.subst, encE, apply_tagged, encE_subst θ a]

/-- Frame stacks as step terms. -/
def encK : List Frame → Tm
  | [] => .const 143
  | .left b :: K => tagged 140 (node (encE b) (encK K))
  | .right v :: K => tagged 141 (node v (encK K))
  | .arg :: K => tagged 142 (encK K)

theorem encK_subst (θ : Subst rows) : ∀ K : List Frame,
    encK (K.map (Frame.subst θ)) = θ.applyTerm (encK K)
  | [] => rfl
  | .left b :: K => by
      simp only [List.map_cons, Frame.subst, encK, apply_tagged, apply_node, encE_subst,
        encK_subst θ K]
  | .right v :: K => by
      simp only [List.map_cons, Frame.subst, encK, apply_tagged, apply_node, encK_subst θ K]
  | .arg :: K => by
      simp only [List.map_cons, Frame.subst, encK, apply_tagged, encK_subst θ K]

/-! ## Source rows -/

/-- **Source rows**: machine threads, the version row, citations, redefinitions and their
results, and tagged data rows. -/
inductive SRow where
  | ev (e : Ex) (K : List Frame)
  | ret (v : Tm) (K : List Frame)
  | ap (w : Tm) (K : List Frame)
  | version (u : ℕ)
  | citation (u : ℕ)
  | redef (u : ℕ)
  | finished
  | data (k : ℕ) (t : Tm)

noncomputable instance : DecidableEq SRow := Classical.decEq _

def SRow.subst (θ : Subst rows) : SRow → SRow
  | .ev e K => .ev (e.subst θ) (K.map (Frame.subst θ))
  | .ret v K => .ret (θ.applyTerm v) (K.map (Frame.subst θ))
  | .ap w K => .ap (θ.applyTerm w) (K.map (Frame.subst θ))
  | .version u => .version u
  | .citation u => .citation u
  | .redef u => .redef u
  | .finished => .finished
  | .data k t => .data k (θ.applyTerm t)

/-- The machine's encoding of source rows. -/
def SRow.enc : SRow → Tm
  | .ev e K => tagged 120 (node (encE e) (encK K))
  | .ret v K => tagged 121 (node v (encK K))
  | .ap w K => tagged 122 (node w (encK K))
  | .version u => ver u
  | .citation u => cite u
  | .redef u => tagged 123 (.const u)
  | .finished => tagged 124 (.const 0)
  | .data k t => tagged k t

theorem SRow.enc_subst (θ : Subst rows) : ∀ s : SRow, (s.subst θ).enc = θ.applyTerm s.enc
  | .ev e K => by simp only [SRow.subst, SRow.enc, apply_tagged, apply_node, encE_subst, encK_subst]
  | .ret v K => by simp only [SRow.subst, SRow.enc, apply_tagged, apply_node, encK_subst]
  | .ap w K => by simp only [SRow.subst, SRow.enc, apply_tagged, apply_node, encK_subst]
  | .version u => by simp only [SRow.subst, SRow.enc, ver, apply_tagged, Subst.applyTerm_const]
  | .citation u => by simp only [SRow.subst, SRow.enc, cite, apply_tagged, Subst.applyTerm_const]
  | .redef u => by simp only [SRow.subst, SRow.enc, apply_tagged, Subst.applyTerm_const]
  | .finished => by simp only [SRow.subst, SRow.enc, apply_tagged, Subst.applyTerm_const]
  | .data k t => by simp only [SRow.subst, SRow.enc, apply_tagged]

/-! ## The reference semantics: reduction in evaluation contexts -/

/-- **The reference semantics of nested calls.** A thread `thread e` whose expression is
`E[redex]` for an evaluation context `E`:
* `E[(pair (val v) (val w))]` builds the data cell;
* `E[(call (val w))]`, beside the installed version `u`, is answered by an equation of `u` renamed
  into a fresh scope `m`: for a most general unifier `θ` of the call with the left-hand side, the
  thread continues with `E[rhs]` under `θ`, the call cites `u`, and `θ` binds the caller's
  variables in every row;
* a redefinition takes the installed version and installs another. -/
inductive CStep (defs : Defs) : Multiset Tm × ℕ → Multiset Tm × ℕ → Prop
  | build (E : ECtx) (v w : Tm) (F : Multiset Tm) (n : ℕ) :
      CStep defs (thread (encE (E.fill (.pair (.val v) (.val w)))) ::ₘ F, n)
        (thread (encE (E.fill (.val (node v w)))) ::ₘ F, n)
  | apply (u : ℕ) (j : Fin (defs u).length) (E : ECtx) (w : Tm) (F : Multiset Tm) (n m : ℕ)
      (fresh : n ≤ m) (θ : Subst rows) (mgu : IsMGU [(((defs u).get j).lhs.at m, w)] θ) :
      CStep defs (thread (encE (E.fill (.call (.val w)))) ::ₘ ver u ::ₘ F, n)
        (thread (encE ((E.fill (((defs u).get j).rhs.at m)).subst θ)) ::ₘ cite u ::ₘ ver u ::ₘ
          F.map θ.applyTerm, m + 1)
  | redefine (u u' : ℕ) (F : Multiset Tm) (n : ℕ) :
      CStep defs (thread (redefTo u') ::ₘ ver u ::ₘ F, n) (thread done ::ₘ ver u' ::ₘ F, n)

/-! ## The frame-stack machine -/

/-- **The frame-stack machine.** `ev e K` evaluates `e` under the frames `K`; `ret v K` returns the
data `v` to them; `ap w K` calls `w`. The first six rules are administrative; `apply` answers a call
by an equation of the installed version, renamed into the firing's scope. -/
inductive KStep (defs : Defs) : Multiset SRow × ℕ → Multiset SRow × ℕ → Prop
  | val (t : Tm) (K : List Frame) (F : Multiset SRow) (n : ℕ) :
      KStep defs (.ev (.val t) K ::ₘ F, n) (.ret t K ::ₘ F, n + 1)
  | pair (a b : Ex) (K : List Frame) (F : Multiset SRow) (n : ℕ) :
      KStep defs (.ev (.pair a b) K ::ₘ F, n) (.ev a (.left b :: K) ::ₘ F, n + 1)
  | call (a : Ex) (K : List Frame) (F : Multiset SRow) (n : ℕ) :
      KStep defs (.ev (.call a) K ::ₘ F, n) (.ev a (.arg :: K) ::ₘ F, n + 1)
  | left (v : Tm) (b : Ex) (K : List Frame) (F : Multiset SRow) (n : ℕ) :
      KStep defs (.ret v (.left b :: K) ::ₘ F, n) (.ev b (.right v :: K) ::ₘ F, n + 1)
  | right (v w : Tm) (K : List Frame) (F : Multiset SRow) (n : ℕ) :
      KStep defs (.ret w (.right v :: K) ::ₘ F, n) (.ret (node v w) K ::ₘ F, n + 1)
  | arg (w : Tm) (K : List Frame) (F : Multiset SRow) (n : ℕ) :
      KStep defs (.ret w (.arg :: K) ::ₘ F, n) (.ap w K ::ₘ F, n + 1)
  | apply (u : ℕ) (j : Fin (defs u).length) (w : Tm) (K : List Frame) (F : Multiset SRow) (n : ℕ)
      (θ : Subst rows) (mgu : IsMGU [(((defs u).get j).lhs.at n, w)] θ) :
      KStep defs (.ap w K ::ₘ .version u ::ₘ F, n)
        (.ev ((((defs u).get j).rhs.at n).subst θ) (K.map (Frame.subst θ)) ::ₘ
          .citation u ::ₘ .version u ::ₘ F.map (SRow.subst θ), n + 1)
  | redefine (u u' : ℕ) (F : Multiset SRow) (n : ℕ) :
      KStep defs (.redef u' ::ₘ .version u ::ₘ F, n) (.finished ::ₘ .version u' ::ₘ F, n + 1)

/-! ## The machine implements the strategy -/

/-- **Unloading a source row**: a thread's focus plugged back into its frames. -/
def SRow.unload : SRow → Tm
  | .ev e K => thread (encE (plug K e))
  | .ret v K => thread (encE (plug K (.val v)))
  | .ap w K => thread (encE (plug K (.call (.val w))))
  | .version u => ver u
  | .citation u => cite u
  | .redef u => thread (redefTo u)
  | .finished => thread done
  | .data k t => tagged k t

theorem SRow.unload_subst (θ : Subst rows) : ∀ s : SRow, (s.subst θ).unload = θ.applyTerm s.unload
  | .ev e K => by
      simp only [SRow.subst, SRow.unload, thread, apply_tagged, ← encE_subst, plug_subst]
  | .ret v K => by
      simp only [SRow.subst, SRow.unload, thread, apply_tagged, ← encE_subst, plug_subst, Ex.subst]
  | .ap w K => by
      simp only [SRow.subst, SRow.unload, thread, apply_tagged, ← encE_subst, plug_subst, Ex.subst]
  | .version u => by simp only [SRow.subst, SRow.unload, ver, apply_tagged, Subst.applyTerm_const]
  | .citation u => by simp only [SRow.subst, SRow.unload, cite, apply_tagged, Subst.applyTerm_const]
  | .redef u => by
      simp only [SRow.subst, SRow.unload, thread, redefTo, apply_tagged, Subst.applyTerm_const]
  | .finished => by simp only [SRow.subst, SRow.unload, thread, done, apply_tagged, Subst.applyTerm_const]
  | .data k t => by simp only [SRow.subst, SRow.unload, apply_tagged]

/-- The reference configuration a machine configuration denotes. -/
def unloadAll (W : Multiset SRow) : Multiset Tm := W.map SRow.unload

theorem unloadAll_cons (s : SRow) (F : Multiset SRow) :
    unloadAll (s ::ₘ F) = s.unload ::ₘ unloadAll F := Multiset.map_cons _ _ _

/-- **Each machine step is no step or one reference step of its unloading**, from any reference
scope `m` up to the machine's: administrative steps unload to the same configuration, building a
cell is a reference build, and answering a call is the reference answer at the machine's scope. -/
theorem kstep_unload {defs : Defs} {s s' : Multiset SRow × ℕ} (step : KStep defs s s') {m : ℕ}
    (le : m ≤ s.2) :
    ∃ m', m' ≤ s'.2 ∧ Relation.ReflGen (CStep defs) (unloadAll s.1, m) (unloadAll s'.1, m') := by
  cases step with
  | val t K F n => exact ⟨m, Nat.le_succ_of_le le, by rw [unloadAll_cons, unloadAll_cons]; exact .refl⟩
  | pair a b K F n => exact ⟨m, Nat.le_succ_of_le le, by rw [unloadAll_cons, unloadAll_cons]; exact .refl⟩
  | call a K F n => exact ⟨m, Nat.le_succ_of_le le, by rw [unloadAll_cons, unloadAll_cons]; exact .refl⟩
  | left v b K F n => exact ⟨m, Nat.le_succ_of_le le, by rw [unloadAll_cons, unloadAll_cons]; exact .refl⟩
  | arg w K F n => exact ⟨m, Nat.le_succ_of_le le, by rw [unloadAll_cons, unloadAll_cons]; exact .refl⟩
  | right v w K F n =>
      refine ⟨m, Nat.le_succ_of_le le, .single ?_⟩
      rw [unloadAll_cons, unloadAll_cons]
      show CStep defs (thread (encE (plug K (.pair (.val v) (.val w)))) ::ₘ unloadAll F, m)
        (thread (encE (plug K (.val (node v w)))) ::ₘ unloadAll F, m)
      rw [plug_ctxOf, plug_ctxOf]
      exact .build (ctxOf K) v w (unloadAll F) m
  | apply u j w K F n θ mgu =>
      refine ⟨n + 1, le_rfl, .single ?_⟩
      simp only [unloadAll_cons]
      show CStep defs (thread (encE (plug K (.call (.val w)))) ::ₘ ver u ::ₘ unloadAll F, m)
        (thread (encE (plug (K.map (Frame.subst θ)) ((((defs u).get j).rhs.at n).subst θ))) ::ₘ
          cite u ::ₘ ver u ::ₘ unloadAll (F.map (SRow.subst θ)), n + 1)
      have rows : unloadAll (F.map (SRow.subst θ)) = (unloadAll F).map θ.applyTerm := by
        rw [unloadAll, unloadAll, Multiset.map_map, Multiset.map_map]
        exact Multiset.map_congr rfl fun s _ => SRow.unload_subst θ s
      rw [rows, ← plug_subst, plug_ctxOf, plug_ctxOf]
      exact .apply u j (ctxOf K) w (unloadAll F) m n le θ mgu
  | redefine u u' F n =>
      refine ⟨m, Nat.le_succ_of_le le, .single ?_⟩
      simp only [unloadAll_cons]
      exact .redefine u u' (unloadAll F) m

/-- **Every machine run is a reference run of its unloading**, with reference scopes below the
machine's. -/
theorem kruns_unload {defs : Defs} {s s' : Multiset SRow × ℕ}
    (run : Relation.ReflTransGen (KStep defs) s s') {m : ℕ} (le : m ≤ s.2) :
    ∃ m', m' ≤ s'.2 ∧ Relation.ReflTransGen (CStep defs) (unloadAll s.1, m) (unloadAll s'.1, m') := by
  induction run with
  | refl => exact ⟨m, le, .refl⟩
  | tail _ step ih =>
      obtain ⟨m₁, le₁, path⟩ := ih
      obtain ⟨m₂, le₂, last⟩ := kstep_unload step le₁
      exact ⟨m₂, le₂, path.trans last.to_reflTransGen⟩

/-- **A halted machine thread is a reference value**: from a thread of `e` alone, a machine run
returning `v` to the empty stack is a reference run from `thread e` to `thread (val v)`. -/
theorem halted_is_value {defs : Defs} {e : Ex} {v : Tm} {F F' : Multiset SRow} {n n' : ℕ}
    (run : Relation.ReflTransGen (KStep defs) (.ev e [] ::ₘ F, n) (.ret v [] ::ₘ F', n')) :
    ∃ m', m' ≤ n' ∧ Relation.ReflTransGen (CStep defs)
      (thread (encE e) ::ₘ unloadAll F, n) (thread (encE (.val v)) ::ₘ unloadAll F', m') := by
  obtain ⟨m', le, path⟩ := kruns_unload run (le_refl n)
  rw [unloadAll_cons, unloadAll_cons] at path
  exact ⟨m', le, path⟩

#print axioms plug_subst
#print axioms ECtx.fill_comp
#print axioms plug_ctxOf
#print axioms EPat.enc_at
#print axioms encE_subst
#print axioms encK_subst
#print axioms SRow.enc_subst
#print axioms SRow.unload_subst
#print axioms kstep_unload
#print axioms kruns_unload
#print axioms halted_is_value

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
