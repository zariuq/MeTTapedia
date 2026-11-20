import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Unions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Divergence.Preserved

/-!
# Unions: the separation from the program text, and divergence

`Composition.SeparateFrom` is a hypothesis about every configuration a run reaches. For the fragment
with `let` (and so for the first fragment) it follows from a condition on the text.

* `calls c`: the call data written in a computation, under `choice` and in both parts of a `let`;
  `writtenCalls P q`: the call data written in the query and in the right sides of `P` (`written_g`);
  `Written P q t`: `t` is an instance of a written call (`(g a)` is not one of `(g)`: `ga_not_written`);
  instances of written calls are closed under instantiation (`written_inst`).
* `CallsWritten P q b`: an alternative of the fragment with `let` all of whose calls, in its focus and
  in the bodies of its pending frames, are instances of written calls. `calls_written`: every
  alternative a run of `P` reaches from the query is such an alternative; the alternative at the call
  `(g a)` is not one for the program `(= (g) d)` and the query `(g)` (`ga_not_callsWritten`).
* `separate_of_text`: **if no instance of a written call unifies with a renamed left side of `Q`, then
  along the runs of `P` from the query no equation of `Q` matches a call** (`SeparateFrom`), for
  programs and queries of the fragment with `let`; `separate_of_text_plain`: the same for the first
  fragment, as a corollary.
* `separate_instance_of_text`: the instance `Controls.separate_instance` (`(= (g) d)` beside the left
  side `(g a)`, on the query `(g)`) by this condition: the one written call is `(g)`, and no instance of
  it unifies with `(g a)`; the same on the query `(let $x (g) $x)` of the fragment with `let`
  (`separate_let_instance_of_text`). The control: the program with no equation beside `(= (g) d)`, where
  the separation fails (`Controls.not_separate`), fails the text condition (`text_fails_at_control`).

The condition is sufficient, not necessary: a written call that no run reaches does not matter to the
runs.

**Divergence.** `union_diverges_iff`: under `SeparateFrom`, the source of `P` diverges from the query
exactly when the source of `P.union Q` does. With `Composition.answers_withDead` (the bags of answers
are equal, configuration by configuration) the correspondence `Composition.unionCorrespondence` keeps
the bag and divergence; what it does not keep is the number of alternatives, dead ones included.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.FromText

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}

/-! ## Written calls -/

section Calls

variable {Ty : Type}

/-- The call data written in a computation: its calls, under `choice` and in both parts of a `let`. -/
def calls : Comp κ Γ star Ty → List (Data κ Γ star)
  | .apply t => [t]
  | .choice c d => calls c ++ calls d
  | .let_ _ _ c k => calls c ++ calls k
  | _ => []

theorem calls_mapData (g : Data κ Γ star → Data κ Γ star) :
    ∀ c : Comp κ Γ star Ty, ArrowComp c → calls (c.mapData g) = (calls c).map g
  | .ret _, _ => rfl
  | .apply _, _ => rfl
  | .let_ _ _ c k, ⟨pc, pk⟩ => by
      show calls (c.mapData g) ++ calls (k.mapData g) = (calls c ++ calls k).map g
      rw [calls_mapData g c pc, calls_mapData g k pk, List.map_append]
  | .choice c d, ⟨pc, pd⟩ => by
      show calls (c.mapData g) ++ calls (d.mapData g) = (calls c ++ calls d).map g
      rw [calls_mapData g c pc, calls_mapData g d pd, List.map_append]
  | .fail, _ => rfl
  | .run _, h => h.elim
  | .query _ _ _, h => h.elim
  | .add _ _ _, h => h.elim
  | .remove _ _ _, h => h.elim
  | .new _ _ _, h => h.elim
  | .check _ _, h => h.elim
  | .delay _ _ _ _, h => h.elim
  | .force _, h => h.elim

/-- The call data written in the body of a pending frame. -/
def frameCalls : SourceLanguage.Frame κ Γ star Ty → List (Data κ Γ star)
  | .bindTo _ _ k => calls k
  | _ => []

/-- **The call data written in the query and in the right sides of the program.** -/
def writtenCalls (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) : List (Data κ Γ star) :=
  calls q ++ P.equations.flatMap fun e => calls e.rhs

/-- A datum that is an instance of a written call. -/
def Written (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty) (t : Data κ Γ star) : Prop :=
  ∃ t₀ ∈ writtenCalls P q, ∃ ρ : Assignment (fam κ) (fam κ), t = instantiate ρ t₀

/-- Instances of written calls are closed under instantiation. -/
theorem written_inst {P : SourceLanguage.Program κ Γ star Ty} {q : Comp κ Γ star Ty} {t : Data κ Γ star}
    (written : Written P q t) (σ : Assignment (fam κ) (fam κ)) : Written P q (instantiate σ t) := by
  obtain ⟨t₀, inText, ρ, rfl⟩ := written
  exact ⟨t₀, inText, fun x => instantiate σ (ρ x), instantiate_comp ρ σ t₀⟩

/-- An alternative of the fragment with `let` that evaluates has a computation of the fragment. -/
theorem arrow_eval {K : List (Constraint κ Γ star)} {c : Comp κ Γ star Ty}
    {fs : List (SourceLanguage.Frame κ Γ star Ty)} {ps : List (Data κ Γ star × Comp κ Γ star Ty)}
    (arrow : ArrowBranch (⟨K, .eval c, fs, ps⟩ : Branch κ Γ star Ty)) : ArrowComp c := by
  obtain ⟨_, ⟨c', focus, arrowC⟩ | ⟨t, focus⟩⟩ := arrow
  · cases focus
    exact arrowC
  · cases focus

end Calls

variable {D : Discipline S Γ star} {P Q : SourceLanguage.Program κ Γ star D.Ty} {supply : ℕ → Term S Γ star}
  {spaces : Term S Γ star → Multiset (Row κ Γ star)} {q : Comp κ Γ star D.Ty}

/-- **An alternative of the fragment with `let` all of whose calls are instances of written calls**, in
its focus and in the bodies of its pending frames. -/
def CallsWritten (P : SourceLanguage.Program κ Γ star D.Ty) (q : Comp κ Γ star D.Ty)
    (b : Branch κ Γ star D.Ty) : Prop :=
  ArrowBranch b ∧ (∀ c, b.focus = .eval c → ∀ t ∈ calls c, Written P q t) ∧
    ∀ fr ∈ b.frames, ∀ t ∈ frameCalls fr, Written P q t

theorem callsWritten_move (arrowP : ArrowProgram P) {w w' : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {bs : Multiset (Branch κ Γ star D.Ty)} (move : Move D P supply w b w' bs) (inv : CallsWritten P q b) :
    ∀ b' ∈ bs, CallsWritten P q b' := by
  obtain ⟨arrow, written, framesWritten⟩ := inv
  cases move
  case ret K t fs ps =>
    intro b' made
    rw [Multiset.mem_singleton.mp made]
    refine ⟨⟨arrow.1, .inr ⟨t, rfl⟩⟩, ?_, framesWritten⟩
    intro c focus
    cases focus
  case apply K t fs ps matched =>
    intro b' made
    obtain ⟨e, eMember, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp made)
    refine ⟨⟨arrow.1, .inl ⟨_, rfl, arrowComp_mapData _ _ (arrowP e eMember)⟩⟩, ?_, framesWritten⟩
    intro c focus t' inCalls
    cases focus
    have inCalls' : t' ∈ calls (e.rhs.mapData (instantiate (copyAt κ w.scope))) := inCalls
    rw [calls_mapData _ _ (arrowP e eMember)] at inCalls'
    obtain ⟨t₀, inRhs, rfl⟩ := List.mem_map.mp inCalls'
    exact ⟨t₀, List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, eMember, inRhs⟩), copyAt κ w.scope, rfl⟩
  case unmatched K t fs ps none =>
    intro b' made
    rw [Multiset.mem_singleton.mp made]
    refine ⟨⟨arrow.1, .inr ⟨t, rfl⟩⟩, ?_, framesWritten⟩
    intro c focus
    cases focus
  case letStart K s p c k fs ps =>
    intro b' made
    rw [Multiset.mem_singleton.mp made]
    have arrowCK : ArrowComp c ∧ ArrowComp k := arrow_eval arrow
    refine ⟨⟨⟨arrowCK.2, arrow.1⟩, .inl ⟨c, rfl, arrowCK.1⟩⟩, ?_, ?_⟩
    · intro c' focus t' inCalls
      cases focus
      exact written _ rfl t' (List.mem_append_left _ inCalls)
    · intro fr member t' inCalls
      rcases List.mem_cons.mp member with rfl | later
      · exact written _ rfl t' (List.mem_append_right _ inCalls)
      · exact framesWritten fr later t' inCalls
  case letBind K v s p k fs ps =>
    intro b' made
    rw [Multiset.mem_singleton.mp made]
    have arrowK : ArrowComp k := arrow.1.1
    refine ⟨⟨arrow.1.2, .inl ⟨_, rfl, arrowComp_mapData _ _ arrowK⟩⟩, ?_, ?_⟩
    · intro c focus t' inCalls
      cases focus
      have inCalls' : t' ∈ calls (k.mapData (instantiate (openAt κ s w.scope))) := inCalls
      rw [calls_mapData _ _ arrowK] at inCalls'
      obtain ⟨t₀, inK, rfl⟩ := List.mem_map.mp inCalls'
      exact written_inst (framesWritten _ List.mem_cons_self t₀ inK) _
    · intro fr member t' inCalls
      exact framesWritten fr (List.mem_cons_of_mem _ member) t' inCalls
  case choice K c d fs ps =>
    intro b' made
    have arrowCD : ArrowComp c ∧ ArrowComp d := arrow_eval arrow
    rcases Multiset.mem_cons.mp made with rfl | other
    · refine ⟨⟨arrow.1, .inl ⟨c, rfl, arrowCD.1⟩⟩, ?_, framesWritten⟩
      intro c' focus t' inCalls
      cases focus
      exact written _ rfl t' (List.mem_append_left _ inCalls)
    · rw [Multiset.mem_singleton.mp other]
      refine ⟨⟨arrow.1, .inl ⟨d, rfl, arrowCD.2⟩⟩, ?_, framesWritten⟩
      intro c' focus t' inCalls
      cases focus
      exact written _ rfl t' (List.mem_append_right _ inCalls)
  case fail K fs ps =>
    intro b' made
    exact absurd made (Multiset.notMem_zero b')
  all_goals first
    | exact (arrow_eval arrow).elim
    | exact arrow.1.elim

/-- **Every call of an alternative a run reaches is an instance of a written call** (the fragment with
`let`): in its focus and in the bodies of its pending frames. -/
theorem calls_written (arrowP : ArrowProgram P) (arrowQ : ArrowComp q) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) : ∀ b ∈ C.branches, CallsWritten P q b := by
  induction runs with
  | refl =>
      intro b member
      rw [Multiset.mem_singleton.mp member]
      refine ⟨⟨trivial, .inl ⟨q, rfl, arrowQ⟩⟩, ?_, fun fr member => by cases member⟩
      intro c focus t inCalls
      cases focus
      exact ⟨t, List.mem_append_left _ inCalls, generator (fam κ), (instantiate_identity t).symm⟩
  | tail _ step ih =>
      obtain ⟨w, w', b, rest, bs, _, move⟩ := step
      intro b' member
      rcases Multiset.mem_add.mp member with made | kept
      · exact callsWritten_move arrowP move (ih b (Multiset.mem_cons_self _ _)) b' made
      · exact ih b' (Multiset.mem_cons_of_mem kept)

/-- **The separation from the text** (the fragment with `let`): if no instance of a call written in the
query or in a right side of `P` unifies with a renamed left side of `Q`, then along the runs of `P` from
the query no equation of `Q` matches a call. -/
theorem separate_of_text (arrowP : ArrowProgram P) (arrowQ : ArrowComp q)
    (apartText : ∀ t₀ ∈ writtenCalls P q, ∀ e ∈ Q.equations, ∀ (ρ : Assignment (fam κ) (fam κ)) (n : ℕ)
      (K : List (Constraint κ Γ star)),
        ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, instantiate ρ t₀)])) :
    SeparateFrom D P Q supply spaces q := by
  intro C runs b member _ t focus e eMember solvable
  obtain ⟨_, written, _⟩ := calls_written arrowP arrowQ runs b member
  obtain ⟨t₀, inText, ρ, rfl⟩ := written (.apply t) focus t (List.mem_singleton_self t)
  exact apartText t₀ inText e eMember ρ C.world.scope b.store solvable

/-- **The separation from the text, first fragment**: the same, as a corollary. -/
theorem separate_of_text_plain (plainP : PlainProgram P) (plainQ : PlainComp q)
    (apartText : ∀ t₀ ∈ writtenCalls P q, ∀ e ∈ Q.equations, ∀ (ρ : Assignment (fam κ) (fam κ)) (n : ℕ)
      (K : List (Constraint κ Γ star)),
        ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, instantiate ρ t₀)])) :
    SeparateFrom D P Q supply spaces q :=
  separate_of_text (fun e member => plainComp_arrow _ (plainP e member)) (plainComp_arrow q plainQ) apartText

/-! ## Divergence of unions -/

/-- The query's configuration is related to itself. -/
theorem start_related (sep : SeparateFrom D P Q supply spaces q) :
    (unionCorrespondence sep).related (Config.initial spaces q) (Config.initial spaces q) :=
  ⟨.refl, rfl, 0, (add_zero _).symm, fun d member => absurd member (Multiset.notMem_zero d)⟩

/-- **Under the separation, `P` diverges from the query exactly when the union does.** -/
theorem union_diverges_iff (sep : SeparateFrom D P Q supply spaces q) :
    (∃ run : ℕ → Config κ Γ star D.Ty, run 0 = Config.initial spaces q ∧
      ∀ k, SourceLanguage.Step D P supply (run k) (run (k + 1))) ↔
      ∃ run : ℕ → Config κ Γ star D.Ty, run 0 = Config.initial spaces q ∧
        ∀ k, SourceLanguage.Step D (P.union Q) supply (run k) (run (k + 1)) := by
  constructor
  · rintro ⟨run, first, steps⟩
    exact (unionCorrespondence sep).infinite_execution_preserved
      (fun {C C₁ C'} related step => by
        obtain ⟨runs, rel⟩ := related
        obtain ⟨C₁', step', rel'⟩ := step_union step rel (sep _ runs)
        exact ⟨C₁', .cons ⟨step'⟩ (.refl _), Nat.succ_pos _, runs.tail step, rel'⟩)
      (start_related sep) run first steps
  · rintro ⟨run, first, steps⟩
    exact Divergence.infinite_reflected (unionCorrespondence sep).toOperationalReadback
      (fun {C C' C₁'} related step => by
        obtain ⟨runs, rel⟩ := related
        obtain ⟨C₁, step', rel'⟩ := step_of_union step rel (sep _ runs)
        exact ⟨C₁, step', runs.tail step', rel'⟩)
      (start_related sep) run first steps

/-! ## The instance and the control, from the text -/

section Instance

open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.Controls

/-- The one call written in `(= (g) d)` and the query `(g)` is `(g)`. -/
theorem written_g : writtenCalls Controls.Q Controls.q = [gT] := rfl

/-- **A negative example**: `(g a)` is not an instance of the written call `(g)`. -/
theorem ga_not_written : ¬ Written Controls.Q Controls.q gaT := by
  rintro ⟨t₀, inText, ρ, same⟩
  rw [written_g, List.mem_singleton] at inText
  subst inText
  change (Term.op (Sum.inl (MOp.tup 2)) _ : MData) = Term.op (Sum.inl (MOp.tup 1)) _ at same
  injection same with _ _ hop _
  simp at hop

/-- **A negative example of `CallsWritten`**: the alternative at the call `(g a)` has a call that is not
an instance of the written call `(g)`. -/
theorem ga_not_callsWritten :
    ¬ CallsWritten (D := Controls.D) Controls.Q Controls.q
      (⟨[], .eval (.apply gaT), [], []⟩ : Branch mkeys [] () MTy) :=
  fun inv => ga_not_written (inv.2.1 _ rfl gaT (List.mem_singleton_self _))

/-- **The instance of the separation, by the condition on the text.** -/
theorem separate_instance_of_text :
    SeparateFrom Controls.D Controls.Q (rowProgram gaT) Controls.supply Controls.sp Controls.q := by
  refine separate_of_text_plain (D := Controls.D) ?_ trivial ?_
  · intro e member
    rw [List.mem_singleton.mp member]
    trivial
  · intro t₀ inText e eMember ρ n K
    rw [written_g, List.mem_singleton] at inText
    subst inText
    rw [List.mem_singleton.mp eMember]
    rintro ⟨X, target, σ, solved⟩
    have same := solved _ (List.mem_append_right _ (List.mem_singleton_self _))
    change (Term.op (Sum.inl (MOp.tup 2)) _ : Term (signature MSig target) [] ()) =
      Term.op (Sum.inl (MOp.tup 1)) _ at same
    injection same with _ _ hop _
    simp at hop

/-- A query with a `let`: `(let $x (g) $x)`. -/
def qLet : Comp mkeys [] () MTy := .let_ [312] xName (.apply gT) (.ret xName)

/-- Its one written call, with the program `(= (g) d)`, is `(g)`. -/
theorem written_let : writtenCalls Controls.Q qLet = [gT] := rfl

/-- **An instance of the separation in the fragment with `let`**: `(= (g) d)` beside the left side
`(g a)`, on the query `(let $x (g) $x)`. -/
theorem separate_let_instance_of_text :
    SeparateFrom Controls.D Controls.Q (rowProgram gaT) Controls.supply Controls.sp qLet := by
  refine separate_of_text (D := Controls.D) ?_ ⟨trivial, trivial⟩ ?_
  · intro e member
    rw [List.mem_singleton.mp member]
    trivial
  · intro t₀ inText e eMember ρ n K
    rw [written_let, List.mem_singleton] at inText
    subst inText
    rw [List.mem_singleton.mp eMember]
    rintro ⟨X, target, σ, solved⟩
    have same := solved _ (List.mem_append_right _ (List.mem_singleton_self _))
    change (Term.op (Sum.inl (MOp.tup 2)) _ : Term (signature MSig target) [] ()) =
      Term.op (Sum.inl (MOp.tup 1)) _ at same
    injection same with _ _ hop _
    simp at hop

/-- **The control fails the text condition**: the program with no equation, beside `(= (g) d)`, on the
query `(g)`: the written call `(g)` unifies with the left side `(g)`, and there the separation fails
(`Controls.not_separate`). -/
theorem text_fails_at_control :
    ¬ ∀ t₀ ∈ writtenCalls Controls.P0 Controls.q, ∀ e ∈ Controls.Q.equations,
      ∀ (ρ : Assignment (fam mkeys) (fam mkeys)) (n : ℕ) (K : List (Constraint mkeys [] ())),
        ¬ Solvable (K ++ [(instantiate (copyAt mkeys n) e.lhs, instantiate ρ t₀)]) :=
  fun apart => apart gT (List.mem_singleton_self _) eg (List.mem_singleton_self _) (copyAt mkeys 0) 0 []
    live_gg

end Instance

#print axioms written_inst
#print axioms callsWritten_move
#print axioms calls_written
#print axioms separate_of_text
#print axioms separate_of_text_plain
#print axioms union_diverges_iff
#print axioms separate_instance_of_text
#print axioms separate_let_instance_of_text
#print axioms text_fails_at_control
#print axioms ga_not_written
#print axioms ga_not_callsWritten

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Composition.FromText
