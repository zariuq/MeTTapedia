import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Independence
import Mathlib.CategoryTheory.Category.Basic

/-!
# The category of dependent traces

Objects are state classes. An arrow from `x` to `y` is a run from a state of class `x` that ends in
class `y` (`Transport.Arrow`); arrows are identified by similarity and trace equivalence
(`Arrow.Rel`), giving traces (`Transport.Trace`). Composition concatenates after transporting the
second run along an isomorphism of the first run's end with the second run's start
(`Arrow.comp`). It is well defined on traces in both arguments (`Arrow.comp_rel_left`,
`Arrow.comp_rel_right`), and traces form a category (`traceCategory`): concatenation is associative
and the empty runs are identities up to similarity (`Similar.append_assoc`, `Similar.append_nil`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF uI

namespace Transport

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport P)

/-- The isomorphism given by an equality of states. -/
def ofEq {s t : State} (same : s = t) : T.Iso s t := same ▸ T.refl s

variable {T}

namespace Similar

/-- Appending the empty run at the end changes nothing, up to similarity. -/
theorem append_nil : ∀ {s : State} (r : P.Run s), T.Similar (r.append (.nil r.last)) r
  | _, .nil _ => Similar.refl _
  | _, .cons _ _ rest => cons_self (append_nil rest)

/-- **Concatenation is associative up to similarity.** The last run is carried along the equality of
the ends. -/
theorem append_assoc : ∀ {s : State} (a : P.Run s) (b : P.Run a.last) (c : P.Run (a.append b).last),
    T.Similar ((a.append b).append c)
      (a.append (b.append (T.moveRun (T.ofEq (Step.Run.last_append a b)) c)))
  | _, .nil _, b, c => Similar.append (Similar.refl b) (Similar.moveRun _ c)
  | _, .cons _ _ rest, b, c => cons_self (append_assoc rest b c)

end Similar

variable (T)

/-- **An arrow between state classes**: a run from a state of the first class to a state of the
second. -/
structure Arrow (x y : T.StateClass) where
  start : State
  run : P.Run start
  start_mem : StateClass.mk T start = x
  last_mem : StateClass.mk T run.last = y

namespace Arrow

variable {T}

/-- Arrows related by a transport and a trace equivalence. -/
def Rel {x y : T.StateClass} (p q : T.Arrow x y) : Prop :=
  ∃ r : P.Run q.start, T.Similar p.run r ∧ T.TraceEquiv q.start r q.run

/-- The isomorphism linking the end of one arrow with the start of the next. -/
noncomputable def link {x y z : T.StateClass} (p : T.Arrow x y) (q : T.Arrow y z) :
    T.Iso q.start p.run.last :=
  Classical.choice ((StateClass.mk_eq_mk_iff T).mp (q.start_mem.trans p.last_mem.symm))

/-- **Composition**: the second run, transported to the end of the first, after the first. -/
noncomputable def comp {x y z : T.StateClass} (p : T.Arrow x y) (q : T.Arrow y z) : T.Arrow x z where
  start := p.start
  run := p.run.append (T.moveRun (p.link q) q.run)
  start_mem := p.start_mem
  last_mem := by
    rw [Step.Run.last_append]
    have ends := Similar.same_last (Similar.moveRun (p.link q) q.run)
    exact ((StateClass.mk_eq_mk_iff T).mpr ends).symm.trans q.last_mem

/-- The empty run at the representative of a class. -/
noncomputable def id (x : T.StateClass) : T.Arrow x x where
  start := Quotient.out x
  run := .nil (Quotient.out x)
  start_mem := Quotient.out_eq x
  last_mem := Quotient.out_eq x

theorem rel_of_similar {x y : T.StateClass} {p q : T.Arrow x y} (similar : T.Similar p.run q.run) :
    Rel p q :=
  ⟨q.run, similar, .refl _⟩

/-- Composition respects the relation in its second argument. -/
theorem comp_rel_right {x y z : T.StateClass} (p : T.Arrow x y) {q q' : T.Arrow y z}
    (related : Rel q q') : Rel (comp p q) (comp p q') := by
  obtain ⟨r, similar, equivalent⟩ := related
  refine ⟨p.run.append (T.moveRun (p.link q') r), ?_, ?_⟩
  · exact Similar.append (Similar.refl p.run)
      (Similar.trans (Similar.symm (Similar.moveRun (p.link q) q.run))
        (Similar.trans similar (Similar.moveRun (p.link q') r)))
  · exact TraceEquiv.append_left p.run (TraceEquiv.moveRun (p.link q') equivalent)

/-- Composition respects the relation in its first argument. -/
theorem comp_rel_left {x y z : T.StateClass} {p p' : T.Arrow x y} (q : T.Arrow y z)
    (related : Rel p p') : Rel (comp p q) (comp p' q) := by
  obtain ⟨r, similar, equivalent⟩ := related
  have toR : T.Iso q.start r.last := T.trans (p.link q) (Classical.choice (Similar.same_last similar))
  refine ⟨r.append (T.moveRun toR q.run), ?_, ?_⟩
  · exact Similar.append similar
      (Similar.trans (Similar.symm (Similar.moveRun (p.link q) q.run)) (Similar.moveRun toR q.run))
  · exact TraceEquiv.append_right equivalent
      (Similar.trans (Similar.symm (Similar.moveRun toR q.run)) (Similar.moveRun (p'.link q) q.run))

end Arrow

/-- **A dependent trace** between state classes. -/
def Trace (x y : T.StateClass) : Type (max uS uF) := Quot (Arrow.Rel (T := T) (x := x) (y := y))

namespace Trace

variable {T}

/-- Composition of traces. -/
noncomputable def comp {x y z : T.StateClass} : T.Trace x y → T.Trace y z → T.Trace x z :=
  Quot.lift₂ (fun p q => Quot.mk _ (Arrow.comp p q))
    (fun p _ _ related => Quot.sound (Arrow.comp_rel_right p related))
    (fun _ _ q related => Quot.sound (Arrow.comp_rel_left q related))

end Trace

/-- **The category of dependent traces.** -/
@[reducible] noncomputable def traceCategory : CategoryTheory.Category T.StateClass where
  Hom x y := T.Trace x y
  id x := Quot.mk _ (Arrow.id x)
  comp f g := Trace.comp f g
  id_comp f := by
    induction f using Quot.inductionOn with
    | h p =>
        apply Quot.sound
        refine ⟨p.run, ?_, .refl _⟩
        exact Similar.symm (Similar.moveRun _ p.run)
  comp_id f := by
    induction f using Quot.inductionOn with
    | h p =>
        apply Quot.sound
        exact Arrow.rel_of_similar (Similar.append_nil p.run)
  assoc f g h := by
    induction f using Quot.inductionOn with
    | h p =>
      induction g using Quot.inductionOn with
      | h q =>
        induction h using Quot.inductionOn with
        | h w =>
            apply Quot.sound
            apply Arrow.rel_of_similar
            show T.Similar ((p.run.append (T.moveRun (p.link q) q.run)).append
                (T.moveRun ((Arrow.comp p q).link w) w.run))
              (p.run.append (T.moveRun (p.link (Arrow.comp q w))
                (q.run.append (T.moveRun (q.link w) w.run))))
            refine Similar.trans (Similar.append_assoc _ _ _) (Similar.append (Similar.refl p.run) ?_)
            refine Similar.trans ?_ (Similar.moveRun _ _)
            exact Similar.append (Similar.symm (Similar.moveRun _ q.run))
              (Similar.trans (Similar.symm (Similar.moveRun _ _))
                (Similar.trans (Similar.symm (Similar.moveRun _ w.run)) (Similar.moveRun _ w.run)))

end Transport

#print axioms Transport.Similar.append_nil
#print axioms Transport.Similar.append_assoc
#print axioms Transport.Arrow.comp_rel_left
#print axioms Transport.Arrow.comp_rel_right
#print axioms Transport.traceCategory

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
