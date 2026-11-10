import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TraceCategory
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Observer

/-!
# Escape-relative transport

The interface's isomorphisms of states accept any isomorphism of frames with the same knowledge and
present occurrences, so a trace category built on them forgets what clients know. This module
builds, for every step and every transport, a transport whose isomorphisms respect what has escaped,
and in which what has escaped grows along runs.

* **What has escaped** (`Escaped`): a state, the public terms clients know at its frame, in the order
  they were published, and the record of the environment (`Observation.Record`): the relations among
  occurrence identities it recorded, such as held references and sighted sets.
* **What clients read, and what a firing makes escape** (`Transport.Escape`): the row of each
  occurrence where the step has one, which every isomorphism carries to the row of the renamed
  occurrence up to the knowledge (`Escape.row_iso`, the row clause of `RowIsoModulo`); the relations a
  firing makes the environment record, which a moved firing records renamed (`Escape.records_move`);
  and the public terms it publishes at its result, which the result isomorphisms carry.
* **The escaping step** (`Transport.Escape.step`): the same firings, admissions and results; a result
  carries the public terms along the firing's morphism and appends the published ones, and its record
  appends the firing's relations. The record only grows along runs (`Escape.record_last`,
  `Escape.records_last`), and the public terms of the start reach the end carried along the run
  (`Escape.names_last`).
* **Escape-relative isomorphisms** (`Transport.EscapeIso`): an isomorphism of the underlying transport
  whose frame isomorphism carries every public term to its counterpart at every solution of the
  knowledge (`Frames.Carried`, the clause `RowIsoModulo` uses for rows and public names), and whose
  occurrence renaming carries the record of the first state to the record of the second. An
  isomorphism of an escaped state to itself therefore renames by an **automorphism of its record**
  (`Observation.Record.automorphisms`): the environment sees the structure of what it recorded, never
  raw identities. For the result isomorphisms to respect it, the underlying transport must be
  **natural** (`Transport.Natural`): its frame isomorphisms and its renamings compose as groupoids, and
  its result isomorphisms commute with the firings' morphisms and keep the renaming.
* **The escape-relative transport** (`Transport.escaping`): the generic trace results instantiate over
  it. Similarity, trace equivalence and the trace category are those of `Transport`
  (`Escape.traceCategory`). Trace-equivalent runs end with records related by the renaming of an
  isomorphism of their ends, which is an automorphism of the start's record (`Escape.traceEquiv_record`,
  `Escape.traceEquiv_past`), and with public terms matched by an isomorphism (`Escape.traceEquiv_names`).
  Forgetting escape maps similar runs to similar runs, swaps to swaps and traces to traces
  (`Escape.Similar.forget`, `Escape.TraceEquiv.forget`): the escape-relative trace equivalence refines
  the underlying one. Escaping keeps naturality (`Natural.escaping`), so escape layers stack: an inner
  layer records what observers inside the system know, an outer one what the environment knows.

## The pointwise case

When the environment's record holds only references, an isomorphism between states with that one
record renames by a renaming that fixes every reference, and every such renaming gives one
(`EscapeIso.nonempty_iff_of_references`; for a client context of the client layer,
`EscapeIso.fixes_of_client`). For every record, fixing the identities it mentions is enough
(`EscapeIso.ofFixes`). A sighted set is not a list of references: a renaming that exchanges its
members carries it to itself (`Observation.RecordControls.sighting_swap`).

## Runs of at most one firing

Swaps need two firings, so trace equivalence relates runs of at most one firing only by similarity
(`Transport.TraceEquiv.similar_of_length_le_one`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Observation (Client Record)

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing}

/-! ## Natural transport and escape data -/

namespace Transport

/-- **A natural transport**: its frame isomorphisms compose as a groupoid, up to the frame
equivalence, and the frame isomorphisms of a moved result, and of the results of alike firings,
commute with the firings' morphisms. Its occurrence renamings compose as a groupoid; a moved result
is renamed as its start, and the results of alike firings are not renamed. -/
structure Natural (T : Transport P) : Prop where
  refl : ∀ s : State, X.Agree (T.toStateIso (T.refl s)).frame.hom (X.id (P.frame s))
  symm : ∀ {s t : State} (i : T.Iso s t),
    X.Agree (T.toStateIso (T.symm i)).frame.hom (T.toStateIso i).frame.inv
  trans : ∀ {s t u : State} (i : T.Iso s t) (j : T.Iso t u),
    X.Agree (T.toStateIso (T.trans i j)).frame.hom
      (X.comp (T.toStateIso j).frame.hom (T.toStateIso i).frame.hom)
  result_move : ∀ {s t : State} (i : T.Iso s t) (f : Firing s) (admitted : P.Admits f),
    X.Agree (X.comp (T.toStateIso (T.result_move i f admitted)).frame.hom (P.along f admitted))
      (X.comp (P.along (T.move i f) ((T.admits_move i f).mpr admitted)) (T.toStateIso i).frame.hom)
  result_alike : ∀ {s : State} {f f' : Firing s} (alike : T.Alike f f') (admitted : P.Admits f)
      (admitted' : P.Admits f'),
    X.Agree (X.comp (T.toStateIso (T.result_alike alike admitted admitted')).frame.hom (P.along f admitted))
      (P.along f' admitted')
  rename_refl : ∀ s : State, (T.toStateIso (T.refl s)).rename = Equiv.refl O
  rename_symm : ∀ {s t : State} (i : T.Iso s t), (T.toStateIso (T.symm i)).rename = (T.toStateIso i).rename.symm
  rename_trans : ∀ {s t u : State} (i : T.Iso s t) (j : T.Iso t u),
    (T.toStateIso (T.trans i j)).rename = (T.toStateIso i).rename.trans (T.toStateIso j).rename
  rename_result_move : ∀ {s t : State} (i : T.Iso s t) (f : Firing s) (admitted : P.Admits f),
    (T.toStateIso (T.result_move i f admitted)).rename = (T.toStateIso i).rename
  rename_result_alike : ∀ {s : State} {f f' : Firing s} (alike : T.Alike f f') (admitted : P.Admits f)
      (admitted' : P.Admits f'),
    (T.toStateIso (T.result_alike alike admitted admitted')).rename = Equiv.refl O

/-- **What clients read, and what a firing makes escape**: the row of each occurrence where the step
has one, carried by every isomorphism to the row of the renamed occurrence up to the knowledge; the
relations among identities a firing makes the environment record, which a moved firing records
renamed; and the public terms it publishes at its result. -/
structure Escape (T : Transport P) where
  row : (s : State) → O → Option (Tm (P.frame s))
  row_iso : ∀ {s t : State} (i : T.Iso s t) (o : O),
    Option.Rel (X.Carried (T.toStateIso i).frame.hom (P.knowledge t)) (row s o)
      (row t ((T.toStateIso i).rename o))
  records : {s : State} → Firing s → Record O
  /-- The public terms a prepared firing publishes at its prepared result: part of its effect. -/
  publishes : {s : State} → (f : Firing s) → (p : P.Prepares f) →
    List (Tm (P.frame (P.preparedResult f p)))
  /-- A moved firing records the renamed relations: what it records is equivariant. -/
  records_move : ∀ {s t : State} (i : T.Iso s t) (f : Firing s),
    records (T.move i f) = Record.rename (T.toStateIso i).rename (records f)
  publishes_move : ∀ {s t : State} (i : T.Iso s t) (f : Firing s) (admitted : P.Admits f),
    List.Forall₂ (fun u v => X.E (X.act (T.toStateIso (T.result_move i f admitted)).frame.hom u) v)
      (publishes f (P.prepares admitted)) (publishes (T.move i f) (P.prepares ((T.admits_move i f).mpr admitted)))
  records_alike : ∀ {s : State} {f f' : Firing s}, T.Alike f f' → records f = records f'
  publishes_alike : ∀ {s : State} {f f' : Firing s} (alike : T.Alike f f') (admitted : P.Admits f)
      (admitted' : P.Admits f'),
    List.Forall₂ (fun u v => X.E (X.act (T.toStateIso (T.result_alike alike admitted admitted')).frame.hom u) v)
      (publishes f (P.prepares admitted)) (publishes f' (P.prepares admitted'))

/-- **The escape data that records nothing**: no rows, no relations, no public terms. -/
def Escape.silent (T : Transport P) : T.Escape where
  row _ _ := none
  row_iso _ _ := .none
  records _ := []
  publishes _ _ := []
  records_move _ _ := rfl
  publishes_move _ _ _ := .nil
  records_alike _ := rfl
  publishes_alike _ _ _ := .nil

end Transport

variable (P) in
/-- **A state with what has escaped**: the public terms clients know at its frame, in the order they
were published, and the record of the environment. -/
structure Escaped where
  state : State
  names : List (Tm (P.frame state))
  record : Record O

namespace Transport

variable {T : Transport P}

namespace Escape

variable (D : T.Escape)

/-- **The escaping step**: the same firings, admissions and results; the result carries the public
terms along the firing's morphism, appends the published ones, and appends the firing's relations to
the record. -/
abbrev step : Step X O (Escaped P) (fun x => Firing x.state) where
  frame x := P.frame x.state
  knowledge x := P.knowledge x.state
  present x := P.present x.state
  selection f := P.selection f
  target f := P.target f
  extension f := P.extension f
  information f := P.information f
  information_refines f := P.information_refines f
  Shapes f := P.Shapes f
  Admits f := P.Admits f
  admitted_prepares _ admitted := P.prepares admitted
  preparedResult {x} f p :=
    ⟨P.preparedResult f p, x.names.map (X.act (X.comp (P.preparedSettle f p) (P.extension f))) ++ D.publishes f p,
      x.record ++ D.records f⟩
  present_preparedResult f p := P.present_preparedResult f p
  preparedSettle f p := P.preparedSettle f p
  result_refines f p := P.result_refines f p

instance step_guarded [P.Guarded] : D.step.Guarded where
  holds f := P.Holds f
  admission f := P.admits_iff_prepares f

instance step_literalInformation [P.LiteralInformation] : D.step.LiteralInformation :=
  ⟨fun f => P.transported f⟩

instance step_literalKnowledge [P.LiteralKnowledge] : D.step.LiteralKnowledge :=
  ⟨fun f p => P.knowledge_preparedResult f p⟩

instance step_exact [P.Exact] : D.step.Exact :=
  ⟨fun f p => Step.Exact.exactness (P := P) f p⟩

/-- Forget what has escaped. -/
def forget : {x : Escaped P} → D.step.Run x → P.Run x.state
  | _, .nil x => .nil x.state
  | _, .cons f admitted rest => .cons f admitted (forget rest)

/-- **The record only grows along runs**: the start's record is a prefix of the end's. -/
theorem record_last : ∀ {x : Escaped P} (r : D.step.Run x), ∃ later : Record O,
    r.last.record = x.record ++ later
  | _, .nil _ => ⟨[], (List.append_nil _).symm⟩
  | x, .cons f admitted rest => by
      obtain ⟨later, grown⟩ := record_last rest
      refine ⟨D.records f ++ later, ?_⟩
      show rest.last.record = x.record ++ (D.records f ++ later)
      rw [grown, ← List.append_assoc]

/-- **Every relation a fired firing recorded is in the record at the end of the run.** -/
theorem records_last : ∀ {x : Escaped P} (r : D.step.Run x), ∀ e ∈ r.word,
    ∀ entry ∈ D.records (s := e.1.state) e.2, entry ∈ r.last.record
  | _, .nil _, _, member => by simp [Step.Run.word] at member
  | x, .cons g admitted rest, e, member => by
      rcases List.mem_cons.mp member with here | later
      · subst here
        intro entry inside
        obtain ⟨more, grown⟩ := record_last D rest
        show entry ∈ rest.last.record
        rw [grown]
        exact List.mem_append_left more (List.mem_append_right x.record inside)
      · exact records_last rest e later

theorem map_act_id {a : Obj} (l : List (Tm a)) : l.map (X.act (X.id a)) = l := by
  induction l with
  | nil => rfl
  | cons u rest ih => rw [List.map_cons, X.act_id, ih]

/-- **The public terms of the start reach the end carried along the run.** -/
theorem names_last : ∀ {x : Escaped P} (r : D.step.Run x),
    ∃ later : List (Tm (D.step.frame r.last)), r.last.names = x.names.map (X.act r.toLast) ++ later
  | x, .nil _ => ⟨[], by
      rw [List.append_nil]
      exact (map_act_id x.names).symm⟩
  | x, .cons f admitted rest => by
      obtain ⟨later, carried⟩ := names_last rest
      refine ⟨(D.publishes f (P.prepares admitted)).map (X.act rest.toLast) ++ later, ?_⟩
      have start : (D.step.result f admitted).names =
          x.names.map (X.act (P.along f admitted)) ++ D.publishes f (P.prepares admitted) := rfl
      show rest.last.names = x.names.map (X.act (X.comp rest.toLast (P.along f admitted))) ++
        ((D.publishes f (P.prepares admitted)).map (X.act rest.toLast) ++ later)
      rw [carried, start, List.map_append, List.map_map, List.append_assoc]
      congr 1
      exact List.map_congr_left fun u _ => (X.act_comp _ _ u).symm

end Escape

/-- **An isomorphism relative to what has escaped**: an isomorphism of the underlying transport whose
frame isomorphism carries every public term to its counterpart up to the knowledge
(`Frames.Carried`), and whose renaming carries the record of the first state to the record of the
second. -/
structure EscapeIso (T : Transport P) (x y : Escaped P) where
  base : T.Iso x.state y.state
  names : List.Forall₂ (X.Carried (T.toStateIso base).frame.hom (P.knowledge y.state)) x.names y.names
  record : Record.rename (T.toStateIso base).rename x.record = y.record

/-- **The escape-relative transport.** -/
def escaping (T : Transport P) (natural : T.Natural) (D : T.Escape) : Transport D.step where
  Iso x y := T.EscapeIso x y
  toStateIso i :=
    ⟨(T.toStateIso i.base).frame, (T.toStateIso i.base).knowledge, (T.toStateIso i.base).rename,
      (T.toStateIso i.base).present⟩
  refl x := ⟨T.refl x.state,
    List.forall₂_same.mpr fun u _ => Frames.Carried.of_E (by
      have fixed := natural.refl x.state u
      rwa [X.act_id] at fixed), by rw [natural.rename_refl, Record.rename_refl]⟩
  symm {x y} i := ⟨T.symm i.base, forall₂_swap (fun u v related =>
      Frames.Carried.congr (fun t => (X.equivalence _).symm (natural.symm i.base t))
        (Frames.Carried.symm _ (T.toStateIso i.base).knowledge related)) i.names, by
      rw [natural.rename_symm]
      exact Record.rename_eq_symm i.record⟩
  trans i j := ⟨T.trans i.base j.base,
    forall₂_comp (R₁ := X.Carried (T.toStateIso i.base).frame.hom (P.knowledge _))
      (R₂ := X.Carried (T.toStateIso j.base).frame.hom (P.knowledge _))
      (R₃ := X.Carried (T.toStateIso (T.trans i.base j.base)).frame.hom (P.knowledge _))
      (fun u v w first second =>
      Frames.Carried.congr (fun t => (X.equivalence _).symm (natural.trans i.base j.base t))
        (Frames.Carried.trans (T.toStateIso j.base).knowledge first second)) i.names j.names, by
      rw [natural.rename_trans]
      exact Record.rename_eq_trans i.record j.record⟩
  Alike f f' := T.Alike f f'
  alike_equivalence x := T.alike_equivalence x.state
  selection_alike alike := T.selection_alike alike
  admits_alike alike := T.admits_alike alike
  result_alike {x} {f f'} alike admitted admitted' :=
    ⟨T.result_alike alike admitted admitted', by
      show List.Forall₂
        (X.Carried (T.toStateIso (T.result_alike alike admitted admitted')).frame.hom
          (P.knowledge (P.result f' admitted')))
        (x.names.map (X.act (P.along f admitted)) ++ D.publishes f (P.prepares admitted))
        (x.names.map (X.act (P.along f' admitted')) ++ D.publishes f' (P.prepares admitted'))
      refine forall₂_append (forall₂_map (R := fun u v => u = v) (fun u v same => ?_)
        (List.forall₂_same.mpr fun _ _ => rfl))
        ((D.publishes_alike alike admitted admitted').imp fun _ _ same => Frames.Carried.of_E same)
      subst same
      have square := natural.result_alike alike admitted admitted' u
      rw [X.act_comp] at square
      exact Frames.Carried.of_E square,
      by
        show Record.rename (T.toStateIso (T.result_alike alike admitted admitted')).rename
          (x.record ++ D.records f) = x.record ++ D.records f'
        rw [natural.rename_result_alike, Record.rename_refl, D.records_alike alike]⟩
  move i f := T.move i.base f
  move_alike i _ _ alike := T.move_alike i.base alike
  move_refl f := T.move_refl f
  move_trans i j f := T.move_trans i.base j.base f
  move_symm i f := T.move_symm i.base f
  selection_move i f := T.selection_move i.base f
  admits_move i f := T.admits_move i.base f
  result_move {x y} i f admitted :=
    ⟨T.result_move i.base f admitted, by
      show List.Forall₂ (X.Carried (T.toStateIso (T.result_move i.base f admitted)).frame.hom
          (P.knowledge (P.result (T.move i.base f) ((T.admits_move i.base f).mpr admitted))))
        (x.names.map (X.act (P.along f admitted)) ++ D.publishes f (P.prepares admitted))
        (y.names.map (X.act (P.along (T.move i.base f) ((T.admits_move i.base f).mpr admitted))) ++
          D.publishes (T.move i.base f) (P.prepares ((T.admits_move i.base f).mpr admitted)))
      refine forall₂_append (forall₂_map (fun u v related => ?_) i.names)
        ((D.publishes_move i.base f admitted).imp fun _ _ same => Frames.Carried.of_E same)
      intro c g solved
      have pulled := P.models_along ((T.admits_move i.base f).mpr admitted) g solved
      have there := related c _ pulled
      have square := X.preserves g (natural.result_move i.base f admitted u)
      simp only [X.act_comp] at there square ⊢
      exact (X.equivalence c).trans square there,
      by
        show Record.rename (T.toStateIso (T.result_move i.base f admitted)).rename
          (x.record ++ D.records f) = y.record ++ D.records (T.move i.base f)
        rw [natural.rename_result_move, Record.rename_append, i.record, D.records_move]⟩
  residual g admitted f := T.residual g admitted f
  selection_residual g admitted f := T.selection_residual g admitted f
  move_residual i g admitted f := T.move_residual i.base g admitted f

/-- **Escaping keeps naturality**, so escape layers stack. -/
theorem Natural.escaping {T : Transport P} (natural : T.Natural) (D : T.Escape) :
    (T.escaping natural D).Natural where
  refl x := natural.refl x.state
  symm i := natural.symm i.base
  trans i j := natural.trans i.base j.base
  result_move i f admitted := natural.result_move i.base f admitted
  result_alike alike admitted admitted' := natural.result_alike alike admitted admitted'
  rename_refl x := natural.rename_refl x.state
  rename_symm i := natural.rename_symm i.base
  rename_trans i j := natural.rename_trans i.base j.base
  rename_result_move i f admitted := natural.rename_result_move i.base f admitted
  rename_result_alike alike admitted admitted' := natural.rename_result_alike alike admitted admitted'

/-! ## The pointwise case -/

namespace EscapeIso

/-- **Fixing every identity the record mentions is enough**: between states with one record, a
renaming that fixes them gives an escape-relative isomorphism. -/
def ofFixes {x y : Escaped P} (base : T.Iso x.state y.state)
    (names : List.Forall₂ (X.Carried (T.toStateIso base).frame.hom (P.knowledge y.state)) x.names y.names)
    (same : x.record = y.record)
    (fixes : ∀ o ∈ Record.support x.record, (T.toStateIso base).rename o = o) : T.EscapeIso x y :=
  ⟨base, names, (Record.rename_eq_self_of_fixes fixes).trans same⟩

/-- **The pointwise case**: when the record holds only references, the isomorphisms between states
with that one record are exactly the isomorphisms that fix every reference and carry the public
terms. -/
theorem nonempty_iff_of_references {x y : Escaped P} {l : List O}
    (held : x.record = Record.references l) (same : y.record = x.record) :
    Nonempty (T.EscapeIso x y) ↔ ∃ base : T.Iso x.state y.state,
      List.Forall₂ (X.Carried (T.toStateIso base).frame.hom (P.knowledge y.state)) x.names y.names ∧
        ∀ o ∈ l, (T.toStateIso base).rename o = o := by
  constructor
  · rintro ⟨i⟩
    have carried := i.record
    rw [same, held] at carried
    exact ⟨i.base, i.names, Record.references_rename_eq_iff.mp carried⟩
  · rintro ⟨base, names, fixes⟩
    refine ⟨⟨base, names, ?_⟩⟩
    rw [same, held]
    exact Record.references_rename_eq_iff.mpr fixes

/-- **A client context of the client layer**: an isomorphism between states whose record is the
client context fixes every escaped identity. -/
theorem fixes_of_client {x y : Escaped P} (i : T.EscapeIso x y) {c : Client O}
    (held : x.record = Record.ofClient c) (same : y.record = x.record) :
    ∀ o ∈ c.escaped, (T.toStateIso i.base).rename o = o := by
  have carried := i.record
  rw [same, held] at carried
  exact (Record.ofClient_rename_eq_iff c).mp carried

end EscapeIso

/-! ## Runs of at most one firing -/

variable {T : Transport P}

theorem Similar.length_eq : ∀ {s t : State} {r : P.Run s} {r' : P.Run t}, T.Similar r r' →
    r.word.length = r'.word.length
  | _, _, .nil _, .nil _, _ => rfl
  | _, _, .cons _ _ _, .cons _ _ _, similar => by
      obtain ⟨-, -, tail⟩ := similar_cons_cons.mp similar
      simp [Step.Run.word, Similar.length_eq tail]
  | _, _, .nil _, .cons _ _ _, similar => False.elim similar
  | _, _, .cons _ _ _, .nil _, similar => False.elim similar

theorem SwapStep.length_eq {s : State} {r r' : P.Run s} (step : T.SwapStep r r') :
    r.word.length = r'.word.length ∧ 2 ≤ r.word.length := by
  induction step with
  | here _ _ _ _ _ _ similar =>
      have same := Similar.length_eq similar
      simp [Step.Run.word, same]
  | later _ _ _ ih =>
      obtain ⟨same, long⟩ := ih
      simp only [Step.Run.word, List.length_cons]
      constructor <;> omega

theorem TraceEquiv.length_eq {s : State} {r r' : P.Run s} (equivalent : T.TraceEquiv s r r') :
    r.word.length = r'.word.length := by
  induction equivalent with
  | rel _ _ step =>
      rcases step with step | similar
      · exact step.length_eq.1
      · exact Similar.length_eq similar
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Trace equivalence of runs of at most one firing is similarity.** -/
theorem TraceEquiv.similar_of_length_le_one {s : State} {r r' : P.Run s}
    (equivalent : T.TraceEquiv s r r') (short : r.word.length ≤ 1) : T.Similar r r' := by
  induction equivalent with
  | rel _ _ step =>
      rcases step with step | similar
      · have := step.length_eq.2
        omega
      · exact similar
  | refl r => exact Similar.refl r
  | symm _ _ back ih => exact Similar.symm (ih (by rw [TraceEquiv.length_eq back]; exact short))
  | trans _ _ _ first _ ih₁ ih₂ =>
      exact Similar.trans (ih₁ short) (ih₂ (by rw [← TraceEquiv.length_eq first]; exact short))

/-- One firing and a firing alike to its transport are similar runs. -/
theorem Similar.single {s t : State} (i : T.Iso s t) {f : Firing s} (admitted : P.Admits f)
    {f' : Firing t} (admitted' : P.Admits f') (moved : T.Alike (T.move i f) f') :
    T.Similar (.cons f admitted (.nil _)) (.cons f' admitted' (.nil _)) :=
  similar_cons_cons.mpr ⟨i, moved, similar_nil_nil.mpr
    ⟨T.trans (T.result_move i f admitted) (T.result_alike moved _ admitted')⟩⟩


/-! ## The generic trace results over the escape-relative transport -/

namespace Escape

variable {natural : T.Natural} {D : T.Escape}

/-- **The trace category of the escape-relative transport.** -/
@[reducible] noncomputable def traceCategory (natural : T.Natural) (D : T.Escape) :
    CategoryTheory.Category (T.escaping natural D).StateClass :=
  Transport.traceCategory (T.escaping natural D)

/-- **Trace-equivalent runs end with records related by the renaming of an isomorphism of their
ends.** -/
theorem traceEquiv_record {x : Escaped P} {r r' : D.step.Run x}
    (equivalent : (T.escaping natural D).TraceEquiv x r r') :
    ∃ i : T.Iso r.last.state r'.last.state,
      Record.rename (T.toStateIso i).rename r.last.record = r'.last.record := by
  obtain ⟨i⟩ := TraceEquiv.same_last equivalent
  exact ⟨i.base, i.record⟩

/-- **The common past is respected**: that renaming is an automorphism of the start's record, and it
carries what one run recorded to what the other recorded. -/
theorem traceEquiv_past {x : Escaped P} {r r' : D.step.Run x}
    (equivalent : (T.escaping natural D).TraceEquiv x r r') :
    ∃ i : T.Iso r.last.state r'.last.state,
      (T.toStateIso i).rename ∈ Record.automorphisms x.record ∧
      ∃ later later' : Record O, r.last.record = x.record ++ later ∧
        r'.last.record = x.record ++ later' ∧ Record.rename (T.toStateIso i).rename later = later' := by
  obtain ⟨i, carried⟩ := traceEquiv_record equivalent
  obtain ⟨later, grown⟩ := record_last D r
  obtain ⟨later', grown'⟩ := record_last D r'
  rw [grown, grown'] at carried
  obtain ⟨past, recorded⟩ := Record.rename_prefix carried
  exact ⟨i, past, later, later', grown, grown', recorded⟩

/-- **Trace-equivalent runs end with public terms matched by an isomorphism**, up to the knowledge. -/
theorem traceEquiv_names {x : Escaped P} {r r' : D.step.Run x}
    (equivalent : (T.escaping natural D).TraceEquiv x r r') :
    ∃ i : T.Iso r.last.state r'.last.state,
      List.Forall₂ (X.Carried (T.toStateIso i).frame.hom (P.knowledge r'.last.state)) r.last.names
        r'.last.names := by
  obtain ⟨i⟩ := TraceEquiv.same_last equivalent
  exact ⟨i.base, i.names⟩

/-- **Forgetting escape keeps similarity.** -/
theorem Similar.forget : ∀ {x y : Escaped P} {r : D.step.Run x} {r' : D.step.Run y},
    (T.escaping natural D).Similar r r' → T.Similar (D.forget r) (D.forget r')
  | _, _, .nil _, .nil _, similar => by
      obtain ⟨i⟩ := similar_nil_nil.mp similar
      exact similar_nil_nil.mpr ⟨i.base⟩
  | _, _, .cons _ _ _, .cons _ _ _, similar => by
      obtain ⟨i, moved, tail⟩ := similar_cons_cons.mp similar
      exact similar_cons_cons.mpr ⟨i.base, moved, Similar.forget tail⟩
  | _, _, .nil _, .cons _ _ _, similar => False.elim similar
  | _, _, .cons _ _ _, .nil _, similar => False.elim similar

/-- **Forgetting escape keeps swaps.** -/
theorem SwapStep.forget {x : Escaped P} {r r' : D.step.Run x}
    (step : (T.escaping natural D).SwapStep r r') : T.SwapStep (D.forget r) (D.forget r') := by
  induction step with
  | here first second residualG afterFirst residualF afterSecond similar =>
      exact SwapStep.here (T := T) first second residualG afterFirst residualF afterSecond
        (Similar.forget similar)
  | later f admitted _ ih => exact SwapStep.later (T := T) f admitted ih

/-- **The escape-relative trace equivalence refines the underlying one.** -/
theorem TraceEquiv.forget {x : Escaped P} {r r' : D.step.Run x}
    (equivalent : (T.escaping natural D).TraceEquiv x r r') :
    T.TraceEquiv x.state (D.forget r) (D.forget r') := by
  induction equivalent with
  | rel _ _ step =>
      rcases step with step | similar
      · exact .rel _ _ (.inl (SwapStep.forget step))
      · exact .rel _ _ (.inr (Similar.forget similar))
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

end Escape

end Transport

#print axioms Transport.Escape.silent
#print axioms Transport.Escape.record_last
#print axioms Transport.Escape.records_last
#print axioms Transport.Escape.names_last
#print axioms Transport.escaping
#print axioms Transport.Natural.escaping
#print axioms Transport.EscapeIso.ofFixes
#print axioms Transport.EscapeIso.nonempty_iff_of_references
#print axioms Transport.EscapeIso.fixes_of_client
#print axioms Transport.TraceEquiv.similar_of_length_le_one
#print axioms Transport.Similar.single
#print axioms Transport.Escape.traceCategory
#print axioms Transport.Escape.traceEquiv_record
#print axioms Transport.Escape.traceEquiv_past
#print axioms Transport.Escape.traceEquiv_names
#print axioms Transport.Escape.Similar.forget
#print axioms Transport.Escape.SwapStep.forget
#print axioms Transport.Escape.TraceEquiv.forget

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
