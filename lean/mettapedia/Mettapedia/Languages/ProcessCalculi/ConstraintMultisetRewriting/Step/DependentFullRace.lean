import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullSwap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceGeneric

/-!
# Firings without helpers at dependent frames, placed in the generic races layer

**The step** (`plainStep`). Firings without helpers whose predicate queries are natural form an
instance of the candidate step's interface over the dependent unifier's frames. It is the dependent
full step on those firings: the same admission and the same results (`plainStep_admits_iff`,
`plainStep_result`).

**Transport** (`PlainIso`, `plainTransport`). An isomorphism of states is an isomorphism of
telescopes that carries the knowledge to knowledge with the same solutions, the present occurrences
to themselves and each label to the label. Firings move along it by carrying their data
(`Natural.move`), on the nose, so the transport is strict: alike firings are equal. A firing's
residual after another is the same firing, at the other's result, whose frame is the same.

**Independence** (`plain_closes`, `plain_independent_iff`, `independent_of_clauses`). The diamond closes
whenever both orders are admitted, so the interface's semantic independence is exactly the admission
of both orders; R93's independence condition (`Independent`) implies it.

**The races layer applies** (`plain_bisimilar_of_same`, `plain_stepBisimilar_of_same`): for every
program whose labels are invariant under transport, transport-equivalent states are bisimilar and
step bisimilar, where steps are words of semantically independent firings at dependent frames.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
  {O : Type}

/-! ## Laws used by the transport -/

theorem Make.reindex_id {Δ : Context rules} (m : Make Δ) : m.reindex (𝟙 Δ) = m :=
  congrArg₂ Make.mk m.type.reindex_id (subst_ids m.code)

theorem Natural.move_id {Δ : Context rules} (f : Natural levels O Δ) : f.move (𝟙 Δ) = f := by
  obtain ⟨taken, read, takes, reads, makes, tells, guards, queries⟩ := f
  have actId : (frames levels).act (𝟙 Δ) = id := funext act_one'
  simp only [Natural.move, Natural.mk.injEq, true_and, actId, List.map_id, Plain.applyStore_one]
  refine ⟨(List.map_congr_left fun m _ => ?_).trans (List.map_id _),
    (List.map_congr_left fun q _ => NaturalQuery.move_id q).trans (List.map_id _)⟩
  show (m.1, m.2.reindex (𝟙 Δ)) = m
  rw [Make.reindex_id]

/-- **Admission depends on the knowledge only through its solutions.** -/
theorem Plain.admits_equivalent [DecidableEq O] {Δ : Context rules} (f : Plain levels O Δ)
    {K K' : EquationStore (TotalTerm Δ)} (present : Finset O) (label : O → TotalTerm Δ)
    (same : (frames levels).Equivalent K K') :
    f.Admits ⟨K, present, label⟩ ↔ f.Admits ⟨K', present, label⟩ := by
  have information : (frames levels).Equivalent (f.information ⟨K, present, label⟩)
      (f.information ⟨K', present, label⟩) := fun b τ => by
    show (frames levels).Models τ (K ++ f.own label) ↔ (frames levels).Models τ (K' ++ f.own label)
    rw [Frames.models_append, Frames.models_append, same b τ]
  unfold Plain.Admits
  rw [information.solvable_iff, information.entails_iff]
  rfl

/-- **When both orders are admitted, the composites agree**: the same present occurrences and
labels, and knowledge with the same solutions. -/
theorem agree_of_residuals [DecidableEq O] {Δ : Context rules} {c : Local rules O Δ} {f g : Plain levels O Δ}
    (first : f.Admits c) (second : g.Admits c) (afterFirst : g.Admits (f.after c first.1.2.2.2.2))
    (afterSecond : f.Admits (g.after c second.1.2.2.2.2)) :
    (frames levels).Equivalent (g.after (f.after c first.1.2.2.2.2) second.1.2.2.2.2).knowledge
        (f.after (g.after c second.1.2.2.2.2) first.1.2.2.2.2).knowledge ∧
      (g.after (f.after c first.1.2.2.2.2) second.1.2.2.2.2).present =
        (f.after (g.after c second.1.2.2.2.2) first.1.2.2.2.2).present ∧
      (g.after (f.after c first.1.2.2.2.2) second.1.2.2.2.2).label =
        (f.after (g.after c second.1.2.2.2.2) first.1.2.2.2.2).label := by
  obtain ⟨-, -, -, madeApart, -⟩ := clauses_of_residuals first second afterFirst afterSecond
  refine ⟨?_, ?_, relabel_comm c.label f.makes g.makes _ _ madeApart⟩
  · show (frames levels).Equivalent (g.information (f.after c _)) (f.information (g.after c _))
    rw [information_after first second, information_after second first]
    exact joint_comm f g
  · ext o
    obtain ⟨fTaken, -, -, fFresh⟩ := (f.enabled_iff c).mp first.2.1
    obtain ⟨gTaken, -, -, gFresh⟩ := (g.enabled_iff c).mp second.2.1
    exact fire_fire_comm c f g o (fTaken o) (gTaken o) (fFresh o) (gFresh o)

/-! ## The step -/

variable [DecidableEq O]

variable (levels O) in
/-- **The dependent step on firings without helpers with natural queries.** -/
abbrev plainStep : Interface.Step.Standard (frames levels) O (State rules O) (fun s => Natural levels O s.frame) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.toPlain.selection
  target {s} _ := s.frame
  extension {s} _ := 𝟙 s.frame
  information {s} f := f.toPlain.information s.toLocal
  transported := by
    intro s f e member
    show ((frames levels).act (𝟙 s.frame) e.1, (frames levels).act (𝟙 s.frame) e.2) ∈
      s.knowledge ++ f.toPlain.own s.label
    rw [act_one', act_one']
    exact List.mem_append_left _ member
  Shapes f := f.toPlain.Shapes
  Holds {s} f _ τ := f.toPlain.Holds s.toLocal τ
  Admits {s} f := f.toPlain.Admits s.toLocal
  admits_iff _ := Iff.rfl
  preparedResult {s} f p := (f.toPlain.after s.toLocal p.1.2.2.2.2).toState
  present_preparedResult _ _ := rfl
  preparedSettle {s} _ _ := 𝟙 s.frame
  knowledge_preparedResult _ _ := (Frames.applyStore_id (X := frames levels) _).symm

/-- **It is the dependent full step on these firings**: the same admission. -/
theorem plainStep_admits_iff {s : State rules O} (f : Natural levels O s.frame) :
    (plainStep levels O).Admits f ↔ (step levels O).Admits (Plain.toFiring f.toPlain) :=
  (Plain.admits_toFiring f.toPlain).symm

/-- **And the same results.** -/
theorem plainStep_result {s : State rules O} (f : Natural levels O s.frame)
    (admitted : (plainStep levels O).Admits f) :
    (plainStep levels O).result f admitted =
      (Plain.toFiring (s := s) f.toPlain).after ((plainStep_admits_iff f).mp admitted) :=
  (Plain.after_toFiring f.toPlain _).symm

/-! ## Transport -/

/-- The isomorphism of dependent frames given by an isomorphism of telescopes. -/
def framesIso {Δ Δ' : Context rules} (e : Δ' ≅ Δ) : (frames levels).Iso Δ Δ' where
  hom := e.hom
  inv := e.inv
  inv_hom t := by
    show (frames levels).E ((frames levels).act e.inv ((frames levels).act e.hom t)) t
    rw [act_act, e.inv_hom_id, act_one']
    exact ((frames levels).equivalence _).refl t
  hom_inv t := by
    show (frames levels).E ((frames levels).act e.hom ((frames levels).act e.inv t)) t
    rw [act_act, e.hom_inv_id, act_one']
    exact ((frames levels).equivalence _).refl t

variable (levels) in
/-- **An isomorphism of states**: an isomorphism of telescopes carrying the knowledge to knowledge
with the same solutions, the present occurrences to themselves and each label to the label. -/
structure PlainIso (s t : State rules O) where
  frame : t.frame ≅ s.frame
  knowledge : (frames levels).Equivalent ((frames levels).applyStore frame.hom s.knowledge) t.knowledge
  present : s.present = t.present
  label : ∀ o, t.label o = (frames levels).act frame.hom (s.label o)

namespace PlainIso

def refl (s : State rules O) : PlainIso levels s s :=
  ⟨Iso.refl _, Frames.Iso.equivalent_refl (X := frames levels) s.knowledge, rfl, fun _ => (act_one' _).symm⟩

def symm {s t : State rules O} (i : PlainIso levels s t) : PlainIso levels t s where
  frame := i.frame.symm
  knowledge := Frames.Iso.equivalent_symm (framesIso (levels := levels) i.frame) i.knowledge
  present := i.present.symm
  label o := by
    show s.label o = (frames levels).act i.frame.inv (t.label o)
    rw [i.label, act_act, i.frame.inv_hom_id, act_one']

def trans {s t u : State rules O} (i : PlainIso levels s t) (j : PlainIso levels t u) : PlainIso levels s u where
  frame := j.frame ≪≫ i.frame
  knowledge := Frames.Iso.equivalent_trans (framesIso (levels := levels) i.frame)
    (framesIso (levels := levels) j.frame) i.knowledge j.knowledge
  present := i.present.trans j.present
  label o := by
    show u.label o = (frames levels).act (j.frame.hom ≫ i.frame.hom) (s.label o)
    rw [j.label, i.label, act_act]

/-- The interface's isomorphism of states it gives. -/
def toStateIso {s t : State rules O} (i : PlainIso levels s t) : (plainStep levels O).StateIso s t :=
  ⟨framesIso i.frame, i.knowledge, Equiv.refl O, by
    show s.present.map (Equiv.refl O).toEmbedding = t.present
    rw [Equiv.refl_toEmbedding, Finset.map_refl, i.present]⟩

end PlainIso

omit [DecidableEq O] in
theorem local_move_of_iso {s t : State rules O} (i : PlainIso levels s t) :
    (⟨(frames levels).applyStore i.frame.hom s.knowledge, t.present, t.label⟩ : Local rules O t.frame) =
      s.toLocal.move i.frame.hom :=
  Local.mk_congr rfl i.present.symm (funext i.label)

/-- **Admission moves along isomorphisms of states.** -/
theorem admits_move_plain {s t : State rules O} (i : PlainIso levels s t) (f : Natural levels O s.frame) :
    (f.move i.frame.hom).toPlain.Admits t.toLocal ↔ f.toPlain.Admits s.toLocal :=
  ((f.move i.frame.hom).toPlain.admits_equivalent t.present t.label i.knowledge).symm.trans
    ((Plain.admits_congr rfl (local_move_of_iso i)).trans (Natural.admits_move_iff f i.frame s.toLocal))

/-- **Results move along isomorphisms of states.** -/
def resultMove {s t : State rules O} (i : PlainIso levels s t) (f : Natural levels O s.frame)
    (admitted : (plainStep levels O).Admits f) :
    PlainIso levels ((plainStep levels O).result f admitted)
      ((plainStep levels O).result (f.move i.frame.hom) ((admits_move_plain i f).mpr admitted)) where
  frame := i.frame
  knowledge := by
    have one : (frames levels).Equivalent
        ((frames levels).applyStore i.frame.hom (f.toPlain.information s.toLocal))
        ((f.move i.frame.hom).toPlain.information (s.toLocal.move i.frame.hom)) := by
      rw [Natural.information_move]
      exact fun _ _ => Iff.rfl
    have two : (frames levels).Equivalent ((f.move i.frame.hom).toPlain.information (s.toLocal.move i.frame.hom))
        ((f.move i.frame.hom).toPlain.information t.toLocal) := fun b τ => by
      show (frames levels).Models τ ((s.toLocal.move i.frame.hom).knowledge ++
          (f.move i.frame.hom).toPlain.own (s.toLocal.move i.frame.hom).label) ↔
        (frames levels).Models τ (t.knowledge ++ (f.move i.frame.hom).toPlain.own t.label)
      rw [show (s.toLocal.move i.frame.hom).label = t.label from (funext i.label).symm,
        Frames.models_append, Frames.models_append]
      exact and_congr (i.knowledge b τ) Iff.rfl
    exact one.trans two
  present := by
    show fire s.present (f.toPlain.selection.commit (T := Unit)) =
      fire t.present ((f.move i.frame.hom).toPlain.selection.commit (T := Unit))
    rw [Natural.selection_move, i.present]
  label o := congrFun ((Plain.relabel_row_congr (funext i.label) (f.move i.frame.hom).makes _).trans
    (relabel_move i.frame.hom s.label f.makes _ _)) o

variable (levels O) in
/-- **The strict transport of firings without helpers.** -/
def plainTransport : Transport (plainStep levels O).toStep where
  Iso s t := PlainIso levels s t
  toStateIso := PlainIso.toStateIso
  refl := PlainIso.refl
  symm := PlainIso.symm
  trans := PlainIso.trans
  Alike f f' := f = f'
  alike_equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  selection_alike := fun same => congrArg _ same
  admits_alike := fun same => by subst same; rfl
  result_alike := fun same _ _ => by subst same; exact PlainIso.refl _
  move i f := f.move i.frame.hom
  move_alike := by
    intro s t i f f' same
    exact congrArg (fun g : Natural levels O s.frame => g.move i.frame.hom) same
  move_refl f := Natural.move_id f
  move_trans i j f := (Natural.move_comp i.frame.hom j.frame.hom f).symm
  move_symm i f := by
    show (f.move i.frame.hom).move i.frame.inv = f
    rw [Natural.move_comp, i.frame.inv_hom_id, Natural.move_id]
  selection_move i f := (Natural.selection_move i.frame.hom f).trans (renameSelection_refl _).symm
  admits_move i f := admits_move_plain i f
  result_move i f admitted := resultMove i f admitted
  residual _ _ f := f
  selection_residual _ _ _ := rfl
  move_residual _ _ _ _ := rfl

/-! ## Independence and the races layer -/

/-- **The diamond closes whenever both orders are admitted.** -/
theorem plain_closes : (plainTransport levels O).Closes := by
  intro s f g first second afterFirst afterSecond
  obtain ⟨knowledge, present, label⟩ := agree_of_residuals first second afterFirst afterSecond
  refine ⟨⟨Iso.refl _, ?_, present, fun o => ?_⟩⟩
  · exact (Frames.Iso.equivalent_refl (X := frames levels) _).trans knowledge
  · show (f.toPlain.after (g.toPlain.after s.toLocal _) _).label o =
      (frames levels).act (𝟙 _) ((g.toPlain.after (f.toPlain.after s.toLocal _) _).label o)
    rw [act_one', label]

/-- **The interface's independence is the admission of both orders.** -/
theorem plain_independent_iff {s : State rules O} {f g : Natural levels O s.frame} :
    (plainTransport levels O).Independent s f g ↔
      ∃ (first : (plainStep levels O).Admits f) (second : (plainStep levels O).Admits g),
        (plainStep levels O).Admits ((plainTransport levels O).residual f first g) ∧
          (plainStep levels O).Admits ((plainTransport levels O).residual g second f) :=
  Transport.independent_iff_admits plain_closes

/-- **R93's independence condition implies the interface's independence.** -/
theorem independent_of_clauses {s : State rules O} {f g : Natural levels O s.frame}
    (first : (plainStep levels O).Admits f) (second : (plainStep levels O).Admits g)
    (independent : Independent s.toLocal f.toPlain g.toPlain) :
    (plainTransport levels O).Independent s f g := by
  obtain ⟨one, two, -⟩ := local_diamond first second independent
  exact plain_independent_iff.mpr ⟨first, second, one, two⟩

/-- **Transport-equivalent states are bisimilar**, for every program with invariant labels. -/
theorem plain_bisimilar_of_same {Lab : Type} (offers : Lab → (s : State rules O) → Natural levels O s.frame → Prop)
    (invariant : Race.Generic.Invariant (plainStep levels O).toStep offers (plainTransport levels O))
    {s t : State rules O} (same : (plainTransport levels O).Same s t) :
    Race.Generic.Bisimilar (plainStep levels O).toStep offers s t :=
  Race.Generic.bisimilar_of_same (plainTransport levels O) invariant same

/-- **Transport-equivalent states are step bisimilar**: steps are words of semantically independent
firings at dependent frames. -/
theorem plain_stepBisimilar_of_same {Lab : Type}
    (offers : Lab → (s : State rules O) → Natural levels O s.frame → Prop)
    (invariant : Race.Generic.Invariant (plainStep levels O).toStep offers (plainTransport levels O))
    {s t : State rules O} (same : (plainTransport levels O).Same s t) :
    Race.Generic.StepBisimilar (plainStep levels O).toStep (plainTransport levels O) offers s t :=
  Race.Generic.stepBisimilar_of_same (fun {_ _ _} => Iff.rfl) invariant same

end DependentFull

#print axioms DependentFull.Natural.move_id
#print axioms DependentFull.Plain.admits_equivalent
#print axioms DependentFull.agree_of_residuals
#print axioms DependentFull.plainStep
#print axioms DependentFull.plainStep_admits_iff
#print axioms DependentFull.plainStep_result
#print axioms DependentFull.plainTransport
#print axioms DependentFull.plain_closes
#print axioms DependentFull.plain_independent_iff
#print axioms DependentFull.independent_of_clauses
#print axioms DependentFull.plain_bisimilar_of_same
#print axioms DependentFull.plain_stepBisimilar_of_same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
