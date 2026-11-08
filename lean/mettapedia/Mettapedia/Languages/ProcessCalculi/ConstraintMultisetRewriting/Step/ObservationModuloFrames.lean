import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationFrames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModulo

/-!
# Rows modulo the knowledge over a category of frames

A row isomorphism (`RowIso`) relates two row states by an isomorphism of frames, which renames the
private names of the frame, and a renaming of occurrences that fixes the escaped identities; it
carries every row and every public name to its counterpart up to the frame equivalence. Clients read
rows and public names only at solutions of the knowledge, so this module asks for both **at every
solution of the second state's knowledge** (`RowIsoModulo`).

* **A groupoid** (`RowIsoModulo.refl`, `symm`, `trans`). Solutions correspond both ways along the
  frame isomorphism (`RowIsoModulo.solution`, `solution_back`).
* **It contains the row isomorphisms** (`RowIso.modulo`).
* **Clients respect it** (`FrameProbe.observes_iff_modulo`): the frame probes, whose readouts respect
  the frame equivalence, observe the same at states related modulo the knowledge.
* **The run layer is the one-frame case** (`rowIsoModulo_of_renaming`,
  `rowEquivalentModulo_of_moduloEquivalent`): equivalence modulo the knowledge of configurations
  gives a row isomorphism modulo the knowledge of their row states. In the one-frame case every term
  is public, so no metavariable is renamed there; private frame names are renamed only by the
  frame isomorphisms of a richer category of frames.

## Control: a public hole, rows modulo the knowledge (`FrameModuloControls`)

On the contextual frames with two holes, the first hole a public name and the knowledge that the two
holes are equal, the state holding the first hole and the state holding the second are related modulo
the knowledge (`held_holes_modulo`) and by no row isomorphism (`held_holes_not_rowIso`): an
isomorphism of frames that fixes the public hole cannot carry it to the other hole.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface.Frames (Frame)

universe uO uT uH uOcc

section Rows

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
variable {X : Frames Tm Hom} {P : Obj} {O : Type uOcc}

/-- **A row isomorphism modulo the knowledge relative to the escaped identities `E`**: an
isomorphism of frames, a renaming of occurrences that fixes `E`, knowledge carried to knowledge with
the same solutions, the present occurrences renamed, and every row and every public name carried to
its counterpart at every solution of the second state's knowledge (`Frames.Carried`, the clause the
escape-relative isomorphisms use for public terms, `Transport.EscapeIso`). -/
structure RowIsoModulo (E : Finset O) (s t : RowState X P O) where
  frame : X.Iso s.frame t.frame
  rename : O ≃ O
  fixes : ∀ o ∈ E, rename o = o
  knowledge : X.Equivalent (X.applyStore frame.hom s.knowledge) t.knowledge
  present : s.present.map rename.toEmbedding = t.present
  row : ∀ o, X.Carried frame.hom t.knowledge (s.row o) (t.row (rename o))
  fixesNames : ∀ u : Tm P, X.Carried frame.hom t.knowledge (X.act s.names u) (X.act t.names u)

namespace RowIsoModulo

variable {E : Finset O}

/-- **Solutions correspond**: a solution of the second state's knowledge, composed with the
isomorphism, solves the first state's knowledge. -/
theorem solution {s t : RowState X P O} (i : RowIsoModulo E s t) {b : Obj} {g : Hom t.frame b}
    (solved : X.Models g t.knowledge) : X.Models (X.comp g i.frame.hom) s.knowledge :=
  (Frames.models_applyStore i.frame.hom g s.knowledge).mp ((i.knowledge b g).mpr solved)

/-- **And back**: a solution of the first state's knowledge, composed with the inverse, solves the
second state's knowledge. -/
theorem solution_back {s t : RowState X P O} (i : RowIsoModulo E s t) {b : Obj} {g : Hom s.frame b}
    (solved : X.Models g s.knowledge) : X.Models (X.comp g i.frame.inv) t.knowledge := by
  refine (i.knowledge b _).mp ((Frames.models_applyStore i.frame.hom _ s.knowledge).mpr ?_)
  refine (Frames.models_congrE (fun u => ?_) s.knowledge).mpr solved
  simp only [X.act_comp]
  exact X.preserves g (i.frame.inv_hom u)

/-- **Rows correspond** at corresponding solutions. -/
theorem row_at {s t : RowState X P O} (i : RowIsoModulo E s t) {b : Obj} {g : Hom t.frame b}
    (solved : X.Models g t.knowledge) (o : O) :
    X.E (X.act (X.comp g i.frame.hom) (s.row o)) (X.act g (t.row (i.rename o))) := by
  rw [X.act_comp]
  exact i.row o b g solved

/-- **Public names correspond** at corresponding solutions. -/
theorem names_at {s t : RowState X P O} (i : RowIsoModulo E s t) {b : Obj} {g : Hom t.frame b}
    (solved : X.Models g t.knowledge) (u : Tm P) :
    X.E (X.act (X.comp g i.frame.hom) (X.act s.names u)) (X.act g (X.act t.names u)) := by
  rw [X.act_comp]
  exact i.fixesNames u b g solved

/-- The identity. -/
def refl (s : RowState X P O) : RowIsoModulo E s s where
  frame := Frames.Iso.refl s.frame
  rename := Equiv.refl O
  fixes _ _ := rfl
  knowledge := Frames.Iso.equivalent_refl s.knowledge
  present := by simp
  row o b g _ := by
    show X.E (X.act g (X.act (X.id s.frame) (s.row o))) (X.act g (s.row o))
    rw [X.act_id]
    exact (X.equivalence b).refl _
  fixesNames u b g _ := by
    show X.E (X.act g (X.act (X.id s.frame) (X.act s.names u))) (X.act g (X.act s.names u))
    rw [X.act_id]
    exact (X.equivalence b).refl _

/-- The inverse. -/
def symm {s t : RowState X P O} (i : RowIsoModulo E s t) : RowIsoModulo E t s where
  frame := i.frame.symm
  rename := i.rename.symm
  fixes o member := by
    rw [Equiv.symm_apply_eq]
    exact (i.fixes o member).symm
  knowledge := i.frame.equivalent_symm i.knowledge
  present := by
    rw [← i.present, Finset.map_map, ← Equiv.trans_toEmbedding, Equiv.self_trans_symm]
    simp
  row o := by
    have carried := Frames.Carried.symm i.frame i.knowledge (i.row (i.rename.symm o))
    rwa [Equiv.apply_symm_apply] at carried
  fixesNames u := Frames.Carried.symm i.frame i.knowledge (i.fixesNames u)

/-- The composite. -/
def trans {s t u : RowState X P O} (i : RowIsoModulo E s t) (j : RowIsoModulo E t u) :
    RowIsoModulo E s u where
  frame := i.frame.trans j.frame
  rename := i.rename.trans j.rename
  fixes o member := by rw [Equiv.trans_apply, i.fixes o member, j.fixes o member]
  knowledge := Frames.Iso.equivalent_trans i.frame j.frame i.knowledge j.knowledge
  present := by rw [← j.present, ← i.present, Finset.map_map, Equiv.trans_toEmbedding]
  row o := Frames.Carried.trans j.knowledge (i.row o) (j.row (i.rename o))
  fixesNames w := Frames.Carried.trans j.knowledge (i.fixesNames w) (j.fixesNames w)

/-- **The accepted rows correspond** at corresponding solutions. -/
theorem accepted_at {s t : RowState X P O} (i : RowIsoModulo E s t) {b : Obj}
    (reader : Readout X b Bool) {g : Hom t.frame b} (solved : X.Models g t.knowledge) :
    t.accepted reader g = (s.accepted reader (X.comp g i.frame.hom)).map i.rename.toEmbedding := by
  ext x
  simp only [RowState.accepted, Finset.mem_filter, Finset.mem_map, Equiv.coe_toEmbedding,
    ← i.present]
  constructor
  · rintro ⟨⟨o, member, rfl⟩, hit⟩
    exact ⟨o, ⟨member, (reader.respects (i.row_at solved o)).trans hit⟩, rfl⟩
  · rintro ⟨o, ⟨member, hit⟩, rfl⟩
    exact ⟨⟨o, member, rfl⟩, (reader.respects (i.row_at solved o)).symm.trans hit⟩

/-- **Clients respect row isomorphisms modulo the knowledge, in one direction.** -/
theorem observes {s t : RowState X P O} (i : RowIsoModulo E s t) {p : FrameProbe X P O}
    (named : p.names ⊆ E) (observed : p.Observes s) : p.Observes t := by
  cases p with
  | present reference =>
      have fixed := i.fixes reference (named (Finset.mem_singleton_self reference))
      show reference ∈ t.present
      rw [← i.present]
      exact Finset.mem_map.mpr ⟨reference, observed, fixed⟩
  | test reference reader =>
      have fixed := i.fixes reference (named (Finset.mem_singleton_self reference))
      intro b g solved
      have read := observed b (X.comp g i.frame.hom) (i.solution solved)
      have same := (reader b).respects (i.row_at solved reference)
      rw [fixed] at same
      exact same.symm.trans read
  | count reader number =>
      intro b g solved
      rw [i.accepted_at (reader b) solved, Finset.card_map]
      exact observed b (X.comp g i.frame.hom) (i.solution solved)
  | query reader seen =>
      intro b g solved
      rw [i.accepted_at (reader b) solved, observed b (X.comp g i.frame.hom) (i.solution solved)]
      exact Observation.finset_map_eq_self i.rename fun o member => i.fixes o (named member)
  | equal reference term =>
      have fixed := i.fixes reference (named (Finset.mem_singleton_self reference))
      intro b g solved
      have held := observed b (X.comp g i.frame.hom) (i.solution solved)
      have rows := i.row_at solved reference
      rw [fixed] at rows
      exact (X.equivalence b).trans ((X.equivalence b).symm rows)
        ((X.equivalence b).trans held (i.names_at solved term))

end RowIsoModulo

/-- **One frame, one knowledge, rows the knowledge entails equal**: the identity relates the two
states modulo the knowledge. -/
def RowIsoModulo.ofEntailed {E : Finset O} (a : Obj) (K : EquationStore (Tm a)) (present : Finset O)
    (row row' : O → Tm a) (names : Hom P a)
    (entailed : ∀ o, X.Entails K fun _ g => X.E (X.act g (row o)) (X.act g (row' o))) :
    RowIsoModulo E (⟨a, K, present, row, names⟩ : RowState X P O) ⟨a, K, present, row', names⟩ where
  frame := Frames.Iso.refl a
  rename := Equiv.refl O
  fixes _ _ := rfl
  knowledge := Frames.Iso.equivalent_refl K
  present := by simp
  row o b g solved := by
    show X.E (X.act g (X.act (X.id a) (row o))) (X.act g (row' o))
    rw [X.act_id]
    exact entailed o b g solved
  fixesNames u b g _ := by
    show X.E (X.act g (X.act (X.id a) (X.act names u))) (X.act g (X.act names u))
    rw [X.act_id]
    exact (X.equivalence b).refl _

/-- **Row isomorphisms are row isomorphisms modulo the knowledge.** -/
def RowIso.modulo {E : Finset O} {s t : RowState X P O} (i : RowIso E s t) : RowIsoModulo E s t where
  frame := i.frame
  rename := i.rename
  fixes := i.fixes
  knowledge := i.knowledge
  present := i.present
  row o _ g _ := X.preserves g (i.row o)
  fixesNames u _ g _ := X.preserves g (i.fixesNames u)

/-- Row states related by a row isomorphism modulo the knowledge. -/
def RowEquivalentModulo (E : Finset O) (s t : RowState X P O) : Prop := Nonempty (RowIsoModulo E s t)

theorem rowEquivalentModulo_equivalence (E : Finset O) :
    Equivalence (RowEquivalentModulo (X := X) (P := P) E) :=
  ⟨fun s => ⟨RowIsoModulo.refl s⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩⟩

/-- **Clients respect row isomorphisms modulo the knowledge.** -/
theorem FrameProbe.observes_iff_modulo {E : Finset O} {s t : RowState X P O}
    (i : RowIsoModulo E s t) {p : FrameProbe X P O} (named : p.names ⊆ E) :
    p.Observes s ↔ p.Observes t :=
  ⟨i.observes named, i.symm.observes named⟩

end Rows

/-! ## The run layer is the one-frame case -/

section OneFrame

variable {T : Type uT} {S : Type uH} {O : Type uOcc}
  (A : SubstitutionAction T S) (label : O → T)

/-- **A renaming up to the knowledge gives a row isomorphism modulo the knowledge.** -/
def rowIsoModulo_of_renaming {E : Finset O} {C D : Configuration T O} {π : O ≃ O}
    (k : Observation.RenamingUpTo (Observation.entailedSetoid A C.equations) label E π)
    (same : GuardFreeProcessOrders.SameUpTo A (AnnotatedRuns.renameConfiguration π C) D) :
    RowIsoModulo E (ofConfiguration A label C) (ofConfiguration A label D) where
  frame := Frames.Iso.refl PUnit.unit
  rename := π
  fixes := k.fixes
  knowledge := by
    intro b σ
    show (Frames.ofSubstitution A).Models σ ((Frames.ofSubstitution A).applyStore
      (A.identity) C.equations) ↔ A.Models σ D.equations
    rw [show (Frames.ofSubstitution A).applyStore A.identity C.equations = C.equations from
      Frames.applyStore_id (X := Frames.ofSubstitution A) (a := PUnit.unit) C.equations]
    exact same.1 σ
  present := same.2
  row o b σ solved := by
    show A.E (A.apply σ (A.apply A.identity (label o))) (A.apply σ (label (π o)))
    rw [A.apply_identity]
    have entailed : Observation.Entailed A C.equations (label (π o)) (label o) := k.keeps o
    exact A.equivalence.symm (entailed σ ((same.1 σ).mpr solved))
  fixesNames u b σ _ := by
    show A.E (A.apply σ (A.apply A.identity (A.apply A.identity u)))
      (A.apply σ (A.apply A.identity u))
    rw [A.apply_identity]
    exact A.equivalence.refl _

theorem rowEquivalentModulo_of_moduloEquivalent [DecidableEq O] {E : Finset O}
    {C D : Configuration T O} (h : Observation.ModuloEquivalent A label E C D) :
    RowEquivalentModulo E (ofConfiguration A label C) (ofConfiguration A label D) := by
  obtain ⟨π, k, same⟩ := h
  exact ⟨rowIsoModulo_of_renaming A label k same⟩

end OneFrame

/-! ## Control: a public hole, rows modulo the knowledge -/

namespace FrameModuloControls

open Mettapedia.OSLF.Binding.HereditaryBetaEtaObject
open FrameNameControls (twins holes hole hole_injective named publicHole publicTerm publicTerm_read)

/-- The knowledge that the two holes are equal. -/
def holesMeet : EquationStore (Observation sig twins) := [(hole true, hole false)]

/-- A state at the two holes holding the hole `b`, the first hole public, under `holesMeet`. -/
def knownHole (b : Bool) : RowState (Frames.contextual sig) named Unit :=
  ⟨holes, holesMeet, {()}, fun _ => hole b, publicHole⟩

/-- **The two states are related modulo the knowledge**, by the identity of frames, even for a client
that holds the row and knows the public hole. -/
def held_holes_modulo : RowIsoModulo ({()} : Finset Unit) (knownHole true) (knownHole false) := by
  unfold knownHole
  exact RowIsoModulo.ofEntailed (X := Frames.contextual sig) holes holesMeet {()} (fun _ => hole true)
    (fun _ => hole false) publicHole fun _ _ _ solved => solved (hole true, hole false) (List.mem_singleton_self _)

/-- **No row isomorphism relates them**: one that fixes the public hole cannot carry it to the other
hole. -/
theorem held_holes_not_rowIso :
    ¬ Nonempty (RowIso (∅ : Finset Unit) (knownHole true) (knownHole false)) := by
  rintro ⟨i⟩
  have fixed : instantiateObservation i.frame.hom (instantiateObservation publicHole publicTerm) =
      instantiateObservation publicHole publicTerm := i.fixesNames publicTerm
  have row : instantiateObservation i.frame.hom (hole true) = hole false := i.row ()
  rw [publicTerm_read] at fixed
  exact hole_injective (row.symm.trans fixed)

/-- **The client holding the row and knowing the public hole observes the same at both.** -/
theorem public_probe_agrees :
    (FrameProbe.equal () publicTerm : FrameProbe (Frames.contextual sig) named Unit).Observes
        (knownHole true) ↔
      (FrameProbe.equal () publicTerm : FrameProbe (Frames.contextual sig) named Unit).Observes
        (knownHole false) :=
  FrameProbe.observes_iff_modulo held_holes_modulo (by simp [FrameProbe.names])

end FrameModuloControls

#print axioms RowIsoModulo.solution
#print axioms RowIsoModulo.solution_back
#print axioms RowIsoModulo.symm
#print axioms RowIsoModulo.trans
#print axioms RowIsoModulo.accepted_at
#print axioms RowIsoModulo.observes
#print axioms RowIso.modulo
#print axioms RowIsoModulo.ofEntailed
#print axioms rowEquivalentModulo_equivalence
#print axioms FrameProbe.observes_iff_modulo
#print axioms rowIsoModulo_of_renaming
#print axioms rowEquivalentModulo_of_moduloEquivalent
#print axioms FrameModuloControls.held_holes_modulo
#print axioms FrameModuloControls.held_holes_not_rowIso
#print axioms FrameModuloControls.public_probe_agrees

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
