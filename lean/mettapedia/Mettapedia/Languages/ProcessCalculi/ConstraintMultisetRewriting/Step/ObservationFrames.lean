import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Observation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Transport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.BetaEtaReadings

/-!
# Client readouts respect the frame equivalence

A frame category relates terms by its equivalence `X.E`: equality on the canonical contextual
frames, object beta-eta conversion on the admitted frames (`BetaEtaReadings.admitted`). Once
states are compared up to that equivalence, a client's readout of stored data must not separate
equivalent terms. This module makes that an explicit client obligation and proves that clients who
meet it respect private renaming and frame isomorphism together.

## Readouts and stored rows

* **A readout** (`Readout`) at a frame is a function of its terms together with the obligation that
  it respects the frame's equivalence.
* **A row state** (`RowState`) has a frame, its knowledge, its present occurrences, a stored row at
  the frame for each occurrence, and the public names: a morphism into the frame from a fixed frame
  of names that clients know.
* **A row isomorphism relative to escaped identities `E`** (`RowIso`): an isomorphism of frames, a
  renaming of occurrences that fixes `E`, knowledge carried to knowledge with the same solutions, the
  present occurrences renamed, every row carried to the renamed occurrence's row up to the frame
  equivalence, and every public name carried to itself up to the frame equivalence. Row
  isomorphisms form a groupoid (`RowIso.refl`, `symm`, `trans`).

## Clients respect it

A **frame probe** (`FrameProbe`) asks whether a held reference is present; tests the row of a held
reference with a readout at every solution; counts the rows a readout accepts; asks that the rows a
readout accepts are exactly the identities seen; or asks that the row of a held reference equals a
term over the public names. Its names are the references and the identities seen.

* **Clients respect row isomorphisms** (`FrameProbe.observes_iff`): a probe that names only escaped
  identities observes the same at isomorphic row states. Solutions correspond by composing with the
  isomorphism (`RowIso.solution`), rows by the frame equivalence (`RowIso.row_at`), and each readout
  gives equal values on equivalent rows.

## The canonical frames discharge the obligation; the admitted frames do not

* **On the contextual frames every function is a readout** (`Readout.contextual`), since the frame
  equivalence is equality: the respect theorem holds for every client
  (`contextual_test_respects`).
* **On the admitted frames the head of stored data is not a readout** (`head_not_readout`). The
  stored redex and its reduct give two row states that are isomorphic for the admitted frames
  (`redex_reduct_isomorphic_admitted`), and the head test separates them at a common solution
  (`head_separates_admitted`); on the contextual frames the same two states are not isomorphic
  (`redex_reduct_not_isomorphic_contextual`), so the head test separates nothing that should be
  identified there.

## Frame names: private ones are renamed, public ones are fixed

Two holes of one arity can be swapped by an isomorphism of frames (`FrameNameControls.swapIso`).
With no public names, the swap relates the state whose row is the first hole to the state whose
row is the second (`FrameNameControls.private_holes`), as R45's helper diamond closes up to renaming
fresh helpers. When the first hole is a public name, the swap moves it
(`FrameNameControls.swap_moves_public`), and a client holding the row and knowing the name separates
the two states, so no row isomorphism relates them (`FrameNameControls.public_name_separates`).

## The run layer is the one-frame case

A configuration with its labels as rows is a row state over the one-frame category of its
substitution action (`ofConfiguration`). Private equivalence of configurations gives a row
isomorphism (`rowIso_of_renaming`, `rowEquivalent_of_privatelyEquivalent`), so clients that meet the obligation respect it as
well. The run layer's own respect theorem (`Observation.PrivatelyEquivalent.observes`) needs no
obligation: there, rows are related by equality of labels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface.Frames (Frame)

universe uO uT uH uOcc uV

section Rows

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-- **A readout of stored terms at a frame**, with the client obligation: equivalent terms read
the same. -/
structure Readout (X : Frames Tm Hom) (a : Obj) (V : Type uV) where
  read : Tm a → V
  respects : ∀ {s t : Tm a}, X.E s t → read s = read t

variable {X : Frames Tm Hom} {P : Obj} {O : Type uOcc}

/-- **A row state**: a frame, its knowledge, its present occurrences, a stored row at the frame for
each occurrence, and the public names, read in the frame. -/
structure RowState (X : Frames Tm Hom) (P : Obj) (O : Type uOcc) where
  frame : Obj
  knowledge : EquationStore (Tm frame)
  present : Finset O
  row : O → Tm frame
  names : Hom P frame


/-- **A row isomorphism relative to the escaped identities `E`.** -/
structure RowIso (E : Finset O) (s t : RowState X P O) where
  frame : X.Iso s.frame t.frame
  rename : O ≃ O
  fixes : ∀ o ∈ E, rename o = o
  knowledge : X.Equivalent (X.applyStore frame.hom s.knowledge) t.knowledge
  present : s.present.map rename.toEmbedding = t.present
  row : ∀ o, X.E (X.act frame.hom (s.row o)) (t.row (rename o))
  fixesNames : ∀ u : Tm P, X.E (X.act frame.hom (X.act s.names u)) (X.act t.names u)

namespace RowIso

variable {E : Finset O}

/-- The identity. -/
def refl (s : RowState X P O) : RowIso E s s where
  frame := Frames.Iso.refl s.frame
  rename := Equiv.refl O
  fixes _ _ := rfl
  knowledge := Frames.Iso.equivalent_refl s.knowledge
  present := by simp
  row o := by
    show X.E (X.act (X.id s.frame) (s.row o)) (s.row o)
    rw [X.act_id]
    exact (X.equivalence _).refl _
  fixesNames u := by
    show X.E (X.act (X.id s.frame) (X.act s.names u)) (X.act s.names u)
    rw [X.act_id]
    exact (X.equivalence _).refl _

/-- The inverse. -/
def symm {s t : RowState X P O} (i : RowIso E s t) : RowIso E t s where
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
    have carried := i.row (i.rename.symm o)
    rw [Equiv.apply_symm_apply] at carried
    show X.E (X.act i.frame.inv (t.row o)) (s.row (i.rename.symm o))
    exact (X.equivalence _).trans ((X.equivalence _).symm (X.preserves i.frame.inv carried))
      (i.frame.inv_hom _)
  fixesNames u := by
    show X.E (X.act i.frame.inv (X.act t.names u)) (X.act s.names u)
    exact (X.equivalence _).trans ((X.equivalence _).symm (X.preserves i.frame.inv (i.fixesNames u)))
      (i.frame.inv_hom _)

/-- The composite. -/
def trans {s t u : RowState X P O} (i : RowIso E s t) (j : RowIso E t u) : RowIso E s u where
  frame := i.frame.trans j.frame
  rename := i.rename.trans j.rename
  fixes o member := by rw [Equiv.trans_apply, i.fixes o member, j.fixes o member]
  knowledge := Frames.Iso.equivalent_trans i.frame j.frame i.knowledge j.knowledge
  present := by rw [← j.present, ← i.present, Finset.map_map, Equiv.trans_toEmbedding]
  row o := by
    show X.E (X.act (X.comp j.frame.hom i.frame.hom) (s.row o)) (u.row (j.rename (i.rename o)))
    rw [X.act_comp]
    exact (X.equivalence _).trans (X.preserves j.frame.hom (i.row o)) (j.row (i.rename o))
  fixesNames w := by
    show X.E (X.act (X.comp j.frame.hom i.frame.hom) (X.act s.names w)) (X.act u.names w)
    rw [X.act_comp]
    exact (X.equivalence _).trans (X.preserves j.frame.hom (i.fixesNames w)) (j.fixesNames w)

/-- **Solutions correspond**: a solution of the second state's knowledge, composed with the
isomorphism, solves the first state's knowledge. -/
theorem solution {s t : RowState X P O} (i : RowIso E s t) {b : Obj} {g : Hom t.frame b}
    (solved : X.Models g t.knowledge) : X.Models (X.comp g i.frame.hom) s.knowledge :=
  (Frames.models_applyStore i.frame.hom g s.knowledge).mp ((i.knowledge b g).mpr solved)

/-- **Rows correspond** at corresponding solutions, up to the frame equivalence. -/
theorem row_at {s t : RowState X P O} (i : RowIso E s t) {b : Obj} (g : Hom t.frame b) (o : O) :
    X.E (X.act (X.comp g i.frame.hom) (s.row o)) (X.act g (t.row (i.rename o))) := by
  rw [X.act_comp]
  exact X.preserves g (i.row o)

/-- **Public names correspond** at corresponding solutions. -/
theorem names_at {s t : RowState X P O} (i : RowIso E s t) {b : Obj} (g : Hom t.frame b)
    (u : Tm P) :
    X.E (X.act (X.comp g i.frame.hom) (X.act s.names u)) (X.act g (X.act t.names u)) := by
  rw [X.act_comp]
  exact X.preserves g (i.fixesNames u)

end RowIso

/-- Row states related by a row isomorphism. -/
def RowEquivalent (E : Finset O) (s t : RowState X P O) : Prop := Nonempty (RowIso E s t)

theorem rowEquivalent_equivalence (E : Finset O) :
    Equivalence (RowEquivalent (X := X) (P := P) E) :=
  ⟨fun s => ⟨RowIso.refl s⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩⟩

/-! ## Clients -/

/-- **A frame probe**: whether a held reference is present; a test of its row with a readout at
every solution; the number of rows a readout accepts; that the rows a readout accepts are exactly
the identities seen; or that the row of a held reference equals a term over the public names. -/
inductive FrameProbe (X : Frames Tm Hom) (P : Obj) (O : Type uOcc) where
  | present (reference : O)
  | test (reference : O) (reader : (b : Obj) → Readout X b Bool)
  | count (reader : (b : Obj) → Readout X b Bool) (number : ℕ)
  | query (reader : (b : Obj) → Readout X b Bool) (seen : Finset O)
  | equal (reference : O) (term : Tm P)

/-- The occurrences whose rows a readout accepts at a solution. -/
def RowState.accepted (s : RowState X P O) {b : Obj} (reader : Readout X b Bool)
    (f : Hom s.frame b) : Finset O :=
  s.present.filter fun o => reader.read (X.act f (s.row o)) = true

namespace FrameProbe

/-- The identities a frame probe names. -/
def names : FrameProbe X P O → Finset O
  | present reference => {reference}
  | test reference _ => {reference}
  | count _ _ => ∅
  | query _ seen => seen
  | equal reference _ => {reference}

/-- **What a frame probe observes at a row state.** -/
def Observes : FrameProbe X P O → RowState X P O → Prop
  | present reference, s => reference ∈ s.present
  | test reference reader, s =>
      X.Entails s.knowledge fun b f => (reader b).read (X.act f (s.row reference)) = true
  | count reader number, s =>
      X.Entails s.knowledge fun b f => (s.accepted (reader b) f).card = number
  | query reader seen, s => X.Entails s.knowledge fun b f => s.accepted (reader b) f = seen
  | equal reference term, s =>
      X.Entails s.knowledge fun _ f => X.E (X.act f (s.row reference)) (X.act f (X.act s.names term))

end FrameProbe

namespace RowIso

variable {E : Finset O}

/-- **The accepted rows correspond**: at corresponding solutions, the rows a readout accepts at the
second state are the renamed rows it accepts at the first. -/
theorem accepted_at {s t : RowState X P O} (i : RowIso E s t) {b : Obj} (reader : Readout X b Bool)
    (g : Hom t.frame b) :
    t.accepted reader g = (s.accepted reader (X.comp g i.frame.hom)).map i.rename.toEmbedding := by
  ext x
  simp only [RowState.accepted, Finset.mem_filter, Finset.mem_map, Equiv.coe_toEmbedding,
    ← i.present]
  constructor
  · rintro ⟨⟨o, member, rfl⟩, hit⟩
    exact ⟨o, ⟨member, (reader.respects (i.row_at g o)).trans hit⟩, rfl⟩
  · rintro ⟨o, ⟨member, hit⟩, rfl⟩
    exact ⟨⟨o, member, rfl⟩, (reader.respects (i.row_at g o)).symm.trans hit⟩

/-- **Clients respect row isomorphisms, in one direction.** -/
theorem observes {s t : RowState X P O} (i : RowIso E s t) {p : FrameProbe X P O}
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
      have same := (reader b).respects (i.row_at g reference)
      rw [fixed] at same
      exact same.symm.trans read
  | count reader number =>
      intro b g solved
      rw [i.accepted_at (reader b) g, Finset.card_map]
      exact observed b (X.comp g i.frame.hom) (i.solution solved)
  | query reader seen =>
      intro b g solved
      rw [i.accepted_at (reader b) g, observed b (X.comp g i.frame.hom) (i.solution solved)]
      exact Observation.finset_map_eq_self i.rename fun o member => i.fixes o (named member)
  | equal reference term =>
      have fixed := i.fixes reference (named (Finset.mem_singleton_self reference))
      intro b g solved
      have held := observed b (X.comp g i.frame.hom) (i.solution solved)
      have rows := i.row_at g reference
      rw [fixed] at rows
      exact (X.equivalence b).trans ((X.equivalence b).symm rows)
        ((X.equivalence b).trans held (i.names_at g term))

end RowIso

/-- **Clients respect row isomorphisms**: a frame probe that names only escaped identities observes
the same at row states isomorphic relative to those identities. -/
theorem FrameProbe.observes_iff {E : Finset O} {s t : RowState X P O} (i : RowIso E s t)
    {p : FrameProbe X P O} (named : p.names ⊆ E) : p.Observes s ↔ p.Observes t :=
  ⟨i.observes named, i.symm.observes named⟩

end Rows

/-! ## The canonical frames discharge the obligation -/

section Canonical

variable {S : Signature}

/-- **On the contextual frames every function of terms is a readout**: the frame equivalence is
equality. -/
def Readout.contextual {F : Frame S} {V : Type uV} (read : Observation S F.arity → V) :
    Readout (Frames.contextual S) F V :=
  ⟨read, fun same => congrArg read same⟩

/-- **The respect theorem for the canonical frames**: every client test of a held row, by any
function at every later frame, observes the same at isomorphic row states. -/
theorem contextual_test_respects {P : Frame S} {O : Type uOcc} {E : Finset O}
    {s t : RowState (Frames.contextual S) P O} (i : RowIso E s t) {reference : O}
    (held : reference ∈ E) (read : (b : Frame S) → Observation S b.arity → Bool) :
    (FrameProbe.test reference fun b => Readout.contextual (read b)).Observes s ↔
      (FrameProbe.test reference fun b => Readout.contextual (read b)).Observes t :=
  FrameProbe.observes_iff i (by simpa [FrameProbe.names] using held)

end Canonical

/-! ## The admitted frames: the head of stored data is not a readout -/

namespace AdmittedControls

open BetaEtaReadings
open Mettapedia.OSLF.Binding.HereditaryBetaEtaObject

/-- The frame without names. -/
abbrev bare : Frame sig := ⟨Empty, closed⟩

/-- **The head of stored data is not a readout of the admitted frames.** -/
theorem head_not_readout :
    ¬ ∃ reader : Readout admitted bare Bool, ∀ t, reader.read t = StoredRedex.isApplication t := by
  rintro ⟨reader, same⟩
  obtain ⟨related, differ⟩ := StoredRedex.head_readout_not_invariant
  apply differ
  rw [← same, ← same]
  exact reader.respects related

/-- A state whose one row is the given observation, over the frames `X`. -/
def stored (X : Frames (fun F : Frame sig => Observation sig F.arity)
      (fun F G : Frame sig => Assignment F.arity G.arity))
    (row : Observation sig closed) : RowState X bare Unit :=
  ⟨bare, [], {()}, fun _ => row, X.id bare⟩

/-- **For the admitted frames, the stored redex and its reduct are isomorphic row states.** -/
def redex_reduct_isomorphic_admitted :
    RowIso (∅ : Finset Unit) (stored admitted (observe StoredRedex.redex))
      (stored admitted (observe StoredRedex.reduct)) where
  frame := Frames.Iso.refl bare
  rename := Equiv.refl Unit
  fixes _ member := absurd member (Finset.notMem_empty _)
  knowledge := Frames.Iso.equivalent_refl (X := admitted) (a := bare) []
  present := by simp [stored]
  row _ := by
    show ObservedConv (instantiateObservation (generator closed) (observe StoredRedex.redex))
      (observe StoredRedex.reduct)
    rw [instantiateObservation_identity]
    exact .mk StoredRedex.converts
  fixesNames u := by
    show ObservedConv (instantiateObservation (generator closed)
      (instantiateObservation (generator closed) u)) (instantiateObservation (generator closed) u)
    rw [instantiateObservation_identity]
    exact ObservedConv.refl _

/-- **The head test separates them at a common solution.** -/
theorem head_separates_admitted :
    StoredRedex.isApplication (admitted.act (admitted.id bare)
        ((stored admitted (observe StoredRedex.redex)).row ())) = true ∧
      StoredRedex.isApplication (admitted.act (admitted.id bare)
        ((stored admitted (observe StoredRedex.reduct)).row ())) = false := by
  refine ⟨?_, ?_⟩
  · show StoredRedex.isApplication (instantiateObservation (generator closed) (observe StoredRedex.redex)) = true
    rw [instantiateObservation_identity]
    rfl
  · show StoredRedex.isApplication (instantiateObservation (generator closed) (observe StoredRedex.reduct)) = false
    rw [instantiateObservation_identity]
    rfl

/-- **On the contextual frames the same two states are not isomorphic**: a closed stored term is
fixed by every morphism, and the redex is not its reduct. -/
theorem redex_reduct_not_isomorphic_contextual :
    ¬ Nonempty (RowIso (∅ : Finset Unit) (stored (Frames.contextual sig) (observe StoredRedex.redex))
      (stored (Frames.contextual sig) (observe StoredRedex.reduct))) := by
  rintro ⟨i⟩
  have closedFixed : ∀ φ : Assignment closed closed,
      instantiateObservation φ (observe StoredRedex.redex) ≠ observe StoredRedex.reduct := by
    intro φ rows
    rw [instantiateObservation_observe,
      instantiate_eq_of_noMeta StoredRedex.redex (by rfl) φ (generator closed), instantiate_identity] at rows
    exact StoredRedex.distinct (observe_injective rows)
  exact closedFixed i.frame.hom (i.row ())

end AdmittedControls

/-! ## Frame names: private ones are renamed, public ones are fixed -/

namespace FrameNameControls

open BetaEtaReadings (closed)
open Mettapedia.OSLF.Binding.HereditaryBetaEtaObject

/-- Two parameterless holes of the base sort. -/
def twins : Bool → MetaArity sig := fun _ => ([], .base)

/-- The frame of the two holes. -/
abbrev holes : Frame sig := ⟨Bool, twins⟩

/-- The hole `b`, as stored data. -/
def hole (b : Bool) : Observation sig twins := observe (generator twins b)

/-- Which hole heads an observation. -/
def whichHole : Observation sig twins → Bool
  | ⟨_, _, .op (.inr (.mk b)) _⟩ => b
  | _ => false

theorem hole_injective : hole false ≠ hole true := fun same => by
  have heads := congrArg whichHole same
  exact absurd heads (by decide)

/-- Swapping the two holes. -/
def swapHoles : Assignment twins twins := fun b => generator twins (!b)

theorem swapHoles_swapHoles : Assignment.compose swapHoles swapHoles = generator twins := by
  funext b
  show instantiate swapHoles (generator twins (!b)) = generator twins b
  rw [instantiate_generator]
  cases b <;> rfl

/-- **Swapping the holes is an isomorphism of frames.** -/
def swapIso : (Frames.contextual sig).Iso holes holes where
  hom := swapHoles
  inv := swapHoles
  inv_hom t := by
    show instantiateObservation swapHoles (instantiateObservation swapHoles t) = t
    rw [instantiateObservation_comp, swapHoles_swapHoles, instantiateObservation_identity]
  hom_inv t := by
    show instantiateObservation swapHoles (instantiateObservation swapHoles t) = t
    rw [instantiateObservation_comp, swapHoles_swapHoles, instantiateObservation_identity]

theorem swap_hole (b : Bool) : instantiateObservation swapHoles (hole b) = hole (!b) := by
  rw [hole, instantiateObservation_observe, instantiate_generator]
  rfl

/-- A state at the two holes whose one row is the hole `b`, with the given public names. -/
def heldHole {P : Frame sig} (names : Assignment P.arity twins) (b : Bool) :
    RowState (Frames.contextual sig) P Unit :=
  ⟨holes, [], {()}, fun _ => hole b, names⟩

/-- No public names. -/
def noNames : Assignment closed twins := fun impossible => impossible.elim

/-- **Private frame names are renamed freely**: with no public names, swapping the holes relates the
state holding the hole `true` to the state holding the hole `false`. -/
def private_holes :
    RowIso (∅ : Finset Unit) (heldHole (P := ⟨Empty, closed⟩) noNames true) (heldHole noNames false) where
  frame := swapIso
  rename := Equiv.refl Unit
  fixes _ member := absurd member (Finset.notMem_empty _)
  knowledge _ _ := Iff.rfl
  present := by simp [heldHole]
  row _ := swap_hole true
  fixesNames u := by
    show instantiateObservation swapHoles (instantiateObservation noNames u) =
      instantiateObservation noNames u
    rw [instantiateObservation_comp]
    congr 1
    funext impossible
    exact impossible.elim

/-- One public name. -/
abbrev named : Frame sig := ⟨Unit, fun _ => ([], .base)⟩

/-- The public name is the hole `true`. -/
def publicHole : Assignment named.arity twins := fun _ => generator twins true

/-- The public name, as a term of the public frame. -/
def publicTerm : Observation sig named.arity := observe (generator named.arity ())

theorem publicTerm_read : instantiateObservation publicHole publicTerm = hole true := by
  rw [publicTerm, instantiateObservation_observe, instantiate_generator]
  rfl

/-- **The swap moves the public name**: it is the only field of a row isomorphism it fails. -/
theorem swap_moves_public :
    instantiateObservation swapHoles (instantiateObservation publicHole publicTerm) ≠
      instantiateObservation publicHole publicTerm := by
  rw [publicTerm_read, swap_hole]
  exact hole_injective

/-- The probe of a client holding the row and knowing the public name. -/
def publicProbe : FrameProbe (Frames.contextual sig) named Unit := .equal () publicTerm

/-- **A client that knows the public name separates the two states**: the row of its held
reference equals the public name at every solution in the first state, and not in the second. -/
theorem public_name_separates :
    publicProbe.Observes (heldHole publicHole true) ∧
      ¬ publicProbe.Observes (heldHole publicHole false) ∧
      ¬ Nonempty (RowIso {()} (heldHole publicHole true) (heldHole publicHole false)) := by
  have first : publicProbe.Observes (heldHole publicHole true) := by
    intro b f _
    have read : ∀ g : Assignment twins b.arity, instantiateObservation g (hole true) =
        instantiateObservation g (instantiateObservation publicHole publicTerm) := fun g => by
      rw [publicTerm_read]
    exact read f
  have second : ¬ publicProbe.Observes (heldHole publicHole false) := by
    intro observed
    have atIdentity := observed holes (generator twins) (Frames.models_nil _)
    change instantiateObservation (generator twins) (hole false) =
      instantiateObservation (generator twins) (instantiateObservation publicHole publicTerm)
      at atIdentity
    rw [instantiateObservation_identity, instantiateObservation_identity, publicTerm_read]
      at atIdentity
    exact hole_injective atIdentity
  refine ⟨first, second, fun ⟨i⟩ => second ((FrameProbe.observes_iff i ?_).mp first)⟩
  intro o member
  exact member

end FrameNameControls

/-! ## The run layer is the one-frame case -/

section OneFrame

variable {T : Type uT} {S : Type uH} {O : Type uOcc}
  (A : SubstitutionAction T S) (label : O → T)

/-- **A configuration as a row state** over the one-frame category of its substitution action: its
labels are its rows. -/
def ofConfiguration (C : Configuration T O) : RowState (Frames.ofSubstitution A) PUnit.unit O :=
  ⟨PUnit.unit, C.equations, C.present, label, A.identity⟩

/-- **Private equivalence gives a row isomorphism.** -/
def rowIso_of_renaming {E : Finset O} {C D : Configuration T O} {π : O ≃ O}
    (priv : Observation.PrivateRenaming label E π)
    (same : GuardFreeProcessOrders.SameUpTo A (AnnotatedRuns.renameConfiguration π C) D) :
    RowIso E (ofConfiguration A label C) (ofConfiguration A label D) where
  frame := Frames.Iso.refl PUnit.unit
  rename := π
  fixes := priv.fixes
  knowledge := by
    intro b σ
    show (Frames.ofSubstitution A).Models σ ((Frames.ofSubstitution A).applyStore
      (A.identity) C.equations) ↔ A.Models σ D.equations
    rw [show (Frames.ofSubstitution A).applyStore A.identity C.equations = C.equations from
      Frames.applyStore_id (X := Frames.ofSubstitution A) (a := PUnit.unit) C.equations]
    exact same.1 σ
  present := same.2
  row o := by
    show A.E (A.apply A.identity (label o)) (label (π o))
    rw [A.apply_identity, priv.keeps]
    exact A.equivalence.refl _
  fixesNames u := by
    show A.E (A.apply A.identity (A.apply A.identity u)) (A.apply A.identity u)
    rw [A.apply_identity]
    exact A.equivalence.refl _

theorem rowEquivalent_of_privatelyEquivalent {E : Finset O} {C D : Configuration T O}
    (h : Observation.PrivatelyEquivalent A label E C D) :
    RowEquivalent E (ofConfiguration A label C) (ofConfiguration A label D) := by
  obtain ⟨π, priv, same⟩ := h
  exact ⟨rowIso_of_renaming A label priv same⟩

end OneFrame

#print axioms RowIso.symm
#print axioms RowIso.trans
#print axioms RowIso.solution
#print axioms RowIso.row_at
#print axioms rowEquivalent_equivalence
#print axioms RowIso.accepted_at
#print axioms RowIso.observes
#print axioms FrameProbe.observes_iff
#print axioms contextual_test_respects
#print axioms AdmittedControls.head_not_readout
#print axioms AdmittedControls.redex_reduct_isomorphic_admitted
#print axioms AdmittedControls.head_separates_admitted
#print axioms AdmittedControls.redex_reduct_not_isomorphic_contextual
#print axioms FrameNameControls.swapIso
#print axioms FrameNameControls.private_holes
#print axioms FrameNameControls.swap_moves_public
#print axioms FrameNameControls.public_name_separates
#print axioms rowIso_of_renaming
#print axioms rowEquivalent_of_privatelyEquivalent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
