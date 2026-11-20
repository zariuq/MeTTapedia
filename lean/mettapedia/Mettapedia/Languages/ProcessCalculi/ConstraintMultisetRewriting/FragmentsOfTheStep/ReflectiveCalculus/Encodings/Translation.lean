import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Barbs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.ByInstantiation.Translation

/-!
# The translation of closed processes into states, as a function on syntax

## Parallel composition of states

The **tensor** of two states (`tensor`) puts them side by side: its frame is the coproduct of their
frames (the unknowns of each side are kept apart: the left ones by `weakenNames`, the right ones by
`canonicalOpening`), its knowledge is both knowledges carried along, and its rows are both stores with
the identities renamed apart (left to even numbers, right to odd numbers). It is total.

**Parallel composition is the tensor** (`tensor_represents`): two states that represent `P` and `Q`
put side by side represent every process whose canonical bag is the sum of theirs. This is the
earlier placement's union theorem (`ReflectiveCalculus.union_represents`) for the step defined by rule
syntax, with the coproduct of frames in place of the shared index space of unknowns.

## The translation

* `twin P`: the twin term of a closed process, computed by the existing translation on syntax
  (`ByInstantiation.toTwin`, total on closed processes), with `read (twin P) = P`.
* `encodeAt`: the null process is no row; a bag is the tensor of its components (a one-element bag is
  its component); every other process, an input, an output or the drop of quoted code, is one row
  (`single`).
* **`encode P`**: the state of a closed process. It represents `P` (`encode_represents`).
* **Parallel composition**: the source's own `P | Q` (`par`, the two-element bag) is sent to the
  tensor, on the nose (`encode_par`).
* **An input or an output is one row determined by the prefix**: the state with the one row of the
  communication rule's input pattern `input(X, K⟨y,p⟩)`, or of its output pattern `output(X, Q)`,
  filled by instantiation with the twin terms of the channel and of the continuation or payload
  (`encode_input`, `encode_output`). The holes are filled with twin terms, not with `encode` of the
  arguments: these are not Gorla's Property 1 for `encode`, which fails at output and input
  (`output_not_compositional`, `input_not_compositional`, in `Compositionality`).

## The single-row translation (a control)

`encodeRow P` is the state with the one row `twin P`. It represents `P` too (`encodeRow_represents`)
and is the form of Gorla's two-level encodings (a one-hole context, "the state with this row", filled
with a translation that is a homomorphism of the binding signatures, here `twin`). It is not
homomorphic on parallel composition (`encodeRow_not_homomorphic`): the image of `0 | 0` has one row,
and the tensor of the images has two.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (canonicalize)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open ByInstantiation (sig G Closed Similar ObsSimilar Grounding GroundSolves read inputT outputT zeroT
  bagT pnilT pconsT dropqT quoteT spine knowledge groundFrame someGrounding)
open Interface.Frames (Frame)

/-! ## The tensor of states -/

/-- Left identities go to even numbers. -/
def evenEmbedding : ℕ ↪ ℕ := ⟨fun o => 2 * o, fun a b same => by
  have twice : 2 * a = 2 * b := same
  omega⟩

/-- Right identities go to odd numbers. -/
def oddEmbedding : ℕ ↪ ℕ := ⟨fun o => 2 * o + 1, fun a b same => by
  have twice : 2 * a + 1 = 2 * b + 1 := same
  omega⟩

/-- The weakening of the left frame into the coproduct. -/
abbrev leftIn (F N : Frame sig) : Assignment F.arity (RuleSyntax.Contextual.extend sig F N).arity :=
  RuleSyntax.Contextual.weakenNames sig F N

/-- The weakening of the right frame into the coproduct. -/
abbrev rightIn (F N : Frame sig) : Assignment N.arity (RuleSyntax.Contextual.extend sig F N).arity :=
  RuleSyntax.Contextual.canonicalOpening sig F N

/-- **The tensor of two states**: the coproduct of their frames, both knowledges carried along, and
both stores, with the identities renamed apart. -/
@[reducible] def tensor (s t : ByInstantiation.State) : ByInstantiation.State where
  frame := RuleSyntax.Contextual.extend sig s.frame t.frame
  knowledge := knowledge.applyStore (leftIn s.frame t.frame) s.knowledge ++
    knowledge.applyStore (rightIn s.frame t.frame) t.knowledge
  present := s.present.map evenEmbedding ∪ t.present.map oddEmbedding
  label o := if o % 2 = 0 then knowledge.act (leftIn s.frame t.frame) (s.label (o / 2))
    else knowledge.act (rightIn s.frame t.frame) (t.label (o / 2))

/-- Values of the tensor: the left side's at even identities, the right side's at odd ones. -/
def tensorValue (left right : ℕ → G [] .pr) (o : ℕ) : G [] .pr :=
  if o % 2 = 0 then left (o / 2) else right (o / 2)

theorem evenEmbedding_apply (k : ℕ) : evenEmbedding k = 2 * k := rfl

theorem oddEmbedding_apply (k : ℕ) : oddEmbedding k = 2 * k + 1 := rfl

theorem mem_tensor {s t : ByInstantiation.State} {o : ℕ} :
    o ∈ (tensor s t).present ↔ (∃ k ∈ s.present, o = 2 * k) ∨ (∃ k ∈ t.present, o = 2 * k + 1) := by
  change o ∈ s.present.map evenEmbedding ∪ t.present.map oddEmbedding ↔ _
  rw [Finset.mem_union, Finset.mem_map, Finset.mem_map]
  constructor
  · rintro (⟨k, member, same⟩ | ⟨k, member, same⟩)
    · exact .inl ⟨k, member, by rw [← same, evenEmbedding_apply]⟩
    · exact .inr ⟨k, member, by rw [← same, oddEmbedding_apply]⟩
  · rintro (⟨k, member, rfl⟩ | ⟨k, member, rfl⟩)
    · exact .inl ⟨k, member, evenEmbedding_apply k⟩
    · exact .inr ⟨k, member, oddEmbedding_apply k⟩

theorem tensor_label_even (s t : ByInstantiation.State) (k : ℕ) :
    (tensor s t).label (2 * k) = knowledge.act (leftIn s.frame t.frame) (s.label k) := by
  simp [tensor]

theorem tensor_label_odd (s t : ByInstantiation.State) (k : ℕ) :
    (tensor s t).label (2 * k + 1) = knowledge.act (rightIn s.frame t.frame) (t.label k) := by
  have odd : (2 * k + 1) % 2 ≠ 0 := by omega
  have half : (2 * k + 1) / 2 = k := by omega
  simp only [tensor, odd, if_false, half]

theorem tensorValue_even (left right : ℕ → G [] .pr) (k : ℕ) :
    tensorValue left right (2 * k) = left k := by
  simp [tensorValue]

theorem tensorValue_odd (left right : ℕ → G [] .pr) (k : ℕ) :
    tensorValue left right (2 * k + 1) = right k := by
  have odd : (2 * k + 1) % 2 ≠ 0 := by omega
  have half : (2 * k + 1) / 2 = k := by omega
  simp only [tensorValue, odd, if_false, half]

/-- A grounding of the tensor solving its knowledge solves each side along its weakening. -/
theorem tensor_solves_left {s t : ByInstantiation.State}
    {g : Grounding (tensor s t).frame} (solved : GroundSolves g (tensor s t).knowledge) :
    GroundSolves (Assignment.compose g (leftIn s.frame t.frame)) s.knowledge := by
  intro e member
  have inside : (knowledge.act (leftIn s.frame t.frame) e.1, knowledge.act (leftIn s.frame t.frame) e.2)
      ∈ (tensor s t).knowledge :=
    List.mem_append_left _ (List.mem_map.mpr ⟨e, member, rfl⟩)
  have similar := solved _ inside
  change ObsSimilar (instantiateObservation g (instantiateObservation (leftIn s.frame t.frame) e.1))
    (instantiateObservation g (instantiateObservation (leftIn s.frame t.frame) e.2)) at similar
  rwa [instantiateObservation_comp, instantiateObservation_comp] at similar

theorem tensor_solves_right {s t : ByInstantiation.State}
    {g : Grounding (tensor s t).frame} (solved : GroundSolves g (tensor s t).knowledge) :
    GroundSolves (Assignment.compose g (rightIn s.frame t.frame)) t.knowledge := by
  intro e member
  have inside : (knowledge.act (rightIn s.frame t.frame) e.1, knowledge.act (rightIn s.frame t.frame) e.2)
      ∈ (tensor s t).knowledge :=
    List.mem_append_right _ (List.mem_map.mpr ⟨e, member, rfl⟩)
  have similar := solved _ inside
  change ObsSimilar (instantiateObservation g (instantiateObservation (rightIn s.frame t.frame) e.1))
    (instantiateObservation g (instantiateObservation (rightIn s.frame t.frame) e.2)) at similar
  rwa [instantiateObservation_comp, instantiateObservation_comp] at similar

/-- A state represents every process with the same canonical bag. -/
theorem RepresentsBy.of_bag {s : ByInstantiation.State} {P Q : RhoProcess} {value : ℕ → G [] .pr}
    (represented : ByInstantiation.RepresentsBy s P value)
    (same : (fromProcess P).1 = (fromProcess Q).1) : ByInstantiation.RepresentsBy s Q value :=
  ⟨represented.solvable, represented.determined, represented.closed,
    represented.inventory_eq.trans same⟩

/-- **Parallel composition is the tensor**: two states that represent `P` and `Q` represent, side by
side, every process whose canonical bag is the sum of theirs. -/
theorem tensor_represents {s t : ByInstantiation.State} {P Q R : RhoProcess}
    {left right : ℕ → G [] .pr} (onLeft : ByInstantiation.RepresentsBy s P left)
    (onRight : ByInstantiation.RepresentsBy t Q right)
    (sum : (fromProcess R).1 = (fromProcess P).1 + (fromProcess Q).1) :
    ByInstantiation.RepresentsBy (tensor s t) R (tensorValue left right) := by
  classical
  obtain ⟨gs, solvesS⟩ := onLeft.solvable
  obtain ⟨gt, solvesT⟩ := onRight.solvable
  refine ⟨⟨RuleSyntax.Contextual.copair sig (B := groundFrame) gs gt, ?_⟩, ?_, ?_, ?_⟩
  · intro e member
    rcases List.mem_append.mp member with inLeft | inRight
    · obtain ⟨e₀, inS, rfl⟩ := List.mem_map.mp inLeft
      change ObsSimilar
          (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) gs gt)
            (instantiateObservation (leftIn s.frame t.frame) e₀.1))
        (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) gs gt)
          (instantiateObservation (leftIn s.frame t.frame) e₀.2))
      rw [RuleSyntax.Contextual.copair_weaken, RuleSyntax.Contextual.copair_weaken]
      exact solvesS e₀ inS
    · obtain ⟨e₀, inT, rfl⟩ := List.mem_map.mp inRight
      change ObsSimilar
          (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) gs gt)
            (instantiateObservation (rightIn s.frame t.frame) e₀.1))
        (instantiateObservation (RuleSyntax.Contextual.copair sig (B := groundFrame) gs gt)
          (instantiateObservation (rightIn s.frame t.frame) e₀.2))
      rw [RuleSyntax.Contextual.copair_opening, RuleSyntax.Contextual.copair_opening]
      exact solvesT e₀ inT
  · intro g solved o member
    rcases mem_tensor.mp member with ⟨k, inS, rfl⟩ | ⟨k, inT, rfl⟩
    · obtain ⟨u, at', similar⟩ := onLeft.determined _ (tensor_solves_left solved) k inS
      refine ⟨u, ?_, ?_⟩
      · rw [tensor_label_even]
        change instantiateObservation g (instantiateObservation (leftIn s.frame t.frame) (s.label k)) = _
        rw [instantiateObservation_comp]
        exact at'
      · rw [tensorValue_even]
        exact similar
    · obtain ⟨u, at', similar⟩ := onRight.determined _ (tensor_solves_right solved) k inT
      refine ⟨u, ?_, ?_⟩
      · rw [tensor_label_odd]
        change instantiateObservation g (instantiateObservation (rightIn s.frame t.frame) (t.label k)) = _
        rw [instantiateObservation_comp]
        exact at'
      · rw [tensorValue_odd]
        exact similar
  · intro o member
    rcases mem_tensor.mp member with ⟨k, inS, rfl⟩ | ⟨k, inT, rfl⟩
    · rw [tensorValue_even]
      exact onLeft.closed k inS
    · rw [tensorValue_odd]
      exact onRight.closed k inT
  · have apart : Disjoint (s.present.map evenEmbedding) (t.present.map oddEmbedding) := by
      rw [Finset.disjoint_left]
      intro o inLeft inRight
      obtain ⟨a, _, atA⟩ := Finset.mem_map.mp inLeft
      obtain ⟨b, _, atB⟩ := Finset.mem_map.mp inRight
      rw [evenEmbedding_apply] at atA
      rw [oddEmbedding_apply] at atB
      omega
    unfold ByInstantiation.inventoryOf
    rw [show (tensor s t).present = s.present.map evenEmbedding ∪ t.present.map oddEmbedding from rfl,
      Finset.sum_union apart, Finset.sum_map, Finset.sum_map, sum, ← onLeft.inventory_eq,
      ← onRight.inventory_eq]
    unfold ByInstantiation.inventoryOf
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      change ReflectiveCalculus.primes (read (tensorValue left right (2 * k))) = _
      rw [tensorValue_even]
    · refine Finset.sum_congr rfl fun k _ => ?_
      change ReflectiveCalculus.primes (read (tensorValue left right (2 * k + 1))) = _
      rw [tensorValue_odd]

/-! ## States with no row and with one row -/

/-- The state with no row. -/
def emptyState : ByInstantiation.State := ⟨groundFrame, [], ∅, fun _ => ⟨[], .pr, zeroT⟩⟩

/-- The state with one row. -/
abbrev single (t : G [] .pr) : ByInstantiation.State := ByInstantiation.initialState t

/-- The empty state represents every process with the empty canonical bag. -/
theorem empty_represents {P : RhoProcess} (empty : (fromProcess P).1 = 0) :
    ByInstantiation.RepresentsBy emptyState P (fun _ => zeroT) := by
  refine ⟨⟨(fun e => nomatch e : Grounding groundFrame), fun _ inside => nomatch inside⟩,
    fun _ _ o member => absurd member (Finset.notMem_empty o),
    fun o member => absurd member (Finset.notMem_empty o), ?_⟩
  rw [empty]
  simp [ByInstantiation.inventoryOf, emptyState]

/-! ## The twin of a closed process -/

theorem toTwin_isSome (P : RhoProcess) : (ByInstantiation.toTwin 0 .pr P.1).isSome := by
  obtain ⟨t, translated, _⟩ := ByInstantiation.toTwin_closed P
  rw [translated]
  rfl

/-- **The twin term of a closed process**, computed by the translation on syntax. -/
def twin (P : RhoProcess) : G [] .pr := (ByInstantiation.toTwin 0 .pr P.1).get (toTwin_isSome P)

theorem toTwin_twin (P : RhoProcess) : ByInstantiation.toTwin 0 .pr P.1 = some (twin P) :=
  (Option.some_get (toTwin_isSome P)).symm

theorem read_twin (P : RhoProcess) : read (twin P) = P.1 := by
  obtain ⟨t, translated, back⟩ := ByInstantiation.toTwin_closed P
  have same : twin P = t := Option.some.inj ((toTwin_twin P).symm.trans translated)
  rw [same, back]

theorem twin_closed (P : RhoProcess) : Closed (twin P) :=
  ByInstantiation.represent_closed_safe (read_twin P)

/-! ## The translation -/

/-- One row when the term is a closed process; no row otherwise. -/
def rowAt : {Γ : Ctx sig} → {s : ByInstantiation.Srt} → G Γ s → ByInstantiation.State
  | [], .pr, t => single t
  | _, _, _ => emptyState

/-- **The translation of a twin term into a state**: no row for the null process; the tensor of the
components for a bag (a one-element bag is its component); one row for every other closed
process. -/
def encodeAt : {Γ : Ctx sig} → {s : ByInstantiation.Srt} → G Γ s → ByInstantiation.State
  | _, _, .op (.inl .zero) .nil => emptyState
  | _, _, .op (.inl .bag) (.cons l .nil) => encodeAt l
  | _, _, .op (.inl .pnil) .nil => emptyState
  | _, _, .op (.inl .pcons) (.cons a (.cons (.op (.inl .pnil) .nil) .nil)) => encodeAt a
  | _, _, .op (.inl .pcons) (.cons a (.cons r .nil)) => tensor (encodeAt a) (encodeAt r)
  | _, _, t => rowAt t

/-- **The translation of a closed process into a state of the step.** -/
def encode (P : RhoProcess) : ByInstantiation.State := encodeAt (twin P)

/-- The canonical bag of a closed process is the primes of its pattern. -/
theorem fromProcess_primes (P : RhoProcess) : (fromProcess P).1 = ReflectiveCalculus.primes P.1 := rfl

/-- The representation of a twin term and of a list of components, by induction on the spine
weight (the recursion of `encodeAt` follows the spine). -/
theorem encodeAt_represents_le : ∀ n : ℕ,
    (∀ (t : G [] .pr) (closed : Closed t), spine t ≤ n →
      ∃ value, ByInstantiation.RepresentsBy (encodeAt t) (ByInstantiation.rowProcess t closed) value) ∧
    (∀ (l : G [] .ps) (closed : Closed l), spine l ≤ n →
      ∃ value, ByInstantiation.RepresentsBy (encodeAt l)
        (ByInstantiation.rowProcess (bagT l) closed) value) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun t closed small => ?_, fun l closed small => ?_⟩
      · match t, closed, small with
        | .op (.inl .zero) .nil, _, small => exact absurd (show 1 ≤ 0 from small) (by omega)
        | .op (.inl .bag) (.cons l .nil), _, small =>
            exact absurd (show spine l + 1 ≤ 0 from small) (by omega)
        | .op (.inl .input) (.cons _ (.cons _ .nil)), closed, _ =>
            exact ⟨_, ByInstantiation.initial_represents (ByInstantiation.rowProcess _ closed) rfl⟩
        | .op (.inl .output) (.cons _ (.cons _ .nil)), closed, _ =>
            exact ⟨_, ByInstantiation.initial_represents (ByInstantiation.rowProcess _ closed) rfl⟩
        | .op (.inl .dropq) (.cons _ .nil), closed, _ =>
            exact ⟨_, ByInstantiation.initial_represents (ByInstantiation.rowProcess _ closed) rfl⟩
        | .op (.inr o) _, _, _ => exact o.key.elim
      · match l, closed, small with
        | .op (.inl .pnil) .nil, closed, _ =>
            exact ⟨_, empty_represents (P := ByInstantiation.rowProcess (bagT pnilT) closed)
              ByInstantiation.primes_empty_bag⟩
        | .op (.inl .pcons) (.cons a (.cons r .nil)), _, small =>
            exact absurd (show spine a + spine r + 1 ≤ 0 from small) (by omega)
        | .op (.inr o) _, _, _ => exact o.key.elim
  | succ n ih =>
      refine ⟨fun t closed small => ?_, fun l closed small => ?_⟩
      · match t, closed, small with
        | .op (.inl .zero) .nil, closed, _ =>
            exact ⟨_, empty_represents (P := ByInstantiation.rowProcess _ closed)
              ReflectiveCalculus.primes_zero⟩
        | .op (.inl .bag) (.cons l .nil), closed, small =>
            exact ih.2 l closed (by have weight : spine l + 1 ≤ n + 1 := small; omega)
        | .op (.inl .input) (.cons _ (.cons _ .nil)), closed, _ =>
            exact ⟨_, ByInstantiation.initial_represents (ByInstantiation.rowProcess _ closed) rfl⟩
        | .op (.inl .output) (.cons _ (.cons _ .nil)), closed, _ =>
            exact ⟨_, ByInstantiation.initial_represents (ByInstantiation.rowProcess _ closed) rfl⟩
        | .op (.inl .dropq) (.cons _ .nil), closed, _ =>
            exact ⟨_, ByInstantiation.initial_represents (ByInstantiation.rowProcess _ closed) rfl⟩
        | .op (.inr o) _, _, _ => exact o.key.elim
      · match l, closed, small with
        | .op (.inl .pnil) .nil, closed, _ =>
            exact ⟨_, empty_represents (P := ByInstantiation.rowProcess (bagT pnilT) closed)
              ByInstantiation.primes_empty_bag⟩
        | .op (.inl .pcons) (.cons a (.cons (.op (.inl .pnil) .nil) .nil)), closed, small =>
            have parts := ByInstantiation.closed_parts (a := a) (r := pnilT) closed
            obtain ⟨value, represented⟩ :=
              ih.1 a parts.1 (by have weight : spine a + 0 + 1 ≤ n + 1 := small; omega)
            refine ⟨value, RepresentsBy.of_bag represented ?_⟩
            rw [fromProcess_primes, fromProcess_primes]
            change ReflectiveCalculus.primes (read a) =
              ReflectiveCalculus.primes (read (bagT (pconsT a pnilT)))
            rw [ByInstantiation.primes_bag_parts]
            change _ = _ + ReflectiveCalculus.primes (.collection .hashBag [] none)
            rw [ByInstantiation.primes_empty_bag, add_zero]
        | .op (.inl .pcons) (.cons a (.cons (.op (.inl .pcons) (.cons b (.cons r .nil))) .nil)),
            closed, small =>
            have parts := ByInstantiation.closed_parts (a := a) (r := pconsT b r) closed
            have weight : spine a + (spine b + spine r + 1) + 1 ≤ n + 1 := small
            obtain ⟨left, onLeft⟩ := ih.1 a parts.1 (by omega)
            obtain ⟨right, onRight⟩ := ih.2 (pconsT b r) parts.2
              (show spine b + spine r + 1 ≤ n by omega)
            refine ⟨tensorValue left right, tensor_represents onLeft onRight ?_⟩
            rw [fromProcess_primes, fromProcess_primes, fromProcess_primes]
            exact ByInstantiation.primes_bag_parts a (pconsT b r)
        | .op (.inl .pcons) (.cons _ (.cons (.op (.inr o) _) .nil)), _, _ => exact o.key.elim
        | .op (.inr o) _, _, _ => exact o.key.elim

/-- **The translation represents**: `encode P` represents `P`. -/
theorem encode_represents (P : RhoProcess) : ByInstantiation.Represents (encode P) P := by
  obtain ⟨value, represented⟩ :=
    (encodeAt_represents_le (spine (twin P))).1 (twin P) (twin_closed P) le_rfl
  have same : ByInstantiation.rowProcess (twin P) (twin_closed P) = P := Subtype.ext (read_twin P)
  rw [same] at represented
  exact ⟨value, represented⟩

/-! ## Parallel composition -/

/-- **The source's parallel composition**: `P | Q`, the two-element bag. -/
def par (P Q : RhoProcess) : RhoProcess :=
  ⟨.collection .hashBag [P.1, Q.1] none, (rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.parallel (.cons ((rhoClosedTermWellSorted_process_iff _).mp P.2).1
      (.cons ((rhoClosedTermWellSorted_process_iff _).mp Q.2).1 .nil)),
     by simp [binderSafeAt, binderSafeListAt, ((rhoClosedTermWellSorted_process_iff _).mp P.2).2,
       ((rhoClosedTermWellSorted_process_iff _).mp Q.2).2]⟩⟩

/-- The canonical bag of `P | Q` is the sum of theirs. -/
theorem fromProcess_par (P Q : RhoProcess) :
    (fromProcess (par P Q)).1 = (fromProcess P).1 + (fromProcess Q).1 := by
  rw [fromProcess_primes, fromProcess_primes, fromProcess_primes]
  change ReflectiveCalculus.primes (.collection .hashBag [P.1, Q.1] none) = _
  rw [ByInstantiation.primes_cons_bag, ByInstantiation.primes_cons_bag,
    ByInstantiation.primes_empty_bag, add_zero]

/-- The twin of `P | Q` is the bag of the twins. -/
theorem twin_par (P Q : RhoProcess) :
    twin (par P Q) = bagT (pconsT (twin P) (pconsT (twin Q) pnilT)) := by
  have translated : ByInstantiation.toTwin 0 .pr (par P Q).1 =
      some (bagT (pconsT (twin P) (pconsT (twin Q) pnilT))) := by
    change ByInstantiation.toTwin 0 .pr (.collection .hashBag [P.1, Q.1] none) = _
    simp [ByInstantiation.toTwin, ByInstantiation.toTwinList, toTwin_twin]
    rfl
  exact Option.some.inj ((toTwin_twin (par P Q)).symm.trans translated)

/-- **The translation is homomorphic on parallel composition, on the nose**: the image of `P | Q` is
the tensor of the images. -/
theorem encode_par (P Q : RhoProcess) : encode (par P Q) = tensor (encode P) (encode Q) := by
  unfold encode
  rw [twin_par]
  rfl

/-! ## An input or an output is one row determined by the prefix -/

/-- **The translation of an input is one row determined by the prefix**: the state with the one row of
the communication rule's input pattern, filled by instantiation with the twin terms of its channel and
continuation. The continuation enters as its twin term, not as its translation `encode`; this is not
Gorla's Property 1 for `encode` (`input_not_compositional`). -/
theorem encode_input (P : RhoProcess) {c : G [] .nm} {b : G [.nm, .pr] .pr}
    (shape : twin P = inputT c b) (h : Grounding ByInstantiation.commFrame)
    (channel : h .channel = c) (body : h .body = b) :
    encode P = single (instantiate h ByInstantiation.commInput) := by
  unfold encode
  rw [shape, ByInstantiation.instantiate_commInput, channel, body]
  rfl

/-- **The translation of an output is one row determined by the prefix**: the state with the one row of
the communication rule's output pattern, filled by instantiation with the twin terms of its channel and
payload. The payload enters as its twin term, not as its translation `encode`; this is not Gorla's
Property 1 for `encode` (`output_not_compositional`). -/
theorem encode_output (P : RhoProcess) {c : G [] .nm} {q : G [] .pr}
    (shape : twin P = outputT c q) (h : Grounding ByInstantiation.commFrame)
    (channel : h .channel = c) (payload : h .payload = q) :
    encode P = single (instantiate h ByInstantiation.commOutput) := by
  unfold encode
  rw [shape, ByInstantiation.instantiate_commOutput, channel, payload]
  rfl

/-! ## The single-row translation, a control -/

/-- **The single-row translation**: the state with the one row `twin P`. -/
def encodeRow (P : RhoProcess) : ByInstantiation.State := single (twin P)

theorem encodeRow_represents (P : RhoProcess) : ByInstantiation.Represents (encodeRow P) P :=
  ⟨_, ByInstantiation.initial_represents P (read_twin P)⟩

/-- `0` as a closed process. -/
def nil : RhoProcess := ByInstantiation.rowProcess zeroT (by decide)

/-- **The single-row translation is not homomorphic on parallel composition**: the image of `0 | 0`
has one row, and the tensor of the images of `0` and `0` has two. -/
theorem encodeRow_not_homomorphic :
    (encodeRow (par nil nil)).present.card = 1 ∧
      (tensor (encodeRow nil) (encodeRow nil)).present.card = 2 ∧
      encodeRow (par nil nil) ≠ tensor (encodeRow nil) (encodeRow nil) := by
  have one : (encodeRow (par nil nil)).present.card = 1 := rfl
  have two : (tensor (encodeRow nil) (encodeRow nil)).present.card = 2 := by decide
  refine ⟨one, two, fun same => ?_⟩
  have cards : (encodeRow (par nil nil)).present.card =
      (tensor (encodeRow nil) (encodeRow nil)).present.card :=
    congrArg (fun s : ByInstantiation.State => s.present.card) same
  rw [one, two] at cards
  exact absurd cards (by decide)

#print axioms tensor_represents
#print axioms empty_represents
#print axioms read_twin
#print axioms encodeAt_represents_le
#print axioms encode_represents
#print axioms fromProcess_par
#print axioms twin_par
#print axioms encode_par
#print axioms encode_input
#print axioms encode_output
#print axioms encodeRow_represents
#print axioms encodeRow_not_homomorphic

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
