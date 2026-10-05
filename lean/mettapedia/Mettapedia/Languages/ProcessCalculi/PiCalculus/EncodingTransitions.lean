import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingEquivariance
import Mettapedia.Languages.ProcessCalculi.PiCalculus.UnguardedOutputs
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ChannelSeparation

/-!
# Where the pi-to-rho encoding fails to follow or to reflect a step

A morphism in the sense of a pair of a map on terms and a map on contexts is
asked to preserve transitions along the map on contexts.  Outside the
fragment without restriction and replication the encoding of the pi calculus
into the rho calculus does not, and without freshness of its two names it
does not reflect them either.

* **Under a restriction no step is preserved.**  The encoding of a
  restriction is a request for a fresh name in parallel with an input that
  awaits it; the two are on different channels, so the encoding has no
  reduction at all, while the restricted process reduces whenever its body
  does.
* **A replicated input does not act in the rho calculus proper.**  Its
  encoding is a constructor without a rule; with the unfolding of
  replications added, the unfolding is a step that the process does not
  have.
* **Without freshness of the two names, steps are not reflected, and
  congruent processes are separated.**  A process that listens on the value
  name answers the request of a restriction beside it: the encoding reduces
  and the process does not.  The image of that listening context separates a
  restricted inaction from inaction, which no context separates.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
  (separation separationHead nameCount unfoldCount)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu (ReducesDerived)

/-! ## An exchange -/

/-- **The image of an exchange moves in one step**, whatever the body of the
input: to that body with the quoted payload substituted. -/
theorem encode_exchange_one_step (channel bound datum : Name) (body : Process)
    (n v : String) :
    Nonempty (RhoCalculus.Reduction.Reduces
      (encode (.par (.input channel bound body) (.output channel datum)) n v)
      (.collection .hashBag
        [RhoCalculus.semanticCommSubst (closeFVar 0 bound (encode body (n ++ "_L") v))
          (.apply "PDrop" [.fvar datum])] none)) :=
  ⟨RhoCalculus.Reduction.Reduces.equiv
    (RhoCalculus.StructuralCongruence.par_comm _ _)
    (RhoCalculus.Reduction.Reduces.comm (rest := []))
    (RhoCalculus.StructuralCongruence.refl _)⟩

/-! ## Under a restriction -/

/-- The encoding of a restriction: a request for a fresh name beside the
input that awaits it. -/
theorem encode_nu_eq (bound : Name) (body : Process) (n v : String) :
    encode (.nu bound body) n v =
      .collection .hashBag
        [.apply "POutput" [.fvar v, .fvar n],
          .apply "PInput"
            [.fvar n, .lambda none (closeFVar 0 bound (encode body (n ++ "_" ++ n) v))]]
        none :=
  rfl

/-- The request is on the value name and the input on the namespace name:
separated channels. -/
theorem separation_encode_nu (bound : Name) (body : Process) {n v : String}
    (distinct : n ≠ v) : separation [v] (encode (.nu bound body) n v) = 0 := by
  rw [encode_nu_eq]
  simp [separation, separationHead, nameCount, distinct]

theorem unfoldCount_encode_nu (bound : Name) (body : Process) (n v : String) :
    unfoldCount (encode (.nu bound body) n v) = 0 := by
  rw [encode_nu_eq]
  simp [unfoldCount]

/-- **The encoding of a restriction has no reduction**, whatever its body,
neither in the rho calculus nor with the unfolding of replications added. -/
theorem encode_nu_irreducible (bound : Name) (body : Process) {n v : String}
    (distinct : n ≠ v) (target : Pattern) :
    IsEmpty (RhoCalculus.Reduction.Reduces (encode (.nu bound body) n v) target) ∧
      IsEmpty (ReducesDerived (encode (.nu bound body) n v) target) :=
  ⟨RhoCalculus.Reduction.not_reduces_of_separation_eq_zero [v]
      (separation_encode_nu bound body distinct) target,
    RhoCalculus.Reduction.not_reducesDerived_of_separation_eq_zero [v]
      (separation_encode_nu bound body distinct) (unfoldCount_encode_nu bound body n v) target⟩

/-- **A step under a restriction is not preserved.**  Whenever the body of a
restriction reduces, the restriction reduces, and its encoding has no
reduction: the transition labelled by the restriction context has no image. -/
theorem restricted_step_not_preserved (bound : Name) {body reduct : Process}
    (step : Nonempty (PiCalculus.Reduces body reduct)) {n v : String} (distinct : n ≠ v) :
    Nonempty (PiCalculus.Reduces ((ProcessContext.nu bound .hole).fill body)
        ((ProcessContext.nu bound .hole).fill reduct)) ∧
      ∀ target : Pattern,
        IsEmpty (RhoCalculus.Reduction.Reduces
          ((ProcessContext.nu bound .hole).encode n v
            (encode body ((ProcessContext.nu bound .hole).parameter n) v)) target) := by
  refine ⟨(ProcessContext.Reactive.nu bound .hole).reduces step, fun target => ?_⟩
  rw [← ProcessContext.encode_fill]
  exact (encode_nu_irreducible bound body distinct target).1

/-- A communication: `a(y).0 | a⟨z⟩` reduces to `0`. -/
theorem exchange_reduces (channel bound datum : Name) :
    Nonempty (PiCalculus.Reduces
      (.par (.input channel bound .nil) (.output channel datum)) .nil) := by
  simpa only [Process.substitute_nil] using
    (show Nonempty (PiCalculus.Reduces
      (.par (.input channel bound .nil) (.output channel datum))
      (Process.nil.substitute bound datum)) from ⟨Reduces.comm channel bound datum .nil⟩)

/-- **The instance.**  `(νx)(a(y).0 | a⟨z⟩)` reduces to `(νx)0`, and its
encoding at two different names has no reduction. -/
theorem restricted_exchange_not_preserved (restricted channel bound datum : Name)
    {n v : String} (distinct : n ≠ v) :
    Nonempty (PiCalculus.Reduces
        (.nu restricted (.par (.input channel bound .nil) (.output channel datum)))
        (.nu restricted .nil)) ∧
      ∀ target : Pattern,
        IsEmpty (RhoCalculus.Reduction.Reduces
          (encode (.nu restricted (.par (.input channel bound .nil) (.output channel datum)))
            n v) target) :=
  ⟨(ProcessContext.Reactive.nu restricted .hole).reduces
      (exchange_reduces channel bound datum),
    fun target => (encode_nu_irreducible restricted _ distinct target).1⟩

/-! ## Replication -/

/-- `!x(y).P | x⟨z⟩` reduces: the replication unfolds by structural
congruence and communicates. -/
theorem replicated_exchange_reduces (channel bound datum : Name) (body : Process) :
    Nonempty (PiCalculus.Reduces
      (.par (.replicate channel bound body) (.output channel datum))
      (.par (body.substitute bound datum) (.replicate channel bound body))) := by
  let input := Process.input channel bound body
  let server := Process.replicate channel bound body
  let output := Process.output channel datum
  have rearrange : ((input ||| server) ||| output) ≡ ((input ||| output) ||| server) :=
    StructuralCongruence.trans _ _ _
      (StructuralCongruence.par_assoc input server output)
      (StructuralCongruence.trans _ _ _
        (StructuralCongruence.par_cong _ _ _ _
          (StructuralCongruence.refl input) (StructuralCongruence.par_comm server output))
        (StructuralCongruence.symm _ _ (StructuralCongruence.par_assoc input output server)))
  refine ⟨Reduces.struct _ _ _ _ ?_
    (Reduces.par_left _ _ server (Reduces.comm channel bound datum body))
    (StructuralCongruence.refl _)⟩
  exact StructuralCongruence.trans _ _ _
    (StructuralCongruence.par_cong _ _ _ _
      (StructuralCongruence.replicate_unfold channel bound body)
      (StructuralCongruence.refl output)) rearrange

/-- **In the rho calculus proper the encoding of that process has no
reduction**: the encoded replication is a constructor without a rule, and
nothing else listens on the channel. -/
theorem encode_replicated_exchange_irreducible (channel bound datum : Name) (body : Process)
    (n v : String) (target : Pattern) :
    IsEmpty (RhoCalculus.Reduction.Reduces
      (encode (.par (.replicate channel bound body) (.output channel datum)) n v) target) := by
  have unfolded : encode (.par (.replicate channel bound body) (.output channel datum)) n v =
      .collection .hashBag
        [.apply "PReplicate"
            [rhoInput (piNameToRhoName channel) bound
              (encode body ((n ++ "_L") ++ "_rep") v)],
          .apply "POutput" [.fvar channel, .apply "PDrop" [.fvar datum]]] none := rfl
  rw [unfolded]
  apply RhoCalculus.Reduction.not_reduces_of_separation_eq_zero [channel]
  have mentioned : nameCount [channel] (Pattern.fvar channel) = 1 :=
    RhoCalculus.Reduction.nameCount_fvar_of_mem (List.mem_singleton.mpr rfl)
  simp [separation, separationHead, mentioned]

/-- **With the unfolding of replications added, a step of the image is not
reflected.**  The encoding of a replication unfolds, and the replication has
no reduction. -/
theorem replicate_unfolding_not_reflected (channel bound : Name) (body : Process)
    (n v : String) :
    (∃ target : Pattern,
        Nonempty (ReducesDerived (encode (.replicate channel bound body) n v) target)) ∧
      ∀ target : Process,
        IsEmpty (PiCalculus.Reduces (.replicate channel bound body) target) :=
  ⟨⟨_, ⟨ReducesDerived.rep_unfold⟩⟩, not_reduces_of_unguardedOutputs_eq_zero rfl⟩

/-! ## Without freshness of the names -/

/-- A restriction beside a process that listens on a name. -/
def listenerBeside (restricted listened bound : Name) : Process :=
  .par (.nu restricted .nil) (.input listened bound .nil)

/-- It has no reduction: it has no output. -/
theorem listenerBeside_irreducible (restricted listened bound : Name) (target : Process) :
    IsEmpty (PiCalculus.Reduces (listenerBeside restricted listened bound) target) :=
  not_reduces_of_unguardedOutputs_eq_zero rfl target

/-- **A step that is not reflected.**  When the name listened on is the value
name of the encoding, the request of the restriction is answered by the
listener: the encoding reduces, and the process has no reduction. -/
theorem listener_step_not_reflected (restricted bound : Name) (n v : String) :
    (∃ target : Pattern, Nonempty
        (RhoCalculus.Reduction.Reduces (encode (listenerBeside restricted v bound) n v) target)) ∧
      ∀ target : Process,
        IsEmpty (PiCalculus.Reduces (listenerBeside restricted v bound) target) := by
  refine ⟨?_, listenerBeside_irreducible restricted v bound⟩
  have unfolded : encode (listenerBeside restricted v bound) n v =
      .collection .hashBag
        [.apply "POutput" [.fvar v, .fvar (n ++ "_L")],
          .apply "PInput"
            [.fvar (n ++ "_L"),
              .lambda none
                (closeFVar 0 restricted
                  (encode .nil ((n ++ "_L") ++ "_" ++ (n ++ "_L")) v))],
          .apply "PInput"
            [.fvar v, .lambda none (closeFVar 0 bound (encode .nil (n ++ "_R") v))]] none :=
    rfl
  rw [unfolded]
  exact ⟨_, ⟨RhoCalculus.Reduction.Reduces.equiv
    (RhoCalculus.StructuralCongruence.par_perm _ _
      (List.Perm.cons _ (List.Perm.swap _ _ [])))
    (RhoCalculus.Reduction.Reduces.comm (rest := [_]))
    (RhoCalculus.StructuralCongruence.refl _)⟩⟩

/-- The listener uses the value name: the process is not fresh for the names
of the encoding. -/
theorem listenerBeside_not_fresh (restricted bound : Name) (n v : String) :
    ¬ EncodingFreshAt (listenerBeside restricted v bound) n v := by
  intro fresh
  have used : (v : Name) ∈ (listenerBeside restricted v bound).freeNames :=
    Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have seed : (v : Name) ∈ ({n, v} : Finset Name) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact (Finset.disjoint_left.mp fresh) used seed

/-! ## Congruent sources, separated images -/

/-- A context that listens on a name beside its hole. -/
def listenerContext (listened bound : Name) : ProcessContext :=
  .parLeft .hole (.input listened bound .nil)

/-- **The image of a context separates the images of two processes that no
context separates.**  A restricted inaction is structurally congruent to
inaction, so every context gives the two the same reducts.  The image of the
context that listens on the value name sends the first to a term that
reduces, the request being answered, and the second to a term that does
not. -/
theorem congruent_sources_separated_by_image (restricted bound : Name) (n v : String) :
    (∀ (context : ProcessContext) (target : Process),
        Nonempty (PiCalculus.Reduces (context.fill (.nu restricted .nil)) target) ↔
          Nonempty (PiCalculus.Reduces (context.fill .nil) target)) ∧
      (∃ target : Pattern, Nonempty
        (RhoCalculus.Reduction.Reduces
          ((listenerContext v bound).encode n v
            (encode (.nu restricted .nil) ((listenerContext v bound).parameter n) v))
          target)) ∧
      ∀ target : Pattern,
        IsEmpty (RhoCalculus.Reduction.Reduces
          ((listenerContext v bound).encode n v
            (encode .nil ((listenerContext v bound).parameter n) v))
          target) := by
  refine ⟨fun context target =>
      context.reduces_iff_of_congruent (StructuralCongruence.nu_nil restricted) target, ?_, ?_⟩
  · rw [← ProcessContext.encode_fill]
    exact (listener_step_not_reflected restricted bound n v).1
  · intro target
    rw [← ProcessContext.encode_fill]
    have unfolded : encode ((listenerContext v bound).fill .nil) n v =
        .collection .hashBag
          [.apply "PInput"
            [.fvar v, .lambda none (closeFVar 0 bound (encode .nil (n ++ "_R") v))]] none :=
      rfl
    rw [unfolded]
    apply RhoCalculus.Reduction.not_reduces_of_separation_eq_zero []
    simp [separation, separationHead, nameCount]

end Mettapedia.Languages.ProcessCalculi.PiCalculus
