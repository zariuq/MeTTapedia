import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingTransitions
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingNotSignatureMap

/-!
# The full encoding does not follow a step under a restriction in one step

The full encoding places the name server beside the encoding of a process.
For a restriction, its outputs are the request for a fresh name and the seed
of the server, and its only input awaits the fresh name: separated channels,
so the full encoding of a restriction has no reduction in the rho calculus
proper.  With the unfolding of replications added, a step can only unfold a
replication, which never removes an input or an output.

A step of the pi calculus that consumes actions is therefore not matched by
one step of the full encoding, even up to structural congruence: every term
reached in one step has at least as many inputs and outputs as the source,
and the full encoding of the reduct has fewer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
  (separation separationHead nameCount unfoldCount ioCount ioCount_SC)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu (ReducesDerived)

open private rhoPar_to_two from
  Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation

/-! ## Inputs and outputs of an encoding -/

/-- The count of inputs and outputs of an application depends on its
arguments only through their counts. -/
theorem ioCount_apply_of_sum_eq (label : String) {first second : List Pattern}
    (same : (first.map ioCount).sum = (second.map ioCount).sum) :
    ioCount (.apply label first) = ioCount (.apply label second) := by
  unfold ioCount
  split <;> split <;> simp_all

/-- Binding a free name does not change the inputs and outputs. -/
theorem ioCount_closeFVar (name : String) (pattern : Pattern) :
    ∀ depth : Nat, ioCount (closeFVar depth name pattern) = ioCount pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth; simp [closeFVar]
  | hfvar other =>
      intro depth
      rw [closeFVar]
      split <;> simp [ioCount]
  | happly constructor arguments recurse =>
      intro depth
      rw [closeFVar]
      apply ioCount_apply_of_sum_eq
      rw [List.map_map]
      exact congrArg List.sum
        (List.map_congr_left fun argument membership => recurse argument membership depth)
  | hlambda binder body recurse =>
      intro depth
      rw [closeFVar]
      simp only [ioCount, recurse]
  | hmultiLambda arity binders body recurse =>
      intro depth
      rw [closeFVar]
      simp only [ioCount, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro depth
      rw [closeFVar]
      simp only [ioCount, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      intro depth
      rw [closeFVar]
      simp only [ioCount, List.map_map]
      exact congrArg List.sum
        (List.map_congr_left fun element membership => recurse element membership depth)

/-- A flattened parallel composition has the inputs and outputs of its two
sides. -/
theorem ioCount_rhoPar (left right : Pattern) :
    ioCount (rhoPar left right) = ioCount left + ioCount right := by
  rw [ioCount_SC (rhoPar_to_two left right)]
  simp [ioCount]

theorem ioCount_fvar (name : String) : ioCount (.fvar name) = 0 := by
  simp [ioCount]

/-- An input contributes one, beside its channel and its body. -/
theorem ioCount_rhoInput (channel : Pattern) (bound : String) (body : Pattern) :
    ioCount (rhoInput channel bound body) = 1 + ioCount channel + ioCount body := by
  simp only [rhoInput, ioCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    ioCount_closeFVar bound body 0]
  omega

/-- An output contributes one, beside its channel and its payload. -/
theorem ioCount_rhoOutput (channel payload : Pattern) :
    ioCount (rhoOutput channel payload) = 1 + ioCount channel + ioCount payload := by
  simp only [rhoOutput, ioCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem ioCount_rhoDrop (name : Pattern) : ioCount (rhoDrop name) = ioCount name := by
  simp [rhoDrop, ioCount]

theorem ioCount_rhoReplicate (body : Pattern) : ioCount (rhoReplicate body) = ioCount body := by
  simp [rhoReplicate, ioCount]

/-- The inputs and outputs that the encoding of a process has: one per
input, output and replication, and two per restriction. -/
def Process.actionCount (process : Process) : Nat :=
  process.inputCount + process.outputCount + process.replicationCount +
    2 * process.restrictionCount

/-- **The encoding of a process has as many inputs and outputs as the process
has actions**, whatever the two names. -/
theorem ioCount_encode :
    ∀ (process : Process) (n v : String), ioCount (encode process n v) = process.actionCount
  | .nil, _, _ => by
      simp [encode, rhoNil, ioCount, Process.actionCount, Process.inputCount,
        Process.outputCount, Process.replicationCount, Process.restrictionCount]
  | .par left right, n, v => by
      rw [encode, ioCount_rhoPar, ioCount_encode left, ioCount_encode right]
      simp only [Process.actionCount, Process.inputCount, Process.outputCount,
        Process.replicationCount, Process.restrictionCount]
      omega
  | .input channel bound body, n, v => by
      rw [encode, ioCount_rhoInput (piNameToRhoName channel) bound (encode body n v),
        show ioCount (piNameToRhoName channel) = 0 from ioCount_fvar channel,
        ioCount_encode body n v]
      simp only [Process.actionCount, Process.inputCount, Process.outputCount,
        Process.replicationCount, Process.restrictionCount]
      omega
  | .output channel datum, n, v => by
      rw [encode, ioCount_rhoOutput, ioCount_rhoDrop,
        show ioCount (piNameToRhoName channel) = 0 from ioCount_fvar channel,
        show ioCount (piNameToRhoName datum) = 0 from ioCount_fvar datum]
      simp [Process.actionCount, Process.inputCount, Process.outputCount,
        Process.replicationCount, Process.restrictionCount]
  | .nu bound body, n, v => by
      rw [encode, ioCount_rhoPar, ioCount_rhoOutput,
        ioCount_rhoInput (.fvar n) bound (encode body (n ++ "_" ++ n) v), ioCount_fvar,
        ioCount_fvar, ioCount_encode body (n ++ "_" ++ n) v]
      simp only [Process.actionCount, Process.inputCount, Process.outputCount,
        Process.replicationCount, Process.restrictionCount]
      omega
  | .replicate channel bound body, n, v => by
      rw [encode, ioCount_rhoReplicate,
        ioCount_rhoInput (piNameToRhoName channel) bound (encode body (n ++ "_rep") v),
        show ioCount (piNameToRhoName channel) = 0 from ioCount_fvar channel,
        ioCount_encode body (n ++ "_rep") v]
      simp only [Process.actionCount, Process.inputCount, Process.outputCount,
        Process.replicationCount, Process.restrictionCount]
      omega

/-- **Structurally congruent encodings have the same number of actions.** -/
theorem actionCount_eq_of_encode_congruent {first second : Process} {n v n' v' : String}
    (related : RhoCalculus.StructuralCongruence (encode first n v) (encode second n' v')) :
    first.actionCount = second.actionCount := by
  rw [← ioCount_encode first n v, ← ioCount_encode second n' v']
  exact ioCount_SC related

/-- **The encoding does not respect the restriction law.**  A restricted
inaction is structurally congruent to inaction, and their encodings are not
structurally congruent, at any names: the first keeps its request and its
awaiting input. -/
theorem nu_nil_not_respected (restricted : Name) (n v n' v' : String) :
    Nonempty (PiCalculus.StructuralCongruence (.nu restricted .nil) .nil) ∧
      ¬ RhoCalculus.StructuralCongruence (encode (.nu restricted .nil) n v)
        (encode .nil n' v') :=
  ⟨⟨StructuralCongruence.nu_nil restricted⟩, fun related => by
    have same := actionCount_eq_of_encode_congruent related
    simp [Process.actionCount, Process.inputCount, Process.outputCount,
      Process.replicationCount, Process.restrictionCount] at same⟩

/-- **The encoding does not respect the unfolding of a replication.**  A
replication is structurally congruent to its unfolding, and their encodings
are not structurally congruent: the unfolding has the actions of the body
twice. -/
theorem replicate_unfold_not_respected (channel bound : Name) (body : Process)
    (n v n' v' : String) :
    Nonempty (PiCalculus.StructuralCongruence (.replicate channel bound body)
        (.input channel bound (.par body (.replicate channel bound body)))) ∧
      ¬ RhoCalculus.StructuralCongruence (encode (.replicate channel bound body) n v)
        (encode (.input channel bound (.par body (.replicate channel bound body))) n' v') :=
  ⟨⟨StructuralCongruence.replicate_unfold channel bound body⟩, fun related => by
    have same := actionCount_eq_of_encode_congruent related
    simp only [Process.actionCount, Process.inputCount, Process.outputCount,
      Process.replicationCount, Process.restrictionCount] at same
    omega⟩

/-! ## Steps of a term with separated channels -/

/-- **A derived step of a term with separated channels removes no input or
output**: it can only unfold a replication. -/
theorem ioCount_le_of_reducesDerived (names : List String) {source target : Pattern}
    (step : ReducesDerived source target) :
    separation names source = 0 → ioCount source ≤ ioCount target := by
  induction step with
  | core reduction =>
      intro separated
      exact absurd (RhoCalculus.Reduction.separation_pos_of_reduces names reduction)
        (by omega)
  | @rep_unfold body =>
      intro _
      have unfolded : ioCount (.apply "PReplicate" [body]) = ioCount body := by
        simp [ioCount]
      rw [unfolded]
      simp [ioCount]
  | par _ recurse =>
      intro separated
      simp only [separation, List.map_cons, List.sum_cons] at separated
      have inner := recurse (by omega)
      simp only [ioCount, List.map_cons, List.sum_cons]
      omega
  | par_any _ recurse =>
      intro separated
      simp only [separation, List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil] at separated
      have inner := recurse (by omega)
      simp only [ioCount, List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil]
      omega

/-! ## The full encoding of a restriction -/

/-- The full encoding of a restriction: the request, the awaiting input, the
replicated server, the replicated drop, and the seed. -/
theorem fullEncode_nu_eq (bound : Name) (body : Process) :
    fullEncode (.nu bound body) =
      .collection .hashBag
        [.apply "POutput" [.fvar "v_init", .fvar "n_init"],
          .apply "PInput"
            [.fvar "n_init",
              .lambda none
                (closeFVar 0 bound (encode body ("n_init" ++ "_" ++ "n_init") "v_init"))],
          rhoReplicate (nameServerBody "ns_x" "ns_z" "v_init"),
          dropOperation "ns_x",
          rhoOutput (.fvar "ns_z") (.apply "PDrop" [.fvar "ns_seed"])] none :=
  rfl

/-- In the full encoding of a restriction the outputs are on the value name
and the seed channel, and the input is on the namespace name. -/
theorem separation_fullEncode_nu (bound : Name) (body : Process) :
    separation ["v_init", "ns_z"] (fullEncode (.nu bound body)) = 0 := by
  rw [fullEncode_nu_eq]
  simp [separation, separationHead, nameCount, rhoReplicate, dropOperation, rhoOutput]

/-- **The full encoding of a restriction has no reduction in the rho calculus
proper.** -/
theorem fullEncode_nu_irreducible (bound : Name) (body : Process) (target : Pattern) :
    IsEmpty (RhoCalculus.Reduction.Reduces (fullEncode (.nu bound body)) target) :=
  RhoCalculus.Reduction.not_reduces_of_separation_eq_zero ["v_init", "ns_z"]
    (separation_fullEncode_nu bound body) target

/-- The inputs and outputs of the full encoding of a restriction: those of
the name server, the request and the awaiting input, and the actions of the
body. -/
theorem ioCount_fullEncode_nu (bound : Name) (body : Process) :
    ioCount (fullEncode (.nu bound body)) =
      ioCount (nameServer "ns_x" "ns_z" "v_init" "ns_seed") + 2 + body.actionCount := by
  have split : fullEncode (.nu bound body) =
      rhoPar (encode (.nu bound body) "n_init" "v_init")
        (nameServer "ns_x" "ns_z" "v_init" "ns_seed") := rfl
  rw [split, ioCount_rhoPar, ioCount_encode]
  simp only [Process.actionCount, Process.inputCount, Process.outputCount,
    Process.replicationCount, Process.restrictionCount]
  omega

/-- **One step of the full encoding does not match a step that consumes
actions.**  If the reduct of the body has fewer actions than the body, no
term reached in one derived step from the full encoding of the restricted
body is structurally congruent to the full encoding of the restricted
reduct. -/
theorem fullEncode_nu_step_not_matched (bound : Name) {body reduct : Process}
    (fewer : reduct.actionCount < body.actionCount) {successor : Pattern}
    (step : ReducesDerived (fullEncode (.nu bound body)) successor) :
    ¬ RhoCalculus.StructuralCongruence successor (fullEncode (.nu bound reduct)) := by
  intro matched
  have kept := ioCount_le_of_reducesDerived ["v_init", "ns_z"] step
    (separation_fullEncode_nu bound body)
  rw [ioCount_SC matched, ioCount_fullEncode_nu, ioCount_fullEncode_nu] at kept
  omega

/-- **The instance.**  `(νx)(a(y).0 | a⟨z⟩)` reduces to `(νx)0`; the full
encoding of the source has no reduction in the rho calculus proper, and no
term it reaches in one derived step is congruent to the full encoding of the
target. -/
theorem fullEncode_restricted_exchange_not_matched (restricted channel bound datum : Name) :
    Nonempty (PiCalculus.Reduces
        (.nu restricted (.par (.input channel bound .nil) (.output channel datum)))
        (.nu restricted .nil)) ∧
      (∀ target : Pattern,
        IsEmpty (RhoCalculus.Reduction.Reduces
          (fullEncode
            (.nu restricted (.par (.input channel bound .nil) (.output channel datum))))
          target)) ∧
      ∀ successor : Pattern,
        ReducesDerived
            (fullEncode
              (.nu restricted (.par (.input channel bound .nil) (.output channel datum))))
            successor →
          ¬ RhoCalculus.StructuralCongruence successor (fullEncode (.nu restricted .nil)) :=
  ⟨(restricted_exchange_not_preserved restricted channel bound datum
      (n := "n") (v := "v") (by decide)).1,
    fullEncode_nu_irreducible restricted _,
    fun _ step => fullEncode_nu_step_not_matched restricted
      (by
        simp [Process.actionCount, Process.inputCount, Process.outputCount,
          Process.replicationCount, Process.restrictionCount])
      step⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus
