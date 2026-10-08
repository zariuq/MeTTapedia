import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2Grammar
import Mathlib.Data.List.Perm.Basic

/-!
# Two orders of the same instantiated MM2 writes

The row-major profile applies each matched row's authored sinks before
moving to the next row. The existing source profile stages all rows for
each sink. Both retain their literal execution order; agreement is proved
only for the compact-key support observation under commuting writes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorWrites

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

inductive Write where
  | add (atom : Atom)
  | remove (atom : Atom)
  deriving DecidableEq

def Write.atom : Write → Atom
  | .add atom | .remove atom => atom

def Write.adds : Write → Bool
  | .add _ => true
  | .remove _ => false

def Write.apply (space : List Atom) : Write → List Atom
  | .add atom => morkInsertSupport space atom
  | .remove atom => morkEraseSupport space atom

def support (space : List Atom) : Finset MorkSupportKey :=
  (space.map morkSupportKey).toFinset

def Write.onSupport (keys : Finset MorkSupportKey) : Write → Finset MorkSupportKey
  | .add atom => insert (morkSupportKey atom) keys
  | .remove atom => keys.erase (morkSupportKey atom)

def Allowed : Sink → Prop
  | .add _ | .remove _ => True
  | .head _ _ | .tail _ _ => False

/-- Output-local variables and opaque captures use the source instantiator.
The admitted native grammar has no extrema sinks. -/
def instantiate (input : InputSpec) (row : Subst) : Sink → Option Write
  | .add atom => (instantiateRuleTemplateAtom? input row atom).map Write.add
  | .remove atom => (instantiateRuleTemplateAtom? input row atom).map Write.remove
  | .head _ _ | .tail _ _ => none

def one (input : InputSpec) (row : Subst) (space : List Atom) (sink : Sink) : List Atom :=
  match instantiate input row sink with
  | none => space
  | some write => write.apply space

def row (input : InputSpec) (sinks : List Sink) (space : List Atom) (substitution : Subst) :
    List Atom := sinks.foldl (one input substitution) space

def rows (input : InputSpec) (substitutions : List Subst) (sinks : List Sink)
    (space : List Atom) : List Atom :=
  substitutions.foldl (row input sinks) space

def rowWrites (input : InputSpec) (substitutions : List Subst) (sinks : List Sink) :
    List Write :=
  substitutions.flatMap fun substitution =>
    sinks.flatMap fun sink => (instantiate input substitution sink).toList

def sinkWrites (input : InputSpec) (substitutions : List Subst) (sinks : List Sink) :
    List Write :=
  sinks.flatMap fun sink =>
    substitutions.flatMap fun substitution => (instantiate input substitution sink).toList

theorem support_insert (space : List Atom) (atom : Atom) :
    support (morkInsertSupport space atom) = insert (morkSupportKey atom) (support space) := by
  unfold morkInsertSupport
  split
  · rename_i present
    have member : morkSupportKey atom ∈ support space := by
      simpa [support] using (morkSupportContains_eq_true_iff_key_mem space atom).mp present
    exact (Finset.insert_eq_of_mem member).symm
  · simp [support]

theorem support_remove (space : List Atom) (atom : Atom) :
    support (morkEraseSupport space atom) = (support space).erase (morkSupportKey atom) := by
  ext key
  simp only [support, List.mem_toFinset, List.mem_map, morkEraseSupport,
    List.mem_filter, sameMorkSupportAtom, Finset.mem_erase]
  constructor
  · rintro ⟨candidate, ⟨member, different⟩, equal⟩
    have differentKey : morkSupportKey candidate ≠ morkSupportKey atom := by
      simpa using different
    exact ⟨equal ▸ differentKey, candidate, member, equal⟩
  · rintro ⟨different, candidate, member, equal⟩
    exact ⟨candidate, ⟨member, by simpa [equal] using different⟩, equal⟩

theorem write_support (space : List Atom) (write : Write) :
    support (write.apply space) = write.onSupport (support space) := by
  cases write with
  | add atom => exact support_insert space atom
  | remove atom => exact support_remove space atom

theorem execute_support (writes : List Write) (space : List Atom) :
    support (writes.foldl Write.apply space) = writes.foldl Write.onSupport (support space) := by
  induction writes generalizing space with
  | nil => rfl
  | cons write writes ih =>
      simp only [List.foldl_cons, ih, write_support]

theorem row_ordered_writes (input : InputSpec) (sinks : List Sink) (space : List Atom)
    (substitution : Subst) :
    row input sinks space substitution =
      (sinks.flatMap fun sink => (instantiate input substitution sink).toList).foldl
        Write.apply space := by
  induction sinks generalizing space with
  | nil => rfl
  | cons sink sinks ih =>
      simp only [row, List.foldl_cons, List.flatMap_cons, List.foldl_append] at ih ⊢
      rw [ih]
      cases instantiated : instantiate input substitution sink <;>
        simp [one, instantiated]

theorem rows_ordered_writes (input : InputSpec) (substitutions : List Subst)
    (sinks : List Sink) (space : List Atom) :
    rows input substitutions sinks space = (rowWrites input substitutions sinks).foldl
      Write.apply space := by
  induction substitutions generalizing space with
  | nil => rfl
  | cons substitution rest ih =>
      simp only [rows, List.foldl_cons, rowWrites, List.flatMap_cons,
        List.foldl_append] at ih ⊢
      rw [ih, row_ordered_writes]

theorem rectangle_permutation {A B C : Type*} (first : List A) (second : List B)
    (cell : A → B → List C) :
    (first.flatMap fun a => second.flatMap (cell a)).Perm
      (second.flatMap fun b => first.flatMap fun a => cell a b) := by
  induction first with
  | nil => simp
  | cons a rest ih =>
      simp only [List.flatMap_cons]
      exact (ih.append_left _).trans
        (List.flatMap_append_perm second (cell a) (fun b => rest.flatMap fun a => cell a b))

theorem writes_permutation (input : InputSpec) (substitutions : List Subst)
    (sinks : List Sink) :
    (rowWrites input substitutions sinks).Perm (sinkWrites input substitutions sinks) :=
  rectangle_permutation substitutions sinks
    (fun substitution sink => (instantiate input substitution sink).toList)

/-- Equal-polarity writes commute on support. Opposite polarities require
distinct physical keys; literal variable spelling is not the criterion. -/
def Independent (first second : Write) : Prop :=
  first.adds = second.adds ∨ morkSupportKey first.atom ≠ morkSupportKey second.atom

theorem independent_commutes (first second : Write) (independent : Independent first second)
    (keys : Finset MorkSupportKey) :
    second.onSupport (first.onSupport keys) = first.onSupport (second.onSupport keys) := by
  cases first <;> cases second <;>
    simp only [Independent, Write.adds, Write.atom] at independent <;>
    ext key <;> simp only [Write.onSupport, Finset.mem_insert, Finset.mem_erase] <;>
    aesop

theorem commuting_orders (input : InputSpec) (substitutions : List Subst)
    (sinks : List Sink) (space : List Atom)
    (independent : ∀ first ∈ rowWrites input substitutions sinks,
      ∀ second ∈ rowWrites input substitutions sinks, Independent first second) :
    support (rows input substitutions sinks space) =
      (sinkWrites input substitutions sinks).foldl Write.onSupport (support space) := by
  rw [rows_ordered_writes, execute_support]
  exact (writes_permutation input substitutions sinks).foldl_eq'
    (fun first firstMem second secondMem keys =>
      independent_commutes first second (independent first firstMem second secondMem) keys) _

theorem write_nodup (space : List Atom) (write : Write) (normalized : MorkSupportNodup space) :
    MorkSupportNodup (write.apply space) := by
  cases write with
  | add atom => exact morkInsertSupport_nodup space atom normalized
  | remove atom => exact morkEraseSupport_nodup space atom normalized

theorem rows_nodup (input : InputSpec) (substitutions : List Subst) (sinks : List Sink)
    (space : List Atom) (normalized : MorkSupportNodup space) :
    MorkSupportNodup (rows input substitutions sinks space) := by
  rw [rows_ordered_writes]
  generalize rowWrites input substitutions sinks = writes
  induction writes generalizing space with
  | nil => exact normalized
  | cons write writes ih => exact ih _ (write_nodup space write normalized)

@[simp] theorem support_nil : support [] = ∅ := rfl

@[simp] theorem support_cons (atom : Atom) (rest : List Atom) :
    support (atom :: rest) = insert (morkSupportKey atom) (support rest) := by
  simp [support]

theorem union_support (space staged : List Atom) :
    support (morkUnionSupport space staged) = support space ∪ support staged := by
  induction staged generalizing space with
  | nil => simp [morkUnionSupport]
  | cons atom rest ih =>
      change support (morkUnionSupport (morkInsertSupport space atom) rest) = _
      rw [ih, support_insert, support_cons]
      ext key
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto

theorem subtract_support (space staged : List Atom) :
    support (morkSubtractSupport space staged) = support space \ support staged := by
  induction staged generalizing space with
  | nil => simp [morkSubtractSupport]
  | cons atom rest ih =>
      change support (morkSubtractSupport (morkEraseSupport space atom) rest) = _
      rw [ih, support_remove, support_cons]
      ext key
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto

theorem staging_support (input : InputSpec) (sink : Sink) (substitutions : List Subst)
    (staged : List Atom) :
    support (substitutions.foldl (stageRuleScopedSink input sink) staged) =
      support staged ∪ support
        (substitutions.filterMap fun substitution =>
          instantiateRuleTemplateAtom? input substitution sink.atom) := by
  induction substitutions generalizing staged with
  | nil => simp
  | cons substitution rest ih =>
      rw [List.foldl_cons, ih]
      cases result : instantiateRuleTemplateAtom? input substitution sink.atom with
      | none => simp [stageRuleScopedSink, result]
      | some atom =>
          simp only [stageRuleScopedSink, result, support_insert,
            List.filterMap_cons, support_cons]
          ext key
          simp only [Finset.mem_union, Finset.mem_insert]
          tauto

theorem add_fold_support (input : InputSpec) (atom : Atom) (substitutions : List Subst)
    (keys : Finset MorkSupportKey) :
    (substitutions.flatMap fun substitution =>
      (instantiate input substitution (.add atom)).toList).foldl Write.onSupport keys =
      keys ∪ support (substitutions.filterMap fun substitution =>
        instantiateRuleTemplateAtom? input substitution atom) := by
  induction substitutions generalizing keys with
  | nil => simp
  | cons substitution rest ih =>
      simp only [List.flatMap_cons, List.foldl_append]
      rw [ih]
      cases result : instantiateRuleTemplateAtom? input substitution atom with
      | none => simp [instantiate, result]
      | some value =>
          simp only [instantiate, result, Option.map_some, Option.toList_some,
            List.foldl_cons, List.foldl_nil, Write.onSupport, List.filterMap_cons,
            support_cons]
          ext key
          simp only [Finset.mem_union, Finset.mem_insert]
          tauto

theorem remove_fold_support (input : InputSpec) (atom : Atom) (substitutions : List Subst)
    (keys : Finset MorkSupportKey) :
    (substitutions.flatMap fun substitution =>
      (instantiate input substitution (.remove atom)).toList).foldl Write.onSupport keys =
      keys \ support (substitutions.filterMap fun substitution =>
        instantiateRuleTemplateAtom? input substitution atom) := by
  induction substitutions generalizing keys with
  | nil => simp
  | cons substitution rest ih =>
      simp only [List.flatMap_cons, List.foldl_append]
      rw [ih]
      cases result : instantiateRuleTemplateAtom? input substitution atom with
      | none => simp [instantiate, result]
      | some value =>
          simp only [instantiate, result, Option.map_some, Option.toList_some,
            List.foldl_cons, List.foldl_nil, Write.onSupport, List.filterMap_cons,
            support_cons]
          ext key
          simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
          tauto

theorem single_source_sink_support (input : InputSpec) (substitutions : List Subst)
    (sink : Sink) (allowed : Allowed sink) (space : List Atom) :
    support (finalizeRuleScopedSink sink
      (substitutions.foldl (stageRuleScopedSink input sink) []) space) =
      (substitutions.flatMap fun substitution =>
        (instantiate input substitution sink).toList).foldl Write.onSupport (support space) := by
  cases sink with
  | add atom =>
      rw [add_fold_support]
      simp only [finalizeRuleScopedSink, union_support, staging_support,
        support_nil, Finset.empty_union, Sink.atom]
  | remove atom =>
      rw [remove_fold_support]
      simp only [finalizeRuleScopedSink, subtract_support, staging_support,
        support_nil, Finset.empty_union, Sink.atom]
  | head => cases allowed
  | tail => cases allowed

theorem source_ordered_writes (input : InputSpec) (substitutions : List Subst)
    (sinks : List Sink) (allowed : ∀ sink ∈ sinks, Allowed sink) (space : List Atom) :
    support (cApplyRuleScopedSinkBatch input substitutions space sinks) =
      (sinkWrites input substitutions sinks).foldl Write.onSupport (support space) := by
  induction sinks generalizing space with
  | nil => rfl
  | cons sink rest ih =>
      simp only [cApplyRuleScopedSinkBatch, sinkWrites, List.flatMap_cons,
        List.foldl_append]
      rw [ih (fun other member => allowed other (by simp [member])),
        single_source_sink_support input substitutions sink (allowed sink (by simp))]
      rfl

/-- The two actual finalizers agree on compact-key support whenever every
pair of instantiated writes has compatible polarity or distinct keys. -/
theorem source_agreement (input : InputSpec) (substitutions : List Subst)
    (sinks : List Sink) (allowed : ∀ sink ∈ sinks, Allowed sink) (space : List Atom)
    (independent : ∀ first ∈ rowWrites input substitutions sinks,
      ∀ second ∈ rowWrites input substitutions sinks, Independent first second) :
    support (rows input substitutions sinks space) =
      support (cApplyRuleScopedSinkBatch input substitutions space sinks) := by
  rw [source_ordered_writes input substitutions sinks allowed]
  exact commuting_orders input substitutions sinks space independent

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorWrites
