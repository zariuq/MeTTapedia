import Mettapedia.SetTheory.Profiles.CommonCoreClassicalLogic
import Mettapedia.SetTheory.Profiles.Instances

/-!
# The common material core in hypersets and well-founded sets

Both carriers validate the same independently stated first-order sentences
and interpret deductions from those sentences. Their operations are the
existing quotient constructions, including their actual infinite sets.
The full separation operations validate the bounded schema in the common
core without promoting full Separation to a native common law.

No inaccessible-cardinal hypothesis or object-language choice operator is
needed here. Additional classical semantic consequences are kept separate
from syntactic derivability in any particular native profile.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.CommonCoreClassical

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula substitute)
open ContextualMaterialSetTheory
open ContextualMaterialFormulaSemantics (behindHeadTwo)
open Mettapedia.SetTheory.CarveOuts.Sites (Tarski)
open CommonCoreClassicalLogic (substitute_iff proof_sound)

universe u

/-- Concrete operations sufficient for the common core. This interface is
instantiated below in both existing carriers. -/
structure Operations (S : Type u) (member : S → S → Prop) where
  empty : S
  pair : S → S → S
  union : S → S
  separate : (S → Prop) → S → S
  infinity : S
  successor : S → S
  empty_spec : ∀ child, ¬ member child empty
  pair_spec : ∀ first second child, member child (pair first second) ↔ child = first ∨ child = second
  union_spec : ∀ parent child, member child (union parent) ↔ ∃ middle, member middle parent ∧ member child middle
  separate_spec : ∀ predicate parent child, member child (separate predicate parent) ↔ member child parent ∧ predicate child
  infinity_empty : member empty infinity
  infinity_successor : ∀ child, member child infinity → member (successor child) infinity
  successor_spec : ∀ parent child, member child (successor parent) ↔ member child parent ∨ child = parent
  extensionality : ∀ first second, (∀ child, member child first ↔ member child second) → first = second

variable {S : Type u} {member : S → S → Prop}

theorem empty_valid (operations : Operations S member) (environment : Fin 0 → S) :
    Tarski member emptyAxiom environment :=
  ⟨operations.empty, operations.empty_spec⟩

theorem pairing_valid (operations : Operations S member) (environment : Fin 0 → S) :
    Tarski member pairingAxiom environment := by
  intro first second
  exact ⟨operations.pair first second, fun child =>
    ⟨(operations.pair_spec first second child).mp, (operations.pair_spec first second child).mpr⟩⟩

theorem union_valid (operations : Operations S member) (environment : Fin 0 → S) :
    Tarski member unionAxiom environment := by
  intro parent
  exact ⟨operations.union parent, fun child =>
    ⟨(operations.union_spec parent child).mp, (operations.union_spec parent child).mpr⟩⟩

theorem infinity_valid (operations : Operations S member) (environment : Fin 0 → S) :
    Tarski member infinityAxiom environment := by
  refine ⟨operations.infinity, ⟨operations.empty, operations.empty_spec, operations.infinity_empty⟩, ?_⟩
  intro child belongs
  exact ⟨operations.successor child,
    fun value => ⟨(operations.successor_spec child value).mp, (operations.successor_spec child value).mpr⟩,
    operations.infinity_successor child belongs⟩

theorem extensionality_valid (operations : Operations S member) (environment : Fin 2 → S) :
    Tarski member extensionalityAxiom environment := by
  intro agrees
  exact operations.extensionality (environment 0) (environment 1)
    (fun child => ⟨(agrees child).1, (agrees child).2⟩)

theorem separation_valid (operations : Operations S member) {count : Nat}
    (body : Formula (count+1)) (environment : Fin count → S) :
    Tarski member (separationAxiom body) environment := by
  intro parent
  let predicate := fun child => Tarski member body (Fin.cases child environment)
  refine ⟨operations.separate predicate parent, ?_⟩
  intro child
  have assignment : (fun index =>
      Fin.cases child (Fin.cases (operations.separate predicate parent) (Fin.cases parent environment))
        (behindHeadTwo index)) = Fin.cases child environment := by
    funext index
    exact Fin.cases rfl (fun _ => rfl) index
  have shifted := substitute_iff member behindHeadTwo body
    (Fin.cases child (Fin.cases (operations.separate predicate parent) (Fin.cases parent environment)))
  rw [assignment] at shifted
  constructor
  · intro belongs
    have selected := (operations.separate_spec predicate parent child).mp belongs
    exact ⟨selected.1, shifted.mpr selected.2⟩
  · intro selected
    exact (operations.separate_spec predicate parent child).mpr ⟨selected.1, shifted.mp selected.2⟩

/-- Validation is recursive on the authored adoption, including its
actual substitution spine. -/
theorem validate (operations : Operations S member) {count : Nat} {body : Formula count}
    (adopted : CommonCore.Axiom body) (environment : Fin count → S) :
    Tarski member body environment := by
  induction adopted with
  | empty => exact empty_valid operations environment
  | pairing => exact pairing_valid operations environment
  | union => exact union_valid operations environment
  | infinity => exact infinity_valid operations environment
  | extensionality => exact extensionality_valid operations environment
  | boundedSeparation body => exact separation_valid operations _ environment
  | substitution indices _ inductionHypothesis =>
      exact (substitute_iff member indices _ environment).mpr (inductionHypothesis _)

theorem interpret (operations : Operations S member) {count : Nat} {body : Formula count}
    (derivation : CommonCore.Derivation body) (environment : Fin count → S) :
    Tarski member body environment :=
  proof_sound member derivation.proof environment
    (fun index => validate operations (derivation.adopted index) environment)

/-- The actual well-founded quotient carrier, with its existing operations. -/
def wellFoundedOperations : Operations ZFSet.{u} (· ∈ ·) where
  empty := ∅
  pair first second := {first, second}
  union := ZFSet.sUnion
  separate := ZFSet.sep
  infinity := ZFSet.omega
  successor value := insert value value
  empty_spec := ZFSet.notMem_empty
  pair_spec _ _ _ := ZFSet.mem_pair
  union_spec _ _ := ZFSet.mem_sUnion
  separate_spec _ _ _ := ZFSet.mem_sep
  infinity_empty := ZFSet.omega_zero
  infinity_successor _ := ZFSet.omega_succ
  successor_spec _ _ := ZFSet.mem_insert_iff.trans or_comm
  extensionality _ _ := ZFSet.ext

/-- The natural-number set is included through the actual membership
embedding; all other operations are formed directly on hypersets. -/
def hypersetOperations : Operations HSet.{u} (· ∈ ·) where
  empty := ∅
  pair first second := {first, second}
  union := HSet.sUnion
  separate := HSet.sep
  infinity := HSet.ofZFSet ZFSet.omega
  successor value := insert value value
  empty_spec := HSet.notMem_empty
  pair_spec _ _ _ := HSet.mem_pair
  union_spec _ _ := HSet.mem_sUnion
  separate_spec _ _ _ := HSet.mem_sep
  infinity_empty := by
    rw [← HSet.ofZFSet_empty]
    exact HSet.ofZFSet_mem_ofZFSet_iff.mpr ZFSet.omega_zero
  infinity_successor child belongs := by
    obtain ⟨value, included, rfl⟩ := HSet.mem_ofZFSet_iff.mp belongs
    rw [← HSet.ofZFSet_insert]
    exact HSet.ofZFSet_mem_ofZFSet_iff.mpr (ZFSet.omega_succ included)
  successor_spec _ _ := HSet.mem_insert_iff.trans or_comm
  extensionality _ _ := HSet.ext

theorem wellFounded_validate {count : Nat} {body : Formula count}
    (adopted : CommonCore.Axiom body) (environment : Fin count → ZFSet.{u}) :
    Tarski (· ∈ ·) body environment := validate wellFoundedOperations adopted environment

theorem hyperset_validate {count : Nat} {body : Formula count}
    (adopted : CommonCore.Axiom body) (environment : Fin count → HSet.{u}) :
    Tarski (· ∈ ·) body environment := validate hypersetOperations adopted environment

theorem wellFounded_interpret {count : Nat} {body : Formula count}
    (derivation : CommonCore.Derivation body) (environment : Fin count → ZFSet.{u}) :
    Tarski (· ∈ ·) body environment := interpret wellFoundedOperations derivation environment

theorem hyperset_interpret {count : Nat} {body : Formula count}
    (derivation : CommonCore.Derivation body) (environment : Fin count → HSet.{u}) :
    Tarski (· ∈ ·) body environment := interpret hypersetOperations derivation environment

/-- A sentence not adopted by the common core. -/
def quineSentence : Formula 0 :=
  .exist (.all (equivalent (.member 0 1) (.equal 0 1)))

theorem hyperset_quine (environment : Fin 0 → HSet.{u}) :
    Tarski (· ∈ ·) quineSentence environment :=
  ⟨HSet.quineAtom, fun _ => ⟨HSet.mem_quineAtom.mp, HSet.mem_quineAtom.mpr⟩⟩

theorem wellFounded_no_quine (environment : Fin 0 → ZFSet.{u}) :
    ¬ Tarski (· ∈ ·) quineSentence environment := by
  rintro ⟨value, satisfies⟩
  exact ZFSet.mem_irrefl value ((satisfies value).2 rfl)

theorem wellFounded_foundation (environment : Fin 0 → ZFSet.{u}) :
    Tarski (· ∈ ·) CommonCore.foundationAxiom environment := by
  intro parent inhabited
  have nonempty : parent ≠ ∅ := by
    rintro rfl
    obtain ⟨child, belongs⟩ := inhabited
    exact ZFSet.notMem_empty child belongs
  obtain ⟨minimal, belongs, disjoint⟩ := ZFSet.regularity parent nonempty
  refine ⟨minimal, belongs, ?_⟩
  intro child below alsoIn
  have impossible : child ∈ parent ∩ minimal := ZFSet.mem_inter.mpr ⟨alsoIn, below⟩
  rw [disjoint] at impossible
  exact ZFSet.notMem_empty child impossible

theorem hyperset_not_foundation (environment : Fin 0 → HSet.{u}) :
    ¬ Tarski (· ∈ ·) CommonCore.foundationAxiom environment := by
  intro foundation
  obtain ⟨minimal, belongs, disjoint⟩ := foundation HSet.quineAtom
    ⟨HSet.quineAtom, HSet.quineAtom_mem_self⟩
  have same : minimal = HSet.quineAtom := HSet.mem_quineAtom.mp belongs
  subst minimal
  exact disjoint HSet.quineAtom HSet.quineAtom_mem_self HSet.quineAtom_mem_self

/-- Thus the shared proof calculus cannot prove regularity. -/
theorem foundation_not_derivable : ¬ Nonempty (CommonCore.Derivation CommonCore.foundationAxiom) := by
  rintro ⟨proof⟩
  exact hyperset_not_foundation.{0} Fin.elim0 (hyperset_interpret proof Fin.elim0)

/-- Nor does the shared proof calculus decide in favor of a Quine atom. -/
theorem quine_not_derivable : ¬ Nonempty (CommonCore.Derivation quineSentence) := by
  rintro ⟨proof⟩
  exact wellFounded_no_quine.{0} Fin.elim0 (wellFounded_interpret proof Fin.elim0)

end Mettapedia.SetTheory.Profiles.CommonCoreClassical
