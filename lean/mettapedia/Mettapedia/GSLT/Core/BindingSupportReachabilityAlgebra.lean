import Mathlib

/-!
# Support-directed reachability for fresh binding frames

A compiled rule pattern carries a finite set of source variables.  At one
activation epoch, materializing the pattern replaces each source variable by
its current binding, or by the corresponding unbound epoch variable.  An
occurs check does not need that materialized term when it can inspect the same
finite support directly.

The main theorem proves that direct support inspection and
materialize-then-reachability agree.  The negative canary records the important
boundary: a new epoch alone is insufficient once one of its variables has
already been bound to the target.  This is an admission law for an optimized
observer, not a model of every physical detail of a production matcher.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.BindingSupportReachabilityAlgebra

universe u

variable {Var : Type u} [DecidableEq Var]

/-- Finite syntactic variable support. -/
abbrev Support (Var : Type u) [DecidableEq Var] := Finset Var

/-- The logical variable graph exposed by one binding environment. -/
structure Environment (Var : Type u) [DecidableEq Var] where
  lookup : Var → Option (Support Var)

/-- Transitive reachability through binding values. -/
inductive Reaches (environment : Environment Var) : Var → Var → Prop
  | edge {source target value} :
      environment.lookup source = some value →
      target ∈ value →
      Reaches environment source target
  | trans {source middle target} :
      Reaches environment source middle →
      Reaches environment middle target →
      Reaches environment source target

/-- A term support reaches `target` either immediately or through bindings. -/
def supportReaches (environment : Environment Var)
    (support : Support Var) (target : Var) : Prop :=
  ∃ element ∈ support,
    element = target ∨ Reaches environment element target

/-- The support contributed by one source variable after materialization. -/
def materializedVariableSupport (environment : Environment Var)
    (element : Var) : Support Var :=
  (environment.lookup element).getD {element}

/-- The support of a materialized source pattern. -/
def materializedSupport (environment : Environment Var)
    (sourceSupport : Support Var) : Support Var :=
  sourceSupport.biUnion (materializedVariableSupport environment)

/-- Direct inspection of the compiled source support. -/
def directSourceReaches (environment : Environment Var)
    (sourceSupport : Support Var) (target : Var) : Prop :=
  ∃ source ∈ sourceSupport,
    match environment.lookup source with
    | none => source = target
    | some value => supportReaches environment value target

@[simp] theorem supportReaches_singleton
    (environment : Environment Var) (element target : Var) :
    supportReaches environment {element} target ↔
      element = target ∨ Reaches environment element target := by
  simp [supportReaches]

theorem not_reaches_of_unbound
    (environment : Environment Var) {source target : Var}
    (unbound : environment.lookup source = none) :
    ¬ Reaches environment source target := by
  intro reaches
  induction reaches with
  | edge bound _ => simp [unbound] at bound
  | trans first _ firstImpossible _ => exact firstImpossible unbound

/-- Direct support inspection commutes with materialization. -/
theorem directSourceReaches_iff_materialized
    (environment : Environment Var) (sourceSupport : Support Var)
    (target : Var) :
    directSourceReaches environment sourceSupport target ↔
      supportReaches environment
        (materializedSupport environment sourceSupport) target := by
  constructor
  · rintro ⟨source, sourceMember, direct⟩
    cases bound : environment.lookup source with
    | none =>
        simp only [bound] at direct
        refine ⟨source, ?_, Or.inl direct⟩
        rw [materializedSupport, Finset.mem_biUnion]
        exact ⟨source, sourceMember,
          by simp [materializedVariableSupport, bound]⟩
    | some value =>
        simp only [bound] at direct
        rcases direct with ⟨element, elementMember, reaches⟩
        refine ⟨element, ?_, reaches⟩
        rw [materializedSupport, Finset.mem_biUnion]
        exact ⟨source, sourceMember,
          by simpa [materializedVariableSupport, bound] using elementMember⟩
  · rintro ⟨element, elementMember, reaches⟩
    rw [materializedSupport, Finset.mem_biUnion] at elementMember
    obtain ⟨source, sourceMember, elementMember⟩ := elementMember
    refine ⟨source, sourceMember, ?_⟩
    cases bound : environment.lookup source with
    | none =>
        have elementEq : element = source := by
          simpa [materializedVariableSupport, bound] using elementMember
        subst element
        rcases reaches with equal | transitive
        · exact equal
        · exact False.elim
            (not_reaches_of_unbound environment bound transitive)
    | some value =>
        exact ⟨element,
          by simpa [materializedVariableSupport, bound] using elementMember,
          reaches⟩

/-! ## Epoch-separated canaries -/

section Epoch

variable {Epoch Base : Type u} [DecidableEq Epoch] [DecidableEq Base]

abbrev EpochVar (Epoch Base : Type u) := Epoch × Base

def tag (epoch : Epoch) (base : Base) : EpochVar Epoch Base := (epoch, base)

/-- If every source variable is genuinely unbound, a target from another
epoch cannot occur in the materialized support. -/
theorem unbound_fresh_epoch_absent
    (environment : Environment (EpochVar Epoch Base))
    (sourceSupport : Support Base) (epoch : Epoch)
    (target : EpochVar Epoch Base)
    (different : target.1 ≠ epoch)
    (unbound : ∀ base ∈ sourceSupport,
      environment.lookup (tag epoch base) = none) :
    ¬ directSourceReaches environment
      (sourceSupport.image (tag epoch)) target := by
  rintro ⟨source, sourceMember, direct⟩
  rw [Finset.mem_image] at sourceMember
  obtain ⟨base, baseMember, rfl⟩ := sourceMember
  rw [unbound base baseMember] at direct
  exact different (congrArg Prod.fst direct).symm

namespace Canaries

def unboundEnvironment : Environment (Nat × Nat) where
  lookup _ := none

example :
    ¬ directSourceReaches unboundEnvironment
      ({(7, 1), (7, 2)} : Support (Nat × Nat)) (3, 9) := by
  simp [directSourceReaches, unboundEnvironment]

/-- Negative control: a fresh epoch does not license absence after its source
slot has been bound to the target. -/
def reboundEnvironment : Environment (Nat × Nat) where
  lookup element :=
    if element = (7, 1) then some {(3, 9)} else none

example :
    directSourceReaches reboundEnvironment
      ({(7, 1)} : Support (Nat × Nat)) (3, 9) := by
  exact ⟨(7, 1), by simp, by simp [reboundEnvironment, supportReaches]⟩

example :
    supportReaches reboundEnvironment
      (materializedSupport reboundEnvironment {(7, 1)}) (3, 9) := by
  exact (directSourceReaches_iff_materialized
    reboundEnvironment {(7, 1)} (3, 9)).mp
      ⟨(7, 1), by simp, by simp [reboundEnvironment, supportReaches]⟩

end Canaries

end Epoch

#print axioms supportReaches_singleton
#print axioms not_reaches_of_unbound
#print axioms directSourceReaches_iff_materialized
#print axioms unbound_fresh_epoch_absent

end Mettapedia.GSLT.Core.BindingSupportReachabilityAlgebra
