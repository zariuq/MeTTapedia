import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidDecomposition

/-!
# General permutation: bringing a deep metavariable to the newest position

The pattern rule solves the newest metavariable, and adjacent exchange reaches the one below it. A
solvable metavariable deeper in the context stays out of reach. **Rotation** moves the declaration
at depth `j` to the newest position, past the `j` later declarations, each strengthened so that it
no longer mentions the moved one; the moved declaration is weakened past them.

A **renaming isomorphism** of contexts, mutually inverse renamings compatible with every declared
type in both directions, gives a solver update that loses nothing: every solution factors through
it and nothing is chosen. The rotated context is computed from the store; its formation is checked
by the executable context checker, and its compatibility in both directions and the inverse law are
decided. When all checks pass, the store moves along the isomorphism and the pattern rule runs at
the new newest declaration.

The **permuting round** runs the rigid round and, when that round is stuck, tries every rotation
deeper than the two newest declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPermutation

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentPatternSolver

variable {Head : Type}

/-! ## Renaming isomorphisms of contexts -/

section Iso

variable {rules : Rules Head}

/-- A renaming compatible with every declared type is a context morphism. -/
def renamingHom {Θ Θ' : Context rules} (π : Ren Θ.arity Θ'.arity) (compatible : CtxRen Θ.raw Θ'.raw π) : Θ' ⟶ Θ :=
  ⟨renSub π, fun index => by
    change Typed rules Θ'.raw (.var (π index)) (subst (renSub π) (Ctx.lookup Θ.raw index))
    rw [subst_renSub, ← compatible index]
    exact .var _⟩

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

/-- **A renaming isomorphism of contexts is an update that loses nothing.** The store moves along
the renaming; every solution factors through it. -/
def ofRenamingIso {Θ Θ' : Context rules} (problem : EquationStore (TotalTerm Θ)) (π : Ren Θ.arity Θ'.arity)
    (π' : Ren Θ'.arity Θ.arity) (forth : CtxRen Θ.raw Θ'.raw π) (back : CtxRen Θ'.raw Θ.raw π')
    (inverse : ∀ i, π' (π i) = i) : Update levels problem :=
  ContextualDependentPrune.ofRetraction levels problem (renamingHom π forth) (renamingHom π' back)
    (Hom.ext (funext fun index => congrArg Tm.var (inverse index)))

theorem ofRenamingIso_target {Θ Θ' : Context rules} (problem : EquationStore (TotalTerm Θ)) (π : Ren Θ.arity Θ'.arity)
    (π' : Ren Θ'.arity Θ.arity) (forth : CtxRen Θ.raw Θ'.raw π) (back : CtxRen Θ'.raw Θ.raw π')
    (inverse : ∀ i, π' (π i) = i) : (ofRenamingIso levels problem π π' forth back inverse).target = Θ' := rfl

/-- The moved store has the original solutions, transported. -/
theorem ofRenamingIso_solvable_iff {Θ Θ' : Context rules} (problem : EquationStore (TotalTerm Θ))
    (π : Ren Θ.arity Θ'.arity) (π' : Ren Θ'.arity Θ.arity) (forth : CtxRen Θ.raw Θ'.raw π)
    (back : CtxRen Θ'.raw Θ.raw π') (inverse : ∀ i, π' (π i) = i) :
    (frames levels).Solvable problem ↔
      (frames levels).Solvable (ofRenamingIso levels problem π π' forth back inverse).remaining :=
  (ofRenamingIso levels problem π π' forth back inverse).solvable_iff

end Iso

/-! ## Rotation -/

/-- Move the variable at depth `depth` to depth `0`; the variables above it move down by one. -/
def rotRen (n depth : Nat) : Ren n n := fun i =>
  if i.val = depth then ⟨0, by have := i.isLt; omega⟩
  else if h : i.val < depth ∧ i.val + 1 < n then ⟨i.val + 1, h.2⟩ else i

/-- The inverse of `rotRen`. -/
def rotInv (n depth : Nat) : Ren n n := fun i =>
  if i.val = 0 then (if h : depth < n then ⟨depth, h⟩ else i)
  else if h : i.val ≤ depth then ⟨i.val - 1, by have := i.isLt; omega⟩ else i

/-- **The rotated telescope**: the declaration at depth `depth` moved to the newest position, the
later declarations strengthened past it, the moved one weakened past them. A later declaration that
mentions the moved one has no strengthening, and rotation fails. -/
def rotateRaw : {n : Nat} → Ctx Head n → Nat → Option (Ctx Head n)
  | _, context, 0 => some context
  | _, .nil, _ + 1 => none
  | _, .snoc earlier later, depth + 1 =>
      match rotateRaw earlier depth with
      | none => none
      | some rotated =>
          match rotated with
          | .nil => none
          | .snoc below moved =>
              (ContextualDependentInversion.invert (ContextualDependentPatternSolver.withoutNewest _)
                  (rename (rotRen _ depth) later)).map fun strengthened =>
                .snoc (.snoc below strengthened) (rename wk moved)

/-! ## The rotation rule -/

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- Rotate the declaration at one depth to the newest position, then run the pattern rule there. -/
def rotateAt (fuel depth : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  match rotateRaw Θ.raw depth with
  | none => none
  | some raw =>
      match ExecutableChecking.formContext S.R choices reducer fuel raw with
      | none => none
      | some checked =>
          if forth : CtxRen Θ.raw raw (rotRen Θ.arity depth) then
            if back : CtxRen raw Θ.raw (rotInv Θ.arity depth) then
              if inverse : ∀ i, rotInv Θ.arity depth (rotRen Θ.arity depth i) = i then
                let rotated : Context S.R :=
                  ⟨Θ.arity, raw, ExecutableChecking.ContextAlgorithm.sound facts roots heads algebra declared checked.down⟩
                let moved := ofRenamingIso S.levels problem (Θ' := rotated) (rotRen Θ.arity depth)
                  (rotInv Θ.arity depth) forth back inverse
                match patternRule rigid facts complete roots heads algebra declared choices reducer root normalizes
                    certifyNormal fuel moved.remaining with
                | some (.solved solved smaller) => some (.solved (moved.then solved) smaller)
                | some (.refuted absent) => some (.refuted fun solvable => absent (moved.solvable_iff.mp solvable))
                | none => none
              else none
            else none
          else none

/-- Try the depths in turn. -/
def rotateSearch (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    List Nat → Option (Found problem)
  | [] => none
  | depth :: rest =>
      match rotateAt rigid complete facts roots heads algebra declared choices reducer root normalizes certifyNormal
          fuel depth problem with
      | some found => some found
      | none => rotateSearch fuel problem rest

/-- **The rotation rule**: every depth below the two newest declarations. -/
def rotateRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option (Found problem) :=
  rotateSearch rigid complete facts roots heads algebra declared choices reducer root normalizes certifyNormal fuel
    problem (List.range' 2 (Θ.arity - 2))

/-- **One permuting round**: the rigid round, and when it is stuck, the rotation rule. -/
def permutingRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels size problem :=
  match ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared choices
      reducer root normalizes certifyNormal headTypingUnique fuel problem with
  | .stuck =>
      match rotateRule rigid complete facts roots heads algebra declared choices reducer root normalizes certifyNormal
          fuel problem with
      | some (.solved update smaller) => .progress update (Prod.Lex.left _ _ smaller)
      | some (.refuted absent) => .refuted absent
      | none => .stuck
  | .progress update smaller => .progress update smaller
  | .refuted absent => .refuted absent

/-- **The permuting solver.** -/
def permutingSolver (fuel : Nat) : Solver S.levels where
  rank := size
  round := permutingRound rigid complete facts roots heads algebra declared choices reducer root normalizes
    certifyNormal headTypingUnique fuel

/-- **The permuting round loses no solution and refutes only with a certificate**: every refutation
is the rigid round's, or the pattern rule's after a renaming isomorphism. -/
theorem permutingRound_refuted {fuel : Nat} {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {absent : ¬ (frames S.levels).Solvable problem}
    (refuted : permutingRound rigid complete facts roots heads algebra declared choices reducer root normalizes
      certifyNormal headTypingUnique fuel problem = .refuted absent) :
    (∃ absent', ContextualDependentRigidDecomposition.rigidRound rigid complete facts roots heads algebra declared
        choices reducer root normalizes certifyNormal headTypingUnique fuel problem = .refuted absent') ∨
      ∃ absent', rotateRule rigid complete facts roots heads algebra declared choices reducer root normalizes
        certifyNormal fuel problem = some (.refuted absent') := by
  unfold permutingRound at refuted
  split at refuted
  · split at refuted
    · cases refuted
    · rename_i absent' computed
      exact .inr ⟨absent', computed⟩
    · cases refuted
  · cases refuted
  · rename_i absent' computed
    exact .inl ⟨absent', computed⟩

end ContextualDependentPermutation
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
