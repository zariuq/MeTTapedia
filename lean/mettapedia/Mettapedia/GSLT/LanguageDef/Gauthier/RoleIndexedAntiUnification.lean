/-
# Role-indexed first-order anti-unification for Gauthier programs

The mathematical anti-unification is performed on unfolded ranked terms.
Hole identity is the triple `(role,left subtree,right subtree)`.  This is an
executable memo key: repeated disagreement pairs reuse exactly one hole, while
the same pair in code and value positions cannot alias.  Numeric hole names
are an export concern and have no bearing on canonicity.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.Gauthier.SharedProgramDAG

namespace Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierProgramDAG

universe u

/-- Root, higher-order-code, and ordinary-value contexts are distinct sorts
of anti-unification holes. -/
inductive HoleRole where
  | root
  | code
  | value
  deriving DecidableEq, Repr

def childHoleRole (entry : Entry σ) (index : Nat) : HoleRole :=
  if index < entry.hoArity then .code else .value

def childHoleRoleAt (sig : Signature σ) (op index : Nat) : HoleRole :=
  match entryAt sig op with
  | none => .value
  | some entry => childHoleRole entry index

/-- Canonical memo key for one disagreement.  Storing the actual ranked terms
keeps the trusted algorithm independent of hash collisions. -/
structure HoleKey where
  role : HoleRole
  left : Prog
  right : Prog
  deriving DecidableEq, Repr

/-- First-order patterns over the established Gauthier operator ids. -/
inductive Pattern where
  | hole : HoleKey → Pattern
  | node : Nat → List Pattern → Pattern
  deriving Repr

mutual

/-- Executable structural equality for anti-unification patterns. -/
def patternDecEq : (left right : Pattern) → Decidable (left = right)
  | .hole left, .hole right =>
      match decEq left right with
      | isTrue h => isTrue (by simp [h])
      | isFalse h => isFalse (fun equality => h (Pattern.hole.inj equality))
  | .hole _, .node _ _ => isFalse (by intro equality; cases equality)
  | .node _ _, .hole _ => isFalse (by intro equality; cases equality)
  | .node leftOp leftChildren, .node rightOp rightChildren =>
      match decEq leftOp rightOp with
      | isFalse hop => isFalse (fun equality => hop (Pattern.node.inj equality).1)
      | isTrue hop =>
          match patternListDecEq leftChildren rightChildren with
          | isFalse hchildren =>
              isFalse (fun equality => hchildren (Pattern.node.inj equality).2)
          | isTrue hchildren => isTrue (by simp [hop, hchildren])
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf; omega

/-- Executable structural equality for vectors of patterns. -/
def patternListDecEq : (left right : List Pattern) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro equality; cases equality)
  | _ :: _, [] => isFalse (by intro equality; cases equality)
  | left :: lefts, right :: rights =>
      match patternDecEq left right with
      | isFalse hhead => isFalse (fun equality => hhead (List.cons.inj equality).1)
      | isTrue hhead =>
          match patternListDecEq lefts rights with
          | isFalse htail => isFalse (fun equality => htail (List.cons.inj equality).2)
          | isTrue htail => isTrue (by simp [hhead, htail])
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf; omega

end

instance : DecidableEq Pattern := patternDecEq

abbrev TermSubstitution := HoleKey → Prog
abbrev PatternSubstitution := HoleKey → Pattern

def leftSubstitution : TermSubstitution := fun key => key.left
def rightSubstitution : TermSubstitution := fun key => key.right

/-- Total first-order instantiation. -/
def instantiate (substitution : TermSubstitution) : Pattern → Prog
  | .hole key => substitution key
  | .node op children => .node op (children.map (instantiate substitution))

/-- Pattern-for-hole instantiation, used for the generalization order. -/
def instantiatePattern (substitution : PatternSubstitution) : Pattern → Pattern
  | .hole key => substitution key
  | .node op children => .node op (children.map (instantiatePattern substitution))

/-- `general` is at least as general as `specific`. -/
def MoreGeneral (general specific : Pattern) : Prop :=
  ∃ substitution, instantiatePattern substitution general = specific

mutual

/-- Deterministic Plotkin anti-unification.  Matching ranked constructors are
retained; every other pair becomes its canonical role-indexed memo key. -/
def lgg (sig : Signature σ) (role : HoleRole) : Prog → Prog → Pattern
  | left@(.node leftOp leftChildren), right@(.node rightOp rightChildren) =>
      if leftOp = rightOp ∧ leftChildren.length = rightChildren.length then
        .node leftOp (lggChildren sig leftOp 0 leftChildren rightChildren)
      else
        .hole { role, left, right }
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf; omega

/-- Pairwise anti-unification of equally positioned child vectors. -/
def lggChildren (sig : Signature σ) (parentOp index : Nat) :
    List Prog → List Prog → List Pattern
  | left :: lefts, right :: rights =>
      lgg sig (childHoleRoleAt sig parentOp index) left right ::
        lggChildren sig parentOp (index + 1) lefts rights
  | _, _ => []
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf; omega

end

mutual

/-- Structural weight used to interleave recursion on a program with recursion
on its child vector. -/
def progWeight : Prog → Nat
  | .node _ children => progListWeight children + 1

def progListWeight : List Prog → Nat
  | [] => 0
  | head :: tail => progWeight head + progListWeight tail

end


mutual

/-- Structural weight used for mutual induction on patterns and child vectors. -/
def patternWeight : Pattern → Nat
  | .hole _ => 1
  | .node _ children => patternListWeight children + 1

def patternListWeight : List Pattern → Nat
  | [] => 0
  | head :: tail => patternWeight head + patternListWeight tail

end

/-- The left projection of every memo key reconstructs the left input. -/
theorem instantiate_left_lgg (sig : Signature σ) (role : HoleRole)
    (left right : Prog) :
    instantiate leftSubstitution (lgg sig role left right) = left := by
  exact Prog.rec
    (motive_1 := fun source => ∀ (signature : Signature σ)
      (sourceRole : HoleRole) (target : Prog),
      instantiate leftSubstitution
        (lgg signature sourceRole source target) = source)
    (motive_2 := fun sources => ∀ (signature : Signature σ)
      (parentOp index : Nat) (targets : List Prog),
      sources.length = targets.length →
      (lggChildren signature parentOp index sources targets).map
        (instantiate leftSubstitution) = sources)
    (fun sourceOp sources childrenResult signature sourceRole target => by
      cases target with
      | node targetOp targets =>
          rw [lgg]
          by_cases hsame : sourceOp = targetOp ∧
              sources.length = targets.length
          · simp only [hsame, if_true, instantiate, Prog.node.injEq, true_and]
            have hop := hsame.1
            subst targetOp
            exact childrenResult signature sourceOp 0 targets hsame.2
          · simp [hsame, instantiate, leftSubstitution])
    (by
      intro signature parentOp index targets hlength
      cases targets with
      | nil => simp only [lggChildren.eq_def, List.map_nil]
      | cons _ _ => simp at hlength)
    (fun source sources sourceResult sourcesResult signature parentOp index
        targets hlength => by
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          simp only [lggChildren, List.map_cons, List.cons.injEq]
          exact ⟨sourceResult signature
              (childHoleRoleAt signature parentOp index) target,
            sourcesResult signature parentOp (index + 1) targets hlength⟩)
    left sig role right

/-- The right projection of every memo key reconstructs the right input. -/
theorem instantiate_right_lgg (sig : Signature σ) (role : HoleRole)
    (left right : Prog) :
    instantiate rightSubstitution (lgg sig role left right) = right := by
  exact Prog.rec
    (motive_1 := fun source => ∀ (signature : Signature σ)
      (sourceRole : HoleRole) (target : Prog),
      instantiate rightSubstitution
        (lgg signature sourceRole source target) = target)
    (motive_2 := fun sources => ∀ (signature : Signature σ)
      (parentOp index : Nat) (targets : List Prog),
      sources.length = targets.length →
      (lggChildren signature parentOp index sources targets).map
        (instantiate rightSubstitution) = targets)
    (fun sourceOp sources childrenResult signature sourceRole target => by
      cases target with
      | node targetOp targets =>
          rw [lgg]
          by_cases hsame : sourceOp = targetOp ∧
              sources.length = targets.length
          · simp only [hsame, if_true, instantiate, Prog.node.injEq, true_and]
            have hop := hsame.1
            subst targetOp
            exact childrenResult signature sourceOp 0 targets hsame.2
          · simp [hsame, instantiate, rightSubstitution])
    (by
      intro signature parentOp index targets hlength
      cases targets with
      | nil => simp only [lggChildren.eq_def, List.map_nil]
      | cons _ _ => simp at hlength)
    (fun source sources sourceResult sourcesResult signature parentOp index
        targets hlength => by
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          simp only [lggChildren, List.map_cons, List.cons.injEq]
          exact ⟨sourceResult signature
              (childHoleRoleAt signature parentOp index) target,
            sourcesResult signature parentOp (index + 1) targets hlength⟩)
    left sig role right

/-- Reconstruction transports the original well-formedness proofs to both
returned substitutions. -/
theorem lgg_substitutions_wellFormed {sig : Signature σ} {role : HoleRole}
    {left right : Prog} (hleft : WellFormed sig left)
    (hright : WellFormed sig right) :
    WellFormed sig (instantiate leftSubstitution (lgg sig role left right)) ∧
      WellFormed sig (instantiate rightSubstitution (lgg sig role left right)) := by
  rw [instantiate_left_lgg, instantiate_right_lgg]
  exact ⟨hleft, hright⟩

/-- Pairwise traversal preserves vector length when the two input vectors have
the same length. -/
theorem lggChildren_length (sig : Signature σ) (parentOp index : Nat)
    (left right : List Prog) (hlength : left.length = right.length) :
    (lggChildren sig parentOp index left right).length = left.length := by
  induction left generalizing right index with
  | nil =>
      cases right with
      | nil => simp only [lggChildren.eq_def, List.length_nil]
      | cons _ _ => simp at hlength
  | cons head tail ih =>
      cases right with
      | nil => simp at hlength
      | cons rightHead rightTail =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          simp [lggChildren, ih (index + 1) rightTail hlength]

mutual

/-- Every occurrence of a hole reports the context in which it occurs. -/
inductive RolesCorrect (sig : Signature σ) : HoleRole → Pattern → Prop where
  | hole {role : HoleRole} {key : HoleKey} :
      key.role = role → RolesCorrect sig role (.hole key)
  | node {role : HoleRole} {op : Nat} {children : List Pattern}
      {entry : Entry σ} :
      entryAt sig op = some entry →
      children.length = entry.arity →
      RolesCorrectChildren sig entry 0 children →
      RolesCorrect sig role (.node op children)

inductive RolesCorrectChildren (sig : Signature σ) :
    Entry σ → Nat → List Pattern → Prop where
  | nil {entry : Entry σ} {index : Nat} : RolesCorrectChildren sig entry index []
  | cons {entry : Entry σ} {index : Nat} {head : Pattern} {tail : List Pattern} :
      RolesCorrect sig (childHoleRole entry index) head →
      RolesCorrectChildren sig entry (index + 1) tail →
      RolesCorrectChildren sig entry index (head :: tail)

end

/-- Well-formed input programs produce an arity-correct pattern whose holes
are confined to their code/value contexts. -/
theorem lgg_rolesCorrect {sig : Signature σ} {role : HoleRole}
    {left right : Prog} (hleft : WellFormed sig left)
    (hright : WellFormed sig right) :
    RolesCorrect sig role (lgg sig role left right) := by
  exact Prog.rec
    (motive_1 := fun source => ∀ (signature : Signature σ)
      (sourceRole : HoleRole) (target : Prog),
      WellFormed signature source → WellFormed signature target →
      RolesCorrect signature sourceRole
        (lgg signature sourceRole source target))
    (motive_2 := fun sources => ∀ (signature : Signature σ)
      (parentOp index : Nat) (targets : List Prog) (entry : Entry σ),
      entryAt signature parentOp = some entry →
      sources.length = targets.length →
      (∀ program ∈ sources, WellFormed signature program) →
      (∀ program ∈ targets, WellFormed signature program) →
      RolesCorrectChildren signature entry index
        (lggChildren signature parentOp index sources targets))
    (fun sourceOp sources childrenResult signature sourceRole target
        hsource htarget => by
      cases target with
      | node targetOp targets =>
          rw [lgg]
          by_cases hsame : sourceOp = targetOp ∧
              sources.length = targets.length
          · rw [if_pos hsame]
            have hop := hsame.1
            subst targetOp
            cases hsource with
            | node hentry hsourceLength hsourceChildren =>
              cases htarget with
              | node _ _ htargetChildren =>
                refine RolesCorrect.node hentry ?_ ?_
                · rw [lggChildren_length signature sourceOp 0 sources targets
                    hsame.2]
                  exact hsourceLength
                · exact childrenResult signature sourceOp 0 targets _ hentry
                    hsame.2 hsourceChildren htargetChildren
          · rw [if_neg hsame]
            exact RolesCorrect.hole rfl)
    (by
      intro signature parentOp index targets entry hentry hlength _ _
      cases targets with
      | nil => simpa only [lggChildren.eq_def] using
          (RolesCorrectChildren.nil :
            RolesCorrectChildren signature entry index [])
      | cons _ _ => simp at hlength)
    (fun source sources sourceResult sourcesResult signature parentOp index
        targets entry hentry hlength hsource htarget => by
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          rw [lggChildren]
          apply RolesCorrectChildren.cons
          · simpa [childHoleRoleAt, hentry] using
              sourceResult signature (childHoleRole entry index) target
                (hsource source (by simp)) (htarget target (by simp))
          · apply sourcesResult signature parentOp (index + 1) targets entry
              hentry hlength
            · intro program hprogram
              exact hsource program (by simp [hprogram])
            · intro program hprogram
              exact htarget program (by simp [hprogram]))
    left sig role right hleft hright

/-- A single canonical memo key cannot be shared across incompatible roles. -/
theorem holeKey_role_injective {left right : Prog} {first second : HoleRole}
    (h : ({ role := first, left, right } : HoleKey) =
      { role := second, left, right }) :
    first = second := by
  exact congrArg HoleKey.role h

/-- Canonical renaming that exchanges the two input projections. -/
def swapHoleKey (key : HoleKey) : HoleKey :=
  { role := key.role, left := key.right, right := key.left }

def renameHoles (f : HoleKey → HoleKey) : Pattern → Pattern
  | .hole key => .hole (f key)
  | .node op children => .node op (children.map (renameHoles f))

/-- Swapping the inputs changes only hole names; the retained ranked skeleton
is canonical. -/
theorem renameHoles_swap_lgg (sig : Signature σ) (role : HoleRole)
    (left right : Prog) :
    renameHoles swapHoleKey (lgg sig role left right) =
      lgg sig role right left := by
  exact Prog.rec
    (motive_1 := fun source => ∀ (signature : Signature σ)
      (sourceRole : HoleRole) (target : Prog),
      renameHoles swapHoleKey (lgg signature sourceRole source target) =
        lgg signature sourceRole target source)
    (motive_2 := fun sources => ∀ (signature : Signature σ)
      (parentOp index : Nat) (targets : List Prog),
      sources.length = targets.length →
      (lggChildren signature parentOp index sources targets).map
          (renameHoles swapHoleKey) =
        lggChildren signature parentOp index targets sources)
    (fun sourceOp sources childrenResult signature sourceRole target => by
      cases target with
      | node targetOp targets =>
          simp only [lgg]
          by_cases hsame : sourceOp = targetOp ∧
              sources.length = targets.length
          · have hreverse : targetOp = sourceOp ∧
                targets.length = sources.length :=
              ⟨hsame.1.symm, hsame.2.symm⟩
            rw [if_pos hsame, if_pos hreverse]
            have hop := hsame.1
            subst targetOp
            simp only [renameHoles, Pattern.node.injEq, true_and]
            exact childrenResult signature sourceOp 0 targets hsame.2
          · have hreverse : ¬(targetOp = sourceOp ∧
                targets.length = sources.length) := by
              intro h
              exact hsame ⟨h.1.symm, h.2.symm⟩
            rw [if_neg hsame, if_neg hreverse]
            simp [renameHoles, swapHoleKey])
    (by
      intro signature parentOp index targets hlength
      cases targets with
      | nil => simp only [lggChildren.eq_def, List.map_nil]
      | cons _ _ => simp at hlength)
    (fun source sources sourceResult sourcesResult signature parentOp index
        targets hlength => by
      cases targets with
      | nil => simp at hlength
      | cons target targets =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          simp only [lggChildren, List.map_cons, List.cons.injEq]
          exact ⟨sourceResult signature
              (childHoleRoleAt signature parentOp index) target,
            sourcesResult signature parentOp (index + 1) targets hlength⟩)
    left sig role right

/-! ## Leastness among role-respecting generalizers -/

/-- A role-respecting common generalizer of two terms. -/
structure Generalizes (sig : Signature σ) (role : HoleRole)
    (pattern : Pattern) (left right : Prog) where
  roles : RolesCorrect sig role pattern
  leftSubstitution : TermSubstitution
  rightSubstitution : TermSubstitution
  instantiateLeft : instantiate leftSubstitution pattern = left
  instantiateRight : instantiate rightSubstitution pattern = right

/-- The canonical specialization induced by a common generalizer's two term
substitutions. -/
def lggSpecialization (sig : Signature σ)
    (left right : TermSubstitution) : PatternSubstitution :=
  fun key => lgg sig key.role (left key) (right key)

/-- Specializing every hole of a role-correct pattern by the LGG of its two
images agrees with taking the LGG after term instantiation. -/
theorem instantiatePattern_lggSpecialization (sig : Signature σ)
    (left right : TermSubstitution) (role : HoleRole) (pattern : Pattern)
    (hroles : RolesCorrect sig role pattern) :
    instantiatePattern (lggSpecialization sig left right) pattern =
      lgg sig role (instantiate left pattern) (instantiate right pattern) := by
  exact Pattern.rec
    (motive_1 := fun source => ∀ (sourceRole : HoleRole),
      RolesCorrect sig sourceRole source →
      instantiatePattern (lggSpecialization sig left right) source =
        lgg sig sourceRole (instantiate left source) (instantiate right source))
    (motive_2 := fun sources => ∀ (parentOp index : Nat) (entry : Entry σ),
      entryAt sig parentOp = some entry →
      RolesCorrectChildren sig entry index sources →
      sources.map (instantiatePattern (lggSpecialization sig left right)) =
        lggChildren sig parentOp index
          (sources.map (instantiate left)) (sources.map (instantiate right)))
    (fun key sourceRole hsource => by
      cases hsource with
      | hole hrole =>
          subst sourceRole
          simp [instantiatePattern, lggSpecialization, instantiate])
    (fun op sources childrenResult sourceRole hsource => by
      cases hsource with
      | node hentry hlength hchildren =>
          simp only [instantiatePattern, instantiate, lgg]
          rw [if_pos (by simp)]
          simp only [Pattern.node.injEq, true_and]
          exact childrenResult op 0 _ hentry hchildren)
    (by
      intro parentOp index entry hentry _
      simp only [List.map_nil, lggChildren.eq_def])
    (fun source sources sourceResult sourcesResult parentOp index entry hentry
        hsource => by
      cases hsource with
      | cons hhead htail =>
          simp only [List.map_cons, lggChildren, List.cons.injEq]
          exact ⟨by
              simpa [childHoleRoleAt, hentry] using
                sourceResult (childHoleRole entry index) hhead,
            sourcesResult parentOp (index + 1) entry hentry htail⟩)
    pattern role hroles

/-- Plotkin leastness: every role-respecting common generalizer specializes to
the canonical memoized LGG. -/
theorem generalizer_specializes_to_lgg {sig : Signature σ}
    {role : HoleRole} {pattern : Pattern} {left right : Prog}
    (generalizer : Generalizes sig role pattern left right) :
    instantiatePattern
        (lggSpecialization sig generalizer.leftSubstitution
          generalizer.rightSubstitution)
        pattern = lgg sig role left right := by
  calc
    instantiatePattern
          (lggSpecialization sig generalizer.leftSubstitution
            generalizer.rightSubstitution) pattern =
        lgg sig role
          (instantiate generalizer.leftSubstitution pattern)
          (instantiate generalizer.rightSubstitution pattern) :=
      instantiatePattern_lggSpecialization sig
        generalizer.leftSubstitution generalizer.rightSubstitution role pattern
        generalizer.roles
    _ = lgg sig role left right := by
      rw [generalizer.instantiateLeft, generalizer.instantiateRight]

/-- Consequently the computed pattern is least in the ordinary first-order
generalization preorder. -/
theorem lgg_least {sig : Signature σ} {role : HoleRole}
    {pattern : Pattern} {left right : Prog}
    (generalizer : Generalizes sig role pattern left right) :
    MoreGeneral pattern (lgg sig role left right) := by
  exact ⟨lggSpecialization sig generalizer.leftSubstitution
    generalizer.rightSubstitution,
    generalizer_specializes_to_lgg generalizer⟩

/-! ## Required positive and negative examples -/

def zero : Prog := .node 0 []
def one : Prog := .node 1 []
def repeatedLeft : Prog := .node 3 [zero, zero]
def repeatedRight : Prog := .node 3 [one, one]

def repeatedKey : HoleKey := { role := .value, left := zero, right := one }

theorem repeated_disagreement_reuses_one_hole :
    lgg orgMemoSignature .root repeatedLeft repeatedRight =
      .node 3 [.hole repeatedKey, .hole repeatedKey] := by
  simp [repeatedLeft, repeatedRight, zero, one, lgg, lggChildren,
    repeatedKey, childHoleRoleAt, childHoleRole, orgMemoSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.orgSignature,
    Mettapedia.GSLT.LanguageDef.GauthierE2.listOps, entryAt, listGet?, entry]

def freshSecondKey : HoleKey :=
  { role := .value, left := one, right := zero }

def freshAtEveryMismatch : Pattern :=
  .node 3 [.hole repeatedKey, .hole freshSecondKey]

/-- Fresh variables at every occurrence are strictly too general: they can be
specialized to the repeated-hole LGG. -/
theorem fresh_mismatch_specializes_to_memoized :
    MoreGeneral freshAtEveryMismatch
      (.node 3 [.hole repeatedKey, .hole repeatedKey]) := by
  refine ⟨fun key => if key = freshSecondKey then .hole repeatedKey else .hole key, ?_⟩
  simp [instantiatePattern, freshAtEveryMismatch, repeatedKey, freshSecondKey,
    zero, one]

/-- The reverse specialization is impossible, so fresh-per-occurrence output
is not least. -/
theorem memoized_not_specialize_to_fresh_mismatch :
    ¬ MoreGeneral (.node 3 [.hole repeatedKey, .hole repeatedKey])
      freshAtEveryMismatch := by
  rintro ⟨substitution, h⟩
  simp only [instantiatePattern, freshAtEveryMismatch] at h
  injection h with _ hchildren
  have hfirst := congrArg (fun xs => xs[0]?) hchildren
  have hsecond := congrArg (fun xs => xs[1]?) hchildren
  simp [repeatedKey, freshSecondKey] at hfirst hsecond
  have hholes : Pattern.hole repeatedKey = Pattern.hole freshSecondKey :=
    hfirst.symm.trans hsecond
  have hkeys : repeatedKey = freshSecondKey := Pattern.hole.inj hholes
  have hzeroOne : zero ≠ one := by simp [zero, one]
  exact hzeroOne (congrArg HoleKey.left hkeys)

def codeValueRoleConflict : Pattern :=
  .node 9 [.hole repeatedKey, .hole repeatedKey, .hole repeatedKey]

/-- Operator 9 has one higher-order child.  Reusing a value-role hole there is
rejected by the role contract. -/
theorem role_blind_reuse_rejected :
    ¬ RolesCorrect orgMemoSignature .root codeValueRoleConflict := by
  intro hroles
  cases hroles with
  | node hentry _ hchildren =>
      cases hchildren with
      | cons hhead _ =>
          cases hhead with
          | hole hrole =>
              have htable : entryAt orgMemoSignature 9 =
                  some (entry "loop" 3 1
                    Mettapedia.GSLT.LanguageDef.GauthierE2.Prim.loop) := rfl
              rw [htable] at hentry
              injection hentry with hentry
              subst hentry
              simp [childHoleRole, repeatedKey, entry] at hrole

def leftNested : Prog := .node 3 [zero, .node 3 [zero, zero]]
def rightNested : Prog := .node 3 [.node 3 [zero, zero], zero]

/-- Equal postfix positions need not be equal tree coordinates: position two
is a leaf in the left tree and the inner constructor in the right tree. -/
theorem token_position_not_tree_coordinate :
    (rpnTokens leftNested)[2]? = some 0 ∧
      (rpnTokens rightNested)[2]? = some 3 := by
  simp [leftNested, rightNested, zero, rpnTokens]

#print axioms instantiate_left_lgg
#print axioms instantiate_right_lgg
#print axioms lgg_substitutions_wellFormed
#print axioms lgg_rolesCorrect
#print axioms holeKey_role_injective
#print axioms renameHoles_swap_lgg
#print axioms generalizer_specializes_to_lgg
#print axioms lgg_least
#print axioms repeated_disagreement_reuses_one_hole
#print axioms memoized_not_specialize_to_fresh_mismatch
#print axioms role_blind_reuse_rejected
#print axioms token_position_not_tree_coordinate

end Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification
