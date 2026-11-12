import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralUnary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidGlb
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ArrowDecision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbDecided
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrows

/-!
# One solver for the decided fragments

**Absorption.** The glb-join fragment contains the other fragments of flex–flex families over telescopes of universe
families: the fragment of meet groups with several parameters (`inGlbJoinFragmentK_of_meetK`, no condition on
equivalent codomains) and the unary fragment of glb groups (`inGlbJoinFragmentK_of_glbGroups`; a declaration of several
parameters that occurs in no equation is kept apart, as in `SeveralUnary`).

**The pieces** (`Piece`, `InPiece`, `pieceSolver`): Miller patterns with the glb round, equations between arrow codes
with unknowns at domains and codomains (which contain the first-order arrow codes, without their chain), flex–rigid
equations with unknowns at codomains (which contain those without the chain), glb groups, and the glb join. Each is
decided by its own solver of the tree's driver, whose rounds keep its fragment.

**The combined run** (`unionRun`): a classifier reads which piece a store lies in, once, and that piece's solver runs; a
store read into no piece is reported pending (suspended, never refuted). With a sound classifier, every store it reads
into a piece is decided: from some budget on the run is fixed and ends with a principal answer or a certified refutation
(`unionRun_decided`). With the classifier that takes the first piece whose fragment holds (`firstPiece`), this is every
store of the union (`union_decided`).

**Why the piece is read once.** The solvers' ranks differ: the Miller solver's (weight, equations) and the arrow
solver's (unknowns, size) are lexicographic pairs; the others count equations. A store can move between pieces: a
decomposition of arrow codes leaves equations between unknowns, which are Miller equations, and a Miller store whose
equations with binders are solved leaves equations between unknowns, which are equations between arrow codes. A round
that re-reads the piece at every store needs one rank decreasing under every rule of every piece; the driver's ranks
are pairs of numbers, and the lexicographic sum of two such ranks does not fit in a pair.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Absorption -/

section Absorption

variable {S : Setting Head L} (algebra : CumulativeAlgebra S.R)

include algebra in
/-- **A unary glb-group compatibility crosses well.** -/
theorem crossCompat_of_glbCompat {p c p' c' : Head} (h : GlbCompat S.R p c p' c') :
    CrossCompat S.R [p] c [p'] c' := by
  rcases h with h | h
  · exact crossCompat_of_compatJ algebra (compatJ_of_compatK algebra (compatK_of_compat h))
  · exact fun _ => .cons (fun _ _ => ⟨h.2.2.1, h.2.2.2.1⟩) .nil

include algebra in
/-- **The fragment of meet groups with several parameters lies inside**, over a telescope of universe families; no
condition on equivalent codomains. -/
theorem inGlbJoinFragmentK_of_meetK {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InMeetFragmentK problem) (families : Miller.Families Θ) : InGlbJoinFragmentK problem := by
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  exact ⟨families, inside.shapes, ⟨group, grouped, fun i j ne together psi ci psj cj di dj =>
    crossCompat_of_compatJ algebra (compatJ_of_compatK algebra (comparable i j ne together psi ci psj cj di dj))⟩⟩

variable [DecidableEq Head]

include algebra in
/-- **The unary fragment of glb groups lies inside**, over a telescope of universe families. -/
theorem inGlbJoinFragmentK_of_glbGroups {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InGlbFragment problem) (families : Miller.Families Θ) : InGlbJoinFragmentK problem := by
  obtain ⟨group, grouped, comparable⟩ := inside.grouped
  have unaryOf : ∀ e ∈ problem, ∀ v : FitFlex e, isUnary Θ.raw v.left = true ∧ isUnary Θ.raw v.right = true :=
    fun _ _ v => ⟨isUnary_of v.declared_left, isUnary_of v.declared_right⟩
  refine ⟨families, fun e member => ?_, ⟨apartGroup Θ.raw group, fun e member u => ?_, ?_⟩⟩
  · obtain ⟨v⟩ := inside.shapes e member
    exact ⟨v.toK⟩
  · obtain ⟨v⟩ := inside.shapes e member
    obtain ⟨hl, hr⟩ := FlexK.unique u v.toK
    obtain ⟨ul, ur⟩ := unaryOf e member v
    unfold apartGroup
    rw [hl, hr]
    change (if isUnary Θ.raw v.left = true then 2 * group v.left else 2 * v.left.val + 1) =
      (if isUnary Θ.raw v.right = true then 2 * group v.right else 2 * v.right.val + 1)
    rw [if_pos ul, if_pos ur, grouped e member v]
  · intro i j ne same psi ci psj cj di dj
    unfold apartGroup at same
    by_cases ui : isUnary Θ.raw i = true <;> by_cases uj : isUnary Θ.raw j = true
    · rw [if_pos ui, if_pos uj] at same
      obtain ⟨pi, rfl⟩ := unary_shape di ui
      obtain ⟨pj, rfl⟩ := unary_shape dj uj
      exact crossCompat_of_glbCompat algebra (comparable i j ne (by omega) pi ci pj cj di dj)
    · rw [if_pos ui, if_neg uj] at same
      omega
    · rw [if_neg ui, if_pos uj] at same
      omega
    · rw [if_neg ui, if_neg uj] at same
      exact absurd (Fin.ext (by omega)) ne

end Absorption

/-! ## The pieces -/

/-- **The decided pieces.** -/
inductive Piece where
  | miller
  | arrows
  | flexRigid
  | glbGroups
  | glbJoin
  deriving DecidableEq

section Union

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Miller.Inhabitants S.R)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
  (declared : DeclaredTypesFormed S.R)
  (strengthening : ContextualDependentIntersectionGeneral.EqualStrengthening S.R)
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- **The fragment of a piece.** -/
def InPiece : Piece → {Θ : Context S.R} → EquationStore (TotalTerm Θ) → Prop
  | .miller, _, problem => Miller.InMillerGlb (S := S) problem
  | .arrows, _, problem => InArrowsCod choices problem
  | .flexRigid, _, problem => InFlexCod choices problem
  | .glbGroups, _, problem => InGlbFragment problem
  | .glbJoin, _, problem => InGlbJoinFragmentK problem

/-- **The solver of a piece.** -/
def pieceSolver : Piece → ContextualDependentWorklist.Solver S.levels
  | .miller => Miller.millerGlbSolver facts roots heads algebra rigid complete normalizes inh headsTyped glb spec
  | .arrows => arrowCodSolver choices glb spec facts roots heads algebra rigid complete headsTyped declared strengthening
  | .flexRigid => flexCodSolver choices glb spec facts roots heads algebra rigid complete headsTyped declared
  | .glbGroups => glbGroupSolver facts roots heads algebra rigid complete headsTyped glb spec
  | .glbJoin => glbJoinSolverK facts roots heads algebra rigid complete headsTyped join joinSound glb spec

/-- **The combined run**: the classifier reads the store's piece once and that piece's solver runs; a store read into
no piece is reported pending. -/
def unionRun (classify : ∀ {Θ : Context S.R}, EquationStore (TotalTerm Θ) → Option Piece) {Θ : Context S.R}
    (original : EquationStore (TotalTerm Θ)) (fuel : Nat) : Outcome S.levels original :=
  match classify original with
  | some k =>
      run (pieceSolver choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb
        spec k) original fuel
  | none => .stuck (Update.pending S.levels original)

theorem unionRun_of_picked (classify : ∀ {Θ : Context S.R}, EquationStore (TotalTerm Θ) → Option Piece)
    {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)} {k : Piece} (picked : classify original = some k)
    (fuel : Nat) :
    unionRun choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb spec
        classify original fuel =
      run (pieceSolver choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb
        spec k) original fuel := by
  unfold unionRun
  split
  · rename_i k' h
    have h' : classify original = some k' := h
    rw [picked] at h'
    cases h'
    rfl
  · rename_i h
    have h' : classify original = none := h
    rw [picked] at h'
    cases h'

/-- **A store read into no piece is pending**: its readout is suspended, never refuted. -/
theorem unionRun_of_none (classify : ∀ {Θ : Context S.R}, EquationStore (TotalTerm Θ) → Option Piece)
    {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)} (unread : classify original = none) (fuel : Nat) :
    (unionRun choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb spec
      classify original fuel).readout = .suspended := by
  unfold unionRun
  split
  · rename_i k h
    have h' : classify original = some k := h
    rw [unread] at h'
    cases h'
  · rfl

variable (joinTotal : ∀ {u v : Head}, S.R.isUniverse u → S.R.isUniverse v → ∃ w, join u v = some w)
  (glbTotal : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening joinSound spec joinTotal
  glbTotal in
/-- **Each piece is decided by its solver.** -/
theorem piece_decided (k : Piece) {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InPiece choices k original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (pieceSolver choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb
          spec k) original larger =
        run (pieceSolver choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb
          spec k) original fuel ∧
        ((∃ state finished,
            run (pieceSolver choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound
                glb spec k) original larger = .solved state finished ∧
              (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (pieceSolver choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound
              glb spec k) original larger = .refuted absent)) := by
  cases k with
  | miller =>
      exact Miller.millerGlb_decided facts roots heads algebra rigid complete normalizes inh headsTyped glb spec
        glbTotal inside
  | arrows =>
      exact arrowsCod_decided choices glb spec facts roots heads algebra rigid complete headsTyped declared strengthening
        glbTotal inside
  | flexRigid =>
      exact flexCod_decided choices glb spec facts roots heads algebra rigid complete headsTyped declared glbTotal inside
  | glbGroups => exact glbGroup_decided facts roots heads algebra rigid complete headsTyped glb spec glbTotal inside
  | glbJoin =>
      exact glbJoinK_decided facts roots heads algebra rigid complete headsTyped join joinSound glb spec joinTotal
        glbTotal inside

include facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening joinSound spec joinTotal
  glbTotal in
/-- **The combined run decides every store a sound classifier reads into a piece**: from some budget on the run is
fixed, and it ends with a principal answer or a certified refutation. -/
theorem unionRun_decided (classify : ∀ {Θ : Context S.R}, EquationStore (TotalTerm Θ) → Option Piece)
    (sound : ∀ {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {k : Piece}, classify problem = some k →
      InPiece choices k problem)
    {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)} {k : Piece} (picked : classify original = some k) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      unionRun choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb spec
          classify original larger =
        unionRun choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb spec
          classify original fuel ∧
        ((∃ state finished,
            unionRun choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb
                spec classify original larger = .solved state finished ∧
              (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            unionRun choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb
              spec classify original larger = .refuted absent)) := by
  obtain ⟨fuel, ends⟩ := piece_decided choices facts roots heads algebra rigid complete normalizes inh headsTyped
    declared strengthening join joinSound glb spec joinTotal glbTotal k (sound picked)
  refine ⟨fuel, fun larger enough => ?_⟩
  rw [unionRun_of_picked choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound
      glb spec classify picked larger,
    unionRun_of_picked choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound
      glb spec classify picked fuel]
  exact ends larger enough

/-- **The classifier that takes the first piece whose fragment holds**: Miller patterns, flex–rigid, arrow codes, the
glb join, glb groups. -/
noncomputable def firstPiece {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Option Piece := by
  classical
  exact if InPiece choices .miller problem then some .miller
    else if InPiece choices .flexRigid problem then some .flexRigid
    else if InPiece choices .arrows problem then some .arrows
    else if InPiece choices .glbJoin problem then some .glbJoin
    else if InPiece choices .glbGroups problem then some .glbGroups
    else none

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
theorem firstPiece_sound {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {k : Piece}
    (picked : firstPiece choices problem = some k) : InPiece choices k problem := by
  unfold firstPiece at picked
  split_ifs at picked with h1 h2 h3 h4 h5 <;> cases picked <;> assumption

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
theorem firstPiece_complete {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {k : Piece}
    (inside : InPiece choices k problem) : ∃ k', firstPiece choices problem = some k' := by
  unfold firstPiece
  split_ifs with h1 h2 h3 h4 h5
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · cases k with
    | miller => exact absurd inside h1
    | flexRigid => exact absurd inside h2
    | arrows => exact absurd inside h3
    | glbJoin => exact absurd inside h4
    | glbGroups => exact absurd inside h5

include facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening joinSound spec joinTotal
  glbTotal in
/-- **The union of the decided fragments is decided by one run**: every store of the union, from some budget on,
reaches a fixed outcome, a principal answer or a certified refutation. -/
theorem union_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : ∃ k, InPiece choices k original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      unionRun choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb spec
          (firstPiece choices) original larger =
        unionRun choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb spec
          (firstPiece choices) original fuel ∧
        ((∃ state finished,
            unionRun choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb
                spec (firstPiece choices) original larger = .solved state finished ∧
              (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            unionRun choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb
              spec (firstPiece choices) original larger = .refuted absent)) := by
  obtain ⟨k, inside⟩ := inside
  obtain ⟨k', picked⟩ := firstPiece_complete choices inside
  exact unionRun_decided choices facts roots heads algebra rigid complete normalizes inh headsTyped declared strengthening join joinSound glb
    spec joinTotal glbTotal (firstPiece choices) (firstPiece_sound choices) picked

end Union

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
