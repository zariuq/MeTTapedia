/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.PeTTaSpec.PrologMgu
Purpose: Deterministic, most-general first-order unification over canonical
  Prolog trees.
Trusted boundary: none
Main exports: TreeMgu, TreesMgu, TreeIsMgu
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.PeTTaSpec.PrologTermAlgebra

namespace Mettapedia.Languages.MeTTa.PLeaTTa.PeTTaSpec.PrologCore.Canonical

/-!
The resolver needs more than an existential statement that some substitution
works.  This module specifies the ordered Robinson-style choices themselves:
reflexivity first, then left-variable elimination, then right-variable
elimination, then rigid-node decomposition from left to right.  It is stated
over the canonical tree algebra, so proper/dotted list presentation cannot
change the result.

The finite-tree occurs check is explicit.  SWI's rational-tree extension is
therefore outside this certified local fragment rather than silently folded
into it.
-/

abbrev TreeEquation := Tree × Tree

/-- Ordered pointwise equations.  Callers that construct an MGU derivation
also prove equal length; the mismatch cases remain total but carry no semantic
claim on their own. -/
def treeEquations : List Tree → List Tree → List TreeEquation
  | left :: lefts, right :: rights =>
      (left, right) :: treeEquations lefts rights
  | _, _ => []

/-- Pointwise unification in the canonical algebra. -/
def TreeUnifiesEquations (binding : TreeSubstitution)
    (equations : List TreeEquation) : Prop :=
  ∀ equation, equation ∈ equations →
    TreeSubstitution.apply binding equation.1 =
      TreeSubstitution.apply binding equation.2

/-- Canonical substitution factorization. -/
def TreeFactorsThrough (specific general : TreeSubstitution) : Prop :=
  ∃ residual : TreeSubstitution, ∀ tree,
    TreeSubstitution.apply specific tree =
      TreeSubstitution.apply residual
        (TreeSubstitution.apply general tree)

/-- Most-generality over every canonical tree, not only the finite terms in
one regression corpus. -/
def TreeIsMgu (binding : TreeSubstitution)
    (equations : List TreeEquation) : Prop :=
  TreeUnifiesEquations binding equations ∧
    ∀ candidate, TreeUnifiesEquations candidate equations →
      TreeFactorsThrough candidate binding

/-- Apply one substitution to both sides of every equation. -/
def TreeSubstitution.applyEquations (binding : TreeSubstitution)
    (equations : List TreeEquation) : List TreeEquation :=
  equations.map fun equation =>
    (TreeSubstitution.apply binding equation.1,
      TreeSubstitution.apply binding equation.2)

/-- Empty constraints have the identity MGU. -/
theorem tree_empty_is_mgu : TreeIsMgu [] [] := by
  constructor
  · intro equation member
    simp at member
  · intro candidate _
    exact ⟨candidate, fun _ => rfl⟩

/-- A reflexive canonical equation contributes no binding. -/
theorem tree_reflexive_is_mgu (tree : Tree) :
    TreeIsMgu [] [(tree, tree)] := by
  constructor
  · intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    rfl
  · intro candidate _
    exact ⟨candidate, fun _ => rfl⟩

/-- One absent variable can be eliminated most-generally. -/
theorem tree_singleton_variable_is_mgu (source : LogicVar) (value : Tree)
    (absent : Tree.occurs source value = false) :
    TreeIsMgu [(source, value)] [(.variable source, value)] := by
  constructor
  · intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    simp only [TreeSubstitution.apply, Tree.instantiateOne, ite_true]
    exact (Tree.instantiateOne_eq_self_of_occurs_false source value value
      absent).symm
  · intro candidate candidateUnifies
    have identifies :
        TreeSubstitution.apply candidate (.variable source) =
          TreeSubstitution.apply candidate value :=
      candidateUnifies (.variable source, value) (by simp)
    refine ⟨candidate, ?_⟩
    intro tree
    change TreeSubstitution.apply candidate tree =
      TreeSubstitution.apply candidate
        (Tree.instantiateOne source value tree)
    exact (TreeSubstitution.apply_instantiateOne_of_unifier candidate source
      value identifies tree).symm

/-- Generic MGU composition for an ordered prefix and an already-instantiated
suffix.  This is the algebraic workhorse behind left-to-right child
unification. -/
theorem TreeIsMgu.compose_append
    {base extension : TreeSubstitution}
    {prior suffix : List TreeEquation}
    (baseMgu : TreeIsMgu base prior)
    (extensionMgu : TreeIsMgu extension
      (TreeSubstitution.applyEquations base suffix)) :
    TreeIsMgu (extension ++ base) (prior ++ suffix) := by
  constructor
  · intro equation member
    rcases List.mem_append.mp member with old | new
    · rw [TreeSubstitution.apply_append,
          TreeSubstitution.apply_append]
      exact congrArg (TreeSubstitution.apply extension)
        (baseMgu.1 equation old)
    · have normalized :
          (TreeSubstitution.apply base equation.1,
              TreeSubstitution.apply base equation.2) ∈
            TreeSubstitution.applyEquations base suffix := by
        exact List.mem_map_of_mem new
      have resolved := extensionMgu.1 _ normalized
      simpa [TreeSubstitution.apply_append] using resolved
  · intro candidate candidateUnifies
    have candidatePrefix : TreeUnifiesEquations candidate prior := by
      intro equation member
      exact candidateUnifies equation (List.mem_append_left _ member)
    rcases baseMgu.2 candidate candidatePrefix with
      ⟨residual, candidateFactors⟩
    have residualSuffix : TreeUnifiesEquations residual
        (TreeSubstitution.applyEquations base suffix) := by
      intro normalized normalizedMember
      simp only [TreeSubstitution.applyEquations, List.mem_map]
        at normalizedMember
      obtain ⟨equation, member, rfl⟩ := normalizedMember
      rw [← candidateFactors equation.1, ← candidateFactors equation.2]
      exact candidateUnifies equation (List.mem_append_right _ member)
    rcases extensionMgu.2 residual residualSuffix with
      ⟨final, residualFactors⟩
    refine ⟨final, ?_⟩
    intro tree
    rw [candidateFactors tree,
      residualFactors (TreeSubstitution.apply base tree),
      TreeSubstitution.apply_append]

/-! ## Ordered canonical MGU derivations -/

mutual

/-- Deterministic root priority plus recursive rigid-node decomposition. -/
inductive TreeMgu : Tree → Tree → TreeSubstitution → Prop where
  | reflexive (tree : Tree) : TreeMgu tree tree []
  | bindLeft (source : LogicVar) (value : Tree)
      (different : value ≠ .variable source)
      (absent : Tree.occurs source value = false) :
      TreeMgu (.variable source) value [(source, value)]
  | bindRight (value : Tree) (target : LogicVar)
      (notVariable : ∀ identity, value ≠ .variable identity)
      (absent : Tree.occurs target value = false) :
      TreeMgu value (.variable target) [(target, value)]
  | node {binding : TreeSubstitution} (symbol : RigidSymbol)
      (left right : List Tree)
      (different : left ≠ right) (children : TreesMgu left right binding) :
      TreeMgu (.node symbol left) (.node symbol right) binding

/-- Equal-arity children are unified left-to-right.  The head MGU is applied
to every remaining child before the tail derivation proceeds. -/
inductive TreesMgu : List Tree → List Tree →
    TreeSubstitution → Prop where
  | nil : TreesMgu [] [] []
  | cons (left right : Tree) (lefts rights : List Tree)
      (base extension : TreeSubstitution)
      (head : TreeMgu left right base)
      (tail : TreesMgu (TreeSubstitution.applyTrees base lefts)
        (TreeSubstitution.applyTrees base rights) extension) :
      TreesMgu (left :: lefts) (right :: rights) (extension ++ base)

end

/-- Prove the tree and ordered-forest laws from the same constructor cases.
In the forest case the tail is solved after applying the exact head binding,
and its extension precedes that binding in the result. -/
theorem TreeMgu.inductBoth
    {tree : Tree → Tree → TreeSubstitution → Prop}
    {forest : List Tree → List Tree → TreeSubstitution → Prop}
    (same : ∀ value, tree value value [])
    (bindLeft : ∀ source value, value ≠ .variable source →
      Tree.occurs source value = false → tree (.variable source) value [(source, value)])
    (bindRight : ∀ value target, (∀ identity, value ≠ .variable identity) →
      Tree.occurs target value = false → tree value (.variable target) [(target, value)])
    (node : ∀ {binding} symbol left right, left ≠ right →
      TreesMgu left right binding → forest left right binding →
        tree (.node symbol left) (.node symbol right) binding)
    (empty : forest [] [] [])
    (cons : ∀ left right lefts rights base extension,
      TreeMgu left right base →
      TreesMgu (TreeSubstitution.applyTrees base lefts)
        (TreeSubstitution.applyTrees base rights) extension →
      tree left right base →
      forest (TreeSubstitution.applyTrees base lefts)
        (TreeSubstitution.applyTrees base rights) extension →
      forest (left :: lefts) (right :: rights) (extension ++ base)) :
    (∀ {left right binding}, TreeMgu left right binding → tree left right binding) ∧
      (∀ {left right binding}, TreesMgu left right binding → forest left right binding) :=
  ⟨fun derivation => TreeMgu.rec
    (motive_1 := fun left right binding _ => tree left right binding)
    (motive_2 := fun left right binding _ => forest left right binding)
    same bindLeft bindRight node empty cons derivation,
  fun derivation => TreesMgu.rec
    (motive_1 := fun left right binding _ => tree left right binding)
    (motive_2 := fun left right binding _ => forest left right binding)
    same bindLeft bindRight node empty cons derivation⟩

/-- One replacement preserves child-list length. -/
@[simp] theorem Trees.instantiateOne_length (source : LogicVar)
    (replacement : Tree) (trees : List Tree) :
    (Trees.instantiateOne source replacement trees).length = trees.length := by
  induction trees with
  | nil => rfl
  | cons tree trees induction =>
      simp only [Trees.instantiateOne, List.length_cons, induction]

/-- Tree substitution preserves child-list length. -/
@[simp] theorem TreeSubstitution.applyTrees_length
    (binding : TreeSubstitution) (trees : List Tree) :
    (TreeSubstitution.applyTrees binding trees).length = trees.length := by
  induction binding with
  | nil => rfl
  | cons entry binding induction =>
      rcases entry with ⟨source, replacement⟩
      simp only [TreeSubstitution.applyTrees, Trees.instantiateOne_length,
        induction]

/-- Every child derivation is arity preserving. -/
theorem TreesMgu.length_eq {left right : List Tree}
    {binding : TreeSubstitution} (derivation : TreesMgu left right binding) :
    left.length = right.length := by
  exact TreesMgu.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun left right _ _ => left.length = right.length)
    (fun _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial)
    rfl
    (fun _ _ _ _ _ _ _ _ _ tailLengths => by
      simp only [List.length_cons]
      simpa using tailLengths)
    derivation

/-- Pointwise unification of a nonempty equation list is head unification
plus pointwise unification of the tail. -/
theorem TreeUnifiesEquations.cons_iff (binding : TreeSubstitution)
    (equation : TreeEquation) (equations : List TreeEquation) :
    TreeUnifiesEquations binding (equation :: equations) ↔
      TreeSubstitution.apply binding equation.1 =
          TreeSubstitution.apply binding equation.2 ∧
        TreeUnifiesEquations binding equations := by
  constructor
  · intro unifies
    constructor
    · exact unifies equation (by simp)
    · intro candidate member
      exact unifies candidate (by simp [member])
  · rintro ⟨head, tail⟩ candidate member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact head
    · exact tail candidate member

/-- For equal arity, pointwise equations are equivalent to equality of the
substituted ordered child lists. -/
theorem treeUnifiesEquations_iff_applyTrees_eq
    (binding : TreeSubstitution) :
    ∀ {left right : List Tree}, left.length = right.length →
      (TreeUnifiesEquations binding (treeEquations left right) ↔
        TreeSubstitution.applyTrees binding left =
          TreeSubstitution.applyTrees binding right)
  | [], [], _ => by
      simp [treeEquations, TreeUnifiesEquations]
  | left :: lefts, right :: rights, lengths => by
      have tailLengths : lefts.length = rights.length := by
        simpa only [List.length_cons, Nat.succ.injEq] using lengths
      rw [show treeEquations (left :: lefts) (right :: rights) =
          (left, right) :: treeEquations lefts rights by rfl,
        TreeUnifiesEquations.cons_iff,
        treeUnifiesEquations_iff_applyTrees_eq binding tailLengths,
        TreeSubstitution.applyTrees_cons,
        TreeSubstitution.applyTrees_cons,
        List.cons.injEq]

/-- Applying a substitution to pointwise equations is the same as first
applying it to both ordered child lists. -/
theorem TreeSubstitution.applyEquations_treeEquations
    (binding : TreeSubstitution) :
    ∀ {left right : List Tree}, left.length = right.length →
      TreeSubstitution.applyEquations binding (treeEquations left right) =
        treeEquations (TreeSubstitution.applyTrees binding left)
          (TreeSubstitution.applyTrees binding right)
  | [], [], _ => by simp [treeEquations,
      TreeSubstitution.applyEquations]
  | left :: lefts, right :: rights, lengths => by
      have tailLengths : lefts.length = rights.length := by
        simpa only [List.length_cons, Nat.succ.injEq] using lengths
      simp only [treeEquations, TreeSubstitution.applyEquations,
        List.map_cons, TreeSubstitution.applyTrees_cons]
      congr 1
      exact TreeSubstitution.applyEquations_treeEquations binding tailLengths

/-- Right-variable elimination has the same principal solution with the
ordered spelling fixed by `TreeMgu.bindRight`. -/
theorem tree_singleton_right_variable_is_mgu (value : Tree)
    (target : LogicVar)
    (absent : Tree.occurs target value = false) :
    TreeIsMgu [(target, value)] [(value, .variable target)] := by
  constructor
  · intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    simp only [TreeSubstitution.apply, Tree.instantiateOne, ite_true]
    exact Tree.instantiateOne_eq_self_of_occurs_false target value value absent
  · intro candidate candidateUnifies
    have identifies :
        TreeSubstitution.apply candidate (.variable target) =
          TreeSubstitution.apply candidate value :=
      (candidateUnifies (value, .variable target) (by simp)).symm
    refine ⟨candidate, ?_⟩
    intro tree
    change TreeSubstitution.apply candidate tree =
      TreeSubstitution.apply candidate
        (Tree.instantiateOne target value tree)
    exact (TreeSubstitution.apply_instantiateOne_of_unifier candidate target
      value identifies tree).symm

/-- Most-generality of child equations lifts through one rigid node with the
same symbol. -/
theorem TreeIsMgu.rigidNode {binding : TreeSubstitution}
    (symbol : RigidSymbol) {left right : List Tree}
    (lengths : left.length = right.length)
    (children : TreeIsMgu binding (treeEquations left right)) :
    TreeIsMgu binding [(.node symbol left, .node symbol right)] := by
  constructor
  · intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    simp only [TreeSubstitution.apply_node, Tree.node.injEq, true_and]
    exact (treeUnifiesEquations_iff_applyTrees_eq binding lengths).mp
      children.1
  · intro candidate candidateUnifies
    apply children.2 candidate
    apply (treeUnifiesEquations_iff_applyTrees_eq candidate lengths).mpr
    have nodeEquality := candidateUnifies
      (.node symbol left, .node symbol right) (by simp)
    simpa only [TreeSubstitution.apply_node, Tree.node.injEq, true_and]
      using nodeEquality

/-- One recursor minor for left-to-right child composition. -/
private theorem treesMgu_cons_isMostGeneral
    (left right : Tree) (lefts rights : List Tree)
    (base extension : TreeSubstitution)
    (_head : TreeMgu left right base)
    (tail : TreesMgu (TreeSubstitution.applyTrees base lefts)
      (TreeSubstitution.applyTrees base rights) extension)
    (headMgu : TreeIsMgu base [(left, right)])
    (tailMgu : TreeIsMgu extension
      (treeEquations (TreeSubstitution.applyTrees base lefts)
        (TreeSubstitution.applyTrees base rights))) :
    TreeIsMgu (extension ++ base)
      (treeEquations (left :: lefts) (right :: rights)) := by
  have appliedLengths := tail.length_eq
  have lengths : lefts.length = rights.length := by
    simpa using appliedLengths
  have normalized : TreeSubstitution.applyEquations base
        (treeEquations lefts rights) =
      treeEquations (TreeSubstitution.applyTrees base lefts)
        (TreeSubstitution.applyTrees base rights) :=
    TreeSubstitution.applyEquations_treeEquations base lengths
  have tailOnApplied : TreeIsMgu extension
      (TreeSubstitution.applyEquations base
        (treeEquations lefts rights)) := by
    rw [normalized]
    exact tailMgu
  simpa [treeEquations] using headMgu.compose_append tailOnApplied

private theorem treeAndForest_isMostGeneral :
    (∀ {left right binding}, TreeMgu left right binding →
      TreeIsMgu binding [(left, right)]) ∧
    (∀ {left right binding}, TreesMgu left right binding →
      TreeIsMgu binding (treeEquations left right)) :=
  TreeMgu.inductBoth
    (tree := fun left right binding =>
      TreeIsMgu binding [(left, right)])
    (forest := fun left right binding =>
      TreeIsMgu binding (treeEquations left right))
    tree_reflexive_is_mgu
    (fun source value _ absent =>
      tree_singleton_variable_is_mgu source value absent)
    (fun value target _ absent =>
      tree_singleton_right_variable_is_mgu value target absent)
    (fun symbol _ _ _ children childrenMgu =>
      TreeIsMgu.rigidNode symbol children.length_eq childrenMgu)
    tree_empty_is_mgu
    treesMgu_cons_isMostGeneral

/-- Every ordered canonical derivation computes a semantic MGU. -/
theorem TreeMgu.isMostGeneral {left right : Tree}
    {binding : TreeSubstitution} (derivation : TreeMgu left right binding) :
    TreeIsMgu binding [(left, right)] :=
  treeAndForest_isMostGeneral.1 derivation

/-- Ordered child derivations likewise compute the MGU of their exact
left-to-right equation sequence. -/
theorem TreesMgu.isMostGeneral {left right : List Tree}
    {binding : TreeSubstitution} (derivation : TreesMgu left right binding) :
    TreeIsMgu binding (treeEquations left right) :=
  treeAndForest_isMostGeneral.2 derivation

/-! ## Completeness for every finite-tree unifier -/

/-- Pointwise lifting of a substitution factorization to ordered children. -/
theorem TreeSubstitution.applyTrees_factor
    {specific residual general : TreeSubstitution}
    (factor : ∀ tree,
      TreeSubstitution.apply specific tree =
        TreeSubstitution.apply residual
          (TreeSubstitution.apply general tree)) :
    ∀ trees,
      TreeSubstitution.applyTrees specific trees =
        TreeSubstitution.applyTrees residual
          (TreeSubstitution.applyTrees general trees)
  | [] => by simp
  | tree :: trees => by
      simp only [TreeSubstitution.applyTrees_cons, List.cons.injEq]
      exact ⟨factor tree,
        TreeSubstitution.applyTrees_factor factor trees⟩

/-- Tree and child-list problems share one semantic induction.  The extra
unit in the list measure makes a list problem strictly larger than its head;
the two rigid roots make a tree problem strictly larger than its children. -/
private inductive MguProblem where
  | tree (left right : Tree)
  | trees (left right : List Tree)

private def MguProblem.Unifies (candidate : TreeSubstitution) :
    MguProblem → Prop
  | .tree left right =>
      TreeSubstitution.apply candidate left =
        TreeSubstitution.apply candidate right
  | .trees left right =>
      TreeSubstitution.applyTrees candidate left =
        TreeSubstitution.applyTrees candidate right

private def MguProblem.Solved : MguProblem → Prop
  | .tree left right => ∃ binding, TreeMgu left right binding
  | .trees left right => ∃ binding, TreesMgu left right binding

private def MguProblem.measure (candidate : TreeSubstitution) :
    MguProblem → Nat
  | .tree left right =>
      Tree.weight (TreeSubstitution.apply candidate left) +
        Tree.weight (TreeSubstitution.apply candidate right)
  | .trees left right =>
      1 + Trees.weight (TreeSubstitution.applyTrees candidate left) +
        Trees.weight (TreeSubstitution.applyTrees candidate right)

/-- Semantic completeness of the ordered finite-tree algorithm.  The
induction measure observes the terms *after* a candidate unifier.  When a
head MGU is factored out, the residual therefore sees exactly the same tail
sizes, while the solved head has disappeared.  This avoids any false claim
that syntactic substitution itself must decrease term size. -/
private theorem mguProblem_complete
    (problem : MguProblem) (candidate : TreeSubstitution)
    (unified : problem.Unifies candidate) : problem.Solved := by
  generalize measureEq : problem.measure candidate = measure
  induction measure using Nat.strongRecOn generalizing problem candidate with
  | ind measure induction =>
      cases problem with
      | tree left right =>
          cases left
          next source =>
              by_cases same : right = .variable source
              · subst right
                exact ⟨[], .reflexive (.variable source)⟩
              · have absent : Tree.occurs source right = false := by
                  cases present : Tree.occurs source right with
                  | false => rfl
                  | true =>
                      exact False.elim
                        ((Tree.no_finite_unifier_of_occurs_true candidate
                          source right present same) unified)
                exact ⟨[(source, right)],
                  .bindLeft source right same absent⟩
          next leftSymbol leftChildren =>
              cases right
              next target =>
                  have notVariable : ∀ identity,
                      Tree.node leftSymbol leftChildren ≠
                        .variable identity := by
                    intro identity equality
                    cases equality
                  have different : Tree.node leftSymbol leftChildren ≠
                      .variable target := notVariable target
                  have absent :
                      Tree.occurs target (.node leftSymbol leftChildren) =
                        false := by
                    cases present : Tree.occurs target
                        (.node leftSymbol leftChildren) with
                    | false => rfl
                    | true =>
                        exact False.elim
                          ((Tree.no_finite_unifier_of_occurs_true candidate
                            target (.node leftSymbol leftChildren) present
                            different) unified.symm)
                  exact ⟨[(target, .node leftSymbol leftChildren)],
                    .bindRight (.node leftSymbol leftChildren) target
                      notVariable absent⟩
              next rightSymbol rightChildren =>
                  have normalized :
                      Tree.node leftSymbol
                          (TreeSubstitution.applyTrees candidate leftChildren) =
                        Tree.node rightSymbol
                          (TreeSubstitution.applyTrees candidate
                            rightChildren) := by
                    simpa only [MguProblem.Unifies,
                      TreeSubstitution.apply_node] using unified
                  injection normalized with symbolsEqual childrenEqual
                  subst rightSymbol
                  by_cases sameChildren : leftChildren = rightChildren
                  · subst rightChildren
                    exact ⟨[], .reflexive (.node leftSymbol leftChildren)⟩
                  · have smaller :
                        (MguProblem.trees leftChildren rightChildren).measure
                            candidate < measure := by
                      rw [← measureEq]
                      simp only [MguProblem.measure,
                        TreeSubstitution.apply_node, Tree.weight]
                      omega
                    have childrenSolved := induction _ smaller
                      (MguProblem.trees leftChildren rightChildren)
                      candidate childrenEqual rfl
                    rcases childrenSolved with ⟨binding, children⟩
                    exact ⟨binding,
                      .node leftSymbol leftChildren rightChildren
                        sameChildren children⟩
      | trees left right =>
          cases left with
          | nil =>
              cases right with
              | nil => exact ⟨[], .nil⟩
              | cons tree trees =>
                  simp only [MguProblem.Unifies,
                    TreeSubstitution.applyTrees_nil,
                    TreeSubstitution.applyTrees_cons] at unified
                  cases unified
          | cons left lefts =>
              cases right with
              | nil =>
                  simp only [MguProblem.Unifies,
                    TreeSubstitution.applyTrees_nil,
                    TreeSubstitution.applyTrees_cons] at unified
                  cases unified
              | cons right rights =>
                  simp only [MguProblem.Unifies,
                    TreeSubstitution.applyTrees_cons,
                    List.cons.injEq] at unified
                  have headSmaller :
                      (MguProblem.tree left right).measure candidate <
                        measure := by
                    rw [← measureEq]
                    simp only [MguProblem.measure,
                      TreeSubstitution.applyTrees_cons, Trees.weight]
                    have leftPositive :=
                      Tree.weight_positive
                        (TreeSubstitution.apply candidate left)
                    have rightPositive :=
                      Tree.weight_positive
                        (TreeSubstitution.apply candidate right)
                    omega
                  have headSolved := induction _ headSmaller
                    (MguProblem.tree left right) candidate unified.1 rfl
                  rcases headSolved with ⟨base, head⟩
                  have candidateUnifiesHead : TreeUnifiesEquations candidate
                      [(left, right)] := by
                    intro equation member
                    simp only [List.mem_singleton] at member
                    subst equation
                    exact unified.1
                  rcases head.isMostGeneral.2 candidate candidateUnifiesHead
                    with ⟨residual, factor⟩
                  have leftFactor :=
                    TreeSubstitution.applyTrees_factor factor lefts
                  have rightFactor :=
                    TreeSubstitution.applyTrees_factor factor rights
                  have tailUnified :
                      TreeSubstitution.applyTrees residual
                          (TreeSubstitution.applyTrees base lefts) =
                        TreeSubstitution.applyTrees residual
                          (TreeSubstitution.applyTrees base rights) := by
                    rw [← leftFactor, ← rightFactor]
                    exact unified.2
                  have tailSmaller :
                      (MguProblem.trees
                          (TreeSubstitution.applyTrees base lefts)
                          (TreeSubstitution.applyTrees base rights)).measure
                            residual < measure := by
                    rw [← measureEq]
                    simp only [MguProblem.measure,
                      TreeSubstitution.applyTrees_cons, Trees.weight]
                    rw [← leftFactor, ← rightFactor]
                    have leftPositive :=
                      Tree.weight_positive
                        (TreeSubstitution.apply candidate left)
                    have rightPositive :=
                      Tree.weight_positive
                        (TreeSubstitution.apply candidate right)
                    omega
                  have tailSolved := induction _ tailSmaller
                    (MguProblem.trees
                      (TreeSubstitution.applyTrees base lefts)
                      (TreeSubstitution.applyTrees base rights))
                    residual tailUnified rfl
                  rcases tailSolved with ⟨extension, tail⟩
                  exact ⟨extension ++ base,
                    .cons left right lefts rights base extension head tail⟩

/-- Every semantic finite-tree unifier is witnessed by the ordered MGU
derivation; cyclic rational-tree equations are excluded by the proved occurs
check, not by an assumption. -/
theorem TreeMgu.complete {left right : Tree}
    (candidate : TreeSubstitution)
    (unified : TreeSubstitution.apply candidate left =
      TreeSubstitution.apply candidate right) :
    ∃ binding, TreeMgu left right binding :=
  mguProblem_complete (.tree left right) candidate unified

/-- Ordered child-list completeness companion. -/
theorem TreesMgu.complete {left right : List Tree}
    (candidate : TreeSubstitution)
    (unified : TreeSubstitution.applyTrees candidate left =
      TreeSubstitution.applyTrees candidate right) :
    ∃ binding, TreesMgu left right binding :=
  mguProblem_complete (.trees left right) candidate unified

/-- Ordered equations are well formed when both sides of every occurrence
are source-reifiable canonical trees. -/
def TreeEquationsWellFormed (equations : List TreeEquation) : Prop :=
  ∀ equation, equation ∈ equations →
    equation.1.WellFormed ∧ equation.2.WellFormed

/-- Applying a well-formed substitution preserves equation well-formedness.
-/
theorem TreeEquationsWellFormed.apply
    {equations : List TreeEquation} (equationsFormed :
      TreeEquationsWellFormed equations)
    {binding : TreeSubstitution} (bindingFormed : binding.WellFormed) :
    TreeEquationsWellFormed
      (TreeSubstitution.applyEquations binding equations) := by
  intro normalized normalizedMember
  simp only [TreeSubstitution.applyEquations, List.mem_map]
    at normalizedMember
  obtain ⟨equation, member, rfl⟩ := normalizedMember
  have original := equationsFormed equation member
  exact ⟨TreeSubstitution.apply_wellFormed bindingFormed original.1,
    TreeSubstitution.apply_wellFormed bindingFormed original.2⟩

private theorem treeAndForest_binding_wellFormed :
    (∀ {left right binding}, TreeMgu left right binding →
      left.WellFormed → right.WellFormed → binding.WellFormed) ∧
    (∀ {left right binding}, TreesMgu left right binding →
      Trees.WellFormed left → Trees.WellFormed right →
        binding.WellFormed) :=
  TreeMgu.inductBoth
    (tree := fun left right binding =>
      left.WellFormed → right.WellFormed → binding.WellFormed)
    (forest := fun left right binding =>
      Trees.WellFormed left → Trees.WellFormed right →
        binding.WellFormed)
    (fun _ _ _ => TreeSubstitution.wellFormed_nil)
    (fun source value _ _ _ valueFormed =>
      TreeSubstitution.WellFormed.singleton source valueFormed)
    (fun value target _ _ valueFormed _ =>
      TreeSubstitution.WellFormed.singleton target valueFormed)
    (fun _ _ _ _ _ childrenInduction leftNode rightNode =>
      childrenInduction leftNode.children rightNode.children)
    (fun _ _ => TreeSubstitution.wellFormed_nil)
    (fun _ _ _ _ base extension _ _ headInduction tailInduction
        leftChildren rightChildren => by
      have baseFormed := headInduction leftChildren.head rightChildren.head
      have extensionFormed := tailInduction
        (TreeSubstitution.applyTrees_wellFormed baseFormed
          leftChildren.tail)
        (TreeSubstitution.applyTrees_wellFormed baseFormed
          rightChildren.tail)
      exact extensionFormed.append baseFormed)

/-- A canonical MGU of well-formed inputs carries only well-formed
replacements, hence can be reified back to source `Term`s. -/
theorem TreeMgu.binding_wellFormed {left right : Tree}
    {binding : TreeSubstitution} (derivation : TreeMgu left right binding)
    (leftFormed : left.WellFormed) (rightFormed : right.WellFormed) :
    binding.WellFormed :=
  treeAndForest_binding_wellFormed.1 derivation leftFormed rightFormed

/-- Ordered child MGU bindings are likewise well formed. -/
theorem TreesMgu.binding_wellFormed {left right : List Tree}
    {binding : TreeSubstitution} (derivation : TreesMgu left right binding)
    (leftFormed : Trees.WellFormed left)
    (rightFormed : Trees.WellFormed right) : binding.WellFormed :=
  treeAndForest_binding_wellFormed.2 derivation leftFormed rightFormed

/-! ## Determinism and anti-vacuity -/

private theorem treeMgu_node_unique {binding : TreeSubstitution}
    (symbol : RigidSymbol) (left right : List Tree)
    (different : left ≠ right) (children : TreesMgu left right binding)
    (childrenUnique : ∀ {other}, TreesMgu left right other →
      binding = other) :
    ∀ {other}, TreeMgu (.node symbol left) (.node symbol right) other →
      binding = other := by
  intro other derivation
  cases derivation with
  | reflexive => exact False.elim (different rfl)
  | node _ _ _ _ otherChildren => exact childrenUnique otherChildren

private theorem treesMgu_cons_unique
    (left right : Tree) (lefts rights : List Tree)
    (base extension : TreeSubstitution)
    (_head : TreeMgu left right base)
    (_tail : TreesMgu (TreeSubstitution.applyTrees base lefts)
      (TreeSubstitution.applyTrees base rights) extension)
    (headUnique : ∀ {other}, TreeMgu left right other → base = other)
    (tailUnique : ∀ {other},
      TreesMgu (TreeSubstitution.applyTrees base lefts)
        (TreeSubstitution.applyTrees base rights) other →
      extension = other) :
    ∀ {other}, TreesMgu (left :: lefts) (right :: rights) other →
      extension ++ base = other := by
  intro other derivation
  cases derivation with
  | cons _ _ _ _ secondBase secondExtension secondHead secondTail =>
      have baseEquality := headUnique secondHead
      subst secondBase
      have extensionEquality := tailUnique secondTail
      subst secondExtension
      rfl

private theorem treeAndForest_deterministic :
    (∀ {left right first}, TreeMgu left right first →
      ∀ {second}, TreeMgu left right second → first = second) ∧
    (∀ {left right first}, TreesMgu left right first →
      ∀ {second}, TreesMgu left right second → first = second) :=
  TreeMgu.inductBoth
    (tree := fun left right first =>
      ∀ {second}, TreeMgu left right second → first = second)
    (forest := fun left right first =>
      ∀ {second}, TreesMgu left right second → first = second)
    (fun _ {second} secondDerivation => by
      cases secondDerivation <;> simp_all)
    (fun _ _ _ _ {second} secondDerivation => by
      cases secondDerivation <;> simp_all)
    (fun _ _ _ _ {second} secondDerivation => by
      cases secondDerivation <;> simp_all)
    treeMgu_node_unique
    (fun {second} secondDerivation => by cases secondDerivation; rfl)
    treesMgu_cons_unique

/-- Ordered root priority and left-to-right child composition choose one
canonical substitution spelling. -/
theorem TreeMgu.deterministic {left right : Tree}
    {first second : TreeSubstitution}
    (one : TreeMgu left right first) (two : TreeMgu left right second) :
    first = second :=
  treeAndForest_deterministic.1 one two

/-- Ordered child unification is deterministic as well. -/
theorem TreesMgu.deterministic {left right : List Tree}
    {first second : TreeSubstitution}
    (one : TreesMgu left right first) (two : TreesMgu left right second) :
    first = second :=
  treeAndForest_deterministic.2 one two

/-! ## Ordered equation worklists and source-term bridge -/

/-- Robinson elimination over an ordered equation worklist. -/
inductive OrderedTreeMgu : List TreeEquation → TreeSubstitution → Prop where
  | nil : OrderedTreeMgu [] []
  | cons (left right : Tree) (equations : List TreeEquation)
      (base extension : TreeSubstitution)
      (head : TreeMgu left right base)
      (tail : OrderedTreeMgu
        (TreeSubstitution.applyEquations base equations) extension) :
      OrderedTreeMgu ((left, right) :: equations) (extension ++ base)

/-- The ordered worklist relation always produces an MGU. -/
theorem OrderedTreeMgu.isMostGeneral {equations : List TreeEquation}
    {binding : TreeSubstitution}
    (derivation : OrderedTreeMgu equations binding) :
    TreeIsMgu binding equations := by
  induction derivation with
  | nil => exact tree_empty_is_mgu
  | cons left right equations base extension head tail induction =>
      simpa using head.isMostGeneral.compose_append induction

/-- Every finite ordered equation worklist that has a unifier has the
deterministic ordered MGU derivation.  Recursion is on worklist length;
normalizing the tail by a head MGU preserves that length exactly. -/
theorem OrderedTreeMgu.complete {equations : List TreeEquation}
    (candidate : TreeSubstitution)
    (unifies : TreeUnifiesEquations candidate equations) :
    ∃ binding, OrderedTreeMgu equations binding := by
  generalize lengthEq : equations.length = length
  induction length generalizing equations candidate with
  | zero =>
      cases equations with
      | nil => exact ⟨[], .nil⟩
      | cons equation equations => simp at lengthEq
  | succ length induction =>
      cases equations with
      | nil => simp at lengthEq
      | cons equation equations =>
          rcases equation with ⟨left, right⟩
          have headUnifies :
              TreeSubstitution.apply candidate left =
                TreeSubstitution.apply candidate right :=
            unifies (left, right) (by simp)
          rcases TreeMgu.complete candidate headUnifies with ⟨base, head⟩
          have candidateUnifiesHead : TreeUnifiesEquations candidate
              [(left, right)] := by
            intro equation member
            simp only [List.mem_singleton] at member
            subst equation
            exact headUnifies
          rcases head.isMostGeneral.2 candidate candidateUnifiesHead with
            ⟨residual, factor⟩
          have residualUnifies : TreeUnifiesEquations residual
              (TreeSubstitution.applyEquations base equations) := by
            intro normalized normalizedMember
            simp only [TreeSubstitution.applyEquations, List.mem_map]
              at normalizedMember
            obtain ⟨equation, member, rfl⟩ := normalizedMember
            rw [← factor equation.1, ← factor equation.2]
            exact unifies equation (by simp [member])
          have tailLength : equations.length = length := by
            simpa only [List.length_cons, Nat.succ.injEq] using lengthEq
          have normalizedLength :
              (TreeSubstitution.applyEquations base equations).length =
                length := by
            simp only [TreeSubstitution.applyEquations, List.length_map,
              tailLength]
          rcases induction residual residualUnifies normalizedLength with
            ⟨extension, tail⟩
          exact ⟨extension ++ base,
            .cons left right equations base extension head tail⟩

/-- Ordered worklist unification never leaves the source-reifiable tree
fragment when its input equations came from source terms. -/
theorem OrderedTreeMgu.binding_wellFormed
    {equations : List TreeEquation} {binding : TreeSubstitution}
    (derivation : OrderedTreeMgu equations binding)
    (equationsFormed : TreeEquationsWellFormed equations) :
    binding.WellFormed := by
  induction derivation with
  | nil => exact TreeSubstitution.wellFormed_nil
  | cons left right equations base extension head tail induction =>
      have headInputs := equationsFormed (left, right) (by simp)
      have baseFormed := head.binding_wellFormed
        headInputs.1 headInputs.2
      have remainingFormed : TreeEquationsWellFormed equations := by
        intro equation member
        exact equationsFormed equation (by simp [member])
      have normalizedFormed : TreeEquationsWellFormed
          (TreeSubstitution.applyEquations base equations) :=
        remainingFormed.apply baseFormed
      exact (induction normalizedFormed).append baseFormed

/-- The ordered worklist relation has one substitution spelling. -/
theorem OrderedTreeMgu.deterministic {equations : List TreeEquation}
    {first second : TreeSubstitution}
    (one : OrderedTreeMgu equations first)
    (two : OrderedTreeMgu equations second) : first = second := by
  induction one generalizing second with
  | nil =>
      cases two
      rfl
  | cons left right equations base extension head tail induction =>
      cases two with
      | cons _ _ _ secondBase secondExtension secondHead secondTail =>
          have baseEquality := head.deterministic secondHead
          subst secondBase
          have extensionEquality := induction secondTail
          subst secondExtension
          rfl

/-- Canonical presentation of source-level equations. -/
def denoteEquations (equations : List (Term × Term)) :
    List TreeEquation :=
  equations.map fun equation =>
    (Term.denote equation.1, Term.denote equation.2)

/-- Every source equation denotes a pair of source-reifiable canonical
trees. -/
theorem denoteEquations_wellFormed (equations : List (Term × Term)) :
    TreeEquationsWellFormed (denoteEquations equations) := by
  intro denoted denotedMember
  simp only [denoteEquations, List.mem_map] at denotedMember
  obtain ⟨equation, _, rfl⟩ := denotedMember
  exact ⟨Term.denote_wellFormed equation.1,
    Term.denote_wellFormed equation.2⟩

/-- A source substitution is computed, rather than merely postulated, when
it is the exact canonical reification of the ordered MGU result.  Requiring
exact reification (not merely equal denotation) prevents two raw dotted-list
presentations from inducing different subsequent source-goal syntax. -/
def ComputesDenotationalMgu (equations : List (Term × Term))
    (binding : OpenSubstitution.Substitution) : Prop :=
  ∃ canonicalBinding,
    OrderedTreeMgu (denoteEquations equations) canonicalBinding ∧
      binding = TreeSubstitution.reify canonicalBinding

/-- Every ordered canonical derivation over source equations computes an
actual typed source substitution: no abstract canonical replacement is
silently left without a `Term` representation. -/
theorem OrderedTreeMgu.computesReified
    {equations : List (Term × Term)} {binding : TreeSubstitution}
    (derivation : OrderedTreeMgu (denoteEquations equations) binding) :
    ComputesDenotationalMgu equations (TreeSubstitution.reify binding) := by
  exact ⟨binding, derivation, rfl⟩

/-- Completeness reaches the typed source surface: whenever one source
substitution unifies an ordered equation worklist denotationally, the
canonical algorithm computes a reified source MGU for that worklist. -/
theorem ComputesDenotationalMgu.exists_of_unifier
    {equations : List (Term × Term)}
    (candidate : OpenSubstitution.Substitution)
    (unifies : DenotationalUnifiesEquations candidate equations) :
    ∃ binding, ComputesDenotationalMgu equations binding := by
  have canonicalUnifies : TreeUnifiesEquations
      (Substitution.denote candidate) (denoteEquations equations) := by
    intro denoted denotedMember
    simp only [denoteEquations, List.mem_map] at denotedMember
    obtain ⟨equation, member, rfl⟩ := denotedMember
    exact unifies equation member
  rcases OrderedTreeMgu.complete (Substitution.denote candidate)
      canonicalUnifies with ⟨binding, derivation⟩
  exact ⟨TreeSubstitution.reify binding, derivation.computesReified⟩

/-- A canonical tree MGU is strong enough to establish the source-facing
denotational MGU contract. -/
theorem TreeIsMgu.toDenotational
    {binding : OpenSubstitution.Substitution}
    {equations : List (Term × Term)}
    (canonical : TreeIsMgu (Substitution.denote binding)
      (denoteEquations equations)) :
    IsDenotationalMgu binding equations := by
  constructor
  · intro equation member
    have denoted : (Term.denote equation.1, Term.denote equation.2) ∈
        denoteEquations equations := by
      exact List.mem_map_of_mem member
    exact canonical.1 _ denoted
  · intro candidate candidateUnifies
    apply canonical.2 (Substitution.denote candidate)
    intro denoted denotedMember
    simp only [denoteEquations, List.mem_map] at denotedMember
    obtain ⟨equation, member, rfl⟩ := denotedMember
    exact candidateUnifies equation member

/-- A computed source substitution is genuinely most-general. -/
theorem ComputesDenotationalMgu.isMostGeneral
    {equations : List (Term × Term)}
    {binding : OpenSubstitution.Substitution}
    (computed : ComputesDenotationalMgu equations binding) :
    IsDenotationalMgu binding equations := by
  rcases computed with ⟨canonicalBinding, derivation, rfl⟩
  apply TreeIsMgu.toDenotational
  rw [TreeSubstitution.denote_reify
    (derivation.binding_wellFormed
      (denoteEquations_wellFormed equations))]
  exact derivation.isMostGeneral

/-- Exact reification plus deterministic ordered unification gives one source
substitution spelling, not merely one denotation. -/
theorem ComputesDenotationalMgu.unique
    {equations : List (Term × Term)}
    {first second : OpenSubstitution.Substitution}
    (one : ComputesDenotationalMgu equations first)
    (two : ComputesDenotationalMgu equations second) : first = second := by
  rcases one with ⟨firstCanonical, firstDerivation, rfl⟩
  rcases two with ⟨secondCanonical, secondDerivation, rfl⟩
  rw [firstDerivation.deterministic secondDerivation]

/-- Canonical denotation uniqueness follows from exact source uniqueness. -/
theorem ComputesDenotationalMgu.denotation_unique
    {equations : List (Term × Term)}
    {first second : OpenSubstitution.Substitution}
    (one : ComputesDenotationalMgu equations first)
    (two : ComputesDenotationalMgu equations second) :
    Substitution.denote first = Substitution.denote second := by
  exact congrArg Substitution.denote (one.unique two)

/-- Source-facing constructor for the ordered left-variable rule. -/
theorem computes_singleton_left_variable (source : LogicVar) (value : Term)
    (different : Term.denote value ≠ .variable source)
    (absent : Tree.occurs source (Term.denote value) = false) :
    ComputesDenotationalMgu [(.variable source, value)]
      (TreeSubstitution.reify [(source, Term.denote value)]) := by
  apply OrderedTreeMgu.computesReified
  exact .cons (.variable source) (Term.denote value) []
    [(source, Term.denote value)] []
    (.bindLeft source (Term.denote value) different absent) .nil

/-- Source-facing constructor for the ordered right-variable rule. -/
theorem computes_singleton_right_variable (value : Term) (target : LogicVar)
    (notVariable : ∀ identity, Term.denote value ≠ .variable identity)
    (absent : Tree.occurs target (Term.denote value) = false) :
    ComputesDenotationalMgu [(value, .variable target)]
      (TreeSubstitution.reify [(target, Term.denote value)]) := by
  apply OrderedTreeMgu.computesReified
  exact .cons (Term.denote value) (.variable target) []
    [(target, Term.denote value)] []
    (.bindRight (Term.denote value) target notVariable absent) .nil

/-! ### Nontrivial positive and negative witnesses -/

def compoundWitnessX : LogicVar := .source "X"
def compoundWitnessY : LogicVar := .source "Y"
def compoundWitnessA : Tree := .node (.atom "a") []
def compoundWitnessB : Tree := .node (.atom "b") []

/-- Rigid decomposition really runs left-to-right: the first child binds `X`
to `b`, the second then binds `Y` to `a`, and the newer extension is prepended
to the earlier one. -/
theorem compound_two_children_ordered_mgu : TreeMgu
    (.node (.compound "p")
      [.variable compoundWitnessX, compoundWitnessA])
    (.node (.compound "p")
      [compoundWitnessB, .variable compoundWitnessY])
    [(compoundWitnessY, compoundWitnessA),
      (compoundWitnessX, compoundWitnessB)] := by
  apply TreeMgu.node (.compound "p")
    [.variable compoundWitnessX, compoundWitnessA]
    [compoundWitnessB, .variable compoundWitnessY]
  · intro equality
    injection equality with first
    cases first
  · apply TreesMgu.cons (.variable compoundWitnessX) compoundWitnessB
      [compoundWitnessA] [.variable compoundWitnessY]
      [(compoundWitnessX, compoundWitnessB)]
      [(compoundWitnessY, compoundWitnessA)]
    · exact .bindLeft compoundWitnessX compoundWitnessB
        (by intro equality; cases equality) (by rfl)
    · simpa [compoundWitnessX, compoundWitnessY, compoundWitnessA,
        compoundWitnessB, TreeSubstitution.applyTrees,
        Trees.instantiateOne, TreeSubstitution.apply,
        Tree.instantiateOne] using
        (TreesMgu.cons compoundWitnessA (.variable compoundWitnessY)
          [] [] [(compoundWitnessY, compoundWitnessA)] []
          (.bindRight compoundWitnessA compoundWitnessY
            (by intro identity equality; cases equality) (by rfl))
          TreesMgu.nil)

/-- The nontrivial compound derivation carries an actual MGU theorem, not
only an algorithm trace. -/
theorem compound_two_children_is_mgu : TreeIsMgu
    [(compoundWitnessY, compoundWitnessA),
      (compoundWitnessX, compoundWitnessB)]
    [((.node (.compound "p")
        [.variable compoundWitnessX, compoundWitnessA]),
      (.node (.compound "p")
        [compoundWitnessB, .variable compoundWitnessY]))] :=
  compound_two_children_ordered_mgu.isMostGeneral

/-- The canonical algorithm computes the proper-list-tail substitution that
the older raw-syntax MGU definition could not even recognize. -/
theorem dotted_list_computed_mgu : ComputesDenotationalMgu
    [(dottedListWitness, properListExpected)]
    [(.source "X", properListReplacement)] := by
  let atomA : Tree := .node (.atom "a") []
  let atomB : Tree := .node (.atom "b") []
  let nilTree : Tree := .node .nil []
  let listB : Tree := .node .cons [atomB, nilTree]
  let result : TreeSubstitution := [(.source "X", listB)]
  have first : TreeMgu atomA atomA [] := .reflexive atomA
  have second : TreeMgu (.variable (.source "X")) listB result := by
    exact .bindLeft (.source "X") listB (by simp [listB]) (by rfl)
  have children : TreesMgu [atomA, .variable (.source "X")]
      [atomA, listB] result := by
    apply TreesMgu.cons atomA atomA [.variable (.source "X")] [listB]
      [] result first
    simpa [TreeSubstitution.applyTrees] using
      (TreesMgu.cons (.variable (.source "X")) listB [] [] result []
        second TreesMgu.nil)
  have treeMgu : TreeMgu
      (Term.denote dottedListWitness) (Term.denote properListExpected)
      result := by
    simpa [dottedListWitness, properListExpected, atomA, atomB, nilTree,
      listB, Term.denote, Terms.denote, Tree.prologList] using
      (TreeMgu.node .cons [atomA, .variable (.source "X")]
        [atomA, listB] (by simp [listB]) children)
  have derivation : OrderedTreeMgu
      (denoteEquations [(dottedListWitness, properListExpected)]) result :=
    .cons _ _ [] result [] treeMgu .nil
  simpa [result, listB, atomB, nilTree, properListReplacement,
    TreeSubstitution.reify, Tree.reify, Term.prepend] using
    derivation.computesReified

/-- Different rigid symbols cannot acquire a derivation. -/
theorem distinct_rigid_nodes_have_no_mgu :
    ¬ ∃ binding, TreeMgu
      (.node (.atom "a") []) (.node (.atom "b") []) binding := by
  rintro ⟨binding, derivation⟩
  have unifies := derivation.isMostGeneral.1
    ((.node (.atom "a") []), (.node (.atom "b") [])) (by simp)
  simp at unifies

/-- The finite-tree occurs check rejects a cyclic binding.  Rational trees
remain an explicit external semantic extension. -/
theorem occurs_check_rejects_cycle (source : LogicVar) :
    ¬ ∃ binding, TreeMgu (.variable source)
      (.node (.compound "f") [.variable source]) binding := by
  rintro ⟨binding, derivation⟩
  cases derivation with
  | bindLeft _ _ _ absent => simp [Tree.occurs, Trees.occurs] at absent

end Mettapedia.Languages.MeTTa.PLeaTTa.PeTTaSpec.PrologCore.Canonical
