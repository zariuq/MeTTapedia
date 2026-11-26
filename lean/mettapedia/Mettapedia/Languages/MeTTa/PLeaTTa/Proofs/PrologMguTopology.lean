-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologMguTopology
Purpose: Prove that the independent ordered finite-tree MGU carries an
  acyclic elimination order, and prepare that order for transport to the
  executable open substitution.
Trusted boundary: none
Main exports:
  TreeSubstitutionTopological,
  TreeMgu.binding_topological,
  TreesMgu.binding_topological,
  OrderedTreeMgu.binding_topological
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologMguOpenAgreement

namespace Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguTopology

open Mettapedia.Languages.MeTTa.PLeaTTa.Source (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguBridge
open PrologMguOpenAgreement
open PrologPrefilterBridge
open PrologStateBridge

/-! ## Generic support calculus -/

mutual

/-- Strengthening a pointwise variable predicate strengthens the complete
tree support certificate. -/
theorem TreeVariablesSatisfy.mono
    {first second : LogicVar → Prop}
    (included : ∀ identity, first identity → second identity) :
    ∀ {tree : Tree}, TreeVariablesSatisfy first tree →
      TreeVariablesSatisfy second tree
  | .variable identity, supported => included identity supported
  | .node _ _children, supported =>
      TreesVariablesSatisfy.mono included supported

/-- Ordered-list companion to `TreeVariablesSatisfy.mono`. -/
theorem TreesVariablesSatisfy.mono
    {first second : LogicVar → Prop}
    (included : ∀ identity, first identity → second identity) :
    ∀ {trees : List Tree}, TreesVariablesSatisfy first trees →
      TreesVariablesSatisfy second trees
  | [], _ => trivial
  | _ :: _, supported =>
      ⟨TreeVariablesSatisfy.mono included supported.1,
        TreesVariablesSatisfy.mono included supported.2⟩

end

mutual

/-- Two support certificates on one tree can be paired pointwise. -/
theorem TreeVariablesSatisfy.and
    {first second : LogicVar → Prop} :
    ∀ {tree : Tree},
      TreeVariablesSatisfy first tree →
      TreeVariablesSatisfy second tree →
      TreeVariablesSatisfy (fun identity =>
        first identity ∧ second identity) tree
  | .variable _, firstSupported, secondSupported =>
      ⟨firstSupported, secondSupported⟩
  | .node _ _, firstSupported, secondSupported =>
      TreesVariablesSatisfy.and firstSupported secondSupported

/-- Ordered-list companion to `TreeVariablesSatisfy.and`. -/
theorem TreesVariablesSatisfy.and
    {first second : LogicVar → Prop} :
    ∀ {trees : List Tree},
      TreesVariablesSatisfy first trees →
      TreesVariablesSatisfy second trees →
      TreesVariablesSatisfy (fun identity =>
        first identity ∧ second identity) trees
  | [], _, _ => trivial
  | _ :: _, firstSupported, secondSupported =>
      ⟨TreeVariablesSatisfy.and firstSupported.1 secondSupported.1,
        TreesVariablesSatisfy.and firstSupported.2 secondSupported.2⟩

end

mutual

/-- Every finite tree trivially satisfies the constantly true support
predicate. -/
theorem treeVariablesSatisfy_true :
    ∀ tree : Tree, TreeVariablesSatisfy (fun _ => True) tree
  | .variable _ => trivial
  | .node _ children => treesVariablesSatisfy_true children

/-- Ordered-list companion to `treeVariablesSatisfy_true`. -/
theorem treesVariablesSatisfy_true :
    ∀ trees : List Tree, TreesVariablesSatisfy (fun _ => True) trees
  | [] => trivial
  | tree :: trees =>
      ⟨treeVariablesSatisfy_true tree,
        treesVariablesSatisfy_true trees⟩

end

mutual

/-- Boolean absence gives the corresponding pointwise support certificate. -/
theorem treeVariablesSatisfy_ne_of_occurs_false
    (source : LogicVar) :
    ∀ {tree : Tree}, Tree.occurs source tree = false →
      TreeVariablesSatisfy (fun identity => identity ≠ source) tree
  | .variable identity, absent => by
      change identity ≠ source
      simpa [Tree.occurs, decide_eq_false_iff_not] using absent
  | .node _ _, absent =>
      treesVariablesSatisfy_ne_of_occurs_false source absent

/-- Ordered-list companion to variable absence. -/
theorem treesVariablesSatisfy_ne_of_occurs_false
    (source : LogicVar) :
    ∀ {trees : List Tree}, Trees.occurs source trees = false →
      TreesVariablesSatisfy (fun identity => identity ≠ source) trees
  | [], _ => trivial
  | _ :: _, absent => by
      simp only [Trees.occurs, Bool.or_eq_false_iff] at absent
      exact
        ⟨treeVariablesSatisfy_ne_of_occurs_false source absent.1,
          treesVariablesSatisfy_ne_of_occurs_false source absent.2⟩

end

mutual

/-- Replacing one distinguished variable eliminates it from a support
predicate.  The input may contain the distinguished source; every other
variable must already satisfy the target predicate. -/
theorem treeVariablesSatisfy_instantiateOne_eliminate
    {predicate : LogicVar → Prop}
    (source : LogicVar) {replacement : Tree}
    (replacementSupported :
      TreeVariablesSatisfy predicate replacement) :
    ∀ {tree : Tree},
      TreeVariablesSatisfy
        (fun identity => identity = source ∨ predicate identity) tree →
      TreeVariablesSatisfy predicate
        (Tree.instantiateOne source replacement tree)
  | .variable identity, supported => by
      by_cases same : identity = source
      · subst identity
        simpa [Tree.instantiateOne] using replacementSupported
      · rcases supported with impossible | supported
        · exact False.elim (same impossible)
        · simpa [Tree.instantiateOne, same,
            TreeVariablesSatisfy] using supported
  | .node _ _, supported => by
      exact treesVariablesSatisfy_instantiateOne_eliminate source
        replacementSupported supported

/-- Ordered-list companion to distinguished-variable elimination. -/
theorem treesVariablesSatisfy_instantiateOne_eliminate
    {predicate : LogicVar → Prop}
    (source : LogicVar) {replacement : Tree}
    (replacementSupported :
      TreeVariablesSatisfy predicate replacement) :
    ∀ {trees : List Tree},
      TreesVariablesSatisfy
        (fun identity => identity = source ∨ predicate identity) trees →
      TreesVariablesSatisfy predicate
        (Trees.instantiateOne source replacement trees)
  | [], _ => trivial
  | _ :: _, supported =>
      ⟨treeVariablesSatisfy_instantiateOne_eliminate source
          replacementSupported supported.1,
        treesVariablesSatisfy_instantiateOne_eliminate source
          replacementSupported supported.2⟩

end

/-! ## Canonical topological substitutions -/

/-- Canonical substitution domain in stored elimination order. -/
def TreeSubstitution.keys (binding : TreeSubstitution) : List LogicVar :=
  binding.map Prod.fst

/-- An independent substitution is topological when its keys are unique and
every bound dependency in a replacement occurs strictly earlier than the
replacement's source.  Unbound residual variables need not be keys. -/
structure TreeSubstitutionTopological
    (binding : TreeSubstitution) : Prop where
  nodup : (TreeSubstitution.keys binding).Nodup
  decreases :
    ∀ entry, entry ∈ binding →
      TreeVariablesSatisfy
        (fun dependency =>
          dependency ∈ TreeSubstitution.keys binding →
            (TreeSubstitution.keys binding).idxOf dependency <
              (TreeSubstitution.keys binding).idxOf entry.1)
        entry.2

/-- The empty independent substitution has the empty elimination order. -/
theorem TreeSubstitutionTopological.nil :
    TreeSubstitutionTopological [] := by
  constructor
  · exact List.nodup_nil
  · intro entry member
    simp at member

/-- One occurs-checked elimination is topological. -/
theorem TreeSubstitutionTopological.singleton
    (source : LogicVar) (value : Tree)
    (absent : Tree.occurs source value = false) :
    TreeSubstitutionTopological [(source, value)] := by
  constructor
  · simp [TreeSubstitution.keys]
  · intro entry member
    simp only [List.mem_singleton] at member
    subst entry
    exact TreeVariablesSatisfy.mono
      (first := fun identity => identity ≠ source)
      (second := fun dependency =>
        dependency ∈ TreeSubstitution.keys [(source, value)] →
          (TreeSubstitution.keys [(source, value)]).idxOf dependency <
            (TreeSubstitution.keys [(source, value)]).idxOf source)
      (fun dependency different dependencyBound => by
        simp [TreeSubstitution.keys] at dependencyBound
        exact False.elim (different dependencyBound))
      (treeVariablesSatisfy_ne_of_occurs_false source absent)

/-- Removing the newest entry preserves topological ordering. -/
theorem TreeSubstitutionTopological.tail
    {entry : LogicVar × Tree} {binding : TreeSubstitution}
    (topological :
      TreeSubstitutionTopological (entry :: binding)) :
    TreeSubstitutionTopological binding := by
  rcases entry with ⟨source, value⟩
  constructor
  · simpa [TreeSubstitution.keys] using topological.nodup.tail
  · intro candidate member
    have candidateOrder :=
      topological.decreases candidate (by simp [member])
    have nodupParts :
        source ∉ TreeSubstitution.keys binding ∧
          (TreeSubstitution.keys binding).Nodup := by
      exact List.nodup_cons.mp (by
        simpa [TreeSubstitution.keys] using topological.nodup)
    have sourceDifferent : candidate.1 ≠ source := by
      intro same
      subst source
      exact nodupParts.1
        (List.mem_map_of_mem member)
    exact TreeVariablesSatisfy.mono
      (fun dependency before dependencyMember => by
        have dependencyDifferent : dependency ≠ source := by
          intro same
          subst source
          exact nodupParts.1 dependencyMember
        have fullOrder := before (by
          simp only [TreeSubstitution.keys, List.map_cons, List.mem_cons]
          exact Or.inr dependencyMember)
        change
          List.idxOf dependency
              (source :: TreeSubstitution.keys binding) <
            List.idxOf candidate.1
              (source :: TreeSubstitution.keys binding) at fullOrder
        rw [List.idxOf_cons_ne _ (Ne.symm dependencyDifferent),
          List.idxOf_cons_ne _ (Ne.symm sourceDifferent)] at fullOrder
        omega)
      candidateOrder

/-- A topological canonical substitution eliminates every variable in its
own domain from the result of applying it to an arbitrary tree. -/
theorem TreeSubstitutionTopological.apply_avoids
    {binding : TreeSubstitution}
    (topological : TreeSubstitutionTopological binding) :
    ∀ tree,
      TreeVariablesSatisfy
        (fun identity =>
          identity ∉ TreeSubstitution.keys binding)
        (TreeSubstitution.apply binding tree) := by
  induction binding with
  | nil =>
      intro tree
      exact TreeVariablesSatisfy.mono
        (first := fun _ => True)
        (second := fun identity =>
          identity ∉ TreeSubstitution.keys [])
        (fun _ _ => by simp [TreeSubstitution.keys])
        (treeVariablesSatisfy_true tree)
  | cons entry binding inductionHypothesis =>
      rcases entry with ⟨source, replacement⟩
      intro tree
      have tailTopological := topological.tail
      have appliedTail :=
        inductionHypothesis tailTopological tree
      have replacementAvoids :
          TreeVariablesSatisfy
            (fun identity =>
              identity ∉
                TreeSubstitution.keys
                  ((source, replacement) :: binding))
            replacement := by
        have headOrder :=
          topological.decreases (source, replacement) (by simp)
        exact TreeVariablesSatisfy.mono
          (fun dependency before dependencyMember => by
            have impossible := before dependencyMember
            simp [TreeSubstitution.keys] at impossible)
          headOrder
      have tailAllowsSource :
          TreeVariablesSatisfy
            (fun identity =>
              identity = source ∨
                identity ∉
                  TreeSubstitution.keys
                    ((source, replacement) :: binding))
            (TreeSubstitution.apply binding tree) := by
        exact TreeVariablesSatisfy.mono
          (fun identity outsideTail => by
            by_cases same : identity = source
            · exact Or.inl same
            · exact Or.inr (by
                simp only [TreeSubstitution.keys, List.map_cons,
                  List.mem_cons, not_or]
                exact ⟨same, outsideTail⟩))
          appliedTail
      exact treeVariablesSatisfy_instantiateOne_eliminate source
        replacementAvoids tailAllowsSource

/-- Ordered-list version of domain elimination. -/
theorem TreeSubstitutionTopological.applyTrees_avoids
    {binding : TreeSubstitution}
    (topological : TreeSubstitutionTopological binding) :
    ∀ trees,
      TreesVariablesSatisfy
        (fun identity =>
          identity ∉ TreeSubstitution.keys binding)
        (TreeSubstitution.applyTrees binding trees)
  | [] => by simp [TreesVariablesSatisfy]
  | tree :: trees => by
      rw [TreeSubstitution.applyTrees_cons]
      exact
        ⟨topological.apply_avoids tree,
          topological.applyTrees_avoids trees⟩

mutual

/-- A pointwise proof that `source` is absent is sufficient to show that one
canonical instantiation leaves a tree unchanged.  Keeping this statement in
the support calculus avoids converting the structural invariant back through
the boolean `occurs` test. -/
theorem TreeVariablesSatisfy.instantiateOne_eq_self
    (source : LogicVar) {replacement : Tree} :
    ∀ {tree : Tree},
      TreeVariablesSatisfy (fun identity => identity ≠ source) tree →
        Tree.instantiateOne source replacement tree = tree
  | .variable identity, supported => by
      change identity ≠ source at supported
      simp [Tree.instantiateOne, supported]
  | .node _ _, supported => by
      simp only [Tree.instantiateOne, Tree.node.injEq, true_and]
      exact
        TreesVariablesSatisfy.instantiateOne_eq_self
          source supported

/-- Ordered-list companion to
`TreeVariablesSatisfy.instantiateOne_eq_self`. -/
theorem TreesVariablesSatisfy.instantiateOne_eq_self
    (source : LogicVar) {replacement : Tree} :
    ∀ {trees : List Tree},
      TreesVariablesSatisfy (fun identity => identity ≠ source) trees →
        Trees.instantiateOne source replacement trees = trees
  | [], _ =>
      rfl
  | _ :: _, supported => by
      simp only [Trees.instantiateOne, List.cons.injEq]
      exact
        ⟨TreeVariablesSatisfy.instantiateOne_eq_self
            source supported.1,
          TreesVariablesSatisfy.instantiateOne_eq_self
            source supported.2⟩

end

/-- A canonical substitution has no effect on a tree whose variables all lie
outside its domain. -/
theorem TreeSubstitution.apply_eq_self_of_variables_outside
    {binding : TreeSubstitution} {tree : Tree}
    (outside :
      TreeVariablesSatisfy
        (fun identity => identity ∉ TreeSubstitution.keys binding) tree) :
    TreeSubstitution.apply binding tree = tree := by
  induction binding with
  | nil =>
      rfl
  | cons entry binding inductionHypothesis =>
      rcases entry with ⟨source, replacement⟩
      have tailOutside :
          TreeVariablesSatisfy
            (fun identity =>
              identity ∉ TreeSubstitution.keys binding) tree :=
        TreeVariablesSatisfy.mono
          (fun identity absent member =>
            absent (by
              simp only [TreeSubstitution.keys, List.map_cons,
                List.mem_cons]
              exact Or.inr member))
          outside
      have sourceAbsent :
          TreeVariablesSatisfy (fun identity => identity ≠ source) tree :=
        TreeVariablesSatisfy.mono
          (fun identity absent same => by
            subst identity
            exact absent (by
              simp [TreeSubstitution.keys]))
          outside
      simp only [TreeSubstitution.apply]
      rw [inductionHypothesis tailOutside]
      exact
        TreeVariablesSatisfy.instantiateOne_eq_self
          source sourceAbsent

/-- Looking up a canonical topological binding has the same denotation as
looking up its replacement.  This is the independent counterpart of
`SubstTopological.subst_var_of_lookup`. -/
theorem TreeSubstitutionTopological.apply_variable_eq_apply_value_of_mem
    {binding : TreeSubstitution}
    (topological : TreeSubstitutionTopological binding)
    {source : LogicVar} {value : Tree}
    (member : (source, value) ∈ binding) :
    TreeSubstitution.apply binding (.variable source) =
      TreeSubstitution.apply binding value := by
  induction binding with
  | nil =>
      simp at member
  | cons entry binding inductionHypothesis =>
      rcases entry with ⟨headSource, headValue⟩
      simp only [List.mem_cons] at member
      rcases member with head | tail
      · cases head
        have nodupParts :
            source ∉ TreeSubstitution.keys binding ∧
              (TreeSubstitution.keys binding).Nodup := by
          exact List.nodup_cons.mp (by
            simpa [TreeSubstitution.keys] using topological.nodup)
        have tailSourceOutside :
            TreeVariablesSatisfy
              (fun identity =>
                identity ∉ TreeSubstitution.keys binding)
              (.variable source) := nodupParts.1
        have valueOutsideFull :
            TreeVariablesSatisfy
              (fun identity =>
                identity ∉
                  TreeSubstitution.keys ((source, value) :: binding))
              value := by
          have headOrder :=
            topological.decreases (source, value) (by simp)
          exact TreeVariablesSatisfy.mono
            (fun dependency before dependencyMember => by
              have impossible := before dependencyMember
              simp [TreeSubstitution.keys] at impossible)
            headOrder
        have valueOutsideTail :
            TreeVariablesSatisfy
              (fun identity =>
                identity ∉ TreeSubstitution.keys binding)
              value :=
          TreeVariablesSatisfy.mono
            (fun identity absent member =>
              absent (by
                simp only [TreeSubstitution.keys, List.map_cons,
                  List.mem_cons]
                exact Or.inr member))
            valueOutsideFull
        have sourceAbsentValue :
            TreeVariablesSatisfy (fun identity => identity ≠ source) value :=
          TreeVariablesSatisfy.mono
            (fun identity absent same => by
              subst identity
              exact absent (by simp [TreeSubstitution.keys]))
            valueOutsideFull
        simp only [TreeSubstitution.apply]
        rw [TreeSubstitution.apply_eq_self_of_variables_outside
              tailSourceOutside,
          TreeSubstitution.apply_eq_self_of_variables_outside
              valueOutsideTail]
        simp only [Tree.instantiateOne, ite_true]
        exact
          (TreeVariablesSatisfy.instantiateOne_eq_self
            source sourceAbsentValue).symm
      · simp only [TreeSubstitution.apply]
        rw [inductionHypothesis topological.tail tail]

/-- If every generated key and replacement avoids the base domain, two
topological substitutions compose in the same `extension ++ base` order as
the canonical MGU. -/
theorem TreeSubstitutionTopological.append
    {base extension : TreeSubstitution}
    (baseTopological : TreeSubstitutionTopological base)
    (extensionTopological : TreeSubstitutionTopological extension)
    (extensionAvoids :
      TreeSubstitutionVariablesSatisfy
        (fun identity =>
          identity ∉ TreeSubstitution.keys base)
        extension) :
    TreeSubstitutionTopological (extension ++ base) := by
  have keyDisjoint :
      List.Disjoint (TreeSubstitution.keys extension)
        (TreeSubstitution.keys base) := by
    rw [List.disjoint_left]
    intro identity extensionMember baseMember
    rcases List.mem_map.mp extensionMember with
      ⟨entry, entryMember, identityShape⟩
    subst identity
    have avoided := (extensionAvoids entry entryMember).1
    exact avoided baseMember
  constructor
  · simpa [TreeSubstitution.keys, List.map_append] using
      List.Nodup.append extensionTopological.nodup
        baseTopological.nodup keyDisjoint
  · intro entry member
    rw [List.mem_append] at member
    rcases member with extensionMember | baseMember
    · have extensionOrder :=
        extensionTopological.decreases entry extensionMember
      have avoided := (extensionAvoids entry extensionMember).2
      exact TreeVariablesSatisfy.mono
        (fun dependency support dependencyMember => by
          rcases support with ⟨before, outsideBase⟩
          have dependencyExtension :
              dependency ∈ TreeSubstitution.keys extension := by
            have split :
                dependency ∈ TreeSubstitution.keys extension ∨
                  dependency ∈ TreeSubstitution.keys base := by
              simpa [TreeSubstitution.keys, List.map_append] using
                dependencyMember
            rcases split with extensionMember | baseMember
            · exact extensionMember
            · exact False.elim (outsideBase baseMember)
          have sourceExtension :
              entry.1 ∈ TreeSubstitution.keys extension :=
            List.mem_map_of_mem extensionMember
          have dependencyIndex :
              (TreeSubstitution.keys (extension ++ base)).idxOf dependency =
                (TreeSubstitution.keys extension).idxOf dependency := by
            simpa [TreeSubstitution.keys, List.map_append] using
              (List.idxOf_append_of_mem
                (l₂ := TreeSubstitution.keys base)
                dependencyExtension)
          have sourceIndex :
              (TreeSubstitution.keys (extension ++ base)).idxOf entry.1 =
                (TreeSubstitution.keys extension).idxOf entry.1 := by
            simpa [TreeSubstitution.keys, List.map_append] using
              (List.idxOf_append_of_mem
                (l₂ := TreeSubstitution.keys base)
                sourceExtension)
          rw [dependencyIndex, sourceIndex]
          exact before dependencyExtension)
        (TreeVariablesSatisfy.and extensionOrder avoided)
    · have baseOrder :=
        baseTopological.decreases entry baseMember
      exact TreeVariablesSatisfy.mono
        (fun dependency before dependencyMember => by
          rw [TreeSubstitution.keys, List.map_append,
            List.mem_append] at dependencyMember
          rcases dependencyMember with
              dependencyExtension | dependencyBase
          · have sourceNotExtension :
                entry.1 ∉ TreeSubstitution.keys extension := by
              intro sourceExtension
              exact (List.disjoint_left.mp keyDisjoint)
                sourceExtension (List.mem_map_of_mem baseMember)
            have dependencyRank :
                (TreeSubstitution.keys extension).idxOf dependency <
                  (TreeSubstitution.keys extension).length :=
              List.idxOf_lt_length_of_mem dependencyExtension
            have dependencyIndex :
                (TreeSubstitution.keys (extension ++ base)).idxOf
                    dependency =
                  (TreeSubstitution.keys extension).idxOf dependency := by
              simpa [TreeSubstitution.keys, List.map_append] using
                (List.idxOf_append_of_mem
                  (l₂ := TreeSubstitution.keys base)
                  dependencyExtension)
            have sourceIndex :
                (TreeSubstitution.keys (extension ++ base)).idxOf entry.1 =
                  (TreeSubstitution.keys extension).length +
                    (TreeSubstitution.keys base).idxOf entry.1 := by
              simpa [TreeSubstitution.keys, List.map_append] using
                (List.idxOf_append_of_notMem
                  (l₂ := TreeSubstitution.keys base)
                  sourceNotExtension)
            rw [dependencyIndex, sourceIndex]
            omega
          · have sourceNotExtension :
                entry.1 ∉ TreeSubstitution.keys extension := by
              intro sourceExtension
              exact (List.disjoint_left.mp keyDisjoint)
                sourceExtension (List.mem_map_of_mem baseMember)
            have dependencyNotExtension :
                dependency ∉ TreeSubstitution.keys extension := by
              intro dependencyExtension
              exact (List.disjoint_left.mp keyDisjoint)
                dependencyExtension dependencyBase
            have dependencyIndex :
                (TreeSubstitution.keys (extension ++ base)).idxOf
                    dependency =
                  (TreeSubstitution.keys extension).length +
                    (TreeSubstitution.keys base).idxOf dependency := by
              simpa [TreeSubstitution.keys, List.map_append] using
                (List.idxOf_append_of_notMem
                  (l₂ := TreeSubstitution.keys base)
                  dependencyNotExtension)
            have sourceIndex :
                (TreeSubstitution.keys (extension ++ base)).idxOf entry.1 =
                  (TreeSubstitution.keys extension).length +
                    (TreeSubstitution.keys base).idxOf entry.1 := by
              simpa [TreeSubstitution.keys, List.map_append] using
                (List.idxOf_append_of_notMem
                  (l₂ := TreeSubstitution.keys base)
                  sourceNotExtension)
            rw [dependencyIndex, sourceIndex]
            exact Nat.add_lt_add_left (before dependencyBase)
              (TreeSubstitution.keys extension).length)
        baseOrder

/-! ## The ordered MGU produces a topological substitution -/

mutual

private theorem treeAndForest_binding_topological :
    (∀ {left right binding}, TreeMgu left right binding →
      TreeSubstitutionTopological binding) ∧
    (∀ {left right binding}, TreesMgu left right binding →
      TreeSubstitutionTopological binding) :=
  TreeMgu.inductBoth
    (tree := fun _ _ binding =>
      TreeSubstitutionTopological binding)
    (forest := fun _ _ binding =>
      TreeSubstitutionTopological binding)
    (fun _ => .nil)
    (fun source value _ absent =>
      .singleton source value absent)
    (fun value target _ absent =>
      .singleton target value absent)
    (fun _ _ _ _ _ childrenInduction => childrenInduction)
    .nil
    (fun left right lefts rights base extension head tail
        headInduction tailInduction => by
      have baseLeft := headInduction.applyTrees_avoids lefts
      have baseRight := headInduction.applyTrees_avoids rights
      have extensionAvoids :=
        treesMgu_binding_variablesSatisfy tail baseLeft baseRight
      exact headInduction.append tailInduction extensionAvoids)

/-- Every canonical one-tree MGU records an acyclic elimination order. -/
theorem TreeMgu.binding_topological
    {left right : Tree} {binding : TreeSubstitution}
    (derivation : TreeMgu left right binding) :
    TreeSubstitutionTopological binding :=
  treeAndForest_binding_topological.1 derivation

/-- Ordered child unification records the same acyclic order. -/
theorem TreesMgu.binding_topological
    {left right : List Tree} {binding : TreeSubstitution}
    (derivation : TreesMgu left right binding) :
    TreeSubstitutionTopological binding :=
  treeAndForest_binding_topological.2 derivation

end

/-- Ordered equation-worklist unification remains topological through every
head normalization and tail composition. -/
theorem OrderedTreeMgu.binding_topological
    {equations : List TreeEquation} {binding : TreeSubstitution}
    (derivation : OrderedTreeMgu equations binding) :
    TreeSubstitutionTopological binding := by
  induction derivation with
  | nil =>
      exact .nil
  | cons left right equations base extension head tail
      inductionHypothesis =>
      have baseTopological :=
        Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguTopology.TreeMgu.binding_topological head
      have normalizedSupported :
          TreeEquationsVariablesSatisfy
            (fun identity =>
              identity ∉ TreeSubstitution.keys base)
            (TreeSubstitution.applyEquations base equations) := by
        intro equation member
        simp only [TreeSubstitution.applyEquations, List.mem_map] at member
        obtain ⟨original, _, rfl⟩ := member
        exact
          ⟨baseTopological.apply_avoids original.1,
            baseTopological.apply_avoids original.2⟩
      have extensionAvoids :=
        orderedTreeMgu_binding_variablesSatisfy tail normalizedSupported
      exact baseTopological.append inductionHypothesis extensionAvoids

/-! ## Transporting the elimination order through alpha agreement -/

/-- Ordered substitution keys agree pointwise under one alpha graph. -/
def AlphaKeysAgree
    (alpha : List (LogicVar × String))
    (canonical : TreeSubstitution) (runtime : Subst) : Prop :=
  List.Forall₂
    (fun identity name => (identity, name) ∈ alpha)
    (TreeSubstitution.keys canonical) (runtime.map Prod.fst)

/-- Raw substitution agreement contains pointwise agreement of the complete
ordered key lists. -/
theorem AlphaTreeSubstitutionAgrees.keys_agree
    {alpha : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaTreeSubstitutionAgrees alpha canonical runtime) :
    AlphaKeysAgree alpha canonical runtime := by
  induction agreement with
  | nil =>
      exact .nil
  | cons linked _ _ inductionHypothesis =>
      exact .cons linked inductionHypothesis

/-- A runtime key membership has a canonical partner at the same aligned
substitution layer. -/
theorem AlphaKeysAgree.canonical_of_runtime_mem
    {alpha : List (LogicVar × String)}
    {canonicalNames : List LogicVar} {runtimeNames : List String}
    (agreement :
      List.Forall₂
        (fun identity name => (identity, name) ∈ alpha)
        canonicalNames runtimeNames) :
    ∀ {name}, name ∈ runtimeNames →
      ∃ identity, identity ∈ canonicalNames ∧
        (identity, name) ∈ alpha := by
  intro name member
  induction agreement with
  | nil =>
      simp at member
  | @cons identity headName canonicalTail runtimeTail linked tail
      inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨identity, by simp, linked⟩
      · obtain ⟨source, sourceMember, sourceLinked⟩ :=
          inductionHypothesis member
        exact ⟨source, by simp [sourceMember], sourceLinked⟩

/-- A canonical key membership has a runtime partner. -/
theorem AlphaKeysAgree.runtime_of_canonical_mem
    {alpha : List (LogicVar × String)}
    {canonicalNames : List LogicVar} {runtimeNames : List String}
    (agreement :
      List.Forall₂
        (fun identity name => (identity, name) ∈ alpha)
        canonicalNames runtimeNames) :
    ∀ {identity}, identity ∈ canonicalNames →
      ∃ name, name ∈ runtimeNames ∧
        (identity, name) ∈ alpha := by
  intro identity member
  induction agreement with
  | nil =>
      simp at member
  | @cons headIdentity headName canonicalTail runtimeTail linked tail
      inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨headName, by simp, linked⟩
      · obtain ⟨name, nameMember, nameLinked⟩ :=
          inductionHypothesis member
        exact ⟨name, by simp [nameMember], nameLinked⟩

/-- Bidirectional alpha functionality makes aligned key positions exact. -/
theorem AlphaKeysAgree.idxOf_eq
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {canonicalNames : List LogicVar} {runtimeNames : List String}
    (agreement :
      List.Forall₂
        (fun identity name => (identity, name) ∈ alpha)
        canonicalNames runtimeNames)
    {identity : LogicVar} {name : String}
    (linked : (identity, name) ∈ alpha)
    (canonicalMember : identity ∈ canonicalNames)
    (runtimeMember : name ∈ runtimeNames) :
    canonicalNames.idxOf identity = runtimeNames.idxOf name := by
  induction agreement with
  | nil =>
      simp at canonicalMember
  | @cons headIdentity headName canonicalTail runtimeTail headLinked tail
      inductionHypothesis =>
      by_cases canonicalHead : identity = headIdentity
      · subst identity
        have runtimeHead : name = headName :=
          shared.forward linked headLinked
        subst name
        simp
      · have runtimeHead : name ≠ headName := by
          intro same
          subst name
          exact canonicalHead (shared.backward linked headLinked)
        have canonicalTailMember : identity ∈ canonicalTail := by
          simpa [canonicalHead] using canonicalMember
        have runtimeTailMember : name ∈ runtimeTail := by
          simpa [runtimeHead] using runtimeMember
        have tailIndex :=
          inductionHypothesis canonicalTailMember runtimeTailMember
        rw [List.idxOf_cons_ne _ (Ne.symm canonicalHead),
          List.idxOf_cons_ne _ (Ne.symm runtimeHead)]
        exact congrArg Nat.succ tailIndex

/-- Aligned runtime keys are unique whenever canonical keys are unique and
the alpha graph is injective in the runtime-to-canonical direction. -/
theorem AlphaKeysAgree.runtime_nodup
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {canonicalNames : List LogicVar} {runtimeNames : List String}
    (agreement :
      List.Forall₂
        (fun identity name => (identity, name) ∈ alpha)
        canonicalNames runtimeNames)
    (canonicalNodup : canonicalNames.Nodup) :
    runtimeNames.Nodup := by
  induction agreement with
  | nil =>
      exact List.nodup_nil
  | @cons identity name canonicalTail runtimeTail linked tail
      inductionHypothesis =>
      rw [List.nodup_cons] at canonicalNodup ⊢
      constructor
      · intro runtimeMember
        obtain ⟨other, canonicalMember, otherLinked⟩ :=
          AlphaKeysAgree.canonical_of_runtime_mem tail runtimeMember
        have same := shared.backward linked otherLinked
        subst other
        exact canonicalNodup.1 canonicalMember
      · exact inductionHypothesis canonicalNodup.2

/-- Runtime lookup is defined exactly on the stored key list. -/
theorem runtime_lookup_ne_none_iff_mem_keys
    (runtime : Subst) (name : String) :
    Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup runtime name ≠ none ↔
      name ∈ runtime.map Prod.fst := by
  induction runtime with
  | nil =>
      simp [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup]
  | cons entry runtime inductionHypothesis =>
      rcases entry with ⟨key, value⟩
      by_cases same : name = key
      · subst name
        simp [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup]
      · have check : (name == key) = false := by simp [same]
        simp only [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup, check, Bool.false_eq_true, if_false,
          List.map_cons, List.mem_cons]
        rw [inductionHypothesis]
        simp [same]

/-- Successful runtime lookup recovers the corresponding canonical entry and
its structural replacement agreement. -/
theorem AlphaTreeSubstitutionAgrees.of_runtime_lookup
    {alpha : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaTreeSubstitutionAgrees alpha canonical runtime)
    {name : String} {atom : Atom}
    (lookup : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup runtime name = some atom) :
    ∃ identity tree,
      (identity, tree) ∈ canonical ∧
        (identity, name) ∈ alpha ∧
        CanonicalRuntimeAgrees alpha tree atom := by
  induction agreement with
  | nil =>
      simp [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup] at lookup
  | @cons identity key tree value canonical runtime linked replacement tail
      inductionHypothesis =>
      by_cases same : name = key
      · subst name
        simp [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup] at lookup
        subst atom
        exact
          ⟨identity, tree, by simp, linked, replacement⟩
      · have check : (name == key) = false := by simp [same]
        simp only [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup, check, Bool.false_eq_true,
          if_false] at lookup
        obtain ⟨source, target, member, sourceLinked, targetAgrees⟩ :=
          inductionHypothesis lookup
        exact
          ⟨source, target, by simp [member], sourceLinked,
            targetAgrees⟩

mutual

/-- Structural representation plus a canonical support certificate maps
every runtime replacement variable back to a supported canonical variable. -/
theorem CanonicalRuntimeAgrees.runtime_variable_supported
    {alpha : List (LogicVar × String)}
    {predicate : LogicVar → Prop}
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom)
    (supported : TreeVariablesSatisfy predicate tree) :
    ∀ {name}, name ∈ atom.vars →
      ∃ identity, (identity, name) ∈ alpha ∧ predicate identity := by
  intro name member
  induction agreement with
  | @«variable» identity runtimeName linked =>
      simp only [Atom.vars, List.mem_singleton] at member
      subst name
      exact ⟨identity, linked, supported⟩
  | atom | trueAtom | falseAtom | integer | float | string | nil =>
      simp [Atom.vars, nilA] at member
  | @partialValue head argumentsTree encodedArguments arguments
      inductionHypothesis =>
      have argumentSupported := supported.2.1
      have argumentMember : name ∈ encodedArguments.vars := by
        simpa [partialC, prologCompoundC, prologCompoundTagA,
          chainOf, consC, nilA, Atom.vars] using member
      exact inductionHypothesis argumentSupported argumentMember
  | @cons headTree tailTree headAtom tailAtom head tail headInduction
      tailInduction =>
      have split :
          name ∈ headAtom.vars ∨ name ∈ tailAtom.vars := by
        simpa [consC, Atom.vars] using member
      rcases split with headMember | tailMember
      · exact headInduction supported.1 headMember
      · exact tailInduction supported.2.1 tailMember

/-- Ordered-list companion is kept mutual for structural recursion. -/
theorem CanonicalRuntimeAgreesList.runtime_variable_supported
    {alpha : List (LogicVar × String)}
    {predicate : LogicVar → Prop}
    {trees : List Tree} {atoms : List Atom}
    (agreement :
      List.Forall₂ (CanonicalRuntimeAgrees alpha) trees atoms)
    (supported : TreesVariablesSatisfy predicate trees) :
    ∀ {name}, name ∈ atoms.flatMap Atom.vars →
      ∃ identity, (identity, name) ∈ alpha ∧ predicate identity := by
  intro name member
  induction agreement with
  | nil =>
      simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.flatMap_cons, List.mem_append] at member
      rcases member with headMember | tailMember
      · exact
          CanonicalRuntimeAgrees.runtime_variable_supported
            head supported.1 headMember
      · exact inductionHypothesis supported.2 tailMember

end

/-- A source variable can agree only with a runtime variable carrying its
exact alpha edge.  This is the source-oriented counterpart of
`runtime_variable_linked`; keeping both projections avoids exposing concrete
fresh-name suffixes in recursive-call proofs. -/
theorem AlphaTermAgrees.source_variable_linked
    {alpha : List (LogicVar × String)} {identity : LogicVar} {atom : Atom}
    (agreement : AlphaTermAgrees alpha (.variable identity) atom) :
    ∃ name, atom = .var name ∧ (identity, name) ∈ alpha := by
  cases agreement with
  | «variable» linked => exact ⟨_, rfl, linked⟩

/-- Every executable variable occurring in an alpha-related term is backed by
an actual edge of that alpha graph.  This projection is the runtime analogue
of canonical variable coverage and is the stable interface for freshness and
capture arguments. -/
theorem AlphaTermAgrees.runtime_variable_linked
    {alpha : List (LogicVar × String)} {term : Term} {atom : Atom}
    (agreement : AlphaTermAgrees alpha term atom) :
    ∀ {name}, name ∈ atom.vars →
      ∃ identity, (identity, name) ∈ alpha := by
  intro name member
  obtain ⟨identity, linked, _supported⟩ :=
    CanonicalRuntimeAgrees.runtime_variable_supported
      (AlphaTermAgrees.canonicalRuntimeAgrees agreement)
      (treeVariablesSatisfy_true (Term.denote term)) member
  exact ⟨identity, linked⟩

/-- If an alpha-linked canonical variable is outside an aligned canonical
domain, its runtime name is outside the aligned runtime domain as well. -/
theorem AlphaKeysAgree.runtime_not_mem_of_canonical_not_mem
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {canonicalNames : List LogicVar} {runtimeNames : List String}
    (agreement :
      List.Forall₂
        (fun identity name => (identity, name) ∈ alpha)
        canonicalNames runtimeNames)
    {identity : LogicVar} {name : String}
    (linked : (identity, name) ∈ alpha)
    (canonicalNotMember : identity ∉ canonicalNames) :
    name ∉ runtimeNames := by
  intro runtimeMember
  obtain ⟨other, canonicalMember, otherLinked⟩ :=
    AlphaKeysAgree.canonical_of_runtime_mem agreement runtimeMember
  have same := shared.backward linked otherLinked
  subst other
  exact canonicalNotMember canonicalMember

private theorem subst_chainOf_local (runtime : Subst)
    (atoms : List Atom) :
    Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime (chainOf atoms) =
      chainOf (atoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime)) := by
  induction atoms with
  | nil =>
      simp [chainOf, nilA]
  | cons head tail inductionHypothesis =>
      change
        Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime (consC head (chainOf tail)) =
          consC (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime head)
            (chainOf (tail.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime)))
      rw [show
        Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime (consC head (chainOf tail)) =
          consC (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime head)
            (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime (chainOf tail)) by
              simp [consC, Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr]]
      rw [inductionHypothesis]

/-- Structural alpha agreement lifts through substitutions when the caller
supplies semantic agreement only for variables actually supported by the
tree.  This support-indexed form is what permits well-founded recursion on
the topological rank of replacement dependencies. -/
theorem CanonicalRuntimeAgrees.apply_of_supported
    {alpha : List (LogicVar × String)}
    {predicate : LogicVar → Prop}
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom)
    (supported : TreeVariablesSatisfy predicate tree)
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation :
      ∀ {identity name}, (identity, name) ∈ alpha →
        predicate identity →
        CanonicalRuntimeAgrees alpha
          (TreeSubstitution.apply canonical (.variable identity))
          (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime (.var name))) :
    CanonicalRuntimeAgrees alpha
      (TreeSubstitution.apply canonical tree)
      (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime atom) := by
  induction agreement with
  | «variable» linked =>
      exact valuation linked supported
  | atom notTrue notFalse =>
      simpa using
        (CanonicalRuntimeAgrees.atom (alpha := alpha) notTrue notFalse)
  | trueAtom =>
      simpa using (CanonicalRuntimeAgrees.trueAtom (alpha := alpha))
  | falseAtom =>
      simpa using (CanonicalRuntimeAgrees.falseAtom (alpha := alpha))
  | integer value =>
      simpa using (CanonicalRuntimeAgrees.integer (alpha := alpha) value)
  | float value =>
      simpa using (CanonicalRuntimeAgrees.float (alpha := alpha) value)
  | string value =>
      simpa using (CanonicalRuntimeAgrees.string (alpha := alpha) value)
  | partialValue arguments inductionHypothesis =>
      simpa [partialC, prologCompoundC, prologCompoundTagA,
        TreeSubstitution.apply_node, subst_chainOf_local] using
        (CanonicalRuntimeAgrees.partialValue
          (inductionHypothesis supported.2.1))
  | nil =>
      simpa [nilA] using (CanonicalRuntimeAgrees.nil (alpha := alpha))
  | cons head tail headInduction tailInduction =>
      simpa [TreeSubstitution.apply_node, consC,
        Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr] using
        (CanonicalRuntimeAgrees.cons
          (headInduction supported.1)
          (tailInduction supported.2.1))

/-- A topological canonical substitution and its raw open alpha spelling
produce a genuine runtime topological certificate.  This is the guard that
rules out cyclic association-list spellings before deep lookup semantics are
compared. -/
def AlphaTreeSubstitutionAgrees.runtime_topological
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaTreeSubstitutionAgrees alpha canonical runtime)
    (canonicalTopological :
      TreeSubstitutionTopological canonical) :
    Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological runtime := by
  let keyAgreement :=
    AlphaTreeSubstitutionAgrees.keys_agree agreement
  refine
    { order := runtime.map Prod.fst
      nodup := AlphaKeysAgree.runtime_nodup shared keyAgreement
        canonicalTopological.nodup
      domain := ?_
      decreases := ?_ }
  · intro name
    exact (runtime_lookup_ne_none_iff_mem_keys runtime name).symm
  · intro source value dependency sourceLookup dependencyMember
      dependencyLookup
    obtain
      ⟨sourceIdentity, sourceTree, sourceCanonicalMember,
        sourceLinked, sourceAgreement⟩ :=
      AlphaTreeSubstitutionAgrees.of_runtime_lookup
        agreement sourceLookup
    have sourceCanonicalKey :
        sourceIdentity ∈ TreeSubstitution.keys canonical :=
      List.mem_map_of_mem sourceCanonicalMember
    have sourceRuntimeKey :
        source ∈ runtime.map Prod.fst :=
      (runtime_lookup_ne_none_iff_mem_keys runtime source).1
        (by simp [sourceLookup])
    have canonicalOrder :=
      canonicalTopological.decreases
        (sourceIdentity, sourceTree) sourceCanonicalMember
    obtain ⟨dependencyIdentity, dependencyLinked, dependencyBefore⟩ :=
      CanonicalRuntimeAgrees.runtime_variable_supported
        sourceAgreement canonicalOrder dependencyMember
    have dependencyRuntimeKey :
        dependency ∈ runtime.map Prod.fst :=
      (runtime_lookup_ne_none_iff_mem_keys runtime dependency).1
        dependencyLookup
    obtain
      ⟨canonicalDependency, canonicalDependencyMember,
        canonicalDependencyLinked⟩ :=
      AlphaKeysAgree.canonical_of_runtime_mem
        keyAgreement dependencyRuntimeKey
    have dependencyIdentityEq :
        dependencyIdentity = canonicalDependency :=
      shared.backward dependencyLinked canonicalDependencyLinked
    subst canonicalDependency
    have canonicalBefore :=
      dependencyBefore canonicalDependencyMember
    have dependencyIndex :=
      AlphaKeysAgree.idxOf_eq shared keyAgreement dependencyLinked
        canonicalDependencyMember dependencyRuntimeKey
    have sourceIndex :=
      AlphaKeysAgree.idxOf_eq shared keyAgreement sourceLinked
        sourceCanonicalKey sourceRuntimeKey
    rw [← dependencyIndex, ← sourceIndex]
    exact canonicalBefore

/-- Below a finite rank bound, raw alpha spelling plus the two topological
certificates already determines identical deep substitution semantics.  The
rank is on canonical keys; dependencies recurse only to strictly earlier
keys, while residual variables outside the domain remain variables on both
sides. -/
theorem AlphaTreeSubstitutionAgrees.valuation_below
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaTreeSubstitutionAgrees alpha canonical runtime)
    (canonicalTopological :
      TreeSubstitutionTopological canonical)
    (limit : Nat) :
    ∀ {identity name}, (identity, name) ∈ alpha →
      (TreeSubstitution.keys canonical).idxOf identity < limit →
      CanonicalRuntimeAgrees alpha
        (TreeSubstitution.apply canonical (.variable identity))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime (.var name)) := by
  let keyAgreement :=
    AlphaTreeSubstitutionAgrees.keys_agree agreement
  let runtimeTopological :=
    AlphaTreeSubstitutionAgrees.runtime_topological
      shared agreement canonicalTopological
  induction limit with
  | zero =>
      intro identity name linked rank
      omega
  | succ limit inductionHypothesis =>
      intro identity name linked rank
      by_cases canonicalMember :
          identity ∈ TreeSubstitution.keys canonical
      · obtain ⟨runtimeName, runtimeMember, runtimeLinked⟩ :=
          AlphaKeysAgree.runtime_of_canonical_mem
            keyAgreement canonicalMember
        have runtimeNameEq : name = runtimeName :=
          shared.forward linked runtimeLinked
        subst runtimeName
        have runtimeLookupDefined :
            Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup runtime name ≠ none :=
          (runtime_lookup_ne_none_iff_mem_keys runtime name).2
            runtimeMember
        cases runtimeLookup : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup runtime name with
        | none =>
            exact False.elim (runtimeLookupDefined runtimeLookup)
        | some value =>
            obtain
              ⟨sourceIdentity, sourceTree, sourceCanonicalMember,
                sourceLinked, sourceAgreement⟩ :=
              AlphaTreeSubstitutionAgrees.of_runtime_lookup
                agreement runtimeLookup
            have sourceIdentityEq : identity = sourceIdentity :=
              shared.backward linked sourceLinked
            subst sourceIdentity
            have canonicalEquation :=
              TreeSubstitutionTopological.apply_variable_eq_apply_value_of_mem
                canonicalTopological sourceCanonicalMember
            have runtimeEquation :=
              Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological.subst_var_of_lookup
                runtime runtimeTopological name value runtimeLookup
            have canonicalOrder :=
              canonicalTopological.decreases
                (identity, sourceTree) sourceCanonicalMember
            have replacementAgreement :
                CanonicalRuntimeAgrees alpha
                  (TreeSubstitution.apply canonical sourceTree)
                  (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime value) :=
              CanonicalRuntimeAgrees.apply_of_supported
                sourceAgreement canonicalOrder (by
                  intro dependency dependencyName dependencyLinked
                    dependencyBefore
                  by_cases dependencyMember :
                      dependency ∈ TreeSubstitution.keys canonical
                  · apply inductionHypothesis dependencyLinked
                    have before :
                        (TreeSubstitution.keys canonical).idxOf dependency <
                          (TreeSubstitution.keys canonical).idxOf identity := by
                      simpa using dependencyBefore dependencyMember
                    omega
                  · have dependencyCanonicalFixed :
                        TreeSubstitution.apply canonical
                            (.variable dependency) =
                          .variable dependency :=
                      TreeSubstitution.apply_eq_self_of_variables_outside
                        dependencyMember
                    have dependencyRuntimeNotMember :
                        dependencyName ∉ runtime.map Prod.fst :=
                      AlphaKeysAgree.runtime_not_mem_of_canonical_not_mem
                        shared keyAgreement dependencyLinked
                          dependencyMember
                    have dependencyRuntimeLookup :
                        Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup runtime dependencyName = none := by
                      cases lookup :
                          Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup runtime dependencyName with
                      | none =>
                          rfl
                      | some target =>
                          exact False.elim
                            (dependencyRuntimeNotMember
                              ((runtime_lookup_ne_none_iff_mem_keys
                                  runtime dependencyName).1
                                (by simp [lookup])))
                    rw [dependencyCanonicalFixed,
                      Mettapedia.Languages.MeTTa.PLeaTTa.subst_var_of_lookup_none
                        runtime dependencyName dependencyRuntimeLookup]
                    exact CanonicalRuntimeAgrees.variable dependencyLinked)
            rw [canonicalEquation, runtimeEquation]
            exact replacementAgreement
      · have canonicalFixed :
            TreeSubstitution.apply canonical (.variable identity) =
              .variable identity :=
          TreeSubstitution.apply_eq_self_of_variables_outside
            canonicalMember
        have runtimeNotMember :
            name ∉ runtime.map Prod.fst :=
          AlphaKeysAgree.runtime_not_mem_of_canonical_not_mem
            shared keyAgreement linked canonicalMember
        have runtimeLookup :
            Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup runtime name = none := by
          cases lookup : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup runtime name with
          | none =>
              rfl
          | some target =>
              exact False.elim
                (runtimeNotMember
                  ((runtime_lookup_ne_none_iff_mem_keys runtime name).1
                    (by simp [lookup])))
        rw [canonicalFixed,
          Mettapedia.Languages.MeTTa.PLeaTTa.subst_var_of_lookup_none runtime name runtimeLookup]
        exact CanonicalRuntimeAgrees.variable linked

/-- Raw open spelling of one topological canonical substitution is already
full denotational agreement under deep executable substitution.  This is the
non-ground bridge: residual variables are preserved up to the shared alpha
graph rather than being collapsed through a grounding valuation. -/
theorem AlphaTreeSubstitutionAgrees.valuation
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaTreeSubstitutionAgrees alpha canonical runtime)
    (canonicalTopological :
      TreeSubstitutionTopological canonical) :
    AlphaValuationAgrees alpha canonical runtime := by
  intro identity name linked
  apply AlphaTreeSubstitutionAgrees.valuation_below
      shared agreement canonicalTopological
      ((TreeSubstitution.keys canonical).length + 1) linked
  have rankBound :
      (TreeSubstitution.keys canonical).idxOf identity ≤
        (TreeSubstitution.keys canonical).length :=
    List.idxOf_le_length
  omega

/-- The ordered canonical MGU therefore has an open runtime spelling that is
already certified acyclic; no grounding valuation or executable run is used. -/
theorem SharedAlphaEquationsAgree.orderedMgu_open_topological_exists
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ runtime,
      AlphaTreeSubstitutionAgrees alpha canonical runtime ∧
        Nonempty (Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological runtime) := by
  obtain ⟨runtime, spelling⟩ :=
    SharedAlphaEquationsAgree.orderedMgu_open_spelling_exists
      agreement derivation
  let runtimeTopological :=
    AlphaTreeSubstitutionAgrees.runtime_topological
      shared spelling (OrderedTreeMgu.binding_topological derivation)
  exact
    ⟨runtime, spelling, ⟨runtimeTopological⟩⟩

/-- The same constructed open spelling is not merely acyclic: it denotes the
ordered canonical MGU under deep executable substitution, with residual
variables related by the original shared alpha graph. -/
theorem SharedAlphaEquationsAgree.orderedMgu_open_valuation_exists
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ runtime,
      AlphaTreeSubstitutionAgrees alpha canonical runtime ∧
        AlphaValuationAgrees alpha canonical runtime ∧
        Nonempty (Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological runtime) := by
  obtain ⟨runtime, spelling⟩ :=
    SharedAlphaEquationsAgree.orderedMgu_open_spelling_exists
      agreement derivation
  have canonicalTopological :=
    OrderedTreeMgu.binding_topological derivation
  let runtimeTopological :=
    AlphaTreeSubstitutionAgrees.runtime_topological
      shared spelling canonicalTopological
  exact
    ⟨runtime, spelling,
      AlphaTreeSubstitutionAgrees.valuation
        shared spelling canonicalTopological,
      ⟨runtimeTopological⟩⟩

/-! ### Anti-vacuity: raw spelling does not certify cycles -/

private def cycleLeft : LogicVar := .source "cycle-left"

private def cycleRight : LogicVar := .source "cycle-right"

private def cycleAlpha : List (LogicVar × String) :=
  [(cycleLeft, "cycle-x"), (cycleRight, "cycle-y")]

private def cycleCanonical : TreeSubstitution :=
  [(cycleLeft, .variable cycleRight),
    (cycleRight, .variable cycleLeft)]

private def cycleRuntime : Subst :=
  [("cycle-x", .var "cycle-y"),
    ("cycle-y", .var "cycle-x")]

/-- Pointwise alpha spelling alone permits a cyclic pair.  The theorem is a
positive inhabitance witness, so the later topology rejection cannot be
attributed to an empty spelling relation. -/
theorem cyclic_raw_spelling_exists :
    AlphaTreeSubstitutionAgrees cycleAlpha
      cycleCanonical cycleRuntime := by
  exact .cons
    (by simp [cycleAlpha, cycleLeft])
    (.variable (by simp [cycleAlpha, cycleRight]))
    (.cons
      (by simp [cycleAlpha, cycleRight])
      (.variable (by simp [cycleAlpha, cycleLeft]))
      .nil)

/-- The independent topology rejects that inhabited cyclic spelling: the
first replacement would need the second key to occur before the first. -/
theorem cyclic_canonical_has_no_topological_certificate :
    ¬ TreeSubstitutionTopological cycleCanonical := by
  intro topological
  have order :=
    topological.decreases
      (cycleLeft, .variable cycleRight) (by
        simp [cycleCanonical])
  have impossible := order (by
    simp [cycleCanonical, TreeSubstitution.keys, cycleRight])
  simp [cycleCanonical, TreeSubstitution.keys, cycleLeft, cycleRight] at impossible

/-- The executable topology independently rejects the same cycle.  Raw
association-list agreement therefore cannot launder a cyclic runtime
substitution into the deep semantic theorem. -/
theorem cyclic_runtime_has_no_topological_certificate :
    ¬ Nonempty (Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological cycleRuntime) := by
  rintro ⟨topological⟩
  have forward :=
    topological.decreases
      "cycle-x" (.var "cycle-y") "cycle-y"
      (by simp [cycleRuntime, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup])
      (by simp [Atom.vars])
      (by simp [cycleRuntime, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup])
  have backward :=
    topological.decreases
      "cycle-y" (.var "cycle-x") "cycle-x"
      (by simp [cycleRuntime, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup])
      (by simp [Atom.vars])
      (by simp [cycleRuntime, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup])
  omega

end Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguTopology
