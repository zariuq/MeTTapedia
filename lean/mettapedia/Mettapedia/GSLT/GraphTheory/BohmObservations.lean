import Mettapedia.GSLT.GraphTheory.BohmTree
import Mettapedia.GSLT.GraphTheory.ParallelReduction
import Mathlib.Data.List.Forall2

/-!
# Mathematical finite-depth Böhm observations

An observation uses an actual reachable head normal form, without a search-fuel
cap. Arguments are observed recursively at smaller depth. The term syntax,
head extractor, reduction relation, and finite tree datatype are shared with
the existing graph-lambda development. No admitted `BohmTheory` law is used.
-/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

private theorem collectArgs_parRed
    {term result : LambdaTerm} (h : term ⇛ result)
    {acc resultAcc : List LambdaTerm} (hAcc : List.Forall₂ ParRed acc resultAcc)
    {head : Nat} {arguments : List LambdaTerm}
    (hExtract : extractHNF.collectArgs term acc = some (head, arguments)) :
    ∃ resultArguments,
      extractHNF.collectArgs result resultAcc = some (head, resultArguments) ∧
      List.Forall₂ ParRed arguments resultArguments := by
  induction h generalizing acc resultAcc head arguments with
  | var n =>
      simp only [extractHNF.collectArgs, Option.some.injEq, Prod.mk.injEq] at hExtract
      rcases hExtract with ⟨rfl, rfl⟩
      exact ⟨resultAcc, rfl, hAcc⟩
  | lam _ _ => simp [extractHNF.collectArgs] at hExtract
  | app hFn hArg ihFn _ =>
      exact ihFn (List.Forall₂.cons hArg hAcc) hExtract
  | beta _ _ _ _ => simp [extractHNF.collectArgs] at hExtract

private theorem extractHNF_app_eq (function argument : LambdaTerm) :
    extractHNF (.app function argument) =
      (extractHNF.collectArgs (.app function argument) []).map
        (fun (head, arguments) => (0, head, arguments)) := by
  cases function with
  | var n => rfl
  | lam body => rfl
  | app f a =>
      simp only [extractHNF, extractHNF.collectArgs]
      cases extractHNF.collectArgs f [a, argument] with
      | none => rfl
      | some value => cases value; rfl

/-- An actual step from HNF retains lambda count, head variable, and argument
positions; each retained argument undergoes an actual parallel step. -/
theorem ParRed.extractHNF_residual {term result : LambdaTerm} (h : term ⇛ result)
    {numLams head : Nat} {arguments : List LambdaTerm}
    (hExtract : extractHNF term = some (numLams, head, arguments)) :
    ∃ resultArguments,
      extractHNF result = some (numLams, head, resultArguments) ∧
      List.Forall₂ ParRed arguments resultArguments := by
  induction h generalizing numLams head arguments with
  | var n =>
      simp only [extractHNF, Option.some.injEq, Prod.mk.injEq] at hExtract
      rcases hExtract with ⟨rfl, rfl, rfl⟩
      exact ⟨[], rfl, .nil⟩
  | @lam body body' hBody ih =>
      cases hInner : extractHNF body with
      | none => simp [extractHNF, hInner] at hExtract
      | some value =>
          rcases value with ⟨count, innerHead, innerArguments⟩
          simp only [extractHNF, hInner, Option.some.injEq, Prod.mk.injEq] at hExtract
          rcases hExtract with ⟨rfl, rfl, rfl⟩
          obtain ⟨resultArguments, hResult, hArguments⟩ := ih hInner
          exact ⟨resultArguments, by simp only [extractHNF, hResult], hArguments⟩
  | @app function function' argument argument' hFn hArg _ _ =>
      rw [extractHNF_app_eq] at hExtract
      cases hCollected : extractHNF.collectArgs (.app function argument) [] with
      | none => simp [hCollected] at hExtract
      | some value =>
          rcases value with ⟨innerHead, innerArguments⟩
          simp only [hCollected, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at hExtract
          rcases hExtract with ⟨rfl, rfl, rfl⟩
          obtain ⟨resultArguments, hResult, hArguments⟩ :=
            collectArgs_parRed (ParRed.app hFn hArg) List.Forall₂.nil hCollected
          exact ⟨resultArguments, by rw [extractHNF_app_eq, hResult]; rfl, hArguments⟩
  | beta _ _ _ _ => simp [extractHNF] at hExtract

private theorem forall₂_parRedStar_trans
    {first second third : List LambdaTerm}
    (h₁ : List.Forall₂ ParRedStar first second)
    (h₂ : List.Forall₂ ParRedStar second third) :
    List.Forall₂ ParRedStar first third := by
  induction h₁ generalizing third with
  | nil => cases h₂; exact .nil
  | cons hHead hTail ih =>
      cases h₂ with
      | cons hHead' hTail' => exact .cons (hHead.trans hHead') (ih hTail')

/-- A whole path from HNF preserves its observable head and transports the
ordered argument spine through actual reduction paths. -/
theorem ParRedStar.extractHNF_residual {term result : LambdaTerm} (h : term ⇛* result)
    {numLams head : Nat} {arguments : List LambdaTerm}
    (hExtract : extractHNF term = some (numLams, head, arguments)) :
    ∃ resultArguments,
      extractHNF result = some (numLams, head, resultArguments) ∧
      List.Forall₂ ParRedStar arguments resultArguments := by
  induction h with
  | refl =>
      exact ⟨arguments, hExtract,
        List.forall₂_same.mpr (fun _ _ => Relation.ReflTransGen.refl)⟩
  | tail _ hStep ih =>
      obtain ⟨middleArguments, hMiddle, hArguments⟩ := ih
      obtain ⟨resultArguments, hResult, hStepArguments⟩ := hStep.extractHNF_residual hMiddle
      exact ⟨resultArguments, hResult, forall₂_parRedStar_trans hArguments
        (hStepArguments.imp (fun _ _ hArg => Relation.ReflTransGen.single hArg))⟩

/-- A mathematical finite-depth observation. Positive-depth bottom requires
actual unsolvability, not exhaustion. A node retains an actual reachable HNF
and recursively observes its ordered argument spine. -/
def BohmObservation : Nat → LambdaTerm → BohmTree → Prop
  | 0, _, tree => tree = .bot
  | _ + 1, term, .bot => term.Unsolvable
  | depth + 1, term, .node numLams head children =>
      ∃ hnf arguments, (term ⇛* hnf) ∧
        extractHNF hnf = some (numLams, head, arguments) ∧
        List.Forall₂ (BohmObservation depth) arguments children

theorem BohmObservation.zero (term : LambdaTerm) : BohmObservation 0 term .bot := rfl

theorem BohmObservation.bottom {depth : Nat} {term : LambdaTerm}
    (h : term.Unsolvable) : BohmObservation (depth + 1) term .bot := h

theorem BohmObservation.node {depth : Nat} {term hnf : LambdaTerm} {numLams head : Nat}
    {arguments : List LambdaTerm} {children : List BohmTree}
    (path : term ⇛* hnf)
    (headForm : extractHNF hnf = some (numLams, head, arguments))
    (subtrees : List.Forall₂ (BohmObservation depth) arguments children) :
    BohmObservation (depth + 1) term (.node numLams head children) :=
  ⟨hnf, arguments, path, headForm, subtrees⟩

private theorem forall₂_transport_observations {depth : Nat}
    {arguments resultArguments : List LambdaTerm} {children : List BohmTree}
    (paths : List.Forall₂ ParRedStar arguments resultArguments)
    (observations : List.Forall₂ (BohmObservation depth) arguments children)
    (transport : ∀ {term result : LambdaTerm} {tree : BohmTree}, (term ⇛* result) →
      BohmObservation depth term tree → BohmObservation depth result tree) :
    List.Forall₂ (BohmObservation depth) resultArguments children := by
  induction paths generalizing children with
  | nil => cases observations; exact .nil
  | cons headPath tailPaths ih =>
      cases observations with
      | cons headObservation tailObservations =>
          exact .cons (transport headPath headObservation) (ih tailObservations)

/-- Genuine observations are invariant under actual reduction. Confluence
joins a witnessed HNF with the computation; head residuals transport every
argument observation inductively. The converse prepends the actual path. -/
theorem BohmObservation.reduction_iff {term result : LambdaTerm}
    (path : term ⇛* result) (depth : Nat) (tree : BohmTree) :
    BohmObservation depth term tree ↔ BohmObservation depth result tree := by
  induction depth generalizing term result tree with
  | zero => rfl
  | succ depth ih =>
      cases tree with
      | bot => exact unsolvable_iff_of_parRedStar path
      | node numLams head children =>
          constructor
          · rintro ⟨hnf, arguments, headPath, headForm, subtrees⟩
            obtain ⟨joined, hHeadJoined, hResultJoined⟩ := confluence headPath path
            obtain ⟨resultArguments, hResultHead, hArgumentPaths⟩ :=
              hHeadJoined.extractHNF_residual headForm
            exact .node hResultJoined hResultHead
              (forall₂_transport_observations hArgumentPaths subtrees
                (fun hArg hObs => (ih hArg _).mp hObs))
          · rintro ⟨hnf, arguments, headPath, headForm, subtrees⟩
            exact .node (path.trans headPath) headForm subtrees

private theorem observations_exist_for_list {depth : Nat}
    (existsObservation : ∀ term, ∃ tree, BohmObservation depth term tree)
    (arguments : List LambdaTerm) :
    ∃ children, List.Forall₂ (BohmObservation depth) arguments children := by
  induction arguments with
  | nil => exact ⟨[], .nil⟩
  | cons head tail ih =>
      obtain ⟨headTree, hHead⟩ := existsObservation head
      obtain ⟨tailTrees, hTail⟩ := ih
      exact ⟨headTree :: tailTrees, .cons hHead hTail⟩

/-- Every term has an observation at every finite depth. This is a classical
mathematical existence theorem, not an executable decision of solvability. -/
theorem BohmObservation.exists (depth : Nat) (term : LambdaTerm) :
    ∃ tree, BohmObservation depth term tree := by
  classical
  induction depth generalizing term with
  | zero => exact ⟨.bot, .zero term⟩
  | succ depth ih =>
      by_cases hSolvable : term.Solvable
      · obtain ⟨hnf, path, head⟩ := hSolvable
        have hSome := (extractHNF_isSome_eq_isHNF hnf).trans head
        cases hExtract : extractHNF hnf with
        | none => simp only [hExtract, Option.isSome_none, Bool.false_eq_true] at hSome
        | some value =>
            rcases value with ⟨numLams, headVar, arguments⟩
            obtain ⟨children, hChildren⟩ := observations_exist_for_list ih arguments
            exact ⟨.node numLams headVar children, .node path hExtract hChildren⟩
      · exact ⟨.bot, .bottom hSolvable⟩

private theorem solvable_of_extracted_head {term hnf : LambdaTerm}
    {numLams head : Nat} {arguments : List LambdaTerm}
    (path : term ⇛* hnf)
    (headForm : extractHNF hnf = some (numLams, head, arguments)) : term.Solvable := by
  refine ⟨hnf, path, ?_⟩
  rw [← extractHNF_isSome_eq_isHNF, headForm]
  rfl

/-- A finite-depth observation is uniquely determined. Different reachable
HNFs have a common reduct with the same head and componentwise reducible
arguments; recursive observations, not literal argument syntax, agree. -/
theorem BohmObservation.unique {depth : Nat} {term : LambdaTerm} {first second : BohmTree}
    (hFirst : BohmObservation depth term first)
    (hSecond : BohmObservation depth term second) : first = second := by
  induction depth generalizing term first second with
  | zero => exact hFirst.trans hSecond.symm
  | succ depth ih =>
      cases first with
      | bot =>
          cases second with
          | bot => rfl
          | node numLams head children =>
              obtain ⟨hnf, arguments, path, headForm, _⟩ := hSecond
              exact (hFirst (solvable_of_extracted_head path headForm)).elim
      | node numLams head children =>
          obtain ⟨hnf, arguments, path, headForm, subtrees⟩ := hFirst
          cases second with
          | bot => exact (hSecond (solvable_of_extracted_head path headForm)).elim
          | node numLams' head' children' =>
              obtain ⟨hnf', arguments', path', headForm', subtrees'⟩ := hSecond
              obtain ⟨joined, hJoined, hJoined'⟩ := confluence path path'
              obtain ⟨joinedArguments, hJoinedHead, hJoinedArgs⟩ :=
                hJoined.extractHNF_residual headForm
              obtain ⟨joinedArguments', hJoinedHead', hJoinedArgs'⟩ :=
                hJoined'.extractHNF_residual headForm'
              have heads := hJoinedHead.symm.trans hJoinedHead'
              simp only [Option.some.injEq, Prod.mk.injEq] at heads
              rcases heads with ⟨rfl, rfl, rfl⟩
              have firstChildren := forall₂_transport_observations hJoinedArgs subtrees
                (fun hArg hObs => (BohmObservation.reduction_iff hArg depth _).mp hObs)
              have secondChildren := forall₂_transport_observations hJoinedArgs' subtrees'
                (fun hArg hObs => (BohmObservation.reduction_iff hArg depth _).mp hObs)
              have hChildren := List.right_unique_forall₂'
                (R := BohmObservation depth)
                (by intro _ _ _ h₁ h₂; exact ih h₁ h₂) firstChildren secondChildren
              exact congrArg (BohmTree.node numLams head) hChildren

/-- The unique mathematical finite-depth observation. Classical choice selects
an existing structural observation, whose uniqueness and reduction invariance
have been proved independently of this definition. -/
noncomputable def BohmObservation.tree (depth : Nat) (term : LambdaTerm) : BohmTree :=
  Classical.choose (BohmObservation.exists depth term)

theorem BohmObservation.tree_observation (depth : Nat) (term : LambdaTerm) :
    BohmObservation depth term (BohmObservation.tree depth term) :=
  Classical.choose_spec (BohmObservation.exists depth term)

theorem BohmObservation.tree_eq_iff (depth : Nat) (term : LambdaTerm) (tree : BohmTree) :
    BohmObservation.tree depth term = tree ↔ BohmObservation depth term tree := by
  constructor
  · intro h
    rw [← h]
    exact BohmObservation.tree_observation depth term
  · exact BohmObservation.unique (BohmObservation.tree_observation depth term)

/-- Actual reduction preserves the complete finite-depth mathematical tree. -/
theorem BohmObservation.tree_reduction_eq {term result : LambdaTerm}
    (path : term ⇛* result) (depth : Nat) :
    BohmObservation.tree depth term = BohmObservation.tree depth result :=
  BohmObservation.unique
    ((BohmObservation.reduction_iff path depth _).mp
      (BohmObservation.tree_observation depth term))
    (BohmObservation.tree_observation depth result)

/-- The source beta equation holds for these uncapped mathematical
observations, in contrast to the search-bounded evaluator observation. -/
theorem BohmObservation.tree_beta_eq (body argument : LambdaTerm) (depth : Nat) :
    BohmObservation.tree depth (.app (.lam body) argument) =
      BohmObservation.tree depth (argument.subst 0 body) :=
  BohmObservation.tree_reduction_eq
    (Relation.ReflTransGen.single (beta_to_parRed body argument)) depth

/-- At positive depth, exact bottom is equivalent to actual unsolvability. -/
theorem BohmObservation.tree_bot_iff (depth : Nat) (term : LambdaTerm) :
    BohmObservation.tree (depth + 1) term = .bot ↔ term.Unsolvable :=
  BohmObservation.tree_eq_iff (depth + 1) term .bot

private theorem tree_observations_for_list (depth : Nat) (arguments : List LambdaTerm) :
    List.Forall₂ (BohmObservation depth) arguments
      (arguments.map (BohmObservation.tree depth)) := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih => exact .cons (BohmObservation.tree_observation depth head) ih

/-- The source's recursive HNF clause holds for every actually reachable HNF,
independently of which such witness is supplied. -/
theorem BohmObservation.tree_node_of_reaches {term hnf : LambdaTerm}
    {numLams head : Nat} {arguments : List LambdaTerm}
    (path : term ⇛* hnf)
    (headForm : extractHNF hnf = some (numLams, head, arguments)) (depth : Nat) :
    BohmObservation.tree (depth + 1) term =
      .node numLams head (arguments.map (BohmObservation.tree depth)) :=
  (BohmObservation.tree_eq_iff _ _ _).mpr
    (.node path headForm (tree_observations_for_list depth arguments))

/-- Structural depth truncation of the shared finite tree datatype. -/
def BohmTree.truncate : Nat → BohmTree → BohmTree
  | 0, _ => .bot
  | _ + 1, .bot => .bot
  | depth + 1, .node numLams head children =>
      .node numLams head (children.map (BohmTree.truncate depth))

/-- A genuine deeper observation restricts to a genuine shallower one by
structural tree truncation, preserving the same actual HNF witness. -/
theorem BohmObservation.truncate {smaller larger : Nat} (hDepth : smaller ≤ larger)
    {term : LambdaTerm} {tree : BohmTree} (h : BohmObservation larger term tree) :
    BohmObservation smaller term (BohmTree.truncate smaller tree) := by
  induction smaller generalizing larger term tree with
  | zero => rfl
  | succ smaller ih =>
      cases larger with
      | zero => omega
      | succ larger =>
          have hSmaller : smaller ≤ larger := Nat.le_of_succ_le_succ hDepth
          cases tree with
          | bot => exact h
          | node numLams head children =>
              obtain ⟨hnf, arguments, path, headForm, subtrees⟩ := h
              apply BohmObservation.node path headForm
              apply List.forall₂_map_right_iff.mpr
              exact subtrees.imp (fun _ _ hChild => ih hSmaller hChild)

/-- The mathematical observations form a coherent family of finite-depth
trees, not unrelated observations at each depth. -/
theorem BohmObservation.tree_truncate (smaller larger : Nat) (hDepth : smaller ≤ larger)
    (term : LambdaTerm) :
    BohmTree.truncate smaller (BohmObservation.tree larger term) =
      BohmObservation.tree smaller term :=
  BohmObservation.unique
    (BohmObservation.truncate hDepth (BohmObservation.tree_observation larger term))
    (BohmObservation.tree_observation smaller term)

/-- The mathematical observation as a proved coherent family of shared finite
trees. This is not an executable normalizer or a graph-model realization. -/
noncomputable def BohmObservation.family (term : LambdaTerm) :
    {observations : Nat → BohmTree // ∀ smaller larger, smaller ≤ larger →
      BohmTree.truncate smaller (observations larger) = observations smaller} :=
  ⟨fun depth => BohmObservation.tree depth term,
    fun smaller larger hDepth => BohmObservation.tree_truncate smaller larger hDepth term⟩

theorem BohmObservation.family_eq_iff (term result : LambdaTerm) :
    BohmObservation.family term = BohmObservation.family result ↔
      ∀ depth, BohmObservation.tree depth term = BohmObservation.tree depth result := by
  constructor
  · intro h depth
    exact congrFun (congrArg Subtype.val h) depth
  · intro h
    apply Subtype.ext
    exact funext h

/-- Reduction preserves the actual coherent mathematical observation family. -/
theorem BohmObservation.family_reduction_eq {term result : LambdaTerm}
    (path : term ⇛* result) :
    BohmObservation.family term = BohmObservation.family result :=
  (BohmObservation.family_eq_iff term result).mpr
    (fun depth => BohmObservation.tree_reduction_eq path depth)

theorem BohmObservation.family_beta_eq (body argument : LambdaTerm) :
    BohmObservation.family (.app (.lam body) argument) =
      BohmObservation.family (argument.subst 0 body) :=
  BohmObservation.family_reduction_eq
    (Relation.ReflTransGen.single (beta_to_parRed body argument))

private theorem zero_observations (arguments : List LambdaTerm) :
    List.Forall₂ (BohmObservation 0) arguments (arguments.map (fun _ => BohmTree.bot)) := by
  induction arguments with
  | nil => exact .nil
  | cons head tail ih => exact .cons (BohmObservation.zero head) ih

/-- A successful depth-one evaluator observation agrees with the mathematical
observation. No deeper agreement is claimed: a successful parent may still
have argument searches that exhausted their budgets. -/
theorem BohmObservation.depth_one_of_search {term hnf : LambdaTerm}
    (search : toHNF 3 term = some hnf) :
    BohmObservation 1 term (bohmTree 1 term) := by
  obtain ⟨path, hHead⟩ := toHNF_sound search
  have hSome := (extractHNF_isSome_eq_isHNF hnf).trans hHead
  cases hExtract : extractHNF hnf with
  | none => simp only [hExtract, Option.isSome_none, Bool.false_eq_true] at hSome
  | some value =>
      rcases value with ⟨numLams, head, arguments⟩
      simp only [bohmTree, search, hExtract]
      exact .node path hExtract (zero_observations arguments)

end Mettapedia.GSLT.GraphTheory
