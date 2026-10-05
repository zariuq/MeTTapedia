import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConstructorView

/-!
# The binary trees of numbers: a second declared datatype

The binary trees of numbers have two constructors, `leaf : tree` and
`node : tree → num → tree → tree`: a constructor with no field, and one with two recursive fields
around a field of the numbers. The results for every simple datatype admissible over the object
package apply to them as instances, with nothing copied; they test that those results do not rest
on the shape of the lists.

* **The declaration** (`btreeDecl`) is admissible (`btreeDecl_admissible`), and its names avoid
  the names the value model keeps for itself (`btreeDecl_avoids`).
* **The reading.** The trees are the domain's declared datatype `btree` at the numbers
  (`dataTypeI_btreeDecl`). Negative: no closed equality `leaf ≡ node l a r` is derivable
  (`leaf_not_equal_node`), and positive: equal nodes have parts with equal readings
  (`node_equal_node_reads`), both instances of the results for every admissible datatype
  (`ctor_not_equal_ctor`, `ctor_equal_ctor_reads`).
* **A closed recursion: the mirror image** (`mirrorOf`), the recursor at the constant motive of
  the trees, `leaf` at a leaf, and at a node the node of the two mirrored subtrees exchanged. It is
  typed (`mirrorOf_typed`), through the type of its step over the motive
  (`mirrorStepType_eq`).
* **Adequacy**: every constant of the package with the trees is adequate, by
  `dataChurch_constAdequate`, so its fundamental lemma holds and its root steps of typed terms are
  equalities, by `dataRootAdmitted`.
* **Strong normalization**: the mirror image of a closed tree is strongly normalizing
  (`mirrorOneNode_sn`).
* **Computation.** The recursor at `node leaf 1 leaf` takes the rule of `node`, and five β-steps
  give the node of the two mirrored leaves around the number (`mirrorOneNode_red`).
* **Canonicity.** Positive: the mirror image of `node leaf 1 leaf` reduces, as an equality at the
  trees, to that node (`mirrorOneNode_canonical`); canonicity says it reaches some constructor
  form, and determinism of the steps says which. Negative: over a tree variable `x` the mirror
  image of `x` is typed and takes no step, and it reduces neither to `leaf` nor to a node: the
  recursor is stuck at the variable (`mirrorVar_not_canonical`).
* **The canonical head.** Positive: `node leaf 1 leaf` and its mirror image, a redex whose node
  has other fields, have the canonical head of `node` (`canonicalHead_oneNode`): the head forgets
  the fields and the timing. Negative: `leaf` and `node leaf 1 leaf` have different canonical
  heads (`canonicalHead_leaf_ne_oneNode`). The mirror of the mirror of `node leaf 1 leaf` selects
  the branch of `node` (`mirror_selects_node`).

**The three faces.** The trees add an instance to each face: the extensional one through the
reading that separates their constructors, the intensional one through the typing of the mirror
image, and the operational one through strong normalization, the computation of the mirror image
and its canonical form.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Presentation.TypedEquality.Impredicative.Domain.Ideal (projT natI ctorI)

namespace CodeModel

/-! ## The binary trees of numbers -/

/-- The type of the binary trees of numbers. -/
def btreeN : DeclName := .str .anonymous "btree"

/-- The empty tree. -/
def leafN : DeclName := .str .anonymous "leaf"

/-- A node: a left tree, a number and a right tree. -/
def nodeN : DeclName := .str .anonymous "node"

/-- The recursor of the trees. -/
def btreeRecN : DeclName := .str .anonymous "btree-rec"

/-- The constructors: `leaf`, and `node` of a tree, a number and a tree. -/
def btreeCtors : List (DeclName × List CtorField) :=
  [(leafN, []), (nodeN, [.recursive, .closed (.const numN), .recursive])]

/-- **The declaration of the binary trees of numbers.** -/
def btreeDecl : Datatype Tower.Head where
  type := btreeN
  typeUniverse := .sort Tower.zero
  ctors := btreeCtors
  recursor := btreeRecN
  motiveUniverse := listMotives

/-- **The declaration of the trees is admissible over the object package.** -/
theorem btreeDecl_admissible : btreeDecl.Admissible objectChurch where
  typeUniverse := LevelTower.IsUniverse.sort _
  motiveUniverse := LevelTower.IsUniverse.sort _
  distinct := {
    ctorsNodup := by decide
    typeNotCtor := by decide
    recNotType := by decide
    recNotCtor := by decide }
  new := {
    typeNew := by decide
    ctorsNew := by decide
    recNew := by decide }
  lamFree := by
    intro entry member F field
    have member' : entry ∈ btreeCtors := member
    simp only [btreeCtors, List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl
    · exact nomatch field
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      rcases field with impossible | same | impossible
      · exact nomatch impossible
      · obtain rfl : F = .const numN := by injection same
        rfl
      · exact nomatch impossible
  fields := by
    intro entry member F field
    have member' : entry ∈ btreeCtors := member
    simp only [btreeCtors, List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl
    · exact nomatch field
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      rcases field with impossible | same | impossible
      · exact nomatch impossible
      · obtain rfl : F = .const numN := by injection same
        exact cnum_typed
      · exact nomatch impossible

/-- The kind of `leaf`. -/
abbrev leafK : Kind := .ctor btreeN leafN []

/-- The kind of `node`: a tree, the datatype's parameter, a tree. -/
abbrev nodeK : Kind := .ctor btreeN nodeN [.self, .param 0, .self]

theorem dataParams_btreeDecl : dataParams btreeDecl = [natI] := by
  show [cinterp objectChurchReading (.const numN : CTm Tower.Head 0) Env.nil] = [natI]
  rw [cinterp_const, objectChurchReading_num]

/-- **The trees in the domain** are the declared datatype `btree` at the numbers. -/
theorem dataTypeI_btreeDecl : dataTypeI btreeDecl = ctorI (Kind.data btreeN) [natI] := by
  rw [dataTypeI, dataParams_btreeDecl]
  rfl

/-- The trees, `leaf` and `node`, as annotated terms. -/
abbrev cbtree {n : Nat} : CTm Tower.Head n := .const btreeN
abbrev cleaf {n : Nat} : CTm Tower.Head n := .const leafN
abbrev cnode {n : Nat} (l a r : CTm Tower.Head n) : CTm Tower.Head n :=
  CTm.appSpine (.const nodeN) [l, a, r]

/-- **Negative: a leaf is no node.** No closed equality `leaf ≡ node l a r` at the trees is
derivable: the instance of `ctor_not_equal_ctor` at the trees. -/
theorem leaf_not_equal_node (l a r : CTm Tower.Head 0) :
    ¬ CEqual (dataChurch btreeDecl) .nil cleaf (cnode l a r) cbtree :=
  ctor_not_equal_ctor btreeDecl_admissible (i := 0) (j := 1) rfl rfl (by decide) [] [l, a, r]

/-- **Positive: equal nodes have subtrees and numbers with equal readings**, the instance of
`ctor_equal_ctor_reads` at the trees. -/
theorem node_equal_node_reads {l a r l' a' r' : CTm Tower.Head 0}
    (h : CEqual (dataChurch btreeDecl) .nil (cnode l a r) (cnode l' a' r') cbtree) :
    [l, a, r].map (cinterp (dataReading btreeDecl) · Env.nil) =
      [l', a', r'].map (cinterp (dataReading btreeDecl) · Env.nil) :=
  ctor_equal_ctor_reads btreeDecl_admissible (i := 1) rfl h


/-! ## A closed recursion over the trees: the mirror image -/

section Mirror

variable {n : Nat} {Γ : CCtx Tower.Head n}

theorem btreeDecls_admissible : AdmissibleDeclarations objectChurch [.datatype btreeDecl] :=
  ⟨trivial, btreeDecl_admissible⟩

theorem btree_typed : CTyped (dataChurch btreeDecl) Γ cbtree cU0 :=
  btreeDecls_admissible.type_typed ConvRules.objectLevels List.mem_cons_self

theorem btree_typed_one : CTyped (dataChurch btreeDecl) Γ cbtree cU1 :=
  CDerivable.cumul btree_typed zero_le_one

theorem num_typed_one_btree : CTyped (dataChurch btreeDecl) Γ cnum cU1 :=
  CDerivable.cumul (CDerivable.withDeclarations _ cnum_typed) zero_le_one

theorem leaf_typed : CTyped (dataChurch btreeDecl) Γ cleaf cbtree :=
  btreeDecls_admissible.ctor_typed ConvRules.objectLevels List.mem_cons_self (i := 0) rfl

theorem nodeConst_typed : CTyped (dataChurch btreeDecl) Γ (.const nodeN)
    (.pi cbtree (.pi cnum (.pi cbtree cbtree))) :=
  btreeDecls_admissible.ctor_typed ConvRules.objectLevels List.mem_cons_self (i := 1) rfl

/-- **A node of two trees and a number is a tree.** -/
theorem node_typed {l a r : CTm Tower.Head n} (hl : CTyped (dataChurch btreeDecl) Γ l cbtree)
    (ha : CTyped (dataChurch btreeDecl) Γ a cnum) (hr : CTyped (dataChurch btreeDecl) Γ r cbtree) :
    CTyped (dataChurch btreeDecl) Γ (cnode l a r) cbtree :=
  .appElim (B := cbtree) (.appElim (B := .pi cbtree cbtree)
    (.appElim (B := .pi cnum (.pi cbtree cbtree)) nodeConst_typed hl) ha) hr

/-- A dependent function type between two types of one universe is a type of it. -/
theorem tpiT {D : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)} {l : LevelExpr Nat}
    (domain : CTyped (dataChurch btreeDecl) Γ D (CU l))
    (codomain : CTyped (dataChurch btreeDecl) (.snoc Γ D) B (CU l)) :
    CTyped (dataChurch btreeDecl) Γ (.pi D B) (CU l) :=
  CDerivable.cumul (.piForm domain (.sort l) codomain (.sort l) (.sorts l l))
    (fun valuation => by simp only [LevelExpr.eval, Nat.max_self, Nat.le_refl])

/-- The motive of the mirror image: every tree gives a tree. -/
abbrev mirrorMotive : CTm Tower.Head n := .lam cbtree cbtree

theorem motiveTypeT_formed : CTyped (dataChurch btreeDecl) Γ (.pi cbtree cU1) cU2 :=
  tpiT (CDerivable.cumul btree_typed zero_le_two)
    (.headType (LevelTower.HeadTyping.sort (.succ Tower.zero)))

theorem mirrorMotive_typed : CTyped (dataChurch btreeDecl) Γ mirrorMotive (.pi cbtree cU1) :=
  .lamIntro (u := LevelTower.Head.sort (.succ (.succ Tower.zero)))
    (w := LevelTower.Head.sort Tower.zero) btree_typed (LevelTower.IsUniverse.sort _)
    motiveTypeT_formed (LevelTower.IsUniverse.sort _) btree_typed_one

theorem mirrorMotive_at {t : CTm Tower.Head n} (ht : CTyped (dataChurch btreeDecl) Γ t cbtree) :
    CEqual (dataChurch btreeDecl) Γ (.app mirrorMotive t) cbtree cU1 :=
  .betaPi (A := cbtree) (B := cU1) (body := cbtree) (a := t)
    (u := LevelTower.Head.sort (.succ (.succ Tower.zero))) motiveTypeT_formed
    (LevelTower.IsUniverse.sort _) btree_typed_one ht

/-- The step of the mirror image: a node with its two mirrored subtrees exchanged. -/
abbrev mirrorStep : CTm Tower.Head n :=
  .lam cbtree (.lam cnum (.lam cbtree (.lam cbtree (.lam cbtree
    (cnode (.var 0) (.var 3) (.var 1))))))

/-- The type of a step of the recursor of the trees over the motive of the mirror image. -/
abbrev mirrorStepType : CTm Tower.Head n :=
  .pi cbtree (.pi cnum (.pi cbtree (.pi (.app mirrorMotive (.var 2))
    (.pi (.app mirrorMotive (.var 1)) (.app mirrorMotive (cnode (.var 4) (.var 3) (.var 2)))))))

theorem mirrorStep_plain : CTyped (dataChurch btreeDecl) Γ mirrorStep
    (.pi cbtree (.pi cnum (.pi cbtree (.pi cbtree (.pi cbtree cbtree))))) := by
  have t₅ : CTyped (dataChurch btreeDecl)
      (.snoc (.snoc (.snoc (.snoc Γ cbtree) cnum) cbtree) cbtree) (.pi cbtree cbtree) cU1 :=
    tpiT btree_typed_one btree_typed_one
  have t₄ : CTyped (dataChurch btreeDecl) (.snoc (.snoc (.snoc Γ cbtree) cnum) cbtree)
      (.pi cbtree (.pi cbtree cbtree)) cU1 := tpiT btree_typed_one t₅
  have t₃ : CTyped (dataChurch btreeDecl) (.snoc (.snoc Γ cbtree) cnum)
      (.pi cbtree (.pi cbtree (.pi cbtree cbtree))) cU1 := tpiT btree_typed_one t₄
  have t₂ : CTyped (dataChurch btreeDecl) (.snoc Γ cbtree)
      (.pi cnum (.pi cbtree (.pi cbtree (.pi cbtree cbtree)))) cU1 := tpiT num_typed_one_btree t₃
  have t₁ : CTyped (dataChurch btreeDecl) Γ
      (.pi cbtree (.pi cnum (.pi cbtree (.pi cbtree (.pi cbtree cbtree))))) cU1 :=
    tpiT btree_typed_one t₂
  exact .lamIntro btree_typed (LevelTower.IsUniverse.sort _) t₁ (LevelTower.IsUniverse.sort _)
    (.lamIntro (CDerivable.withDeclarations _ cnum_typed) (LevelTower.IsUniverse.sort _) t₂
      (LevelTower.IsUniverse.sort _)
      (.lamIntro btree_typed (LevelTower.IsUniverse.sort _) t₃ (LevelTower.IsUniverse.sort _)
        (.lamIntro btree_typed (LevelTower.IsUniverse.sort _) t₄ (LevelTower.IsUniverse.sort _)
          (.lamIntro btree_typed (LevelTower.IsUniverse.sort _) t₅
            (LevelTower.IsUniverse.sort _) (node_typed (.var 0) (.var 3) (.var 1))))))

/-- The plain type of the step is its type over the motive. -/
theorem mirrorStepType_eq :
    CEqual (dataChurch btreeDecl) Γ
      (.pi cbtree (.pi cnum (.pi cbtree (.pi cbtree (.pi cbtree cbtree))))) mirrorStepType
      (CU (.max (.succ Tower.zero) (.max (.succ Tower.zero) (.max (.succ Tower.zero)
        (.max (.succ Tower.zero) (.max (.succ Tower.zero) (.succ Tower.zero))))))) := by
  have atL : CEqual (dataChurch btreeDecl) (.snoc (.snoc (.snoc Γ cbtree) cnum) cbtree) cbtree
      (.app mirrorMotive (.var 2)) cU1 := .symm (mirrorMotive_at (.var 2))
  have atR : CEqual (dataChurch btreeDecl)
      (.snoc (.snoc (.snoc (.snoc Γ cbtree) cnum) cbtree) cbtree) cbtree
      (.app mirrorMotive (.var 1)) cU1 := .symm (mirrorMotive_at (.var 1))
  have atNode : CEqual (dataChurch btreeDecl)
      (.snoc (.snoc (.snoc (.snoc (.snoc Γ cbtree) cnum) cbtree) cbtree) cbtree) cbtree
      (.app mirrorMotive (cnode (.var 4) (.var 3) (.var 2))) cU1 :=
    .symm (mirrorMotive_at (node_typed (.var 4) (.var 3) (.var 2)))
  exact .piCong (.refl btree_typed_one) (LevelTower.IsUniverse.sort _)
    (.piCong (.refl num_typed_one_btree) (LevelTower.IsUniverse.sort _)
      (.piCong (.refl btree_typed_one) (LevelTower.IsUniverse.sort _)
        (.piCong atL (LevelTower.IsUniverse.sort _)
          (.piCong atR (LevelTower.IsUniverse.sort _) atNode (LevelTower.IsUniverse.sort _)
            (.sorts _ _))
          (LevelTower.IsUniverse.sort _) (.sorts _ _))
        (LevelTower.IsUniverse.sort _) (.sorts _ _))
      (LevelTower.IsUniverse.sort _) (.sorts _ _))
    (LevelTower.IsUniverse.sort _) (.sorts _ _)

theorem mirrorStep_typed : CTyped (dataChurch btreeDecl) Γ mirrorStep mirrorStepType :=
  .conv mirrorStep_plain mirrorStepType_eq (LevelTower.IsUniverse.sort _)

theorem mirrorLeaf_typed : CTyped (dataChurch btreeDecl) Γ cleaf (.app mirrorMotive cleaf) :=
  .conv leaf_typed (.symm (mirrorMotive_at leaf_typed)) (LevelTower.IsUniverse.sort _)

/-- **The mirror image of a tree**: the recursor of the trees at the constant motive of trees,
the leaf at a leaf, and a node with its mirrored subtrees exchanged. -/
abbrev mirrorOf (t : CTm Tower.Head n) : CTm Tower.Head n :=
  CTm.appSpine (.const btreeRecN) [mirrorMotive, cleaf, mirrorStep, t]

/-- **The mirror image of a tree is a tree.** -/
theorem mirrorOf_typed {t : CTm Tower.Head n} (ht : CTyped (dataChurch btreeDecl) Γ t cbtree) :
    CTyped (dataChurch btreeDecl) Γ (mirrorOf t) cbtree :=
  .conv
    (btreeDecls_admissible.rec_applied ConvRules.objectLevels List.mem_cons_self
      (σ := fun i => [t, mirrorStep, cleaf, mirrorMotive].getD i.val mirrorMotive)
      (fun j => match j with
        | ⟨0, _⟩ => ht
        | ⟨1, _⟩ => mirrorStep_typed
        | ⟨2, _⟩ => mirrorLeaf_typed
        | ⟨3, _⟩ => mirrorMotive_typed))
    (mirrorMotive_at ht) (LevelTower.IsUniverse.sort _)

end Mirror


/-! ## Adequacy at the trees -/

/-- Positive: the constants of the package with the trees are adequate, so its fundamental lemma
holds with no hypothesis. -/
example :
    ConstAdequate (dataExtension btreeDecl_admissible).reading (dataHead btreeDecl_admissible) :=
  dataChurch_constAdequate btreeDecl_admissible

/-- Positive: the root steps of typed terms of the package with the trees are equalities. -/
example : CRootAdmitted (dataChurch btreeDecl) := dataRootAdmitted btreeDecl_admissible

/-! ## Strong normalization and canonicity at the trees -/

section Canonicity

/-- The names of the trees avoid the names the value model keeps for itself. -/
theorem btreeDecl_avoids : AvoidsModelNames btreeDecl := by
  intro c mem
  simp only [dataNames, List.mem_cons, List.mem_map] at mem
  rcases mem with rfl | rfl | ⟨e, he, rfl⟩
  · decide
  · decide
  · simp only [btreeDecl, btreeCtors, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> decide

/-- The numeral one. -/
abbrev cone {n : Nat} : CTm Tower.Head n := csuc czero

theorem one_typed {n : Nat} {Γ : CCtx Tower.Head n} : CTyped (dataChurch btreeDecl) Γ cone cnum :=
  (dataExtension btreeDecl_admissible).csuc_typed
    ((dataExtension btreeDecl_admissible).lift czero_typed)

/-- The tree with one node, of the number one, between two leaves. -/
abbrev oneNode {n : Nat} : CTm Tower.Head n := cnode cleaf cone cleaf

theorem oneNode_typed {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped (dataChurch btreeDecl) Γ oneNode cbtree :=
  node_typed leaf_typed one_typed leaf_typed

/-- **Positive example: the mirror image of a closed tree is strongly normalizing.** -/
theorem mirrorOneNode_sn : SN (dataRules btreeDecl) (mirrorOf oneNode : CTm Tower.Head 0).erase :=
  (dataRules_sn btreeDecl_admissible btreeDecl_avoids .nil
    (CDerivable.erase (mirrorOf_typed (Γ := .nil) oneNode_typed))).1

/-- A weak-head step of the head of a spine is a step of the spine. -/
theorem headStep_appSpine {n : Nat} {f f' : CTm Tower.Head n}
    (step : (dataHead btreeDecl_admissible).step f f') :
    ∀ as : List (CTm Tower.Head n), (dataHead btreeDecl_admissible).step (CTm.appSpine f as)
      (CTm.appSpine f' as)
  | [] => step
  | a :: as => headStep_appSpine ((dataHead btreeDecl_admissible).appFun a step) as

/-- β at the head of a spine. -/
theorem headStep_beta {n : Nat} (A : CTm Tower.Head n) (body : CTm Tower.Head (n + 1))
    (a : CTm Tower.Head n) (as : List (CTm Tower.Head n)) :
    (dataHead btreeDecl_admissible).step (CTm.appSpine (.lam A body) (a :: as))
      (CTm.appSpine (CTm.inst0 a body) as) :=
  headStep_appSpine ((dataHead btreeDecl_admissible).beta A body a) as

/-- **The mirror image computes**: the recursor at `node leaf 1 leaf` takes the rule of `node`,
and the step of the mirror image exchanges the two mirrored leaves around the number. -/
theorem mirrorOneNode_red :
    Relation.ReflTransGen (dataHead btreeDecl_admissible).step (mirrorOf oneNode : CTm Tower.Head 0)
      (cnode (mirrorOf cleaf) cone (mirrorOf cleaf)) := by
  have iota : (dataHead btreeDecl_admissible).step (mirrorOf oneNode : CTm Tower.Head 0)
      (CTm.appSpine mirrorStep [cleaf, cone, cleaf, mirrorOf cleaf, mirrorOf cleaf]) :=
    (rec_ctor_step btreeDecl_admissible (pre := [mirrorMotive, cleaf, mirrorStep]) rfl
      (i := 1) rfl (args := [cleaf, cone, cleaf]) rfl _).2 rfl
  refine .head iota (.head (headStep_beta _ _ _ _) (.head (headStep_beta _ _ _ _)
    (.head (headStep_beta _ _ _ _) (.head (headStep_beta _ _ _ _)
      (.single (headStep_beta _ _ _ _))))))

/-- **Positive example of canonicity at the trees**: the mirror image of `node leaf 1 leaf`,
a closed recursion, reduces to the node of the two mirrored leaves around the number, an equality
at the trees. -/
theorem mirrorOneNode_canonical :
    CRedTm (dataHead btreeDecl_admissible) .nil (mirrorOf oneNode)
      (cnode (mirrorOf cleaf) cone (mirrorOf cleaf)) cbtree := by
  obtain ⟨i, k, fs, args, hi, length, -, red⟩ := data_canonical btreeDecl_admissible
    btreeDecl_avoids (mirrorOf_typed oneNode_typed)
  have same := (dataHead btreeDecl_admissible).nf_unique red.1 mirrorOneNode_red
    (ShowsCtor.normal btreeDecl_admissible ⟨k, fs, args, hi, length, rfl⟩)
    (ShowsCtor.normal btreeDecl_admissible (i := 1) ⟨nodeN, _, _, rfl, rfl, rfl⟩)
  rw [same] at red
  exact red

/-- The context of one tree. -/
abbrev cOneTree : CCtx Tower.Head 1 := .snoc .nil cbtree

/-- **Negative example: a stuck recursor at a variable.** Over a tree variable `x`, the mirror
image of `x` is typed at the trees, takes no step, and reduces neither to `leaf` nor to a node:
the recursor is stuck at the variable, so canonicity needs closed terms. -/
theorem mirrorVar_not_canonical :
    CTyped (dataChurch btreeDecl) cOneTree (mirrorOf (.var 0)) cbtree ∧
      (dataHead btreeDecl_admissible).Normal (mirrorOf (.var 0) : CTm Tower.Head 1) ∧
      ¬ CRedTm (dataHead btreeDecl_admissible) cOneTree (mirrorOf (.var 0)) cleaf cbtree ∧
      ∀ l a r, ¬ CRedTm (dataHead btreeDecl_admissible) cOneTree (mirrorOf (.var 0))
        (cnode l a r) cbtree := by
  have stuck := rec_var_stuck btreeDecl_admissible (pre := [mirrorMotive, cleaf, mirrorStep])
    rfl (0 : Fin 1)
  exact ⟨mirrorOf_typed (.var 0), stuck.1,
    fun h => stuck.2 0 ⟨_, h.1, leafN, [], [], rfl, rfl, rfl⟩,
    fun l a r h => stuck.2 1 ⟨_, h.1, nodeN, _, [l, a, r], rfl, rfl, rfl⟩⟩

end Canonicity

/-! ## The canonical head at the trees -/

section Heads

/-- The closed tree `node leaf 1 leaf`. -/
abbrev oneNodeAt : ClosedAt btreeDecl := ⟨oneNode, oneNode_typed⟩

/-- Its mirror image. -/
abbrev mirrorOneNodeAt : ClosedAt btreeDecl := ⟨mirrorOf oneNode, mirrorOf_typed oneNode_typed⟩

/-- The closed tree `leaf`. -/
abbrev leafAt : ClosedAt btreeDecl := ⟨cleaf, leaf_typed⟩

/-- **Positive: the canonical head forgets the fields and the timing.** `node leaf 1 leaf` and
its mirror image, a redex whose node has other fields, have the canonical head of `node`. -/
theorem canonicalHead_oneNode :
    canonicalHead btreeDecl_admissible btreeDecl_avoids oneNodeAt = ⟨1, by decide⟩ ∧
      canonicalHead btreeDecl_admissible btreeDecl_avoids mirrorOneNodeAt = ⟨1, by decide⟩ :=
  ⟨(canonicalHead_eq_iff _ _ _ _).2 ⟨_, .refl, nodeN, _, _, rfl, rfl, rfl⟩,
    (canonicalHead_eq_iff _ _ _ _).2 ⟨_, mirrorOneNode_red, nodeN, _, _, rfl, rfl, rfl⟩⟩

/-- **Negative: the canonical head keeps which branch.** `leaf` and `node leaf 1 leaf` have
different canonical heads. -/
theorem canonicalHead_leaf_ne_oneNode :
    canonicalHead btreeDecl_admissible btreeDecl_avoids leafAt ≠
      canonicalHead btreeDecl_admissible btreeDecl_avoids oneNodeAt := by
  rw [canonicalHead_oneNode.1,
    (canonicalHead_eq_iff _ _ _ ⟨0, by decide⟩).2 ⟨_, .refl, leafN, [], [], rfl, rfl, rfl⟩]
  decide

/-- **The mirror image of `node leaf 1 leaf` selects the branch of `node`**: the recursor at it
reduces to the step of the mirror image at the fields of its node. -/
theorem mirror_selects_node :
    Relation.ReflTransGen (dataHead btreeDecl_admissible).step
      (CTm.appSpine (.const btreeRecN) [mirrorMotive, cleaf, mirrorStep, mirrorOf oneNode] :
        CTm Tower.Head 0)
      (CTm.appSpine mirrorStep [mirrorOf cleaf, cone, mirrorOf cleaf, mirrorOf (mirrorOf cleaf),
        mirrorOf (mirrorOf cleaf)]) :=
  (dataHead_rec_red btreeDecl_admissible (pre := [mirrorMotive, cleaf, mirrorStep]) rfl
    mirrorOneNode_red).tail
    ((rec_ctor_step btreeDecl_admissible (pre := [mirrorMotive, cleaf, mirrorStep]) rfl
      (i := 1) rfl (args := [mirrorOf cleaf, cone, mirrorOf cleaf]) rfl _).2 rfl)

end Heads

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
