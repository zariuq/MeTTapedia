import Mettapedia.Logic.HOL.Embedding.ZFSetInductiveFunctions
import Mettapedia.Logic.HOL.Embedding.ZFSetListClosure

/-!
# Indexed well-founded trees in a closed universe

A tree signature names an index set, a shape set, the index a shape builds, the
positions of a shape, and the index wanted at each position. A node is a shape
paired with a function on its positions. The trees are the least family closed
under nodes. Each tree is coded by the function from finite lists of positions
to shapes, with a marker where the list leaves the tree, and the family is the
image of those codes.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetIndexedTrees

open ZFSetHenkinInterpretation ZFSetUniverseClosure ZFSetDependentProducts
open ZFSetIndexedClosure ZFSetList ZFSetTraceProducts ZFSetListClosure
open Mettapedia.SetTheory.ZFSetOrderedPair (first second first_pair second_pair)
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
  (numeral numeral_injective numeral_mem_omega numeral_succ mem_omega_iff natOf
    numeral_natOf natOf_numeral insert_mem_omega)
open ZFSetInductiveFunctions (graph_congr mem_tracePiSet_of_total total_of_mem_tracePiSet
  decode_encode_any finiteRankIndex_mem_of_omega numeral_mem_of_omega)
open scoped ZFSet
open Classical

universe u

/-! ## Signatures and nodes -/

/-- Indices, shapes, the index a shape builds, and the positions of a shape with
the index wanted at each position. -/
structure TreeSignature where
  index : ZFSet.{u}
  shape : ZFSet.{u}
  target : ZFSet.{u} → ZFSet.{u}
  target_mem : ∀ s, s ∈ shape → target s ∈ index
  pos : ZFSet.{u} → ZFSet.{u}
  next : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
  next_mem : ∀ s p, s ∈ shape → p ∈ pos s → next s p ∈ index

/-- A node is an ordered pair of a shape and a function on its positions. -/
def node (s f : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair s f

theorem node_inj {s f s' f' : ZFSet.{u}} (h : node s f = node s' f') :
    s = s' ∧ f = f' :=
  ZFSet.pair_inj.mp h

theorem shapeOf_node (s f : ZFSet.{u}) : first (node s f) = s :=
  first_pair s f

/-- `InTree sig i t` says `t` is a tree of index `i`: a node whose function
sends each position to a tree of the index that position wants. -/
inductive InTree (sig : TreeSignature.{u}) : ZFSet.{u} → ZFSet.{u} → Prop where
  | intro (s f : ZFSet.{u})
      (hs : s ∈ sig.shape)
      (total : f = traceLam (graph (sig.pos s) (fun p => traceApp f p)))
      (values : ∀ p, p ∈ sig.pos s → InTree sig (sig.next s p) (traceApp f p)) :
      InTree sig (sig.target s) (node s f)

/-! ## The immediate-subtree order -/

def Immediate (sig : TreeSignature.{u}) (y x : ZFSet.{u}) : Prop :=
  ∃ s f p, x = node s f ∧ s ∈ sig.shape ∧
    f = traceLam (graph (sig.pos s) (fun q => traceApp f q)) ∧
    p ∈ sig.pos s ∧ y = traceApp f p ∧ InTree sig (sig.next s p) y

theorem child_immediate (sig : TreeSignature.{u}) {s f p : ZFSet.{u}}
    (hs : s ∈ sig.shape)
    (total : f = traceLam (graph (sig.pos s) (fun q => traceApp f q)))
    (values : ∀ q, q ∈ sig.pos s → InTree sig (sig.next s q) (traceApp f q))
    (hp : p ∈ sig.pos s) :
    Immediate sig (traceApp f p) (node s f) :=
  ⟨s, f, p, rfl, hs, total, hp, rfl, values p hp⟩

theorem immediate_inTree (sig : TreeSignature.{u}) {y x : ZFSet.{u}}
    (hy : Immediate sig y x) : ∃ i, InTree sig i y := by
  rcases hy with ⟨_, _, _, _, _, _, _, rfl, hy⟩
  exact ⟨_, hy⟩

theorem inTree_acc (sig : TreeSignature.{u}) {i t : ZFSet.{u}}
    (ht : InTree sig i t) : Acc (Immediate sig) t :=
  InTree.rec (motive := fun _ t _ => Acc (Immediate sig) t)
    (fun s f hs total values ih =>
      Acc.intro (node s f) (fun y hy => by
        rcases hy with ⟨_s', _f', p, heq, _, _, hp, rfl, _⟩
        obtain ⟨rfl, rfl⟩ := node_inj heq
        exact ih p hp))
    ht

theorem immediate_wf (sig : TreeSignature.{u}) : WellFounded (Immediate sig) :=
  ⟨fun x => Acc.intro x (fun _ hy => inTree_acc sig (immediate_inTree sig hy).choose_spec)⟩

/-! ## Recursion along immediate subtrees -/

noncomputable section

noncomputable def totalize (sig : TreeSignature.{u}) (x : ZFSet.{u})
    (ih : ∀ y, Immediate sig y x → ZFSet.{u}) (y : ZFSet.{u}) : ZFSet.{u} :=
  @dite _ (Immediate sig y x) (Classical.propDecidable _) (fun h => ih y h) (fun _ => ∅)

theorem totalize_immediate (sig : TreeSignature.{u}) {x y : ZFSet.{u}}
    (ih : ∀ z, Immediate sig z x → ZFSet.{u}) (h : Immediate sig y x) :
    totalize sig x ih y = ih y h := by
  unfold totalize
  rw [dif_pos h]

noncomputable def recBody (sig : TreeSignature.{u})
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (x : ZFSet.{u}) (ih : ∀ y, Immediate sig y x → ZFSet.{u}) : ZFSet.{u} :=
  @Classical.epsilon ZFSet.{u} ⟨∅⟩ fun result =>
    ∀ s f, node s f = x → s ∈ sig.shape →
      f = traceLam (graph (sig.pos s) (fun p => traceApp f p)) →
      (∀ p, p ∈ sig.pos s → InTree sig (sig.next s p) (traceApp f p)) →
      result = step s f (traceLam (graph (sig.pos s) (fun p =>
        totalize sig x ih (traceApp f p))))

noncomputable def recFun (sig : TreeSignature.{u})
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) : ZFSet.{u} :=
  WellFounded.fix (immediate_wf sig) (fun x ih => recBody sig step x ih) x

theorem recFun_unfold (sig : TreeSignature.{u})
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) :
    recFun sig step x = recBody sig step x (fun y _ => recFun sig step y) := by
  unfold recFun
  exact WellFounded.fix_eq (immediate_wf sig) (fun x ih => recBody sig step x ih) x

theorem recFun_node (sig : TreeSignature.{u})
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {s f : ZFSet.{u}} (hs : s ∈ sig.shape)
    (total : f = traceLam (graph (sig.pos s) (fun p => traceApp f p)))
    (values : ∀ p, p ∈ sig.pos s → InTree sig (sig.next s p) (traceApp f p)) :
    recFun sig step (node s f) =
      step s f (traceLam (graph (sig.pos s) (fun p => recFun sig step (traceApp f p)))) := by
  rw [recFun_unfold]
  let pred : ZFSet.{u} → Prop := fun result =>
    ∀ s' f', node s' f' = node s f → s' ∈ sig.shape →
      f' = traceLam (graph (sig.pos s') (fun p => traceApp f' p)) →
      (∀ p, p ∈ sig.pos s' → InTree sig (sig.next s' p) (traceApp f' p)) →
      result = step s' f' (traceLam (graph (sig.pos s') (fun p =>
        totalize sig (node s f) (fun y _ => recFun sig step y) (traceApp f' p))))
  have existsValue : ∃ result, pred result := by
    refine ⟨step s f (traceLam (graph (sig.pos s) (fun p =>
      totalize sig (node s f) (fun y _ => recFun sig step y) (traceApp f p)))), ?_⟩
    intro _s' _f' heq _ _ _
    obtain ⟨rfl, rfl⟩ := node_inj heq
    rfl
  have spec := Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩ pred existsValue
  have applied := spec s f rfl hs total values
  unfold recBody
  rw [applied]
  apply congrArg (step s f)
  apply congrArg traceLam
  apply graph_congr
  intro p hp
  exact totalize_immediate sig (fun y _ => recFun sig step y)
    (child_immediate sig hs total values hp)

theorem recFun_unique (sig : TreeSignature.{u})
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (g : ZFSet.{u} → ZFSet.{u})
    (equations : ∀ {s f : ZFSet.{u}}, s ∈ sig.shape →
      f = traceLam (graph (sig.pos s) (fun p => traceApp f p)) →
      (∀ p, p ∈ sig.pos s → InTree sig (sig.next s p) (traceApp f p)) →
      g (node s f) = step s f (traceLam (graph (sig.pos s) (fun p => g (traceApp f p)))))
    {i t : ZFSet.{u}} (ht : InTree sig i t) : g t = recFun sig step t :=
  InTree.rec (motive := fun _ t _ => g t = recFun sig step t)
    (fun s f hs total values ih => by
      rw [equations hs total values, recFun_node sig step hs total values]
      apply congrArg (step s f)
      apply congrArg traceLam
      apply graph_congr
      intro p hp
      exact ih p hp)
    ht

/-! ## Path codes -/

noncomputable def positionSet (sig : TreeSignature.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (replacement sig.shape sig.pos)

theorem pos_mem_positionSet (sig : TreeSignature.{u}) {s p : ZFSet.{u}}
    (hs : s ∈ sig.shape) (hp : p ∈ sig.pos s) : p ∈ positionSet sig :=
  ZFSet.mem_sUnion.mpr ⟨sig.pos s, mem_replacement.mpr ⟨s, hs, rfl⟩, hp⟩

noncomputable def paths (sig : TreeSignature.{u}) : ZFSet.{u} :=
  listCode (positionSet sig)

def absentMark : ZFSet.{u} := ZFSet.pair (numeral 0) ∅

def shapeMark (s : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair (numeral 1) s

theorem shapeMark_inj {s s' : ZFSet.{u}} (h : shapeMark s = shapeMark s') : s = s' :=
  (ZFSet.pair_inj.mp h).2

theorem numeral_one_ne_zero : numeral (1 : Nat) ≠ numeral (0 : Nat) :=
  numeral_injective.ne (Nat.succ_ne_zero 0)

theorem absent_ne_shape (s : ZFSet.{u}) : absentMark ≠ shapeMark s := by
  intro h
  exact numeral_one_ne_zero (ZFSet.pair_inj.mp h).1.symm

noncomputable def labelSet (sig : TreeSignature.{u}) : ZFSet.{u} :=
  ({absentMark} : ZFSet.{u}) ∪ replacement sig.shape shapeMark

theorem absentMark_mem (sig : TreeSignature.{u}) : absentMark ∈ labelSet sig :=
  ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_singleton.mpr rfl))

theorem shapeMark_mem (sig : TreeSignature.{u}) {s : ZFSet.{u}} (hs : s ∈ sig.shape) :
    shapeMark s ∈ labelSet sig :=
  ZFSet.mem_union.mpr (Or.inr (mem_replacement.mpr ⟨s, hs, rfl⟩))

noncomputable def labelsOf (sig : TreeSignature.{u}) (s sub : ZFSet.{u}) :
    List (Elements (positionSet sig)) → ZFSet.{u}
  | [] => shapeMark s
  | ⟨p, _⟩ :: rest =>
      @dite _ (p ∈ sig.pos s) (Classical.propDecidable _)
        (fun _ => traceApp (traceApp sub p) (encode rest)) (fun _ => absentMark)

theorem labelsOf_nil (sig : TreeSignature.{u}) (s sub : ZFSet.{u}) :
    labelsOf sig s sub [] = shapeMark s := rfl

theorem labelsOf_pos (sig : TreeSignature.{u}) (s sub : ZFSet.{u})
    {p : ZFSet.{u}} (hp : p ∈ sig.pos s) (hpos : p ∈ positionSet sig)
    (xs : List (Elements (positionSet sig))) :
    labelsOf sig s sub (⟨p, hpos⟩ :: xs) =
      traceApp (traceApp sub p) (encode xs) := by
  conv_lhs => simp only [labelsOf]
  rw [dif_pos hp]

theorem labelsOf_neg (sig : TreeSignature.{u}) (s sub : ZFSet.{u})
    {p : ZFSet.{u}} (hp : p ∉ sig.pos s) (hpos : p ∈ positionSet sig)
    (xs : List (Elements (positionSet sig))) :
    labelsOf sig s sub (⟨p, hpos⟩ :: xs) = absentMark := by
  conv_lhs => simp only [labelsOf]
  rw [dif_neg hp]

noncomputable def labelAt (sig : TreeSignature.{u}) (s sub path : ZFSet.{u}) : ZFSet.{u} :=
  @dite _ (path ∈ paths sig) (Classical.propDecidable _)
    (fun hp => labelsOf sig s sub (decode ⟨path, hp⟩)) (fun _ => absentMark)

theorem labelAt_encode (sig : TreeSignature.{u}) (s sub : ZFSet.{u})
    (xs : List (Elements (positionSet sig))) :
    labelAt sig s sub (encode xs) = labelsOf sig s sub xs := by
  have hp : encode xs ∈ paths sig := ZFSet.mem_range_self xs
  unfold labelAt
  rw [dif_pos hp, decode_encode_any xs hp]

noncomputable def assembled (sig : TreeSignature.{u}) (s sub : ZFSet.{u}) : ZFSet.{u} :=
  traceLam (graph (paths sig) (fun path => labelAt sig s sub path))

theorem traceApp_assembled (sig : TreeSignature.{u}) {s sub q : ZFSet.{u}}
    (hq : q ∈ paths sig) :
    traceApp (assembled sig s sub) q = labelAt sig s sub q :=
  traceApp_graph_beta (fun path => labelAt sig s sub path) hq

noncomputable def assembleStep (sig : TreeSignature.{u})
    (s _f results : ZFSet.{u}) : ZFSet.{u} :=
  assembled sig s results

noncomputable def codeOf (sig : TreeSignature.{u}) (x : ZFSet.{u}) : ZFSet.{u} :=
  recFun sig (assembleStep sig) x

theorem codeOf_node (sig : TreeSignature.{u}) {s f : ZFSet.{u}}
    (hs : s ∈ sig.shape)
    (total : f = traceLam (graph (sig.pos s) (fun p => traceApp f p)))
    (values : ∀ p, p ∈ sig.pos s → InTree sig (sig.next s p) (traceApp f p)) :
    codeOf sig (node s f) =
      assembled sig s (traceLam (graph (sig.pos s) (fun p => codeOf sig (traceApp f p)))) := by
  rw [codeOf, recFun_node sig (assembleStep sig) hs total values]
  rfl

theorem code_root (sig : TreeSignature.{u}) {s f : ZFSet.{u}}
    (hs : s ∈ sig.shape)
    (total : f = traceLam (graph (sig.pos s) (fun p => traceApp f p)))
    (values : ∀ p, p ∈ sig.pos s → InTree sig (sig.next s p) (traceApp f p)) :
    traceApp (codeOf sig (node s f)) (encode (a := positionSet sig) []) = shapeMark s := by
  rw [codeOf_node sig hs total values, traceApp_assembled sig (ZFSet.mem_range_self []),
    labelAt_encode, labelsOf_nil]

theorem code_shift (sig : TreeSignature.{u}) {s f p : ZFSet.{u}}
    (hs : s ∈ sig.shape)
    (total : f = traceLam (graph (sig.pos s) (fun q => traceApp f q)))
    (values : ∀ q, q ∈ sig.pos s → InTree sig (sig.next s q) (traceApp f q))
    (hp : p ∈ sig.pos s) (xs : List (Elements (positionSet sig))) :
    traceApp (codeOf sig (node s f))
        (encode (⟨p, pos_mem_positionSet sig hs hp⟩ :: xs)) =
      traceApp (codeOf sig (traceApp f p)) (encode xs) := by
  rw [codeOf_node sig hs total values,
    traceApp_assembled sig (ZFSet.mem_range_self (⟨p, pos_mem_positionSet sig hs hp⟩ :: xs)),
    labelAt_encode, labelsOf_pos sig s _ hp (pos_mem_positionSet sig hs hp)]
  rw [traceApp_graph_beta (fun q => codeOf sig (traceApp f q)) hp]

theorem code_eta (sig : TreeSignature.{u}) {i t : ZFSet.{u}} (ht : InTree sig i t) :
    codeOf sig t =
      traceLam (graph (paths sig) (fun q => traceApp (codeOf sig t) q)) := by
  cases ht with
  | intro s f hs total values =>
      rw [codeOf_node sig hs total values]
      apply congrArg traceLam
      apply graph_congr
      intro q hq
      exact (traceApp_assembled sig hq).symm

noncomputable def codeSpace (sig : TreeSignature.{u}) : ZFSet.{u} :=
  tracePiSet (paths sig) (fun _ => labelSet sig)

theorem labelAt_mem (sig : TreeSignature.{u}) {s sub : ZFSet.{u}}
    (hs : s ∈ sig.shape)
    (subMem : ∀ p, p ∈ sig.pos s → traceApp sub p ∈ codeSpace sig)
    {q : ZFSet.{u}} (hq : q ∈ paths sig) : labelAt sig s sub q ∈ labelSet sig := by
  unfold labelAt
  rw [dif_pos hq]
  cases decode ⟨q, hq⟩ with
  | nil =>
      exact shapeMark_mem sig hs
  | cons head rest =>
      rcases head with ⟨p, hpos⟩
      cases Classical.propDecidable (p ∈ sig.pos s) with
      | isTrue hp =>
          rw [labelsOf_pos sig s sub hp hpos]
          have hcode : traceApp sub p ∈ codeSpace sig := subMem p hp
          exact traceApp_mem (b := fun _ => labelSet sig) ⟨traceApp sub p, hcode⟩
            ⟨encode rest, ZFSet.mem_range_self rest⟩
      | isFalse hp =>
          rw [labelsOf_neg sig s sub hp hpos]
          exact absentMark_mem sig

theorem codeOf_mem_codeSpace (sig : TreeSignature.{u}) {i t : ZFSet.{u}}
    (ht : InTree sig i t) : codeOf sig t ∈ codeSpace sig :=
  InTree.rec (motive := fun _ t _ => codeOf sig t ∈ codeSpace sig)
    (fun s f hs total values ih => by
      have hsub : ∀ p, p ∈ sig.pos s →
          traceApp (traceLam (graph (sig.pos s) (fun q => codeOf sig (traceApp f q)))) p ∈
            codeSpace sig := by
        intro p hp
        rw [traceApp_graph_beta (fun q => codeOf sig (traceApp f q)) hp]
        exact ih p hp
      rw [codeOf_node sig hs total values]
      apply mem_tracePiSet_of_total
      · apply congrArg traceLam
        apply graph_congr
        intro q hq
        exact (traceApp_assembled sig hq).symm
      · intro q hq
        rw [traceApp_assembled sig hq]
        exact labelAt_mem sig hs hsub hq)
    ht

theorem codeOf_injective (sig : TreeSignature.{u}) {i x : ZFSet.{u}}
    (hx : InTree sig i x) : ∀ {j y}, InTree sig j y → codeOf sig x = codeOf sig y → x = y :=
  InTree.rec
    (motive := fun _ x _ => ∀ {j y}, InTree sig j y → codeOf sig x = codeOf sig y → x = y)
    (fun s f hs total values ih {j y} hy hcode => by
      cases hy with
      | intro s' f' hs' total' values' =>
          have hroot : shapeMark s = shapeMark s' := by
            have happ := congrArg
              (fun c => traceApp c (encode (a := positionSet sig) [])) hcode
            rw [code_root sig hs total values, code_root sig hs' total' values'] at happ
            exact happ
          have hsEq : s = s' := shapeMark_inj hroot
          cases hsEq
          have hchild : ∀ p, p ∈ sig.pos s → traceApp f p = traceApp f' p := by
            intro p hp
            exact ih p hp (values' p hp) (by
              rw [code_eta sig (values p hp), code_eta sig (values' p hp)]
              apply congrArg traceLam
              apply graph_congr
              intro q hq
              obtain ⟨xs, rfl⟩ := mem_listCode.mp hq
              rw [← code_shift sig hs total values hp xs,
                ← code_shift sig hs' total' values' hp xs, hcode])
          rw [total, total']
          apply congrArg (node s)
          apply congrArg traceLam
          apply graph_congr
          exact hchild)
    hx

/-! ## The family, as the image of the codes -/

noncomputable def codeSet (sig : TreeSignature.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun c => ∃ x i, InTree sig i x ∧ codeOf sig x = c) (codeSpace sig)

noncomputable def decodeTarget (sig : TreeSignature.{u}) (c : ZFSet.{u}) : ZFSet.{u} :=
  @Classical.epsilon ZFSet.{u} ⟨∅⟩ (fun x => ∃ i, InTree sig i x ∧ codeOf sig x = c)

noncomputable def allTrees (sig : TreeSignature.{u}) : ZFSet.{u} :=
  replacement (codeSet sig) (decodeTarget sig)

theorem decodeTarget_codeOf (sig : TreeSignature.{u}) {i x : ZFSet.{u}}
    (hx : InTree sig i x) : decodeTarget sig (codeOf sig x) = x := by
  have existsValue : ∃ y, ∃ j, InTree sig j y ∧ codeOf sig y = codeOf sig x :=
    ⟨x, i, hx, rfl⟩
  have spec := Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩
    (fun y => ∃ j, InTree sig j y ∧ codeOf sig y = codeOf sig x) existsValue
  obtain ⟨j, hy, hcode⟩ := spec
  exact codeOf_injective sig hy hx hcode

theorem codeOf_mem_codeSet (sig : TreeSignature.{u}) {i x : ZFSet.{u}}
    (hx : InTree sig i x) : codeOf sig x ∈ codeSet sig :=
  ZFSet.mem_sep.mpr ⟨codeOf_mem_codeSpace sig hx, ⟨x, ⟨i, ⟨hx, rfl⟩⟩⟩⟩

theorem mem_allTrees_of_inTree (sig : TreeSignature.{u}) {i x : ZFSet.{u}}
    (hx : InTree sig i x) : x ∈ allTrees sig :=
  mem_replacement.mpr ⟨codeOf sig x, codeOf_mem_codeSet sig hx, decodeTarget_codeOf sig hx⟩

theorem inTree_of_mem_allTrees (sig : TreeSignature.{u}) {x : ZFSet.{u}}
    (hx : x ∈ allTrees sig) : ∃ i, InTree sig i x := by
  obtain ⟨c, hc, rfl⟩ := mem_replacement.mp hx
  obtain ⟨_, hex⟩ := ZFSet.mem_sep.mp hc
  have spec := Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩
    (fun y => ∃ i, InTree sig i y ∧ codeOf sig y = c) hex
  obtain ⟨i, hi, _⟩ := spec
  exact ⟨i, hi⟩

noncomputable def trees (sig : TreeSignature.{u}) (i : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun t => sig.target (first t) = i) (allTrees sig)

theorem index_of_inTree (sig : TreeSignature.{u}) {i t : ZFSet.{u}}
    (ht : InTree sig i t) : sig.target (first t) = i := by
  cases ht with
  | intro s f hs _ _ =>
      rw [shapeOf_node]

theorem mem_trees_of_inTree (sig : TreeSignature.{u}) {i t : ZFSet.{u}}
    (ht : InTree sig i t) : t ∈ trees sig i :=
  ZFSet.mem_sep.mpr ⟨mem_allTrees_of_inTree sig ht, index_of_inTree sig ht⟩

theorem inTree_of_mem_trees (sig : TreeSignature.{u}) {i t : ZFSet.{u}}
    (ht : t ∈ trees sig i) : InTree sig i t := by
  obtain ⟨hall, hindex⟩ := ZFSet.mem_sep.mp ht
  obtain ⟨j, hj⟩ := inTree_of_mem_allTrees sig hall
  have hidx : j = i := (index_of_inTree sig hj).symm.trans hindex
  cases hidx
  exact hj

theorem mem_trees_iff (sig : TreeSignature.{u}) {i t : ZFSet.{u}} :
    t ∈ trees sig i ↔ InTree sig i t :=
  ⟨inTree_of_mem_trees sig, mem_trees_of_inTree sig⟩

/-! ## Dependent trace families

Task 14's trace-product lemmas fix one codomain. A position here asks for a
tree at its own index, so the family depends on the argument. -/

theorem total_of_mem_tracePiFamily {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    {f : ZFSet.{u}} (hf : f ∈ tracePiSet A B) :
    f = traceLam (graph A (fun a => traceApp f a)) ∧ ∀ a, a ∈ A → traceApp f a ∈ B a := by
  refine ⟨?_, fun a ha => traceApp_mem ⟨f, hf⟩ ⟨a, ha⟩⟩
  have same : (⟨f, hf⟩ : Elements (tracePiSet A B)) =
      traceEncode (traceValue ⟨f, hf⟩) := (trace_eta _).symm
  have hfEq : f = (traceEncode (traceValue ⟨f, hf⟩)).1 := congrArg Subtype.val same
  have body : (traceEncode (traceValue ⟨f, hf⟩)).1 =
      traceLam (graph A (extendFunction (traceValue ⟨f, hf⟩))) := rfl
  rw [hfEq, body]
  apply congrArg traceLam
  apply graph_congr
  intro a ha
  rw [traceApp_graph_beta (extendFunction (traceValue ⟨f, hf⟩)) ha]

theorem mem_tracePiFamily_of_total {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    {f : ZFSet.{u}} (total : f = traceLam (graph A (fun a => traceApp f a)))
    (values : ∀ a, a ∈ A → traceApp f a ∈ B a) : f ∈ tracePiSet A B := by
  have hg : graph A (fun a => traceApp f a) ∈ piSet A B := graph_mem_piSet values
  exact total ▸ mem_tracePiSet.mpr ⟨graph A (fun a => traceApp f a), hg, rfl⟩

/-! ## Closure, leastness, induction, inversion, recursion -/

theorem trees_closed (sig : TreeSignature.{u}) {s f : ZFSet.{u}}
    (hs : s ∈ sig.shape)
    (hf : f ∈ tracePiSet (sig.pos s) (fun p => trees sig (sig.next s p))) :
    node s f ∈ trees sig (sig.target s) := by
  obtain ⟨total, values⟩ := total_of_mem_tracePiFamily hf
  exact mem_trees_of_inTree sig
    (InTree.intro s f hs total (fun p hp => inTree_of_mem_trees sig (values p hp)))

theorem trees_least (sig : TreeSignature.{u}) {X : ZFSet.{u} → ZFSet.{u}}
    (closedX : ∀ {s f : ZFSet.{u}}, s ∈ sig.shape →
      f ∈ tracePiSet (sig.pos s) (fun p => X (sig.next s p)) →
      node s f ∈ X (sig.target s))
    (i : ZFSet.{u}) : trees sig i ⊆ X i := by
  intro t ht
  exact InTree.rec (motive := fun j y _ => y ∈ X j)
    (fun s f hs total _ ih => by
      have hf : f ∈ tracePiSet (sig.pos s) (fun p => X (sig.next s p)) :=
        mem_tracePiFamily_of_total total ih
      exact closedX hs hf)
    (inTree_of_mem_trees sig ht)

theorem trees_induct (sig : TreeSignature.{u}) {P : ZFSet.{u} → Prop}
    (step : ∀ {s f : ZFSet.{u}}, s ∈ sig.shape →
      f ∈ tracePiSet (sig.pos s) (fun p => trees sig (sig.next s p)) →
      (∀ p, p ∈ sig.pos s → P (traceApp f p)) → P (node s f))
    {i t : ZFSet.{u}} (ht : t ∈ trees sig i) : P t :=
  InTree.rec (motive := fun _ y _ => P y)
    (fun s f hs total values ih =>
      step (s := s) (f := f) hs
        (mem_tracePiFamily_of_total total (fun p hp => mem_trees_of_inTree sig (values p hp)))
        ih)
    (inTree_of_mem_trees sig ht)

theorem exists_inversion (sig : TreeSignature.{u}) {i t : ZFSet.{u}}
    (ht : t ∈ trees sig i) :
    ∃ s f, s ∈ sig.shape ∧ sig.target s = i ∧
      f ∈ tracePiSet (sig.pos s) (fun p => trees sig (sig.next s p)) ∧ t = node s f := by
  have ht' := inTree_of_mem_trees sig ht
  cases ht' with
  | intro s f hs total values =>
      exact ⟨s, f, hs, rfl,
        mem_tracePiFamily_of_total total (fun p hp => mem_trees_of_inTree sig (values p hp)), rfl⟩

theorem inversion_unique {s f s' f' : ZFSet.{u}} (h : node s f = node s' f') :
    s = s' ∧ f = f' :=
  node_inj h

theorem recursion_node (sig : TreeSignature.{u})
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    {s f : ZFSet.{u}} (hs : s ∈ sig.shape)
    (hf : f ∈ tracePiSet (sig.pos s) (fun p => trees sig (sig.next s p))) :
    recFun sig step (node s f) =
      step s f (traceLam (graph (sig.pos s) (fun p => recFun sig step (traceApp f p)))) := by
  obtain ⟨total, values⟩ := total_of_mem_tracePiFamily hf
  exact recFun_node sig step hs total (fun p hp => inTree_of_mem_trees sig (values p hp))

theorem recursion_unique (sig : TreeSignature.{u})
    (step : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (g : ZFSet.{u} → ZFSet.{u})
    (equations : ∀ {s f : ZFSet.{u}}, s ∈ sig.shape →
      f ∈ tracePiSet (sig.pos s) (fun p => trees sig (sig.next s p)) →
      g (node s f) = step s f (traceLam (graph (sig.pos s) (fun p => g (traceApp f p)))))
    {i t : ZFSet.{u}} (ht : t ∈ trees sig i) : g t = recFun sig step t :=
  recFun_unique sig step g
    (fun hs total values => equations hs
      (mem_tracePiFamily_of_total total (fun p hp => mem_trees_of_inTree sig (values p hp))))
    (inTree_of_mem_trees sig ht)

/-- An index that no shape builds has no tree. -/
theorem trees_empty_of_target (sig : TreeSignature.{u}) {i : ZFSet.{u}}
    (h : ∀ s, s ∈ sig.shape → sig.target s ≠ i) : trees sig i = ∅ := by
  apply ZFSet.ext
  intro t
  constructor
  · intro ht
    obtain ⟨s, _, hs, htarget, _, _⟩ := exists_inversion sig ht
    exact False.elim (h s hs htarget)
  · intro ht
    exact False.elim (ZFSet.notMem_empty t ht)

/-! ## Membership in a closed universe -/

theorem positionSet_mem {sig : TreeSignature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (hS : sig.shape ∈ U) (hpos : ∀ s, s ∈ sig.shape → sig.pos s ∈ U) :
    positionSet sig ∈ U :=
  closed.union_mem (closed.replacement_mem hS sig.pos hpos)

theorem paths_mem {sig : TreeSignature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U) (hS : sig.shape ∈ U)
    (hpos : ∀ s, s ∈ sig.shape → sig.pos s ∈ U) : paths sig ∈ U :=
  listCode_mem closed (positionSet_mem closed hS hpos)
    (finiteRankIndex_mem_of_omega closed omega)

theorem labelSet_mem {sig : TreeSignature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U) (hS : sig.shape ∈ U) : labelSet sig ∈ U := by
  unfold labelSet absentMark shapeMark
  apply closed.binaryUnion_mem
  · exact closed.singleton_mem (closed.pair_mem
      (numeral_mem_of_omega closed omega 0) (closed.empty_mem omega))
  · exact closed.replacement_mem hS (fun s => ZFSet.pair (numeral 1) s) (fun s hs =>
      closed.pair_mem (numeral_mem_of_omega closed omega 1) (closed.transitive _ hS hs))

theorem codeSpace_mem {sig : TreeSignature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U) (hS : sig.shape ∈ U)
    (hpos : ∀ s, s ∈ sig.shape → sig.pos s ∈ U) : codeSpace sig ∈ U :=
  closed.tracePiSet_mem (paths_mem closed omega hS hpos) (fun _ => labelSet sig)
    (fun _ _ => labelSet_mem closed omega hS)

theorem inTree_mem {sig : TreeSignature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (hS : sig.shape ∈ U) (hpos : ∀ s, s ∈ sig.shape → sig.pos s ∈ U)
    {i t : ZFSet.{u}} (ht : InTree sig i t) : t ∈ U :=
  InTree.rec (motive := fun _ t _ => t ∈ U)
    (fun s f hs total _ ih => by
      rw [total]
      exact closed.pair_mem (closed.transitive _ hS hs) (closed.traceLam_mem (by
        rw [graph]
        exact closed.replacement_mem (hpos s hs) (fun p => ZFSet.pair p (traceApp f p))
          (fun p hp => closed.pair_mem (closed.transitive _ (hpos s hs) hp) (ih p hp)))))
    ht

theorem decodeTarget_mem {sig : TreeSignature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (hS : sig.shape ∈ U) (hpos : ∀ s, s ∈ sig.shape → sig.pos s ∈ U)
    {c : ZFSet.{u}} (hc : c ∈ codeSet sig) : decodeTarget sig c ∈ U := by
  obtain ⟨_, hex⟩ := ZFSet.mem_sep.mp hc
  have spec := Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩
    (fun x => ∃ i, InTree sig i x ∧ codeOf sig x = c) hex
  obtain ⟨_, hi, _⟩ := spec
  exact inTree_mem closed hS hpos hi

theorem allTrees_mem {sig : TreeSignature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U) (hS : sig.shape ∈ U)
    (hpos : ∀ s, s ∈ sig.shape → sig.pos s ∈ U) : allTrees sig ∈ U := by
  unfold allTrees
  exact closed.replacement_mem (closed.separation_mem (codeSpace_mem closed omega hS hpos) _)
    (decodeTarget sig) (fun c hc => decodeTarget_mem closed hS hpos hc)

theorem trees_mem {sig : TreeSignature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U) (hS : sig.shape ∈ U)
    (hpos : ∀ s, s ∈ sig.shape → sig.pos s ∈ U) (i : ZFSet.{u}) : trees sig i ∈ U :=
  closed.separation_mem (allTrees_mem closed omega hS hpos) _

theorem trees_family_mem {sig : TreeSignature.{u}} {U : ZFSet.{u}} (closed : Closed U)
    (omega : ZFSet.omega ∈ U) (hI : sig.index ∈ U) (hS : sig.shape ∈ U)
    (hpos : ∀ s, s ∈ sig.shape → sig.pos s ∈ U) :
    traceLam (graph sig.index (trees sig)) ∈ U := by
  apply closed.traceLam_mem
  rw [graph]
  exact closed.replacement_mem hI (fun i => ZFSet.pair i (trees sig i)) (fun i hi =>
    closed.pair_mem (closed.transitive _ hI hi) (trees_mem closed omega hS hpos i))

/-! ## Empty and singleton functions -/

theorem graph_empty (f : ZFSet.{u} → ZFSet.{u}) : graph (∅ : ZFSet.{u}) f = ∅ := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := mem_graph.mp hz
    exact (ZFSet.notMem_empty x hx).elim
  · intro hz
    exact (ZFSet.notMem_empty z hz).elim

theorem emptyFun_mem (B : ZFSet.{u} → ZFSet.{u}) :
    (∅ : ZFSet.{u}) ∈ tracePiSet (∅ : ZFSet.{u}) B :=
  mem_tracePiFamily_of_total
    (by rw [graph_empty, traceLam_empty])
    (fun p hp => (ZFSet.notMem_empty p hp).elim)

noncomputable def singletonFun (r : ZFSet.{u}) : ZFSet.{u} :=
  traceLam (graph ({∅} : ZFSet.{u}) (fun _ => r))

theorem singletonFun_beta (r : ZFSet.{u}) : traceApp (singletonFun r) ∅ = r := by
  unfold singletonFun
  exact traceApp_graph_beta (fun _ => r) (ZFSet.mem_singleton.mpr rfl)

theorem singletonFun_total (r : ZFSet.{u}) :
    singletonFun r =
      traceLam (graph ({∅} : ZFSet.{u}) (fun p => traceApp (singletonFun r) p)) := by
  unfold singletonFun
  apply congrArg traceLam
  apply graph_congr
  intro p hp
  have hpEq : p = ∅ := ZFSet.mem_singleton.mp hp
  cases hpEq
  exact (singletonFun_beta r).symm

theorem singletonFun_mem {B : ZFSet.{u} → ZFSet.{u}} {r : ZFSet.{u}} (hr : r ∈ B ∅) :
    singletonFun r ∈ tracePiSet ({∅} : ZFSet.{u}) B :=
  mem_tracePiFamily_of_total (singletonFun_total r) (fun p hp => by
    have hpEq : p = ∅ := ZFSet.mem_singleton.mp hp
    cases hpEq
    rw [singletonFun_beta]
    exact hr)

/-! ## Vectors indexed by length -/

namespace Vectors

def vnil : ZFSet.{u} := ZFSet.pair (numeral 0) ∅

def vcons (n a : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair (numeral 1) (ZFSet.pair n a)

noncomputable def vectorShapes (A : ZFSet.{u}) : ZFSet.{u} :=
  ({vnil} : ZFSet.{u}) ∪
    replacement (ZFSet.prod ZFSet.omega A) (fun p => vcons (first p) (second p))

noncomputable def vectorTarget (s : ZFSet.{u}) : ZFSet.{u} :=
  if first s = numeral 0 then numeral 0 else insert (first (second s)) (first (second s))

noncomputable def vectorPos (s : ZFSet.{u}) : ZFSet.{u} :=
  if first s = numeral 0 then ∅ else {∅}

noncomputable def vectorNext (s _p : ZFSet.{u}) : ZFSet.{u} := first (second s)

theorem vectorTarget_nil : vectorTarget vnil = numeral 0 := by
  unfold vectorTarget vnil
  rw [first_pair, if_pos rfl]

theorem vectorTarget_cons (n a : ZFSet.{u}) : vectorTarget (vcons n a) = insert n n := by
  unfold vectorTarget vcons
  rw [first_pair, if_neg numeral_one_ne_zero, second_pair, first_pair]

theorem vectorPos_nil : vectorPos vnil = ∅ := by
  unfold vectorPos vnil
  rw [first_pair, if_pos rfl]

theorem vectorPos_cons (n a : ZFSet.{u}) : vectorPos (vcons n a) = ({∅} : ZFSet.{u}) := by
  unfold vectorPos vcons
  rw [first_pair, if_neg numeral_one_ne_zero]

theorem vectorNext_cons (n a p : ZFSet.{u}) : vectorNext (vcons n a) p = n := by
  unfold vectorNext vcons
  rw [second_pair, first_pair]

theorem vnil_mem (A : ZFSet.{u}) : vnil ∈ vectorShapes A :=
  ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_singleton.mpr rfl))

theorem vcons_mem (A : ZFSet.{u}) {n a : ZFSet.{u}} (hn : n ∈ ZFSet.omega) (ha : a ∈ A) :
    vcons n a ∈ vectorShapes A :=
  ZFSet.mem_union.mpr (Or.inr (mem_replacement.mpr
    ⟨ZFSet.pair n a, ZFSet.pair_mem_prod.mpr ⟨hn, ha⟩, by rw [first_pair, second_pair]⟩))

theorem vectorTarget_mem (A : ZFSet.{u}) {s : ZFSet.{u}} (hs : s ∈ vectorShapes A) :
    vectorTarget s ∈ ZFSet.omega := by
  rcases ZFSet.mem_union.mp hs with hnil | hcons
  · have hsEq : s = vnil := ZFSet.mem_singleton.mp hnil
    cases hsEq
    rw [vectorTarget_nil]
    exact numeral_mem_omega 0
  · obtain ⟨p, hp, rfl⟩ := mem_replacement.mp hcons
    obtain ⟨n, hn, _, _, rfl⟩ := ZFSet.mem_prod.mp hp
    rw [first_pair, second_pair, vectorTarget_cons]
    exact insert_mem_omega hn

theorem vectorNext_mem (A : ZFSet.{u}) {s p : ZFSet.{u}}
    (hs : s ∈ vectorShapes A) (hp : p ∈ vectorPos s) : vectorNext s p ∈ ZFSet.omega := by
  rcases ZFSet.mem_union.mp hs with hnil | hcons
  · have hsEq : s = vnil := ZFSet.mem_singleton.mp hnil
    cases hsEq
    rw [vectorPos_nil] at hp
    exact (ZFSet.notMem_empty p hp).elim
  · obtain ⟨q, hq, rfl⟩ := mem_replacement.mp hcons
    obtain ⟨n, hn, _, _, rfl⟩ := ZFSet.mem_prod.mp hq
    rw [first_pair, second_pair, vectorNext_cons]
    exact hn

noncomputable def vectorSignature (A : ZFSet.{u}) : TreeSignature.{u} where
  index := ZFSet.omega
  shape := vectorShapes A
  target := vectorTarget
  target_mem := fun s hs => vectorTarget_mem A (s := s) hs
  pos := vectorPos
  next := vectorNext
  next_mem := fun s p hs hp => vectorNext_mem A (s := s) (p := p) hs hp

theorem vectorSignature_shape (A : ZFSet.{u}) :
    (vectorSignature A).shape = vectorShapes A := rfl

theorem vectorSignature_target (A : ZFSet.{u}) (s : ZFSet.{u}) :
    (vectorSignature A).target s = vectorTarget s := rfl

theorem vectorSignature_pos (A : ZFSet.{u}) (s : ZFSet.{u}) :
    (vectorSignature A).pos s = vectorPos s := rfl

theorem vectorSignature_next (A : ZFSet.{u}) (s p : ZFSet.{u}) :
    (vectorSignature A).next s p = vectorNext s p := rfl

def nilNode : ZFSet.{u} := node vnil ∅

theorem nil_mem (A : ZFSet.{u}) : nilNode ∈ trees (vectorSignature A) (numeral 0) := by
  have hf : (∅ : ZFSet.{u}) ∈ tracePiSet ((vectorSignature A).pos vnil)
      (fun p => trees (vectorSignature A) ((vectorSignature A).next vnil p)) := by
    rw [vectorSignature_pos, vectorPos_nil]
    exact emptyFun_mem _
  have h := trees_closed (vectorSignature A) (vnil_mem A) hf
  rw [vectorSignature_target, vectorTarget_nil] at h
  exact h

noncomputable def oneNode (a : ZFSet.{u}) : ZFSet.{u} :=
  node (vcons (numeral 0) a) (singletonFun nilNode)

theorem one_mem (A : ZFSet.{u}) {a : ZFSet.{u}} (ha : a ∈ A) :
    oneNode a ∈ trees (vectorSignature A) (numeral 1) := by
  have hf : singletonFun nilNode ∈ tracePiSet ((vectorSignature A).pos (vcons (numeral 0) a))
      (fun p => trees (vectorSignature A) ((vectorSignature A).next (vcons (numeral 0) a) p)) := by
    rw [vectorSignature_pos, vectorPos_cons]
    apply singletonFun_mem
    rw [vectorSignature_next, vectorNext_cons]
    exact nil_mem A
  have h := trees_closed (vectorSignature A) (vcons_mem A (numeral_mem_omega 0) ha) hf
  rw [vectorSignature_target, vectorTarget_cons] at h
  have hnum : numeral (1 : Nat) = insert (numeral 0) (numeral 0) := numeral_succ 0
  rw [← hnum] at h
  exact h

theorem one_not_zero (A : ZFSet.{u}) (a : ZFSet.{u}) :
    oneNode a ∉ trees (vectorSignature A) (numeral 0) := by
  intro ht
  obtain ⟨s, f, _, htarget, _, heq⟩ := exists_inversion (vectorSignature A) ht
  obtain ⟨rfl, rfl⟩ := node_inj heq.symm
  rw [vectorSignature_target, vectorTarget_cons] at htarget
  have hnum : numeral (1 : Nat) = insert (numeral 0) (numeral 0) := numeral_succ 0
  rw [← hnum] at htarget
  exact numeral_one_ne_zero htarget

/-- A vector of length one lies at index `1` and not at index `0`. -/
theorem length_one (A : ZFSet.{u}) {a : ZFSet.{u}} (ha : a ∈ A) :
    oneNode a ∈ trees (vectorSignature A) (numeral 1) ∧
      oneNode a ∉ trees (vectorSignature A) (numeral 0) :=
  ⟨one_mem A ha, one_not_zero A a⟩

/-- An index outside `ω` is the target of no vector shape, so it has no tree. -/
theorem empty_outside (A : ZFSet.{u}) {i : ZFSet.{u}} (hi : i ∉ ZFSet.omega) :
    trees (vectorSignature A) i = ∅ :=
  trees_empty_of_target (vectorSignature A) (fun _ hs htarget =>
    hi (htarget ▸ vectorTarget_mem A hs))

end Vectors

/-! ## The accessible part of a relation -/

namespace Accessibility

def accessible (A : ZFSet.{u}) (r : ZFSet.{u} → ZFSet.{u} → Prop)
    (y x : ZFSet.{u}) : Prop :=
  y ∈ A ∧ r y x

def accPos (A : ZFSet.{u}) (r : ZFSet.{u} → ZFSet.{u} → Prop) (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => r y x) A

def accNext (_x y : ZFSet.{u}) : ZFSet.{u} := y

def accSignature (A : ZFSet.{u}) (r : ZFSet.{u} → ZFSet.{u} → Prop) : TreeSignature.{u} where
  index := A
  shape := A
  target := fun s => s
  target_mem := fun _ hs => hs
  pos := accPos A r
  next := accNext
  next_mem := fun _ _ _ hp => (ZFSet.mem_sep.mp hp).1

theorem accSignature_shape (A : ZFSet.{u}) (r : ZFSet.{u} → ZFSet.{u} → Prop) :
    (accSignature A r).shape = A := rfl

theorem accSignature_target (A : ZFSet.{u}) (r : ZFSet.{u} → ZFSet.{u} → Prop)
    (s : ZFSet.{u}) : (accSignature A r).target s = s := rfl

theorem accSignature_pos (A : ZFSet.{u}) (r : ZFSet.{u} → ZFSet.{u} → Prop)
    (x : ZFSet.{u}) : (accSignature A r).pos x = accPos A r x := rfl

theorem accSignature_next (A : ZFSet.{u}) (r : ZFSet.{u} → ZFSet.{u} → Prop)
    (x y : ZFSet.{u}) : (accSignature A r).next x y = y := rfl

theorem acc_irrefl {rel : ZFSet.{u} → ZFSet.{u} → Prop} {a : ZFSet.{u}} (h : Acc rel a) :
    ¬ rel a a :=
  Acc.rec (motive := fun y _ => ¬ rel y y) (fun y _ ih hyy => ih y hyy hyy) h

theorem exists_of_acc {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop} {x : ZFSet.{u}}
    (hx : x ∈ A) (hacc : Acc (accessible A r) x) :
    ∃ t, t ∈ trees (accSignature A r) x :=
  Acc.rec (motive := fun y _ => y ∈ A → ∃ t, t ∈ trees (accSignature A r) y)
    (fun y _ ih hy => by
      let child : ZFSet.{u} → ZFSet.{u} := fun p =>
        @Classical.epsilon ZFSet.{u} ⟨∅⟩ (fun t => t ∈ trees (accSignature A r) p)
      have hspec : ∀ p, p ∈ accPos A r y → child p ∈ trees (accSignature A r) p := by
        intro p hp
        obtain ⟨hpA, hpr⟩ := ZFSet.mem_sep.mp hp
        exact Classical.epsilon_spec_aux ⟨(∅ : ZFSet.{u})⟩
          (fun t => t ∈ trees (accSignature A r) p) (ih p ⟨hpA, hpr⟩ hpA)
      have hyShape : y ∈ (accSignature A r).shape := by
        unfold accSignature
        exact hy
      have hf : traceLam (graph ((accSignature A r).pos y) child) ∈
          tracePiSet ((accSignature A r).pos y)
            (fun p => trees (accSignature A r) ((accSignature A r).next y p)) := by
        unfold accSignature
        apply mem_tracePiFamily_of_total
        · apply congrArg traceLam
          apply graph_congr
          intro p hp
          exact (traceApp_graph_beta child hp).symm
        · intro p hp
          rw [traceApp_graph_beta child hp]
          exact hspec p hp
      exact ⟨node y (traceLam (graph ((accSignature A r).pos y) child)),
        trees_closed (accSignature A r) hyShape hf⟩)
    hacc hx

theorem acc_of_inTree {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop} {i t : ZFSet.{u}}
    (ht : InTree (accSignature A r) i t) : i ∈ A ∧ Acc (accessible A r) i :=
  InTree.rec (motive := fun i _ _ => i ∈ A ∧ Acc (accessible A r) i)
    (fun s _ hs _ _ ih => by
      refine ⟨?_, Acc.intro s (fun y hy => ?_)⟩
      · rw [accSignature_target]
        rw [accSignature_shape] at hs
        exact hs
      · have hp : y ∈ (accSignature A r).pos s := by
          rw [accSignature_pos]
          exact ZFSet.mem_sep.mpr hy
        have ihAt := ih y hp
        rw [accSignature_next] at ihAt
        exact ihAt.2)
    ht

/-- `trees x` is inhabited exactly when `x` is accessible for `r` inside `A`. -/
theorem nonempty_iff {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop} {x : ZFSet.{u}} :
    (∃ t, t ∈ trees (accSignature A r) x) ↔ x ∈ A ∧ Acc (accessible A r) x := by
  constructor
  · rintro ⟨t, ht⟩
    exact acc_of_inTree (inTree_of_mem_trees (accSignature A r) ht)
  · rintro ⟨hx, hacc⟩
    exact exists_of_acc hx hacc

theorem empty_of_refl {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop} {x : ZFSet.{u}}
    (hx : x ∈ A) (hrr : r x x) : trees (accSignature A r) x = ∅ := by
  apply ZFSet.ext
  intro t
  constructor
  · intro ht
    obtain ⟨_, hacc⟩ := acc_of_inTree (inTree_of_mem_trees (accSignature A r) ht)
    exact (acc_irrefl hacc ⟨hx, hrr⟩).elim
  · intro ht
    exact (ZFSet.notMem_empty t ht).elim

/-- An index outside `A` is the target of no shape. -/
theorem empty_outside {A : ZFSet.{u}} {r : ZFSet.{u} → ZFSet.{u} → Prop} {x : ZFSet.{u}}
    (hx : x ∉ A) : trees (accSignature A r) x = ∅ :=
  trees_empty_of_target (accSignature A r) (fun _ hs htarget => hx (htarget ▸ hs))

end Accessibility

/-! ## Ordinal notations as one-index trees

The correspondence below is for `zero | suc | limit (ω → T)` only. -/

namespace OrdinalComparison

open ZFSetInductive (constructorValue)

def ordShapes : ZFSet.{u} := numeral 3

theorem numeral_zero_mem_one : numeral (0 : Nat) ∈ numeral 1 := by
  have h : numeral 1 = insert (numeral 0) (numeral 0) := numeral_succ 0
  rw [h]
  exact ZFSet.mem_insert _ _

theorem numeral_zero_mem_two : numeral (0 : Nat) ∈ numeral 2 := by
  have h : numeral 2 = insert (numeral 1) (numeral 1) := numeral_succ 1
  rw [h]
  exact ZFSet.mem_insert_of_mem _ numeral_zero_mem_one

theorem numeral_one_mem_two : numeral (1 : Nat) ∈ numeral 2 := by
  have h : numeral 2 = insert (numeral 1) (numeral 1) := numeral_succ 1
  rw [h]
  exact ZFSet.mem_insert _ _

theorem numeral_zero_mem_shapes : numeral (0 : Nat) ∈ ordShapes := by
  have h : numeral 3 = insert (numeral 2) (numeral 2) := numeral_succ 2
  rw [ordShapes, h]
  exact ZFSet.mem_insert_of_mem _ numeral_zero_mem_two

theorem numeral_one_mem_shapes : numeral (1 : Nat) ∈ ordShapes := by
  have h : numeral 3 = insert (numeral 2) (numeral 2) := numeral_succ 2
  rw [ordShapes, h]
  exact ZFSet.mem_insert_of_mem _ numeral_one_mem_two

theorem numeral_two_mem_shapes : numeral (2 : Nat) ∈ ordShapes := by
  have h : numeral 3 = insert (numeral 2) (numeral 2) := numeral_succ 2
  rw [ordShapes, h]
  exact ZFSet.mem_insert _ _

theorem numeral_two_ne_zero : numeral (2 : Nat) ≠ numeral (0 : Nat) :=
  numeral_injective.ne (Nat.succ_ne_zero 1)

theorem numeral_two_ne_one : numeral (2 : Nat) ≠ numeral (1 : Nat) :=
  numeral_injective.ne (Nat.succ_injective.ne (Nat.succ_ne_zero 0))

theorem eq_of_mem_shapes {s : ZFSet.{u}} (hs : s ∈ ordShapes) :
    s = numeral 0 ∨ s = numeral 1 ∨ s = numeral 2 := by
  rw [ordShapes] at hs
  have h3 : numeral 3 = insert (numeral 2) (numeral 2) := numeral_succ 2
  rw [h3, ZFSet.mem_insert_iff] at hs
  rcases hs with rfl | hs
  · exact Or.inr (Or.inr rfl)
  · have h2 : numeral 2 = insert (numeral 1) (numeral 1) := numeral_succ 1
    rw [h2, ZFSet.mem_insert_iff] at hs
    rcases hs with rfl | hs
    · exact Or.inr (Or.inl rfl)
    · have h1 : numeral 1 = insert (numeral 0) (numeral 0) := numeral_succ 0
      rw [h1, ZFSet.mem_insert_iff] at hs
      rcases hs with rfl | hs
      · exact Or.inl rfl
      · exact (ZFSet.notMem_empty s hs).elim

noncomputable def ordPos (s : ZFSet.{u}) : ZFSet.{u} :=
  if s = numeral 0 then ∅ else if s = numeral 1 then {∅} else ZFSet.omega

theorem ordPos_zero : ordPos (numeral 0) = ∅ := by
  unfold ordPos
  rw [if_pos rfl]

theorem ordPos_one : ordPos (numeral 1) = ({∅} : ZFSet.{u}) := by
  unfold ordPos
  rw [if_neg numeral_one_ne_zero, if_pos rfl]

theorem ordPos_two : ordPos (numeral 2) = ZFSet.omega := by
  unfold ordPos
  rw [if_neg numeral_two_ne_zero, if_neg numeral_two_ne_one]

noncomputable def ordTreeSignature : TreeSignature.{u} where
  index := {numeral 3}
  shape := ordShapes
  target := fun _ => numeral 3
  target_mem := fun _ _ => ZFSet.mem_singleton.mpr rfl
  pos := ordPos
  next := fun _ _ => numeral 3
  next_mem := fun _ _ _ _ => ZFSet.mem_singleton.mpr rfl

theorem ordTree_shape : ordTreeSignature.shape = ordShapes := rfl

theorem ordTree_target (s : ZFSet.{u}) : ordTreeSignature.target s = numeral 3 := rfl

theorem ordTree_pos (s : ZFSet.{u}) : ordTreeSignature.pos s = ordPos s := rfl

theorem ordTree_next (s p : ZFSet.{u}) : ordTreeSignature.next s p = numeral 3 := rfl

theorem ordAt {i : Nat} {c : ZFSetInductiveFunctions.Constructor}
    (h : ZFSetInductiveFunctions.OrdinalNotation.ordSignature[i]? = some c) :
    (i = 0 ∧ c = []) ∨
      (i = 1 ∧ c = [ZFSetInductiveFunctions.Field.recursive]) ∨
        (i = 2 ∧ c = [ZFSetInductiveFunctions.Field.ofFun ZFSet.omega]) := by
  cases i with
  | zero =>
      have hget : ZFSetInductiveFunctions.OrdinalNotation.ordSignature[0]? = some [] := rfl
      exact Or.inl ⟨rfl, Option.some_inj.mp (h.symm.trans hget)⟩
  | succ i =>
      cases i with
      | zero =>
          have hget : ZFSetInductiveFunctions.OrdinalNotation.ordSignature[1]? =
              some [ZFSetInductiveFunctions.Field.recursive] := rfl
          exact Or.inr (Or.inl ⟨rfl, Option.some_inj.mp (h.symm.trans hget)⟩)
      | succ i =>
          cases i with
          | zero =>
              have hget : ZFSetInductiveFunctions.OrdinalNotation.ordSignature[2]? =
                  some [ZFSetInductiveFunctions.Field.ofFun ZFSet.omega] := rfl
              exact Or.inr (Or.inr ⟨rfl, Option.some_inj.mp (h.symm.trans hget)⟩)
          | succ i =>
              have hnone :
                  ZFSetInductiveFunctions.OrdinalNotation.ordSignature[i.succ.succ.succ]? =
                    none := rfl
              rw [hnone] at h
              cases h

def toTreeStep (i : Nat) (_args recs : List ZFSet.{u}) : ZFSet.{u} :=
  match i with
  | 0 => node (numeral 0) ∅
  | 1 =>
      match recs with
      | [] => ∅
      | r :: _ => node (numeral 1) (singletonFun r)
  | 2 =>
      match recs with
      | [] => ∅
      | f :: _ => node (numeral 2) f
  | _ => ∅

theorem toTreeStep_zero (args recs : List ZFSet.{u}) :
    toTreeStep 0 args recs = node (numeral 0) ∅ := rfl

theorem toTreeStep_suc (args : List ZFSet.{u}) (r : ZFSet.{u}) (rs : List ZFSet.{u}) :
    toTreeStep 1 args (r :: rs) = node (numeral 1) (singletonFun r) := rfl

theorem toTreeStep_limit (args : List ZFSet.{u}) (f : ZFSet.{u}) (fs : List ZFSet.{u}) :
    toTreeStep 2 args (f :: fs) = node (numeral 2) f := rfl

noncomputable def toTree (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSetInductiveFunctions.recFun
    ZFSetInductiveFunctions.OrdinalNotation.ordSignature toTreeStep x

theorem toTree_eq (x : ZFSet.{u}) :
    toTree x = ZFSetInductiveFunctions.recFun
      ZFSetInductiveFunctions.OrdinalNotation.ordSignature toTreeStep x := rfl

noncomputable def toIndStep (s _f results : ZFSet.{u}) : ZFSet.{u} :=
  if s = numeral 0 then constructorValue 0 []
  else if s = numeral 1 then constructorValue 1 [traceApp results ∅]
  else constructorValue 2 [results]

noncomputable def toInd (x : ZFSet.{u}) : ZFSet.{u} := recFun ordTreeSignature toIndStep x

theorem zero_node_mem :
    (node (numeral 0) ∅ : ZFSet.{u}) ∈ trees ordTreeSignature (numeral 3) := by
  have hs : numeral 0 ∈ ordTreeSignature.shape := by
    rw [ordTree_shape]
    exact numeral_zero_mem_shapes
  have hf : (∅ : ZFSet.{u}) ∈ tracePiSet (ordTreeSignature.pos (numeral 0))
      (fun p => trees ordTreeSignature (ordTreeSignature.next (numeral 0) p)) := by
    rw [ordTree_pos, ordPos_zero]
    exact emptyFun_mem _
  have h := trees_closed ordTreeSignature hs hf
  rw [ordTree_target] at h
  exact h

theorem suc_node_mem {r : ZFSet.{u}} (hr : r ∈ trees ordTreeSignature (numeral 3)) :
    node (numeral 1) (singletonFun r) ∈ trees ordTreeSignature (numeral 3) := by
  have hs : numeral 1 ∈ ordTreeSignature.shape := by
    rw [ordTree_shape]
    exact numeral_one_mem_shapes
  have hf : singletonFun r ∈ tracePiSet (ordTreeSignature.pos (numeral 1))
      (fun p => trees ordTreeSignature (ordTreeSignature.next (numeral 1) p)) := by
    rw [ordTree_pos, ordPos_one]
    exact singletonFun_mem hr
  have h := trees_closed ordTreeSignature hs hf
  rw [ordTree_target] at h
  exact h

theorem limit_node_mem {g : ZFSet.{u}}
    (hvalues : ∀ a, a ∈ ZFSet.omega → traceApp g a ∈ trees ordTreeSignature (numeral 3))
    (htotal : g = traceLam (graph ZFSet.omega (fun a => traceApp g a))) :
    node (numeral 2) g ∈ trees ordTreeSignature (numeral 3) := by
  have hs : numeral 2 ∈ ordTreeSignature.shape := by
    rw [ordTree_shape]
    exact numeral_two_mem_shapes
  have hf : g ∈ tracePiSet (ordTreeSignature.pos (numeral 2))
      (fun p => trees ordTreeSignature (ordTreeSignature.next (numeral 2) p)) := by
    rw [ordTree_pos, ordPos_two]
    exact mem_tracePiFamily_of_total htotal hvalues
  have h := trees_closed ordTreeSignature hs hf
  rw [ordTree_target] at h
  exact h

theorem toInd_node_zero :
    toInd (node (numeral 0) (∅ : ZFSet.{u})) = constructorValue 0 ([] : List ZFSet.{u}) := by
  unfold toInd
  have hs : numeral 0 ∈ ordTreeSignature.shape := by
    rw [ordTree_shape]
    exact numeral_zero_mem_shapes
  have hf : (∅ : ZFSet.{u}) ∈ tracePiSet (ordTreeSignature.pos (numeral 0))
      (fun p => trees ordTreeSignature (ordTreeSignature.next (numeral 0) p)) := by
    rw [ordTree_pos, ordPos_zero]
    exact emptyFun_mem _
  rw [recursion_node ordTreeSignature toIndStep hs hf]
  unfold toIndStep
  rw [if_pos rfl]

theorem toInd_node_suc {r : ZFSet.{u}} (hr : r ∈ trees ordTreeSignature (numeral 3)) :
    toInd (node (numeral 1) (singletonFun r)) = constructorValue 1 [toInd r] := by
  unfold toInd
  have hs : numeral 1 ∈ ordTreeSignature.shape := by
    rw [ordTree_shape]
    exact numeral_one_mem_shapes
  have hf : singletonFun r ∈ tracePiSet (ordTreeSignature.pos (numeral 1))
      (fun p => trees ordTreeSignature (ordTreeSignature.next (numeral 1) p)) := by
    rw [ordTree_pos, ordPos_one]
    exact singletonFun_mem hr
  rw [recursion_node ordTreeSignature toIndStep hs hf]
  unfold toIndStep
  rw [if_neg numeral_one_ne_zero, if_pos rfl]
  apply congrArg (fun z => constructorValue 1 [z])
  rw [ordTree_pos]
  have hp : (∅ : ZFSet.{u}) ∈ ordPos (numeral 1) := by
    rw [ordPos_one]
    exact ZFSet.mem_singleton.mpr rfl
  rw [traceApp_graph_beta _ hp, singletonFun_beta]

theorem toInd_node_limit {g : ZFSet.{u}}
    (hvalues : ∀ a, a ∈ ZFSet.omega → traceApp g a ∈ trees ordTreeSignature (numeral 3))
    (htotal : g = traceLam (graph ZFSet.omega (fun a => traceApp g a))) :
    toInd (node (numeral 2) g) =
      constructorValue 2 [traceLam (graph ZFSet.omega (fun a => toInd (traceApp g a)))] := by
  unfold toInd
  have hs : numeral 2 ∈ ordTreeSignature.shape := by
    rw [ordTree_shape]
    exact numeral_two_mem_shapes
  have hf : g ∈ tracePiSet (ordTreeSignature.pos (numeral 2))
      (fun p => trees ordTreeSignature (ordTreeSignature.next (numeral 2) p)) := by
    rw [ordTree_pos, ordPos_two]
    exact mem_tracePiFamily_of_total htotal hvalues
  rw [recursion_node ordTreeSignature toIndStep hs hf]
  unfold toIndStep
  rw [if_neg numeral_two_ne_zero, if_neg numeral_two_ne_one, ordTree_pos, ordPos_two]

theorem toTree_zero :
    toTree ZFSetInductiveFunctions.OrdinalNotation.zero = node (numeral 0) ∅ := by
  rw [toTree, ZFSetInductiveFunctions.OrdinalNotation.zero,
    ZFSetInductiveFunctions.recursion_constructor toTreeStep rfl
      ZFSetInductiveFunctions.Fits.nil,
    ZFSetInductiveFunctions.mapResults_nil, toTreeStep_zero]

theorem toTree_suc {x : ZFSet.{u}}
    (hx : x ∈ ZFSetInductiveFunctions.carrier
      ZFSetInductiveFunctions.OrdinalNotation.ordSignature) :
    toTree (ZFSetInductiveFunctions.OrdinalNotation.suc x) =
      node (numeral 1) (singletonFun (toTree x)) := by
  rw [toTree, ZFSetInductiveFunctions.OrdinalNotation.suc,
    ZFSetInductiveFunctions.recursion_constructor toTreeStep rfl
      (ZFSetInductiveFunctions.Fits.recursive hx ZFSetInductiveFunctions.Fits.nil),
    ZFSetInductiveFunctions.mapResults_recursive, ZFSetInductiveFunctions.mapResults_nil,
    toTreeStep_suc, toTree]

theorem toTree_limit {f : ZFSet.{u}}
    (hf : f ∈ tracePiSet ZFSet.omega (fun _ => ZFSetInductiveFunctions.carrier
      ZFSetInductiveFunctions.OrdinalNotation.ordSignature)) :
    toTree (ZFSetInductiveFunctions.OrdinalNotation.limit f) =
      node (numeral 2) (traceLam (graph ZFSet.omega (fun a => toTree (traceApp f a)))) := by
  rw [toTree_eq, ZFSetInductiveFunctions.OrdinalNotation.limit,
    ZFSetInductiveFunctions.recursion_constructor toTreeStep rfl
      (ZFSetInductiveFunctions.Fits.ofFun hf ZFSetInductiveFunctions.Fits.nil),
    ZFSetInductiveFunctions.mapResults_ofFun, ZFSetInductiveFunctions.mapResults_nil,
    toTreeStep_limit]
  apply congrArg (node (numeral 2))
  apply congrArg traceLam
  apply graph_congr
  intro a _ha
  exact (toTree_eq (traceApp f a)).symm

private theorem carrier_round {x : ZFSet.{u}}
    (hx : ZFSetInductiveFunctions.InCarrier
      ZFSetInductiveFunctions.OrdinalNotation.ordSignature x) :
    toTree x ∈ trees ordTreeSignature (numeral 3) ∧ toInd (toTree x) = x :=
  ZFSetInductiveFunctions.InCarrier.rec
    (motive_1 := fun y _ =>
      toTree y ∈ trees ordTreeSignature (numeral 3) ∧ toInd (toTree y) = y)
    (motive_2 := fun c args _ =>
      ∀ i, ZFSetInductiveFunctions.OrdinalNotation.ordSignature[i]? = some c →
        toTree (constructorValue i args) ∈ trees ordTreeSignature (numeral 3) ∧
          toInd (toTree (constructorValue i args)) = constructorValue i args)
    (fun atIndex _ ih => ih _ atIndex)
    (fun i atIndex => by
      rcases ordAt atIndex with ⟨rfl, _⟩ | ⟨_, hbad⟩ | ⟨_, hbad⟩
      · have hcomp := ZFSetInductiveFunctions.recFun_constructor
          ZFSetInductiveFunctions.OrdinalNotation.ordSignature toTreeStep atIndex
          ZFSetInductiveFunctions.Deriv.nil
        unfold toTree
        rw [hcomp, ZFSetInductiveFunctions.mapResults_nil, toTreeStep_zero]
        exact ⟨zero_node_mem, toInd_node_zero⟩
      · cases hbad
      · cases hbad)
    (fun member rest hp _ i atIndex => by
      rcases ordAt atIndex with ⟨_, hbad⟩ | ⟨rfl, hlist⟩ | ⟨_, hbad⟩
      · cases hbad
      · injection hlist with _ hfs
        cases hfs
        cases rest
        have hcomp := ZFSetInductiveFunctions.recFun_constructor
          ZFSetInductiveFunctions.OrdinalNotation.ordSignature toTreeStep atIndex
          (ZFSetInductiveFunctions.Deriv.recursive member ZFSetInductiveFunctions.Deriv.nil)
        unfold toTree
        rw [hcomp, ZFSetInductiveFunctions.mapResults_recursive,
          ZFSetInductiveFunctions.mapResults_nil, toTreeStep_suc, ← toTree]
        exact ⟨suc_node_mem hp.1, by rw [toInd_node_suc hp.1, hp.2]⟩
      · cases hbad)
    (fun _ _ _ i atIndex => by
      rcases ordAt atIndex with ⟨_, hbad⟩ | ⟨_, hbad⟩ | ⟨_, hbad⟩
      · cases hbad
      · cases hbad
      · cases hbad)
    (fun {_A _fs _args f} total values rest ihValues _ => fun i atIndex => by
      rcases ordAt atIndex with ⟨_, hbad⟩ | ⟨_, hbad⟩ | ⟨rfl, hlist⟩
      · cases hbad
      · cases hbad
      · injection hlist with hA hfs
        cases hA
        cases hfs
        cases rest
        have hcomp := ZFSetInductiveFunctions.recFun_constructor
          ZFSetInductiveFunctions.OrdinalNotation.ordSignature toTreeStep atIndex
          (ZFSetInductiveFunctions.Deriv.ofFun total values
            ZFSetInductiveFunctions.Deriv.nil)
        unfold toTree
        rw [hcomp, ZFSetInductiveFunctions.mapResults_ofFun,
          ZFSetInductiveFunctions.mapResults_nil, toTreeStep_limit]
        have hfold :
            traceLam (graph ZFSet.omega (fun b =>
              ZFSetInductiveFunctions.recFun
                ZFSetInductiveFunctions.OrdinalNotation.ordSignature toTreeStep
                (traceApp f b))) =
              traceLam (graph ZFSet.omega (fun b => toTree (traceApp f b))) := by
          apply congrArg traceLam
          apply graph_congr
          intro b _hb
          exact (toTree_eq (traceApp f b)).symm
        rw [hfold]
        have hvalues : ∀ a, a ∈ ZFSet.omega →
            traceApp (traceLam (graph ZFSet.omega (fun b => toTree (traceApp f b)))) a ∈
              trees ordTreeSignature (numeral 3) := by
          intro a ha
          rw [traceApp_graph_beta (fun b => toTree (traceApp f b)) ha]
          exact (ihValues a ha).1
        have htotal :
            traceLam (graph ZFSet.omega (fun b => toTree (traceApp f b))) =
              traceLam (graph ZFSet.omega (fun a =>
                traceApp (traceLam (graph ZFSet.omega (fun b => toTree (traceApp f b)))) a)) := by
          apply congrArg traceLam
          apply graph_congr
          intro a ha
          exact (traceApp_graph_beta (fun b => toTree (traceApp f b)) ha).symm
        refine ⟨limit_node_mem hvalues htotal, ?_⟩
        rw [toInd_node_limit hvalues htotal]
        apply congrArg (fun z => constructorValue 2 [z])
        have hback :
            traceLam (graph ZFSet.omega (fun a =>
              toInd (traceApp (traceLam (graph ZFSet.omega
                (fun b => toTree (traceApp f b)))) a))) =
              traceLam (graph ZFSet.omega (fun a => traceApp f a)) := by
          apply congrArg traceLam
          apply graph_congr
          intro a ha
          rw [traceApp_graph_beta (fun b => toTree (traceApp f b)) ha]
          exact (ihValues a ha).2
        rw [hback]
        exact total.symm)
    hx

theorem toTree_mem {x : ZFSet.{u}}
    (hx : x ∈ ZFSetInductiveFunctions.carrier
      ZFSetInductiveFunctions.OrdinalNotation.ordSignature) :
    toTree x ∈ trees ordTreeSignature (numeral 3) :=
  (carrier_round (ZFSetInductiveFunctions.inCarrier_of_mem_carrier hx)).1

theorem toInd_toTree {x : ZFSet.{u}}
    (hx : x ∈ ZFSetInductiveFunctions.carrier
      ZFSetInductiveFunctions.OrdinalNotation.ordSignature) :
    toInd (toTree x) = x :=
  (carrier_round (ZFSetInductiveFunctions.inCarrier_of_mem_carrier hx)).2

private theorem tree_round {t : ZFSet.{u}} (ht : t ∈ trees ordTreeSignature (numeral 3)) :
    toInd t ∈ ZFSetInductiveFunctions.carrier
      ZFSetInductiveFunctions.OrdinalNotation.ordSignature ∧
      toTree (toInd t) = t :=
  trees_induct ordTreeSignature
    (P := fun t =>
      toInd t ∈ ZFSetInductiveFunctions.carrier
        ZFSetInductiveFunctions.OrdinalNotation.ordSignature ∧
        toTree (toInd t) = t)
    (fun {s f} hs hf hchildren => by
    rw [ordTree_shape] at hs
    rw [ordTree_pos] at hf hchildren
    obtain ⟨total, values⟩ := total_of_mem_tracePiFamily hf
    rcases eq_of_mem_shapes hs with rfl | rfl | rfl
    · have hfEmpty : f = ∅ := by
        rw [total, ordPos_zero, graph_empty, traceLam_empty]
      cases hfEmpty
      refine ⟨?_, ?_⟩
      · rw [toInd_node_zero]
        exact ZFSetInductiveFunctions.carrier_closed rfl ZFSetInductiveFunctions.Fits.nil
      · rw [toInd_node_zero]
        exact toTree_zero
    · have hp : (∅ : ZFSet.{u}) ∈ ordPos (numeral 1) := by
        rw [ordPos_one]
        exact ZFSet.mem_singleton.mpr rfl
      have hchild := hchildren ∅ hp
      have hsing : f = singletonFun (traceApp f ∅) := by
        rw [ordPos_one] at total
        refine total.trans ?_
        unfold singletonFun
        apply congrArg traceLam
        apply graph_congr
        intro p hpm
        have hpEq : p = ∅ := ZFSet.mem_singleton.mp hpm
        cases hpEq
        rfl
      have hr : traceApp f ∅ ∈ trees ordTreeSignature (numeral 3) := by
        have hv := values ∅ hp
        rw [ordTree_next] at hv
        exact hv
      refine ⟨?_, ?_⟩
      · rw [hsing, toInd_node_suc hr]
        exact ZFSetInductiveFunctions.carrier_closed rfl
          (ZFSetInductiveFunctions.Fits.recursive hchild.1 ZFSetInductiveFunctions.Fits.nil)
      · rw [hsing, toInd_node_suc hr]
        have htree := toTree_suc hchild.1
        rw [ZFSetInductiveFunctions.OrdinalNotation.suc, hchild.2] at htree
        exact htree
    · rw [ordPos_two] at total values hchildren
      have hvalues : ∀ a, a ∈ ZFSet.omega →
          traceApp f a ∈ trees ordTreeSignature (numeral 3) := by
        intro a ha
        have hv := values a ha
        rw [ordTree_next] at hv
        exact hv
      refine ⟨?_, ?_⟩
      · rw [toInd_node_limit hvalues total]
        apply ZFSetInductiveFunctions.carrier_closed rfl
        apply ZFSetInductiveFunctions.Fits.ofFun
        · apply mem_tracePiSet_of_total
          · apply congrArg traceLam
            apply graph_congr
            intro a ha
            exact (traceApp_graph_beta (fun b => toInd (traceApp f b)) ha).symm
          · intro a ha
            rw [traceApp_graph_beta (fun b => toInd (traceApp f b)) ha]
            exact (hchildren a ha).1
        · exact ZFSetInductiveFunctions.Fits.nil
      · rw [toInd_node_limit hvalues total]
        have hg : traceLam (graph ZFSet.omega (fun a => toInd (traceApp f a))) ∈
            tracePiSet ZFSet.omega (fun _ => ZFSetInductiveFunctions.carrier
              ZFSetInductiveFunctions.OrdinalNotation.ordSignature) :=
          mem_tracePiSet_of_total
            (by
              apply congrArg traceLam
              apply graph_congr
              intro a ha
              exact (traceApp_graph_beta (fun b => toInd (traceApp f b)) ha).symm)
            (fun a ha => by
              rw [traceApp_graph_beta (fun b => toInd (traceApp f b)) ha]
              exact (hchildren a ha).1)
        have htree := toTree_limit hg
        rw [ZFSetInductiveFunctions.OrdinalNotation.limit] at htree
        rw [htree]
        apply congrArg (node (numeral 2))
        suffices hleft :
            traceLam (graph ZFSet.omega (fun a =>
              toTree (traceApp (traceLam (graph ZFSet.omega
                (fun b => toInd (traceApp f b)))) a))) =
              traceLam (graph ZFSet.omega (fun a => traceApp f a)) by
          exact hleft.trans total.symm
        apply congrArg traceLam
        apply graph_congr
        intro a ha
        rw [traceApp_graph_beta (fun b => toInd (traceApp f b)) ha]
        exact (hchildren a ha).2)
    ht

theorem toInd_mem {t : ZFSet.{u}} (ht : t ∈ trees ordTreeSignature (numeral 3)) :
    toInd t ∈ ZFSetInductiveFunctions.carrier
      ZFSetInductiveFunctions.OrdinalNotation.ordSignature :=
  (tree_round ht).1

theorem toTree_toInd {t : ZFSet.{u}} (ht : t ∈ trees ordTreeSignature (numeral 3)) :
    toTree (toInd t) = t :=
  (tree_round ht).2

end OrdinalComparison

end

end Mettapedia.Logic.HOL.Embedding.ZFSetIndexedTrees
