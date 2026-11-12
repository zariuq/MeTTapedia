(** Lean's list functions on permuted lists: map, filter and foldr.

    The functions are the generated readings of Lean's definitions.  Their
    constructor equations are restated here for a type argument that is any
    set (the generated equation theorems keep Lean's universe binders), and
    the lemmas follow by induction over the permutation relation. **)

(** map **)

Theorem LeanListMap_nil : forall A B f,
  Lean_List_map A B f (Lean_List_nil_node A) = Lean_List_nil_node B.
let A B f.
prove Lean_List_rec A (Lean_List_nil_node B) (Lean_List_map_method1_0 A B f) (Lean_List_nil_node A) = Lean_List_nil_node B.
exact Lean_List_iota0 A (Lean_List_nil_node B) (Lean_List_map_method1_0 A B f).
Qed.

Theorem LeanListMap_cons : forall A B, forall f :e (Pi_ ux :e A, B), forall x :e A, forall xs :e Lean_List A,
  Lean_List_map A B f (Lean_List_cons_node A x xs) = Lean_List_cons_node B (f x) (Lean_List_map A B f xs).
let A B f. assume Hf: f :e (Pi_ ux :e A, B). let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
prove Lean_List_rec A (Lean_List_nil_node B) (Lean_List_map_method1_0 A B f) (Lean_List_cons_node A x xs) =
  Lean_List_cons_node B (f x) (Lean_List_rec A (Lean_List_nil_node B) (Lean_List_map_method1_0 A B f) xs).
rewrite Lean_List_iota1 A (Lean_List_nil_node B) (Lean_List_map_method1_0 A B f) x Hx xs Hxs.
rewrite Lean_List_map_method1_0_ap A B f x Hx.
rewrite Lean_List_map_method1_1_ap A B f x xs Hxs.
rewrite Lean_List_map_method1_2_ap A B f x xs
  (Lean_List_rec A (Lean_List_nil_node B) (Lean_List_map_method1_0 A B f) xs) (Lean_List_map_In A B f Hf xs Hxs).
reflexivity.
Qed.

Theorem LeanListPerm_map : forall A B, forall f :e (Pi_ ux :e A, B), forall xs ys,
  LeanListPerm A xs ys -> LeanListPerm B (Lean_List_map A B f xs) (Lean_List_map A B f ys).
let A B f. assume Hf: f :e (Pi_ ux :e A, B).
claim Hfx: forall x :e A, f x :e B.
{ let x. assume Hx: x :e A. exact ap_Pi A (fun _ => B) f x Hf Hx. }
claim Hnil: LeanListPerm B (Lean_List_map A B f (Lean_List_nil_node A)) (Lean_List_map A B f (Lean_List_nil_node A)).
{ rewrite LeanListMap_nil A B f. exact LeanListPerm_nil B. }
claim Hcons: forall x :e A, forall xs ys :e Lean_List A,
  LeanListPerm B (Lean_List_map A B f xs) (Lean_List_map A B f ys) ->
  LeanListPerm B (Lean_List_map A B f (Lean_List_cons_node A x xs)) (Lean_List_map A B f (Lean_List_cons_node A x ys)).
{ let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
  assume IH: LeanListPerm B (Lean_List_map A B f xs) (Lean_List_map A B f ys).
  rewrite LeanListMap_cons A B f Hf x Hx xs Hxs. rewrite LeanListMap_cons A B f Hf x Hx ys Hys.
  exact LeanListPerm_cons B (f x) (Hfx x Hx) (Lean_List_map A B f xs) (Lean_List_map_In A B f Hf xs Hxs)
    (Lean_List_map A B f ys) (Lean_List_map_In A B f Hf ys Hys) IH. }
claim Hswap: forall x y :e A, forall xs :e Lean_List A,
  LeanListPerm B (Lean_List_map A B f (Lean_List_cons_node A y (Lean_List_cons_node A x xs)))
    (Lean_List_map A B f (Lean_List_cons_node A x (Lean_List_cons_node A y xs))).
{ let x. assume Hx: x :e A. let y. assume Hy: y :e A. let xs. assume Hxs: xs :e Lean_List A.
  rewrite LeanListMap_cons A B f Hf y Hy (Lean_List_cons_node A x xs) (Lean_List_cons_typed A x Hx xs Hxs).
  rewrite LeanListMap_cons A B f Hf x Hx (Lean_List_cons_node A y xs) (Lean_List_cons_typed A y Hy xs Hxs).
  rewrite LeanListMap_cons A B f Hf x Hx xs Hxs. rewrite LeanListMap_cons A B f Hf y Hy xs Hxs.
  exact LeanListPerm_swap B (f x) (Hfx x Hx) (f y) (Hfx y Hy) (Lean_List_map A B f xs) (Lean_List_map_In A B f Hf xs Hxs). }
claim Htrans: forall xs ys zs :e Lean_List A,
  LeanListPerm B (Lean_List_map A B f xs) (Lean_List_map A B f ys) ->
  LeanListPerm B (Lean_List_map A B f ys) (Lean_List_map A B f zs) ->
  LeanListPerm B (Lean_List_map A B f xs) (Lean_List_map A B f zs).
{ let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A. let zs. assume Hzs: zs :e Lean_List A.
  exact LeanListPerm_trans B (Lean_List_map A B f xs) (Lean_List_map_In A B f Hf xs Hxs)
    (Lean_List_map A B f ys) (Lean_List_map_In A B f Hf ys Hys)
    (Lean_List_map A B f zs) (Lean_List_map_In A B f Hf zs Hzs). }
exact LeanListPerm_ind A (fun xs ys => LeanListPerm B (Lean_List_map A B f xs) (Lean_List_map A B f ys))
  Hnil Hcons Hswap Htrans.
Qed.

(** filter **)

Theorem LeanListFilter_nil : forall A p,
  Lean_List_filter A p (Lean_List_nil_node A) = Lean_List_nil_node A.
let A p.
prove Lean_List_rec A (Lean_List_nil_node A) (Lean_List_filter_method1_0 A p) (Lean_List_nil_node A) = Lean_List_nil_node A.
exact Lean_List_iota0 A (Lean_List_nil_node A) (Lean_List_filter_method1_0 A p).
Qed.

Theorem LeanListFilter_cons : forall A, forall p :e (Pi_ ux :e A, Lean_Bool), forall x :e A, forall xs :e Lean_List A,
  Lean_List_filter A p (Lean_List_cons_node A x xs) =
  Lean_Bool_rec (Lean_List_filter A p xs) (Lean_List_cons_node A x (Lean_List_filter A p xs)) (p x).
let A p. assume Hp: p :e (Pi_ ux :e A, Lean_Bool). let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
prove Lean_List_rec A (Lean_List_nil_node A) (Lean_List_filter_method1_0 A p) (Lean_List_cons_node A x xs) =
  Lean_Bool_rec (Lean_List_rec A (Lean_List_nil_node A) (Lean_List_filter_method1_0 A p) xs)
    (Lean_List_cons_node A x (Lean_List_rec A (Lean_List_nil_node A) (Lean_List_filter_method1_0 A p) xs)) (p x).
rewrite Lean_List_iota1 A (Lean_List_nil_node A) (Lean_List_filter_method1_0 A p) x Hx xs Hxs.
rewrite Lean_List_filter_method1_0_ap A p x Hx.
rewrite Lean_List_filter_method1_1_ap A p x xs Hxs.
rewrite Lean_List_filter_method1_2_ap A p x xs
  (Lean_List_rec A (Lean_List_nil_node A) (Lean_List_filter_method1_0 A p) xs) (Lean_List_filter_In A p Hp xs Hxs).
reflexivity.
Qed.

Theorem LeanListFilter_cons_false : forall A, forall p :e (Pi_ ux :e A, Lean_Bool), forall x :e A, forall xs :e Lean_List A,
  p x = Lean_Bool_false_node ->
  Lean_List_filter A p (Lean_List_cons_node A x xs) = Lean_List_filter A p xs.
let A p. assume Hp: p :e (Pi_ ux :e A, Lean_Bool). let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
assume Hpx: p x = Lean_Bool_false_node.
rewrite LeanListFilter_cons A p Hp x Hx xs Hxs. rewrite Hpx.
exact Lean_Bool_iota0 (Lean_List_filter A p xs) (Lean_List_cons_node A x (Lean_List_filter A p xs)).
Qed.

Theorem LeanListFilter_cons_true : forall A, forall p :e (Pi_ ux :e A, Lean_Bool), forall x :e A, forall xs :e Lean_List A,
  p x = Lean_Bool_true_node ->
  Lean_List_filter A p (Lean_List_cons_node A x xs) = Lean_List_cons_node A x (Lean_List_filter A p xs).
let A p. assume Hp: p :e (Pi_ ux :e A, Lean_Bool). let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
assume Hpx: p x = Lean_Bool_true_node.
rewrite LeanListFilter_cons A p Hp x Hx xs Hxs. rewrite Hpx.
exact Lean_Bool_iota1 (Lean_List_filter A p xs) (Lean_List_cons_node A x (Lean_List_filter A p xs)).
Qed.

Theorem LeanBool_cases : forall b :e Lean_Bool, b = Lean_Bool_false_node \/ b = Lean_Bool_true_node.
exact Lean_Bool_ind (fun b => b = Lean_Bool_false_node \/ b = Lean_Bool_true_node)
  (orIL (Lean_Bool_false_node = Lean_Bool_false_node) (Lean_Bool_false_node = Lean_Bool_true_node) (Lean_eq_refl Lean_Bool_false_node))
  (orIR (Lean_Bool_true_node = Lean_Bool_false_node) (Lean_Bool_true_node = Lean_Bool_true_node) (Lean_eq_refl Lean_Bool_true_node)).
Qed.

Theorem LeanListPerm_filter : forall A, forall p :e (Pi_ ux :e A, Lean_Bool), forall xs ys,
  LeanListPerm A xs ys -> LeanListPerm A (Lean_List_filter A p xs) (Lean_List_filter A p ys).
let A p. assume Hp: p :e (Pi_ ux :e A, Lean_Bool).
claim Hpx: forall x :e A, p x :e Lean_Bool.
{ let x. assume Hx: x :e A. exact ap_Pi A (fun _ => Lean_Bool) p x Hp Hx. }
claim HF: forall xs :e Lean_List A, Lean_List_filter A p xs :e Lean_List A.
{ exact Lean_List_filter_In A p Hp. }
claim Hnil: LeanListPerm A (Lean_List_filter A p (Lean_List_nil_node A)) (Lean_List_filter A p (Lean_List_nil_node A)).
{ rewrite LeanListFilter_nil A p. exact LeanListPerm_nil A. }
claim Hcons: forall x :e A, forall xs ys :e Lean_List A,
  LeanListPerm A (Lean_List_filter A p xs) (Lean_List_filter A p ys) ->
  LeanListPerm A (Lean_List_filter A p (Lean_List_cons_node A x xs)) (Lean_List_filter A p (Lean_List_cons_node A x ys)).
{ let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
  assume IH: LeanListPerm A (Lean_List_filter A p xs) (Lean_List_filter A p ys).
  apply LeanBool_cases (p x) (Hpx x Hx).
  - assume Hf: p x = Lean_Bool_false_node.
    rewrite LeanListFilter_cons_false A p Hp x Hx xs Hxs Hf. rewrite LeanListFilter_cons_false A p Hp x Hx ys Hys Hf.
    exact IH.
  - assume Ht: p x = Lean_Bool_true_node.
    rewrite LeanListFilter_cons_true A p Hp x Hx xs Hxs Ht. rewrite LeanListFilter_cons_true A p Hp x Hx ys Hys Ht.
    exact LeanListPerm_cons A x Hx (Lean_List_filter A p xs) (HF xs Hxs) (Lean_List_filter A p ys) (HF ys Hys) IH. }
claim Hswap: forall x y :e A, forall xs :e Lean_List A,
  LeanListPerm A (Lean_List_filter A p (Lean_List_cons_node A y (Lean_List_cons_node A x xs)))
    (Lean_List_filter A p (Lean_List_cons_node A x (Lean_List_cons_node A y xs))).
{ let x. assume Hx: x :e A. let y. assume Hy: y :e A. let xs. assume Hxs: xs :e Lean_List A.
  claim Hxxs: Lean_List_cons_node A x xs :e Lean_List A. { exact Lean_List_cons_typed A x Hx xs Hxs. }
  claim Hyxs: Lean_List_cons_node A y xs :e Lean_List A. { exact Lean_List_cons_typed A y Hy xs Hxs. }
  apply LeanBool_cases (p x) (Hpx x Hx).
  - assume Hxf: p x = Lean_Bool_false_node.
    apply LeanBool_cases (p y) (Hpx y Hy).
    + assume Hyf: p y = Lean_Bool_false_node.
      rewrite LeanListFilter_cons_false A p Hp y Hy (Lean_List_cons_node A x xs) Hxxs Hyf.
      rewrite LeanListFilter_cons_false A p Hp x Hx (Lean_List_cons_node A y xs) Hyxs Hxf.
      rewrite LeanListFilter_cons_false A p Hp x Hx xs Hxs Hxf.
      rewrite LeanListFilter_cons_false A p Hp y Hy xs Hxs Hyf.
      exact LeanListPerm_refl A (Lean_List_filter A p xs) (HF xs Hxs).
    + assume Hyt: p y = Lean_Bool_true_node.
      rewrite LeanListFilter_cons_true A p Hp y Hy (Lean_List_cons_node A x xs) Hxxs Hyt.
      rewrite LeanListFilter_cons_false A p Hp x Hx (Lean_List_cons_node A y xs) Hyxs Hxf.
      rewrite LeanListFilter_cons_false A p Hp x Hx xs Hxs Hxf.
      rewrite LeanListFilter_cons_true A p Hp y Hy xs Hxs Hyt.
      exact LeanListPerm_refl A (Lean_List_cons_node A y (Lean_List_filter A p xs))
        (Lean_List_cons_typed A y Hy (Lean_List_filter A p xs) (HF xs Hxs)).
  - assume Hxt: p x = Lean_Bool_true_node.
    apply LeanBool_cases (p y) (Hpx y Hy).
    + assume Hyf: p y = Lean_Bool_false_node.
      rewrite LeanListFilter_cons_false A p Hp y Hy (Lean_List_cons_node A x xs) Hxxs Hyf.
      rewrite LeanListFilter_cons_true A p Hp x Hx (Lean_List_cons_node A y xs) Hyxs Hxt.
      rewrite LeanListFilter_cons_true A p Hp x Hx xs Hxs Hxt.
      rewrite LeanListFilter_cons_false A p Hp y Hy xs Hxs Hyf.
      exact LeanListPerm_refl A (Lean_List_cons_node A x (Lean_List_filter A p xs))
        (Lean_List_cons_typed A x Hx (Lean_List_filter A p xs) (HF xs Hxs)).
    + assume Hyt: p y = Lean_Bool_true_node.
      rewrite LeanListFilter_cons_true A p Hp y Hy (Lean_List_cons_node A x xs) Hxxs Hyt.
      rewrite LeanListFilter_cons_true A p Hp x Hx (Lean_List_cons_node A y xs) Hyxs Hxt.
      rewrite LeanListFilter_cons_true A p Hp x Hx xs Hxs Hxt.
      rewrite LeanListFilter_cons_true A p Hp y Hy xs Hxs Hyt.
      exact LeanListPerm_swap A x Hx y Hy (Lean_List_filter A p xs) (HF xs Hxs). }
claim Htrans: forall xs ys zs :e Lean_List A,
  LeanListPerm A (Lean_List_filter A p xs) (Lean_List_filter A p ys) ->
  LeanListPerm A (Lean_List_filter A p ys) (Lean_List_filter A p zs) ->
  LeanListPerm A (Lean_List_filter A p xs) (Lean_List_filter A p zs).
{ let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A. let zs. assume Hzs: zs :e Lean_List A.
  exact LeanListPerm_trans A (Lean_List_filter A p xs) (HF xs Hxs) (Lean_List_filter A p ys) (HF ys Hys)
    (Lean_List_filter A p zs) (HF zs Hzs). }
exact LeanListPerm_ind A (fun xs ys => LeanListPerm A (Lean_List_filter A p xs) (Lean_List_filter A p ys))
  Hnil Hcons Hswap Htrans.
Qed.

(** foldr **)

Theorem LeanListFoldr_cons : forall A B, forall f :e (Pi_ ux :e A, (Pi_ ux :e B, B)), forall b :e B,
  forall x :e A, forall xs :e Lean_List A,
  Lean_List_foldr A B f b (Lean_List_cons_node A x xs) = f x (Lean_List_foldr A B f b xs).
let A B f. assume Hf: f :e (Pi_ ux :e A, (Pi_ ux :e B, B)). let b. assume Hb: b :e B.
let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
prove Lean_List_rec A b (Lean_List_foldr_method1_0 A B f b) (Lean_List_cons_node A x xs) =
  f x (Lean_List_rec A b (Lean_List_foldr_method1_0 A B f b) xs).
rewrite Lean_List_iota1 A b (Lean_List_foldr_method1_0 A B f b) x Hx xs Hxs.
rewrite Lean_List_foldr_method1_0_ap A B f b x Hx.
rewrite Lean_List_foldr_method1_1_ap A B f b x xs Hxs.
rewrite Lean_List_foldr_method1_2_ap A B f b x xs
  (Lean_List_rec A b (Lean_List_foldr_method1_0 A B f b) xs) (Lean_List_foldr_In A B f Hf b Hb xs Hxs).
reflexivity.
Qed.

Theorem LeanListPerm_foldr : forall A B, forall f :e (Pi_ ux :e A, (Pi_ ux :e B, B)),
  (forall x y :e A, forall value :e B, f y (f x value) = f x (f y value)) ->
  forall b :e B, forall xs ys, LeanListPerm A xs ys ->
  Lean_List_foldr A B f b xs = Lean_List_foldr A B f b ys.
let A B f. assume Hf: f :e (Pi_ ux :e A, (Pi_ ux :e B, B)).
assume Hcomm: forall x y :e A, forall value :e B, f y (f x value) = f x (f y value).
let b. assume Hb: b :e B.
exact LeanListPerm_observer A B (Lean_List_foldr A B f b) (fun x value => f x value)
  (Lean_List_foldr_In A B f Hf b Hb) (LeanListFoldr_cons A B f Hf b Hb) Hcomm.
Qed.
