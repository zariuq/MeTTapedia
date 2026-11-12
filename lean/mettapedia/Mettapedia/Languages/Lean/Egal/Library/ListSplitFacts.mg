(** Lean's List.splitAt: the lengths of its two parts.

    List.reverseAux, List.splitAt.go and List.splitAt are the generated
    readings of Lean's definitions.  Their constructor equations are restated
    here for a type argument that is any set (the generated equation theorems
    keep Lean's universe binders).  A list of length k + d is split at k into
    a list of length k and a list of length d; at half its length, rounded
    up, into the two halves that Lean's merge sort recurses on. **)

Theorem ListSplit_add_zero : forall k, nat_p k -> forall d, nat_p d -> add_nat k d = 0 -> k = 0 /\ d = 0.
let k. assume Hk: nat_p k. let d. assume Hd: nat_p d. assume H: add_nat k d = 0.
apply nat_inv d Hd.
- assume Hd0: d = 0.
  apply andI.
  + prove k = 0.
    claim L1: add_nat k d = k.
    { rewrite Hd0. exact add_nat_0R k. }
    rewrite <- L1. exact H.
  + exact Hd0.
- assume Hex: exists x, nat_p x /\ d = ordsucc x.
  apply Hex. let x. assume Hx: nat_p x /\ d = ordsucc x.
  apply Hx. assume Hx1: nat_p x. assume Hx2: d = ordsucc x.
  apply FalseE.
  apply neq_ordsucc_0 (add_nat k x).
  prove ordsucc (add_nat k x) = 0.
  rewrite <- add_nat_SR k x Hx1.
  rewrite <- Hx2.
  exact H.
Qed.

Theorem ListSplit_double : forall q, nat_p q -> mul_nat q 2 = add_nat q q.
let q. assume Hq: nat_p q.
prove mul_nat q (ordsucc 1) = add_nat q q.
rewrite mul_nat_SR q 1 nat_1.
prove add_nat q (mul_nat q (ordsucc 0)) = add_nat q q.
rewrite mul_nat_SR q 0 nat_0.
rewrite mul_nat_0R q.
rewrite add_nat_0R q.
reflexivity.
Qed.

(** length of a longer list, in numerals **)

Theorem LeanListLength_cons_num : forall A, forall x :e A, forall xs :e Lean_List A, forall n, nat_p n ->
  Lean_List_length A xs = LeanNum n ->
  Lean_List_length A (Lean_List_cons_node A x xs) = LeanNum (ordsucc n).
let A x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A. let n. assume Hn: nat_p n.
assume H: Lean_List_length A xs = LeanNum n.
rewrite LeanListLength_cons A x Hx xs Hxs.
rewrite H.
rewrite LeanNum_add n Hn 1 nat_1.
prove LeanNum (add_nat n (ordsucc 0)) = LeanNum (ordsucc n).
rewrite add_nat_SR n 0 nat_0.
rewrite add_nat_0R n.
reflexivity.
Qed.

(** reverseAux **)

Theorem LeanListReverseAux_nil : forall A, forall ys :e Lean_List A,
  Lean_List_reverseAux A (Lean_List_nil_node A) ys = ys.
let A ys. assume Hys: ys :e Lean_List A.
prove Lean_List_rec A (Lean_List_reverseAux_method0_0 A) (Lean_List_reverseAux_method1_0 A) (Lean_List_nil_node A) ys = ys.
rewrite Lean_List_iota0 A (Lean_List_reverseAux_method0_0 A) (Lean_List_reverseAux_method1_0 A).
exact Lean_List_reverseAux_method0_0_ap A ys Hys.
Qed.

Theorem LeanListReverseAux_cons : forall A, forall x :e A, forall xs :e Lean_List A, forall ys :e Lean_List A,
  Lean_List_reverseAux A (Lean_List_cons_node A x xs) ys
    = Lean_List_reverseAux A xs (Lean_List_cons_node A x ys).
let A x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
prove Lean_List_rec A (Lean_List_reverseAux_method0_0 A) (Lean_List_reverseAux_method1_0 A) (Lean_List_cons_node A x xs) ys
  = Lean_List_rec A (Lean_List_reverseAux_method0_0 A) (Lean_List_reverseAux_method1_0 A) xs (Lean_List_cons_node A x ys).
rewrite Lean_List_iota1 A (Lean_List_reverseAux_method0_0 A) (Lean_List_reverseAux_method1_0 A) x Hx xs Hxs.
rewrite Lean_List_reverseAux_method1_0_ap A x Hx.
rewrite Lean_List_reverseAux_method1_1_ap A x xs Hxs.
rewrite Lean_List_reverseAux_method1_2_ap A x xs
  (Lean_List_rec A (Lean_List_reverseAux_method0_0 A) (Lean_List_reverseAux_method1_0 A) xs)
  (Lean_List_reverseAux_recIn A xs Hxs).
rewrite Lean_List_reverseAux_method1_3_ap A x xs
  (Lean_List_rec A (Lean_List_reverseAux_method0_0 A) (Lean_List_reverseAux_method1_0 A) xs) ys Hys.
reflexivity.
Qed.

Theorem LeanListReverseAux_length : forall A, forall xs :e Lean_List A, forall ys :e Lean_List A,
  forall m, nat_p m -> forall n, nat_p n ->
  Lean_List_length A xs = LeanNum m -> Lean_List_length A ys = LeanNum n ->
  Lean_List_length A (Lean_List_reverseAux A xs ys) = LeanNum (add_nat m n).
let A.
apply Lean_List_ind A (fun xs => forall ys :e Lean_List A, forall m, nat_p m -> forall n, nat_p n ->
  Lean_List_length A xs = LeanNum m -> Lean_List_length A ys = LeanNum n ->
  Lean_List_length A (Lean_List_reverseAux A xs ys) = LeanNum (add_nat m n)).
- let ys. assume Hys: ys :e Lean_List A. let m. assume Hm: nat_p m. let n. assume Hn: nat_p n.
  assume H1: Lean_List_length A (Lean_List_nil_node A) = LeanNum m.
  assume H2: Lean_List_length A ys = LeanNum n.
  claim Lm: m = 0.
  { apply LeanNum_inj m Hm 0 nat_0.
    prove LeanNum m = LeanNum 0.
    rewrite <- H1. exact LeanListLength_nil A. }
  rewrite LeanListReverseAux_nil A ys Hys.
  rewrite Lm.
  rewrite add_nat_0L n Hn.
  exact H2.
- let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
  assume IH: forall ys :e Lean_List A, forall m, nat_p m -> forall n, nat_p n ->
    Lean_List_length A xs = LeanNum m -> Lean_List_length A ys = LeanNum n ->
    Lean_List_length A (Lean_List_reverseAux A xs ys) = LeanNum (add_nat m n).
  let ys. assume Hys: ys :e Lean_List A. let m. assume Hm: nat_p m. let n. assume Hn: nat_p n.
  assume H1: Lean_List_length A (Lean_List_cons_node A x xs) = LeanNum m.
  assume H2: Lean_List_length A ys = LeanNum n.
  apply Lean_Nat_num (Lean_List_length A xs) (Lean_List_length_In A xs Hxs).
  let k. assume Hk: nat_p k /\ Lean_List_length A xs = LeanNum k.
  apply Hk. assume Hk1: nat_p k. assume Hk2: Lean_List_length A xs = LeanNum k.
  claim Lm: m = ordsucc k.
  { apply LeanNum_inj m Hm (ordsucc k) (nat_ordsucc k Hk1).
    prove LeanNum m = LeanNum (ordsucc k).
    rewrite <- H1. exact LeanListLength_cons_num A x Hx xs Hxs k Hk1 Hk2. }
  rewrite LeanListReverseAux_cons A x Hx xs Hxs ys Hys.
  rewrite Lm.
  prove Lean_List_length A (Lean_List_reverseAux A xs (Lean_List_cons_node A x ys)) = LeanNum (add_nat (ordsucc k) n).
  rewrite add_nat_SL k Hk1 n Hn.
  rewrite <- add_nat_SR k n Hn.
  exact IH (Lean_List_cons_node A x ys) (Lean_List_cons_typed A x Hx ys Hys) k Hk1 (ordsucc n) (nat_ordsucc n Hn)
    Hk2 (LeanListLength_cons_num A x Hx ys Hys n Hn H2).
Qed.

Theorem LeanListReverse_length : forall A, forall xs :e Lean_List A, forall m, nat_p m ->
  Lean_List_length A xs = LeanNum m -> Lean_List_length A (Lean_List_reverse A xs) = LeanNum m.
let A xs. assume Hxs: xs :e Lean_List A. let m. assume Hm: nat_p m.
assume H: Lean_List_length A xs = LeanNum m.
claim L: Lean_List_length A (Lean_List_reverseAux A xs (Lean_List_nil_node A)) = LeanNum (add_nat m 0).
{ exact LeanListReverseAux_length A xs Hxs (Lean_List_nil_node A) (Lean_List_nil_typed A) m Hm 0 nat_0
    H (LeanListLength_nil A). }
prove Lean_List_length A (Lean_List_reverseAux A xs (Lean_List_nil_node A)) = LeanNum m.
rewrite L.
rewrite add_nat_0R m.
reflexivity.
Qed.

(** splitAt.go **)

Theorem LeanListSplitAt_go_nil : forall A, forall l :e Lean_List A, forall k :e Lean_Nat, forall acc :e Lean_List A,
  Lean_List_splitAt_go A l (Lean_List_nil_node A) k acc
    = Lean_Prod_mk_node (Lean_List A) (Lean_List A) l (Lean_List_nil_node A).
let A l. assume Hl: l :e Lean_List A. let k. assume Hk: k :e Lean_Nat. let acc. assume Hacc: acc :e Lean_List A.
prove Lean_List_rec A (Lean_List_splitAt_go_method0_0 A l) (Lean_List_splitAt_go_method1_0 A l) (Lean_List_nil_node A) k acc
  = Lean_Prod_mk_node (Lean_List A) (Lean_List A) l (Lean_List_nil_node A).
rewrite Lean_List_iota0 A (Lean_List_splitAt_go_method0_0 A l) (Lean_List_splitAt_go_method1_0 A l).
rewrite Lean_List_splitAt_go_method0_0_ap A l k Hk.
exact Lean_List_splitAt_go_method0_1_ap A l k acc Hacc.
Qed.

Theorem LeanListSplitAt_go_cons : forall A, forall l :e Lean_List A, forall x :e A, forall xs :e Lean_List A,
  forall k :e Lean_Nat, forall acc :e Lean_List A,
  Lean_List_splitAt_go A l (Lean_List_cons_node A x xs) k acc
    = Lean_Nat_casesOn
        (Lean_Prod_mk_node (Lean_List A) (Lean_List A) (Lean_List_reverse A acc) (Lean_List_cons_node A x xs))
        (fun c :e Lean_Nat => Lean_List_splitAt_go A l xs c (Lean_List_cons_node A x acc)) k.
let A l. assume Hl: l :e Lean_List A. let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
let k. assume Hk: k :e Lean_Nat. let acc. assume Hacc: acc :e Lean_List A.
prove Lean_List_rec A (Lean_List_splitAt_go_method0_0 A l) (Lean_List_splitAt_go_method1_0 A l) (Lean_List_cons_node A x xs) k acc
  = Lean_Nat_casesOn
      (Lean_Prod_mk_node (Lean_List A) (Lean_List A) (Lean_List_reverse A acc) (Lean_List_cons_node A x xs))
      (fun c :e Lean_Nat => Lean_List_rec A (Lean_List_splitAt_go_method0_0 A l) (Lean_List_splitAt_go_method1_0 A l) xs c (Lean_List_cons_node A x acc)) k.
rewrite Lean_List_iota1 A (Lean_List_splitAt_go_method0_0 A l) (Lean_List_splitAt_go_method1_0 A l) x Hx xs Hxs.
rewrite Lean_List_splitAt_go_method1_0_ap A l x Hx.
rewrite Lean_List_splitAt_go_method1_1_ap A l x xs Hxs.
rewrite Lean_List_splitAt_go_method1_2_ap A l x xs
  (Lean_List_rec A (Lean_List_splitAt_go_method0_0 A l) (Lean_List_splitAt_go_method1_0 A l) xs)
  (Lean_List_splitAt_go_recIn A l Hl xs Hxs).
rewrite Lean_List_splitAt_go_method1_3_ap A l x xs
  (Lean_List_rec A (Lean_List_splitAt_go_method0_0 A l) (Lean_List_splitAt_go_method1_0 A l) xs) k Hk.
rewrite Lean_List_splitAt_go_method1_4_ap A l x xs
  (Lean_List_rec A (Lean_List_splitAt_go_method0_0 A l) (Lean_List_splitAt_go_method1_0 A l) xs) k acc Hacc.
reflexivity.
Qed.

Theorem LeanListSplitAt_go_cons_zero : forall A, forall l :e Lean_List A, forall x :e A, forall xs :e Lean_List A,
  forall acc :e Lean_List A,
  Lean_List_splitAt_go A l (Lean_List_cons_node A x xs) (LeanNum 0) acc
    = Lean_Prod_mk_node (Lean_List A) (Lean_List A) (Lean_List_reverse A acc) (Lean_List_cons_node A x xs).
let A l. assume Hl: l :e Lean_List A. let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
let acc. assume Hacc: acc :e Lean_List A.
rewrite LeanListSplitAt_go_cons A l Hl x Hx xs Hxs (LeanNum 0) (LeanNum_In 0 nat_0) acc Hacc.
rewrite LeanNum_0.
exact Lean_Nat_casesOn_iota0
  (Lean_Prod_mk_node (Lean_List A) (Lean_List A) (Lean_List_reverse A acc) (Lean_List_cons_node A x xs))
  (fun c :e Lean_Nat => Lean_List_splitAt_go A l xs c (Lean_List_cons_node A x acc)).
Qed.

Theorem LeanListSplitAt_go_cons_succ : forall A, forall l :e Lean_List A, forall x :e A, forall xs :e Lean_List A,
  forall k, nat_p k -> forall acc :e Lean_List A,
  Lean_List_splitAt_go A l (Lean_List_cons_node A x xs) (LeanNum (ordsucc k)) acc
    = Lean_List_splitAt_go A l xs (LeanNum k) (Lean_List_cons_node A x acc).
let A l. assume Hl: l :e Lean_List A. let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
let k. assume Hk: nat_p k. let acc. assume Hacc: acc :e Lean_List A.
rewrite LeanNum_S k Hk.
rewrite LeanListSplitAt_go_cons A l Hl x Hx xs Hxs (Lean_Nat_succ_node (LeanNum k))
  (Lean_Nat_succ_typed (LeanNum k) (LeanNum_In k Hk)) acc Hacc.
rewrite Lean_Nat_casesOn_iota1
  (Lean_Prod_mk_node (Lean_List A) (Lean_List A) (Lean_List_reverse A acc) (Lean_List_cons_node A x xs))
  (fun c :e Lean_Nat => Lean_List_splitAt_go A l xs c (Lean_List_cons_node A x acc))
  (LeanNum k) (LeanNum_In k Hk).
exact beta Lean_Nat (fun c => Lean_List_splitAt_go A l xs c (Lean_List_cons_node A x acc)) (LeanNum k) (LeanNum_In k Hk).
Qed.

(** A list of length k + d, split at k while acc (of length a) holds what was
    passed: the first part has length a + k, the second length d. **)
Theorem LeanListSplitAt_go_lengths : forall A, forall l :e Lean_List A, forall xs :e Lean_List A,
  forall k, nat_p k -> forall d, nat_p d -> forall acc :e Lean_List A, forall a, nat_p a ->
  Lean_List_length A xs = LeanNum (add_nat k d) ->
  Lean_List_length A acc = LeanNum a ->
  Lean_List_length A l = LeanNum (add_nat a (add_nat k d)) ->
  Lean_List_length A (Lean_Prod_fst (Lean_List A) (Lean_List A) (Lean_List_splitAt_go A l xs (LeanNum k) acc)) = LeanNum (add_nat a k)
  /\ Lean_List_length A (Lean_Prod_snd (Lean_List A) (Lean_List A) (Lean_List_splitAt_go A l xs (LeanNum k) acc)) = LeanNum d.
let A l. assume Hl: l :e Lean_List A.
apply Lean_List_ind A (fun xs =>
  forall k, nat_p k -> forall d, nat_p d -> forall acc :e Lean_List A, forall a, nat_p a ->
  Lean_List_length A xs = LeanNum (add_nat k d) ->
  Lean_List_length A acc = LeanNum a ->
  Lean_List_length A l = LeanNum (add_nat a (add_nat k d)) ->
  Lean_List_length A (Lean_Prod_fst (Lean_List A) (Lean_List A) (Lean_List_splitAt_go A l xs (LeanNum k) acc)) = LeanNum (add_nat a k)
  /\ Lean_List_length A (Lean_Prod_snd (Lean_List A) (Lean_List A) (Lean_List_splitAt_go A l xs (LeanNum k) acc)) = LeanNum d).
- let k. assume Hk: nat_p k. let d. assume Hd: nat_p d. let acc. assume Hacc: acc :e Lean_List A.
  let a. assume Ha: nat_p a.
  assume H1: Lean_List_length A (Lean_List_nil_node A) = LeanNum (add_nat k d).
  assume H2: Lean_List_length A acc = LeanNum a.
  assume H3: Lean_List_length A l = LeanNum (add_nat a (add_nat k d)).
  claim Lkd: add_nat k d = 0.
  { apply LeanNum_inj (add_nat k d) (add_nat_p k Hk d Hd) 0 nat_0.
    prove LeanNum (add_nat k d) = LeanNum 0.
    rewrite <- H1. exact LeanListLength_nil A. }
  apply ListSplit_add_zero k Hk d Hd Lkd.
  assume Lk: k = 0. assume Ld: d = 0.
  rewrite LeanListSplitAt_go_nil A l Hl (LeanNum k) (LeanNum_In k Hk) acc Hacc.
  apply andI.
  + rewrite Lean_Prod_fst_mk (Lean_List A) (Lean_List A) l Hl (Lean_List_nil_node A) (Lean_List_nil_typed A).
    prove Lean_List_length A l = LeanNum (add_nat a k).
    rewrite H3. rewrite Lkd. rewrite Lk. reflexivity.
  + rewrite Lean_Prod_snd_mk (Lean_List A) (Lean_List A) l Hl (Lean_List_nil_node A) (Lean_List_nil_typed A).
    prove Lean_List_length A (Lean_List_nil_node A) = LeanNum d.
    rewrite Ld. exact LeanListLength_nil A.
- let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
  assume IH: forall k, nat_p k -> forall d, nat_p d -> forall acc :e Lean_List A, forall a, nat_p a ->
    Lean_List_length A xs = LeanNum (add_nat k d) ->
    Lean_List_length A acc = LeanNum a ->
    Lean_List_length A l = LeanNum (add_nat a (add_nat k d)) ->
    Lean_List_length A (Lean_Prod_fst (Lean_List A) (Lean_List A) (Lean_List_splitAt_go A l xs (LeanNum k) acc)) = LeanNum (add_nat a k)
    /\ Lean_List_length A (Lean_Prod_snd (Lean_List A) (Lean_List A) (Lean_List_splitAt_go A l xs (LeanNum k) acc)) = LeanNum d.
  let k. assume Hk: nat_p k. let d. assume Hd: nat_p d. let acc. assume Hacc: acc :e Lean_List A.
  let a. assume Ha: nat_p a.
  assume H1: Lean_List_length A (Lean_List_cons_node A x xs) = LeanNum (add_nat k d).
  assume H2: Lean_List_length A acc = LeanNum a.
  assume H3: Lean_List_length A l = LeanNum (add_nat a (add_nat k d)).
  apply Lean_Nat_num (Lean_List_length A xs) (Lean_List_length_In A xs Hxs).
  let n. assume Hn: nat_p n /\ Lean_List_length A xs = LeanNum n.
  apply Hn. assume Hn1: nat_p n. assume Hn2: Lean_List_length A xs = LeanNum n.
  claim Lsum: ordsucc n = add_nat k d.
  { apply LeanNum_inj (ordsucc n) (nat_ordsucc n Hn1) (add_nat k d) (add_nat_p k Hk d Hd).
    prove LeanNum (ordsucc n) = LeanNum (add_nat k d).
    rewrite <- H1. symmetry.
    exact LeanListLength_cons_num A x Hx xs Hxs n Hn1 Hn2. }
  apply nat_inv k Hk.
  + assume Hk0: k = 0.
    rewrite Hk0.
    rewrite LeanListSplitAt_go_cons_zero A l Hl x Hx xs Hxs acc Hacc.
    apply andI.
    * rewrite Lean_Prod_fst_mk (Lean_List A) (Lean_List A) (Lean_List_reverse A acc) (Lean_List_reverse_In A acc Hacc)
        (Lean_List_cons_node A x xs) (Lean_List_cons_typed A x Hx xs Hxs).
      rewrite add_nat_0R a.
      exact LeanListReverse_length A acc Hacc a Ha H2.
    * rewrite Lean_Prod_snd_mk (Lean_List A) (Lean_List A) (Lean_List_reverse A acc) (Lean_List_reverse_In A acc Hacc)
        (Lean_List_cons_node A x xs) (Lean_List_cons_typed A x Hx xs Hxs).
      prove Lean_List_length A (Lean_List_cons_node A x xs) = LeanNum d.
      rewrite H1. rewrite Hk0. rewrite add_nat_0L d Hd. reflexivity.
  + assume Hex: exists j, nat_p j /\ k = ordsucc j.
    apply Hex. let j. assume Hj: nat_p j /\ k = ordsucc j.
    apply Hj. assume Hj1: nat_p j. assume Hj2: k = ordsucc j.
    claim Ln: n = add_nat j d.
    { apply ordsucc_inj n (add_nat j d).
      prove ordsucc n = ordsucc (add_nat j d).
      rewrite <- add_nat_SL j Hj1 d Hd.
      rewrite <- Hj2.
      exact Lsum. }
    rewrite Hj2.
    rewrite LeanListSplitAt_go_cons_succ A l Hl x Hx xs Hxs j Hj1 acc Hacc.
    rewrite add_nat_SR a j Hj1.
    rewrite <- add_nat_SL a Ha j Hj1.
    apply IH j Hj1 d Hd (Lean_List_cons_node A x acc) (Lean_List_cons_typed A x Hx acc Hacc) (ordsucc a) (nat_ordsucc a Ha).
    * prove Lean_List_length A xs = LeanNum (add_nat j d).
      rewrite <- Ln. exact Hn2.
    * exact LeanListLength_cons_num A x Hx acc Hacc a Ha H2.
    * prove Lean_List_length A l = LeanNum (add_nat (ordsucc a) (add_nat j d)).
      rewrite H3. rewrite Hj2.
      rewrite add_nat_SL j Hj1 d Hd.
      rewrite add_nat_SR a (add_nat j d) (add_nat_p j Hj1 d Hd).
      rewrite add_nat_SL a Ha (add_nat j d) (add_nat_p j Hj1 d Hd).
      reflexivity.
Qed.

(** splitAt **)

Theorem LeanListSplitAt_lengths : forall A, forall l :e Lean_List A, forall k, nat_p k -> forall d, nat_p d ->
  Lean_List_length A l = LeanNum (add_nat k d) ->
  Lean_List_length A (Lean_Prod_fst (Lean_List A) (Lean_List A) (Lean_List_splitAt A (LeanNum k) l)) = LeanNum k
  /\ Lean_List_length A (Lean_Prod_snd (Lean_List A) (Lean_List A) (Lean_List_splitAt A (LeanNum k) l)) = LeanNum d.
let A l. assume Hl: l :e Lean_List A. let k. assume Hk: nat_p k. let d. assume Hd: nat_p d.
assume H: Lean_List_length A l = LeanNum (add_nat k d).
claim L: Lean_List_length A (Lean_Prod_fst (Lean_List A) (Lean_List A) (Lean_List_splitAt_go A l l (LeanNum k) (Lean_List_nil_node A))) = LeanNum (add_nat 0 k)
  /\ Lean_List_length A (Lean_Prod_snd (Lean_List A) (Lean_List A) (Lean_List_splitAt_go A l l (LeanNum k) (Lean_List_nil_node A))) = LeanNum d.
{ apply LeanListSplitAt_go_lengths A l Hl l Hl k Hk d Hd (Lean_List_nil_node A) (Lean_List_nil_typed A) 0 nat_0 H
    (LeanListLength_nil A).
  prove Lean_List_length A l = LeanNum (add_nat 0 (add_nat k d)).
  rewrite add_nat_0L (add_nat k d) (add_nat_p k Hk d Hd).
  exact H. }
apply L.
assume L1: Lean_List_length A (Lean_Prod_fst (Lean_List A) (Lean_List A) (Lean_List_splitAt_go A l l (LeanNum k) (Lean_List_nil_node A))) = LeanNum (add_nat 0 k).
assume L2: Lean_List_length A (Lean_Prod_snd (Lean_List A) (Lean_List A) (Lean_List_splitAt_go A l l (LeanNum k) (Lean_List_nil_node A))) = LeanNum d.
apply andI.
- prove Lean_List_length A (Lean_Prod_fst (Lean_List A) (Lean_List A) (Lean_List_splitAt_go A l l (LeanNum k) (Lean_List_nil_node A))) = LeanNum k.
  rewrite L1.
  rewrite add_nat_0L k Hk.
  reflexivity.
- exact L2.
Qed.

(** The two halves of a number: n = p + q with p = (n + 1) / 2 and q = n / 2,
    and p is q or its successor. **)
Theorem LeanNat_halves : forall k, nat_p k ->
  exists p, nat_p p /\ (exists q, nat_p q /\ (k = add_nat p q
    /\ ((q c= p /\ p c= ordsucc q)
    /\ (Lean_Nat_div (Lean_Nat_add (LeanNum k) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum k) (LeanNum 2) = LeanNum q)))).
let k. assume Hk: nat_p k.
apply nat_euclid 1 nat_1 k Hk.
let q. assume Hq: nat_p q /\ (exists r, nat_p r /\ (r :e ordsucc 1 /\ k = add_nat (mul_nat q (ordsucc 1)) r)).
apply Hq. assume Hq1: nat_p q.
assume Hq2: exists r, nat_p r /\ (r :e ordsucc 1 /\ k = add_nat (mul_nat q (ordsucc 1)) r).
apply Hq2. let r. assume Hr: nat_p r /\ (r :e ordsucc 1 /\ k = add_nat (mul_nat q (ordsucc 1)) r).
apply Hr. assume Hr1: nat_p r. assume Hr2: r :e ordsucc 1 /\ k = add_nat (mul_nat q (ordsucc 1)) r.
apply Hr2. assume Hr3: r :e ordsucc 1. assume Hr4: k = add_nat (mul_nat q (ordsucc 1)) r.
claim Lqq: nat_p (mul_nat q (ordsucc 1)).
{ exact mul_nat_p q Hq1 (ordsucc 1) nat_2. }
claim Ladd: Lean_Nat_add (LeanNum k) (LeanNum 1) = LeanNum (ordsucc k).
{ rewrite LeanNum_add k Hk 1 nat_1.
  prove LeanNum (add_nat k (ordsucc 0)) = LeanNum (ordsucc k).
  rewrite add_nat_SR k 0 nat_0.
  rewrite add_nat_0R k.
  reflexivity. }
apply ordsuccE 1 r Hr3.
- assume Hr5: r :e 1.
  claim Lr: r = 0.
  { apply ordsuccE 0 r Hr5.
    - assume Hr6: r :e 0. apply FalseE. exact EmptyE r Hr6.
    - assume Hr6: r = 0. exact Hr6. }
  claim Lk: k = add_nat (mul_nat q (ordsucc 1)) 0.
  { rewrite Hr4. rewrite Lr. reflexivity. }
  witness q. apply andI.
  + exact Hq1.
  + witness q. apply andI.
    * exact Hq1.
    * apply andI.
      { prove k = add_nat q q.
        rewrite <- ListSplit_double q Hq1.
        rewrite <- add_nat_0R (mul_nat q 2).
        exact Lk. }
      apply andI.
      { apply andI.
        - exact Subq_ref q.
        - exact ordsuccI1 q. }
      apply andI.
      { rewrite Ladd.
        claim Lk1: ordsucc k = add_nat (mul_nat q (ordsucc 1)) 1.
        { rewrite Lk.
          rewrite add_nat_0R (mul_nat q (ordsucc 1)).
          prove ordsucc (mul_nat q (ordsucc 1)) = add_nat (mul_nat q (ordsucc 1)) (ordsucc 0).
          rewrite add_nat_SR (mul_nat q (ordsucc 1)) 0 nat_0.
          rewrite add_nat_0R (mul_nat q (ordsucc 1)).
          reflexivity. }
        rewrite Lk1.
        exact Lean_Nat_div_num 1 nat_1 1 nat_1 In_1_2 q Hq1. }
      { rewrite Lk.
        exact Lean_Nat_div_num 1 nat_1 0 nat_0 In_0_2 q Hq1. }
- assume Hr5: r = 1.
  claim Lk: k = add_nat (mul_nat q (ordsucc 1)) 1.
  { rewrite Hr4. rewrite Hr5. reflexivity. }
  claim Lk0: k = ordsucc (mul_nat q (ordsucc 1)).
  { rewrite Lk.
    prove add_nat (mul_nat q (ordsucc 1)) (ordsucc 0) = ordsucc (mul_nat q (ordsucc 1)).
    rewrite add_nat_SR (mul_nat q (ordsucc 1)) 0 nat_0.
    rewrite add_nat_0R (mul_nat q (ordsucc 1)).
    reflexivity. }
  witness (ordsucc q). apply andI.
  + exact nat_ordsucc q Hq1.
  + witness q. apply andI.
    * exact Hq1.
    * apply andI.
      { prove k = add_nat (ordsucc q) q.
        rewrite add_nat_SL q Hq1 q Hq1.
        rewrite <- ListSplit_double q Hq1.
        exact Lk0. }
      apply andI.
      { apply andI.
        - exact ordsuccI1 q.
        - exact Subq_ref (ordsucc q). }
      apply andI.
      { rewrite Ladd.
        claim Lk1: ordsucc k = add_nat (mul_nat (ordsucc q) (ordsucc 1)) 0.
        { rewrite add_nat_0R (mul_nat (ordsucc q) (ordsucc 1)).
          rewrite mul_nat_SL q Hq1 (ordsucc 1) nat_2.
          prove ordsucc k = add_nat (mul_nat q (ordsucc 1)) (ordsucc (ordsucc 0)).
          rewrite add_nat_SR (mul_nat q (ordsucc 1)) (ordsucc 0) nat_1.
          rewrite add_nat_SR (mul_nat q (ordsucc 1)) 0 nat_0.
          rewrite add_nat_0R (mul_nat q (ordsucc 1)).
          prove ordsucc k = ordsucc (ordsucc (mul_nat q (ordsucc 1))).
          rewrite <- Lk0.
          reflexivity. }
        rewrite Lk1.
        exact Lean_Nat_div_num 1 nat_1 0 nat_0 In_0_2 (ordsucc q) (nat_ordsucc q Hq1). }
      { rewrite Lk.
        exact Lean_Nat_div_num 1 nat_1 1 nat_1 In_1_2 q Hq1. }
Qed.

(** A list of length n, split at (n + 1) / 2: Lean's two halves. **)
Theorem LeanListSplitAt_halves : forall A, forall n :e Lean_Nat, forall l :e Lean_List A,
  Lean_List_length A l = n ->
  Lean_List_length A (Lean_Prod_fst (Lean_List A) (Lean_List A)
      (Lean_List_splitAt A (Lean_Nat_div (Lean_Nat_add n (LeanNum 1)) (LeanNum 2)) l))
    = Lean_Nat_div (Lean_Nat_add n (LeanNum 1)) (LeanNum 2)
  /\ Lean_List_length A (Lean_Prod_snd (Lean_List A) (Lean_List A)
      (Lean_List_splitAt A (Lean_Nat_div (Lean_Nat_add n (LeanNum 1)) (LeanNum 2)) l))
    = Lean_Nat_div n (LeanNum 2).
let A n. assume Hn: n :e Lean_Nat. let l. assume Hl: l :e Lean_List A.
assume H: Lean_List_length A l = n.
apply Lean_Nat_num n Hn.
let k. assume Hk: nat_p k /\ n = LeanNum k.
apply Hk. assume Hk1: nat_p k. assume Hk2: n = LeanNum k.
apply LeanNat_halves k Hk1.
let p. assume Hp: nat_p p /\ (exists q, nat_p q /\ (k = add_nat p q
    /\ ((q c= p /\ p c= ordsucc q)
    /\ (Lean_Nat_div (Lean_Nat_add (LeanNum k) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum k) (LeanNum 2) = LeanNum q)))).
apply Hp. assume Hp1: nat_p p.
assume Hp2: exists q, nat_p q /\ (k = add_nat p q
    /\ ((q c= p /\ p c= ordsucc q)
    /\ (Lean_Nat_div (Lean_Nat_add (LeanNum k) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum k) (LeanNum 2) = LeanNum q))).
apply Hp2. let q. assume Hq: nat_p q /\ (k = add_nat p q
    /\ ((q c= p /\ p c= ordsucc q)
    /\ (Lean_Nat_div (Lean_Nat_add (LeanNum k) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum k) (LeanNum 2) = LeanNum q))).
apply Hq. assume Hq1: nat_p q.
assume Hq2: k = add_nat p q
    /\ ((q c= p /\ p c= ordsucc q)
    /\ (Lean_Nat_div (Lean_Nat_add (LeanNum k) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum k) (LeanNum 2) = LeanNum q)).
apply Hq2. assume Hq3: k = add_nat p q.
assume Hq3b: (q c= p /\ p c= ordsucc q)
    /\ (Lean_Nat_div (Lean_Nat_add (LeanNum k) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum k) (LeanNum 2) = LeanNum q).
apply Hq3b. assume Hq3c: q c= p /\ p c= ordsucc q.
assume Hq4: Lean_Nat_div (Lean_Nat_add (LeanNum k) (LeanNum 1)) (LeanNum 2) = LeanNum p
        /\ Lean_Nat_div (LeanNum k) (LeanNum 2) = LeanNum q.
apply Hq4.
assume Hq5: Lean_Nat_div (Lean_Nat_add (LeanNum k) (LeanNum 1)) (LeanNum 2) = LeanNum p.
assume Hq6: Lean_Nat_div (LeanNum k) (LeanNum 2) = LeanNum q.
rewrite Hk2.
rewrite Hq5.
rewrite Hq6.
apply LeanListSplitAt_lengths A l Hl p Hp1 q Hq1.
prove Lean_List_length A l = LeanNum (add_nat p q).
rewrite <- Hq3.
rewrite <- Hk2.
exact H.
Qed.

(** An element of the lists of length n has length n. **)
Theorem LeanSubtype_length_val : forall A n,
  forall s :e Lean_Subtype (Lean_List A) (fun x :e Lean_List A => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n),
  Lean_List_length A
    (Lean_Subtype_val (Lean_List A) (fun x :e Lean_List A => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n) s) = n.
let A n.
claim L: forall x0 :e Lean_List A,
  forall x1 :e {z :e 1 | z :e ((fun x :e Lean_List A => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n) x0)},
  Lean_List_length A
    (Lean_Subtype_val (Lean_List A) (fun x :e Lean_List A => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n)
      (Lean_Subtype_mk_node (Lean_List A) (fun x :e Lean_List A => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n) x0 x1)) = n.
{ let x0. assume Hx0: x0 :e Lean_List A.
  let x1. assume Hx1: x1 :e {z :e 1 | z :e ((fun x :e Lean_List A => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n) x0)}.
  rewrite Lean_Subtype_val_mk (Lean_List A) (fun x :e Lean_List A => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n) x0 Hx0 x1 Hx1.
  prove Lean_List_length A x0 = n.
  claim L1: x1 :e (fun x :e Lean_List A => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n) x0.
  { exact SepE2 1 (fun z => z :e ((fun x :e Lean_List A => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n) x0)) x1 Hx1. }
  claim L2: x1 :e Lean_Eq_Prop Lean_Nat (Lean_List_length A x0) n.
  { rewrite <- beta (Lean_List A) (fun x => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n) x0 Hx0.
    exact L1. }
  exact LeanEq_sound Lean_Nat (Lean_List_length A x0) n x1 L2. }
exact Lean_Subtype_ind (Lean_List A) (fun x :e Lean_List A => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n)
  (fun s => Lean_List_length A
    (Lean_Subtype_val (Lean_List A) (fun x :e Lean_List A => Lean_Eq_Prop Lean_Nat (Lean_List_length A x) n) s) = n) L.
Qed.
