(** Multisets without duplicates: Lean's Multiset.Nodup at the class of a
    list, the lists List.range n, and filtering.

    Multiset.Nodup, Multiset.ofList, Multiset.range and Multiset.filter are the
    generated readings of Lean's definitions; a multiset is a class of the
    permutation relation. **)

(** Every element of a quotient is the class of some element. **)
Theorem Lean_Quot_rep : forall A relation, forall value :e Lean_Quot A relation,
  forall p:prop, (forall x :e A, value = Lean_Quot_mk A relation x -> p) -> p.
let A relation value. assume Hvalue: value :e Lean_Quot A relation.
let p. assume Hp: forall x :e A, value = Lean_Quot_mk A relation x -> p.
exact ReplE_impred A (LeanQuotClass A (LeanEqvClosure A (fun x y => 0 :e relation x y))) value Hvalue p Hp.
Qed.

(** The permutation relation as Lean's multisets take it. **)
Definition LeanPermRel : set -> set :=
  fun A => (fun xs :e (Lean_List A) => (fun ys :e (Lean_List A) => Lean_List_Perm_Prop A xs ys)).

Theorem LeanPermRel_ap : forall A, forall xs ys :e Lean_List A,
  (LeanPermRel A) xs ys = Lean_List_Perm_Prop A xs ys.
let A xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
prove (fun xs :e (Lean_List A) => (fun ys :e (Lean_List A) => Lean_List_Perm_Prop A xs ys)) xs ys =
  Lean_List_Perm_Prop A xs ys.
rewrite beta (Lean_List A) (fun xs => (fun ys :e (Lean_List A) => Lean_List_Perm_Prop A xs ys)) xs Hxs.
exact beta (Lean_List A) (fun ys => Lean_List_Perm_Prop A xs ys) ys Hys.
Qed.

Theorem LeanPermRel_perm : forall A, forall xs ys :e Lean_List A,
  0 :e (LeanPermRel A) xs ys -> 0 :e Lean_List_Perm_Prop A xs ys.
let A xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
assume H: 0 :e (LeanPermRel A) xs ys.
exact In_eq_r 0 ((LeanPermRel A) xs ys) (Lean_List_Perm_Prop A xs ys) (LeanPermRel_ap A xs Hxs ys Hys) H.
Qed.

(** Multiset.Nodup at the class of a list is List.Nodup of the list. **)
Theorem LeanMultisetNodup_mk : forall A, forall l :e Lean_List A,
  Lean_Multiset_Nodup A (Lean_Multiset_ofList A l) = Lean_List_Pairwise_Prop A (LeanListNe A) l.
let A l. assume Hl: l :e Lean_List A.
claim Hf: (fun xs :e (Lean_List A) => Lean_List_Pairwise_Prop A (LeanListNe A) xs) :e (Pi_ xs :e (Lean_List A), LeanProp).
{ exact lam_Pi (Lean_List A) (fun _ => LeanProp) (fun xs => Lean_List_Pairwise_Prop A (LeanListNe A) xs)
    (fun xs Hxs => Lean_List_Pairwise_Prop_prop A (LeanListNe A) xs). }
claim Hrespect: forall xs ys :e Lean_List A, 0 :e (LeanPermRel A) xs ys ->
  (fun xs :e (Lean_List A) => Lean_List_Pairwise_Prop A (LeanListNe A) xs) xs =
  (fun xs :e (Lean_List A) => Lean_List_Pairwise_Prop A (LeanListNe A) xs) ys.
{ let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
  assume H: 0 :e (LeanPermRel A) xs ys.
  rewrite beta (Lean_List A) (fun xs => Lean_List_Pairwise_Prop A (LeanListNe A) xs) xs Hxs.
  rewrite beta (Lean_List A) (fun xs => Lean_List_Pairwise_Prop A (LeanListNe A) xs) ys Hys.
  exact Lean_propext_value
    (Lean_List_Pairwise_Prop A (LeanListNe A) xs) (Lean_List_Pairwise_Prop_prop A (LeanListNe A) xs)
    (Lean_List_Pairwise_Prop A (LeanListNe A) ys) (Lean_List_Pairwise_Prop_prop A (LeanListNe A) ys)
    (Lean_List_Perm_nodup_iff_proof A xs Hxs ys Hys (LeanPermRel_perm A xs Hxs ys Hys H)). }
prove Lean_Quot_lift (Lean_List A) (LeanPermRel A) LeanProp
    (fun xs :e (Lean_List A) => Lean_List_Pairwise_Prop A (LeanListNe A) xs) 0
    (Lean_Quot_mk (Lean_List A) (LeanPermRel A) l) = Lean_List_Pairwise_Prop A (LeanListNe A) l.
rewrite Lean_Quot_lift_beta (Lean_List A) (LeanPermRel A) LeanProp
  (fun xs :e (Lean_List A) => Lean_List_Pairwise_Prop A (LeanListNe A) xs) Hf Hrespect 0 l Hl.
exact beta (Lean_List A) (fun xs => Lean_List_Pairwise_Prop A (LeanListNe A) xs) l Hl.
Qed.

(** List.range n has no duplicates: List.range.loop k acc puts the numbers
    below k before acc, so it has none when acc has none and holds only
    numbers from k on. **)
Theorem LeanListRange_loop_nodup : forall k, nat_p k -> forall acc :e Lean_List Lean_Nat,
  LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) acc ->
  (forall j, nat_p j -> LeanListMem Lean_Nat (LeanNum j) acc -> k c= j) ->
  LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) (Lean_List_range_loop (LeanNum k) acc).
claim Hbase: forall acc :e Lean_List Lean_Nat,
  LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) acc ->
  (forall j, nat_p j -> LeanListMem Lean_Nat (LeanNum j) acc -> 0 c= j) ->
  LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) (Lean_List_range_loop (LeanNum 0) acc).
{ let acc. assume Hacc: acc :e Lean_List Lean_Nat.
  assume Hpw: LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) acc.
  assume Hmem: forall j, nat_p j -> LeanListMem Lean_Nat (LeanNum j) acc -> 0 c= j.
  rewrite Lean_List_range_loop_eq_1 acc Hacc. exact Hpw. }
claim Hstep: forall k, nat_p k ->
  (forall acc :e Lean_List Lean_Nat,
    LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) acc ->
    (forall j, nat_p j -> LeanListMem Lean_Nat (LeanNum j) acc -> k c= j) ->
    LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) (Lean_List_range_loop (LeanNum k) acc)) ->
  forall acc :e Lean_List Lean_Nat,
    LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) acc ->
    (forall j, nat_p j -> LeanListMem Lean_Nat (LeanNum j) acc -> ordsucc k c= j) ->
    LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) (Lean_List_range_loop (LeanNum (ordsucc k)) acc).
{ let k. assume Hk: nat_p k.
  assume IH: forall acc :e Lean_List Lean_Nat,
    LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) acc ->
    (forall j, nat_p j -> LeanListMem Lean_Nat (LeanNum j) acc -> k c= j) ->
    LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) (Lean_List_range_loop (LeanNum k) acc).
  let acc. assume Hacc: acc :e Lean_List Lean_Nat.
  assume Hpw: LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) acc.
  assume Hmem: forall j, nat_p j -> LeanListMem Lean_Nat (LeanNum j) acc -> ordsucc k c= j.
  claim HkIn: LeanNum k :e Lean_Nat. { exact LeanNum_In k Hk. }
  claim Hnew: Lean_List_cons_node Lean_Nat (LeanNum k) acc :e Lean_List Lean_Nat.
  { exact Lean_List_cons_typed Lean_Nat (LeanNum k) HkIn acc Hacc. }
  claim Hirr: forall z, k = z -> k :e z -> False.
  { let z. assume E: k = z. rewrite <- E. exact In_irref k. }
  claim Hfresh: forall b :e Lean_Nat, LeanListMem Lean_Nat b acc -> 0 :e (LeanListNe Lean_Nat) (LeanNum k) b.
  { let b. assume Hb: b :e Lean_Nat. assume Hm: LeanListMem Lean_Nat b acc.
    apply Lean_Nat_num b Hb. let j. assume Hj: nat_p j /\ b = LeanNum j.
    apply Hj. assume Hjn: nat_p j. assume Hbj: b = LeanNum j.
    claim Hmj: LeanListMem Lean_Nat (LeanNum j) acc. { rewrite <- Hbj. exact Hm. }
    rewrite Hbj.
    apply LeanListNe_intro Lean_Nat (LeanNum k) HkIn (LeanNum j) (LeanNum_In j Hjn).
    assume Heq: LeanNum k = LeanNum j.
    exact Hirr j (LeanNum_inj k Hk j Hjn Heq) (Hmem j Hjn Hmj k (ordsuccI2 k)). }
  claim Hpw2: LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) (Lean_List_cons_node Lean_Nat (LeanNum k) acc).
  { exact LeanListPairwise_cons Lean_Nat (LeanListNe Lean_Nat) (LeanNum k) HkIn acc Hacc Hfresh Hpw. }
  claim Hmem2: forall j, nat_p j -> LeanListMem Lean_Nat (LeanNum j) (Lean_List_cons_node Lean_Nat (LeanNum k) acc) -> k c= j.
  { let j. assume Hj: nat_p j. assume Hm: LeanListMem Lean_Nat (LeanNum j) (Lean_List_cons_node Lean_Nat (LeanNum k) acc).
    apply LeanListMem_cons_inv Lean_Nat (LeanNum j) (LeanNum k) acc Hm.
    - assume E: LeanNum j = LeanNum k. rewrite LeanNum_inj j Hj k Hk E. exact Subq_ref k.
    - assume Hm2: LeanListMem Lean_Nat (LeanNum j) acc.
      exact Subq_tra k (ordsucc k) j (ordsuccI1 k) (Hmem j Hj Hm2). }
  rewrite LeanNum_S k Hk.
  rewrite Lean_List_range_loop_eq_2 acc Hacc (LeanNum k) HkIn.
  exact IH (Lean_List_cons_node Lean_Nat (LeanNum k) acc) Hnew Hpw2 Hmem2. }
exact nat_ind (fun k => forall acc :e Lean_List Lean_Nat,
    LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) acc ->
    (forall j, nat_p j -> LeanListMem Lean_Nat (LeanNum j) acc -> k c= j) ->
    LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) (Lean_List_range_loop (LeanNum k) acc))
  Hbase Hstep.
Qed.

Theorem LeanListRange_nodup : forall n :e Lean_Nat,
  LeanListPairwise Lean_Nat (LeanListNe Lean_Nat) (Lean_List_range n).
let n. assume Hn: n :e Lean_Nat.
apply Lean_Nat_num n Hn. let k. assume Hk: nat_p k /\ n = LeanNum k.
apply Hk. assume Hkn: nat_p k. assume E: n = LeanNum k.
rewrite E. rewrite Lean_List_range_unfold (LeanNum k).
exact LeanListRange_loop_nodup k Hkn (Lean_List_nil_node Lean_Nat) (Lean_List_nil_typed Lean_Nat)
  (LeanListPairwise_nil Lean_Nat (LeanListNe Lean_Nat))
  (fun j Hj Hm => FalseE (LeanListMem_nil Lean_Nat (LeanNum j) Hm) (k c= j)).
Qed.

(** Filtering keeps members and pairwise relations. **)
Theorem LeanListFilter_mem : forall A, forall p :e (Pi_ ux :e A, Lean_Bool), forall xs :e Lean_List A,
  forall b, LeanListMem A b (Lean_List_filter A p xs) -> LeanListMem A b xs.
let A p. assume Hp: p :e (Pi_ ux :e A, Lean_Bool).
claim Hpx: forall x :e A, p x :e Lean_Bool.
{ let x. assume Hx: x :e A. exact ap_Pi A (fun _ => Lean_Bool) p x Hp Hx. }
claim Hnil: forall b, LeanListMem A b (Lean_List_filter A p (Lean_List_nil_node A)) -> LeanListMem A b (Lean_List_nil_node A).
{ let b. rewrite LeanListFilter_nil A p. assume H: LeanListMem A b (Lean_List_nil_node A). exact H. }
claim Hcons: forall x :e A, forall xs :e Lean_List A,
  (forall b, LeanListMem A b (Lean_List_filter A p xs) -> LeanListMem A b xs) ->
  forall b, LeanListMem A b (Lean_List_filter A p (Lean_List_cons_node A x xs)) -> LeanListMem A b (Lean_List_cons_node A x xs).
{ let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
  assume IH: forall b, LeanListMem A b (Lean_List_filter A p xs) -> LeanListMem A b xs.
  let b.
  apply LeanBool_cases (p x) (Hpx x Hx).
  - assume Hf: p x = Lean_Bool_false_node.
    rewrite LeanListFilter_cons_false A p Hp x Hx xs Hxs Hf.
    assume H: LeanListMem A b (Lean_List_filter A p xs).
    exact LeanListMem_tail A b x Hx xs Hxs (IH b H).
  - assume Ht: p x = Lean_Bool_true_node.
    rewrite LeanListFilter_cons_true A p Hp x Hx xs Hxs Ht.
    assume H: LeanListMem A b (Lean_List_cons_node A x (Lean_List_filter A p xs)).
    apply LeanListMem_cons_inv A b x (Lean_List_filter A p xs) H.
    + assume Hbx: b = x. rewrite Hbx. exact LeanListMem_head A x xs Hxs.
    + assume Hm: LeanListMem A b (Lean_List_filter A p xs).
      exact LeanListMem_tail A b x Hx xs Hxs (IH b Hm). }
exact Lean_List_ind A (fun xs => forall b, LeanListMem A b (Lean_List_filter A p xs) -> LeanListMem A b xs)
  Hnil Hcons.
Qed.

Theorem LeanListFilter_pairwise : forall A, forall R :e (Pi_ a :e A, Pi_ b :e A, LeanProp),
  forall p :e (Pi_ ux :e A, Lean_Bool), forall xs :e Lean_List A,
  LeanListPairwise A R xs -> LeanListPairwise A R (Lean_List_filter A p xs).
let A R. assume HR: R :e (Pi_ a :e A, Pi_ b :e A, LeanProp). let p. assume Hp: p :e (Pi_ ux :e A, Lean_Bool).
claim Hpx: forall x :e A, p x :e Lean_Bool.
{ let x. assume Hx: x :e A. exact ap_Pi A (fun _ => Lean_Bool) p x Hp Hx. }
claim Hnil: LeanListPairwise A R (Lean_List_nil_node A) -> LeanListPairwise A R (Lean_List_filter A p (Lean_List_nil_node A)).
{ rewrite LeanListFilter_nil A p. assume H: LeanListPairwise A R (Lean_List_nil_node A). exact H. }
claim Hcons: forall x :e A, forall xs :e Lean_List A,
  (LeanListPairwise A R xs -> LeanListPairwise A R (Lean_List_filter A p xs)) ->
  LeanListPairwise A R (Lean_List_cons_node A x xs) ->
  LeanListPairwise A R (Lean_List_filter A p (Lean_List_cons_node A x xs)).
{ let x. assume Hx: x :e A. let xs. assume Hxs: xs :e Lean_List A.
  assume IH: LeanListPairwise A R xs -> LeanListPairwise A R (Lean_List_filter A p xs).
  assume Hpw: LeanListPairwise A R (Lean_List_cons_node A x xs).
  apply LeanListPairwise_cons_inv A R HR x Hx xs Hpw.
  assume Hall: forall b :e A, LeanListMem A b xs -> 0 :e R x b.
  assume Hrest: LeanListPairwise A R xs.
  apply LeanBool_cases (p x) (Hpx x Hx).
  - assume Hf: p x = Lean_Bool_false_node.
    rewrite LeanListFilter_cons_false A p Hp x Hx xs Hxs Hf. exact IH Hrest.
  - assume Ht: p x = Lean_Bool_true_node.
    rewrite LeanListFilter_cons_true A p Hp x Hx xs Hxs Ht.
    exact LeanListPairwise_cons A R x Hx (Lean_List_filter A p xs) (Lean_List_filter_In A p Hp xs Hxs)
      (fun b Hb Hm => Hall b Hb (LeanListFilter_mem A p Hp xs Hxs b Hm)) (IH Hrest). }
exact Lean_List_ind A (fun xs => LeanListPairwise A R xs -> LeanListPairwise A R (Lean_List_filter A p xs))
  Hnil Hcons.
Qed.

(** Multiset.filter at the class of a list is the class of the filtered list. **)
Theorem LeanMultisetFilter_mk : forall A, forall p :e (Pi_ ux :e A, LeanProp),
  forall inst :e (Pi_ x :e A, (Lean_Decidable (p x))), forall l :e Lean_List A,
  Lean_Multiset_filter A p inst (Lean_Multiset_ofList A l) =
  Lean_Multiset_ofList A (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) l).
let A p. assume Hp: p :e (Pi_ ux :e A, LeanProp). let inst. assume Hinst: inst :e (Pi_ x :e A, (Lean_Decidable (p x))).
let l. assume Hl: l :e Lean_List A.
claim Hq: (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) :e (Pi_ ux :e A, Lean_Bool).
{ exact lam_Pi A (fun _ => Lean_Bool) (fun b => Lean_Decidable_decide (p b) (inst b))
    (fun b Hb => Lean_Decidable_decide_In (p b) (ap_Pi A (fun _ => LeanProp) p b Hp Hb)
      (inst b) (ap_Pi A (fun x => Lean_Decidable (p x)) inst b Hinst Hb)). }
claim Hf: (fun v_l :e (Lean_List A) =>
    (Lean_Multiset_ofList A (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) v_l)))
  :e (Pi_ v_l :e (Lean_List A), Lean_Quot (Lean_List A) (LeanPermRel A)).
{ exact lam_Pi (Lean_List A) (fun _ => Lean_Quot (Lean_List A) (LeanPermRel A))
    (fun v_l => Lean_Multiset_ofList A (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) v_l))
    (fun v_l Hv => Lean_Multiset_ofList_In A
      (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) v_l)
      (Lean_List_filter_In A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) Hq v_l Hv)). }
claim Hrespect: forall xs ys :e Lean_List A, 0 :e (LeanPermRel A) xs ys ->
  (fun v_l :e (Lean_List A) =>
    (Lean_Multiset_ofList A (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) v_l))) xs =
  (fun v_l :e (Lean_List A) =>
    (Lean_Multiset_ofList A (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) v_l))) ys.
{ let xs. assume Hxs: xs :e Lean_List A. let ys. assume Hys: ys :e Lean_List A.
  assume H: 0 :e (LeanPermRel A) xs ys.
  rewrite beta (Lean_List A)
    (fun v_l => Lean_Multiset_ofList A (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) v_l)) xs Hxs.
  rewrite beta (Lean_List A)
    (fun v_l => Lean_Multiset_ofList A (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) v_l)) ys Hys.
  claim Hfx: Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) xs :e Lean_List A.
  { exact Lean_List_filter_In A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) Hq xs Hxs. }
  claim Hfy: Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) ys :e Lean_List A.
  { exact Lean_List_filter_In A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) Hq ys Hys. }
  claim Hperm: 0 :e Lean_List_Perm_Prop A
    (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) xs)
    (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) ys).
  { exact Lean_List_Perm_filter_proof A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) Hq xs Hxs ys Hys
      (LeanPermRel_perm A xs Hxs ys Hys H). }
  prove Lean_Quot_mk (Lean_List A) (LeanPermRel A)
      (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) xs) =
    Lean_Quot_mk (Lean_List A) (LeanPermRel A)
      (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) ys).
  apply Lean_Quot_mk_sound (Lean_List A) (LeanPermRel A)
    (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) xs) Hfx
    (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) ys) Hfy.
  rewrite LeanPermRel_ap A
    (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) xs) Hfx
    (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) ys) Hfy.
  exact Hperm. }
prove Lean_Quot_lift (Lean_List A) (LeanPermRel A) (Lean_Quot (Lean_List A) (LeanPermRel A))
    (fun v_l :e (Lean_List A) =>
      (Lean_Multiset_ofList A (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) v_l)))
    0 (Lean_Quot_mk (Lean_List A) (LeanPermRel A) l) =
  Lean_Multiset_ofList A (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) l).
rewrite Lean_Quot_lift_beta (Lean_List A) (LeanPermRel A) (Lean_Quot (Lean_List A) (LeanPermRel A))
  (fun v_l :e (Lean_List A) =>
    (Lean_Multiset_ofList A (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) v_l)))
  Hf Hrespect 0 l Hl.
exact beta (Lean_List A)
  (fun v_l => Lean_Multiset_ofList A (Lean_List_filter A (fun b :e A => (Lean_Decidable_decide (p b) (inst b))) v_l)) l Hl.
Qed.
