
(** Rejection control: Finset.nodup is the projection of Finset's proof field, so it is
    proved of a Finset's value.  Everything here is as that theorem requires but one thing:
    m is a multiset, not a Finset. **)
Theorem projection_off_structure : forall l, nat_p l -> forall A :e LeanUniv l, forall m :e Lean_Multiset A,
  0 :e Lean_Multiset_Nodup A (Lean_Finset_val A m).
let l. assume Hl: nat_p l. let A. assume HA: A :e LeanUniv l. let m. assume Hm: m :e Lean_Multiset A.
exact Lean_Finset_nodup_proof l Hl A HA m Hm.
Qed.
