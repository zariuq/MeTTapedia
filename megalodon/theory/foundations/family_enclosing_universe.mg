(** Family enclosure in the Egal/HOTG universe interface.

    A dependent family is represented extensionally by a base set A and a
    meta-level family B : set -> set. The seed contains A and the replacement
    image of B over A. UnivOf then provides the least transitive ZF-closed
    universe selected by the existing HOTG interface. **)

Definition familyImage : set -> (set -> set) -> set :=
  fun A B => {B x|x :e A}.

Definition familySeed : set -> (set -> set) -> set :=
  fun A B => {A,familyImage A B}.

Definition familyUniverse : set -> (set -> set) -> set :=
  fun A B => UnivOf (familySeed A B).

Theorem family_seed_in_universe : forall A:set, forall B:set->set,
  familySeed A B :e familyUniverse A B.
let A B.
exact (UnivOf_In (familySeed A B)).
Qed.

Theorem family_base_in_universe : forall A:set, forall B:set->set,
  A :e familyUniverse A B.
let A B.
claim Hseed: familySeed A B :e familyUniverse A B.
{ exact (family_seed_in_universe A B). }
claim Htrans: TransSet (familyUniverse A B).
{ exact (UnivOf_TransSet (familySeed A B)). }
apply Htrans (familySeed A B) Hseed A.
exact (UPairI1 A (familyImage A B)).
Qed.

Theorem family_image_in_universe : forall A:set, forall B:set->set,
  familyImage A B :e familyUniverse A B.
let A B.
claim Hseed: familySeed A B :e familyUniverse A B.
{ exact (family_seed_in_universe A B). }
claim Htrans: TransSet (familyUniverse A B).
{ exact (UnivOf_TransSet (familySeed A B)). }
apply Htrans (familySeed A B) Hseed (familyImage A B).
exact (UPairI2 A (familyImage A B)).
Qed.

Theorem family_fibre_in_universe : forall A:set, forall B:set->set,
  forall a :e A, B a :e familyUniverse A B.
let A B a.
assume Ha: a :e A.
claim Himage: familyImage A B :e familyUniverse A B.
{ exact (family_image_in_universe A B). }
claim Htrans: TransSet (familyUniverse A B).
{ exact (UnivOf_TransSet (familySeed A B)). }
apply Htrans (familyImage A B) Himage (B a).
exact (ReplI A B a Ha).
Qed.

Theorem family_universe_transitive : forall A:set, forall B:set->set,
  TransSet (familyUniverse A B).
let A B.
exact (UnivOf_TransSet (familySeed A B)).
Qed.

Theorem family_universe_zf_closed : forall A:set, forall B:set->set,
  ZF_closed (familyUniverse A B).
let A B.
exact (UnivOf_ZF_closed (familySeed A B)).
Qed.

Theorem family_universe_contract : forall A:set, forall B:set->set,
  A :e familyUniverse A B
  /\ (forall a :e A, B a :e familyUniverse A B)
  /\ TransSet (familyUniverse A B)
  /\ ZF_closed (familyUniverse A B).
let A B.
apply and4I.
- exact (family_base_in_universe A B).
- exact (family_fibre_in_universe A B).
- exact (family_universe_transitive A B).
- exact (family_universe_zf_closed A B).
Qed.

Theorem family_universe_minimal : forall A U:set, forall B:set->set,
  A :e U
  -> (forall a :e A, B a :e U)
  -> TransSet U
  -> ZF_closed U
  -> familyUniverse A B c= U.
let A U B.
assume Hbase: A :e U.
assume Hfibres: forall a :e A, B a :e U.
assume Htrans: TransSet U.
assume Hclosed: ZF_closed U.
claim Himage: familyImage A B :e U.
{
  apply ZF_Repl_closed U Hclosed A Hbase B.
  exact Hfibres.
}
claim Hseed: familySeed A B :e U.
{
  exact (ZF_UPair_closed U Hclosed A Hbase (familyImage A B)
    Himage).
}
exact (UnivOf_Min (familySeed A B) U Hseed Htrans Hclosed).
Qed.

(** Negative control: enclosure does not make the selected universe a member
    of itself. A later universe is still required to internalize this one. **)
Theorem family_universe_not_self_member : forall A:set, forall B:set->set,
  familyUniverse A B /:e familyUniverse A B.
let A B.
exact (In_irref (familyUniverse A B)).
Qed.
