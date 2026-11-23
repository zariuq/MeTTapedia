(** Mahlo universes and the reflection of family operators.

    A closed universe is a transitive ZF-closed set containing omega. In the
    Lean development these are exactly the levels V_mu at inaccessible mu
    (closed_omega_mem_iff), so closed universes play the role of inaccessible
    cardinals here.

    A Mahlo universe is a closed universe U such that every function on sets
    that maps U into U has a closed universe V in U closed under it. Mirrors
    isMahlo_iff_forall_closed_under: for U = V_kappa at an inaccessible kappa
    this says that kappa is a Mahlo cardinal. No Mahlo universe is
    constructed: every statement takes one as a hypothesis.

    A family operator is a pair Phi0, Phi1: the family indexed by A with
    fibres B is sent to the family indexed by Phi0 A B with fibres
    Phi1 A B. It respects the index when it depends on B only through its
    values on A. A set is closed on families under the operator when the
    operator sends every family with index and fibres in the set to a family
    with index and fibres in the set.

    The theorem: a Mahlo universe U has, for every family operator that maps
    the families of U into U and respects the index, a closed universe V in U
    closed on families under the operator. Mirrors IsMahlo.mahloReflection,
    where codes are members and a code decodes to its members.

    This file uses the closure lemmas closed_Empty, closed_setsum and
    closed_Sigma of megalodon_hotg_tower_inside_sets.mg and is checked after
    that file. **)

Definition ClosedUniverse : set -> prop :=
  fun V => TransSet V /\ ZF_closed V /\ omega :e V.

Definition MahloUniverse : set -> prop :=
  fun U => ClosedUniverse U
    /\ forall F:set -> set, (forall x :e U, F x :e U) ->
         exists V :e U, ClosedUniverse V /\ forall x :e V, F x :e V.

Definition FamilyClosed : set -> (set -> (set -> set) -> set)
    -> (set -> (set -> set) -> set -> set) -> prop :=
  fun V Phi0 Phi1 => forall A :e V, forall B:set -> set, (forall a :e A, B a :e V) ->
    Phi0 A B :e V /\ forall c :e Phi0 A B, Phi1 A B c :e V.

Definition RespectsIndex : (set -> (set -> set) -> set)
    -> (set -> (set -> set) -> set -> set) -> prop :=
  fun Phi0 Phi1 => forall A:set, forall B C:set -> set, (forall a :e A, B a = C a) ->
    Phi0 A B = Phi0 A C /\ forall c:set, Phi1 A B c = Phi1 A C c.

(** Positive example: the least closed universe around omega. **)
Theorem UnivOf_omega_ClosedUniverse : ClosedUniverse (UnivOf omega).
prove TransSet (UnivOf omega) /\ ZF_closed (UnivOf omega) /\ omega :e UnivOf omega.
apply and3I.
- exact (UnivOf_TransSet omega).
- exact (UnivOf_ZF_closed omega).
- exact (UnivOf_In omega).
Qed.

(** Negative example: the empty set is not a closed universe. **)
Theorem empty_not_ClosedUniverse : ~ClosedUniverse 0.
assume H: ClosedUniverse 0.
apply H.
assume H12: TransSet 0 /\ ZF_closed 0.
assume Homega: omega :e 0.
exact (EmptyE omega Homega).
Qed.

(** A Mahlo universe is a closed universe. **)
Theorem MahloUniverse_ClosedUniverse : forall U:set, MahloUniverse U -> ClosedUniverse U.
let U.
assume H: MahloUniverse U.
apply H.
assume HU: ClosedUniverse U.
assume HMF: forall F:set -> set, (forall x :e U, F x :e U) ->
  exists V :e U, ClosedUniverse V /\ forall x :e V, F x :e V.
exact HU.
Qed.

(** Negative example: the least closed universe around omega is not a Mahlo
    universe; it has no closed universe as a member. Mirrors
    IsLeastInaccessible.not_isMahlo. **)
Theorem UnivOf_omega_not_MahloUniverse : ~MahloUniverse (UnivOf omega).
assume HM: MahloUniverse (UnivOf omega).
apply HM.
assume HU: ClosedUniverse (UnivOf omega).
assume HMF: forall F:set -> set, (forall x :e UnivOf omega, F x :e UnivOf omega) ->
  exists V :e UnivOf omega, ClosedUniverse V /\ forall x :e V, F x :e V.
apply (HMF (fun x => x) (fun x Hx => Hx)).
let V.
assume HVex: V :e UnivOf omega /\ (ClosedUniverse V /\ forall x :e V, x :e V).
apply HVex.
assume HVU: V :e UnivOf omega.
assume HVrest: ClosedUniverse V /\ forall x :e V, x :e V.
apply HVrest.
assume HV: ClosedUniverse V.
assume Hid: forall x :e V, x :e V.
apply HV.
assume HV12: TransSet V /\ ZF_closed V.
assume HVomega: omega :e V.
apply HV12.
assume HVT: TransSet V.
assume HVZ: ZF_closed V.
apply (In_irref V).
exact (UnivOf_Min omega V HVomega HVT HVZ V HVU).
Qed.

(** Vacuous control: the empty set is closed on families under every
    operator. Closure on families alone has no content; the reflected set
    must be a closed universe. **)
Theorem empty_FamilyClosed : forall Phi0:set -> (set -> set) -> set,
  forall Phi1:set -> (set -> set) -> set -> set, FamilyClosed 0 Phi0 Phi1.
let Phi0 Phi1 A.
assume HA: A :e 0.
apply (EmptyE A HA).
Qed.

(** The image of a family under the operator, as one set: its index and its
    fibres. **)
Definition familyOutput : (set -> (set -> set) -> set)
    -> (set -> (set -> set) -> set -> set) -> set -> (set -> set) -> set :=
  fun Phi0 Phi1 A B => {Phi0 A B} :\/: {Phi1 A B c|c :e Phi0 A B}.

(** The family coded by a set x has index x 0 and fibre x 1 a at a. **)
Definition codeGood : set -> set -> prop :=
  fun U x => x 0 :e U /\ forall a :e x 0, x 1 a :e U.

(** The function on sets whose closure points reflect the family operator. **)
Definition reflector : set -> (set -> (set -> set) -> set)
    -> (set -> (set -> set) -> set -> set) -> set -> set :=
  fun U Phi0 Phi1 x =>
    if codeGood U x then familyOutput Phi0 Phi1 (x 0) (fun a => x 1 a) else 0.

Theorem familyOutput_closed : forall V:set, ZF_closed V ->
  forall Phi0:set -> (set -> set) -> set, forall Phi1:set -> (set -> set) -> set -> set,
  forall A:set, forall B:set -> set,
  Phi0 A B :e V -> (forall c :e Phi0 A B, Phi1 A B c :e V) ->
  familyOutput Phi0 Phi1 A B :e V.
let V.
assume HVZ: ZF_closed V.
let Phi0 Phi1 A B.
assume H0: Phi0 A B :e V.
assume H1: forall c :e Phi0 A B, Phi1 A B c :e V.
prove {Phi0 A B} :\/: {Phi1 A B c|c :e Phi0 A B} :e V.
apply (ZF_binunion_closed V HVZ).
- exact (ZF_Sing_closed V HVZ (Phi0 A B) H0).
- exact (ZF_Repl_closed V HVZ (Phi0 A B) H0 (Phi1 A B) H1).
Qed.

Theorem familyOutput_members : forall V:set, TransSet V ->
  forall Phi0:set -> (set -> set) -> set, forall Phi1:set -> (set -> set) -> set -> set,
  forall A:set, forall B:set -> set, familyOutput Phi0 Phi1 A B :e V ->
  Phi0 A B :e V /\ forall c :e Phi0 A B, Phi1 A B c :e V.
let V.
assume HVT: TransSet V.
let Phi0 Phi1 A B.
assume HOut: familyOutput Phi0 Phi1 A B :e V.
apply andI.
- prove Phi0 A B :e V.
  exact (HVT (familyOutput Phi0 Phi1 A B) HOut (Phi0 A B)
    (binunionI1 {Phi0 A B} {Phi1 A B c|c :e Phi0 A B} (Phi0 A B) (SingI (Phi0 A B)))).
- let c.
  assume Hc: c :e Phi0 A B.
  prove Phi1 A B c :e V.
  exact (HVT (familyOutput Phi0 Phi1 A B) HOut (Phi1 A B c)
    (binunionI2 {Phi0 A B} {Phi1 A B c|c :e Phi0 A B} (Phi1 A B c)
      (ReplI (Phi0 A B) (Phi1 A B) c Hc))).
Qed.

Theorem reflector_maps : forall U:set, ClosedUniverse U ->
  forall Phi0:set -> (set -> set) -> set, forall Phi1:set -> (set -> set) -> set -> set,
  FamilyClosed U Phi0 Phi1 -> forall x :e U, reflector U Phi0 Phi1 x :e U.
let U.
assume HU: ClosedUniverse U.
let Phi0 Phi1.
assume HPhi: FamilyClosed U Phi0 Phi1.
let x.
assume Hx: x :e U.
apply HU.
assume HU12: TransSet U /\ ZF_closed U.
assume HUomega: omega :e U.
apply HU12.
assume HUT: TransSet U.
assume HUZ: ZF_closed U.
apply (xm (codeGood U x)).
- assume HG: codeGood U x.
  prove (if codeGood U x then familyOutput Phi0 Phi1 (x 0) (fun a => x 1 a) else 0) :e U.
  rewrite (If_i_1 (codeGood U x) (familyOutput Phi0 Phi1 (x 0) (fun a => x 1 a)) 0 HG).
  apply HG.
  assume HG0: x 0 :e U.
  assume HG1: forall a :e x 0, x 1 a :e U.
  apply (HPhi (x 0) HG0 (fun a => x 1 a) HG1).
  assume H0: Phi0 (x 0) (fun a => x 1 a) :e U.
  assume H1: forall c :e Phi0 (x 0) (fun a => x 1 a), Phi1 (x 0) (fun a => x 1 a) c :e U.
  exact (familyOutput_closed U HUZ Phi0 Phi1 (x 0) (fun a => x 1 a) H0 H1).
- assume HG: ~codeGood U x.
  prove (if codeGood U x then familyOutput Phi0 Phi1 (x 0) (fun a => x 1 a) else 0) :e U.
  rewrite (If_i_0 (codeGood U x) (familyOutput Phi0 Phi1 (x 0) (fun a => x 1 a)) 0 HG).
  exact (closed_Empty U HUT HUZ omega HUomega).
Qed.

(** A set coding a family with index and fibres in a transitive set closed
    under the reflector sends the family into that set. **)
Theorem reflector_code_closed : forall U V:set, TransSet V -> V c= U ->
  forall Phi0:set -> (set -> set) -> set, forall Phi1:set -> (set -> set) -> set -> set,
  RespectsIndex Phi0 Phi1 ->
  forall x A:set, forall B:set -> set, x 0 = A -> (forall a :e A, x 1 a = B a) ->
  A :e V -> (forall a :e A, B a :e V) -> reflector U Phi0 Phi1 x :e V ->
  Phi0 A B :e V /\ forall c :e Phi0 A B, Phi1 A B c :e V.
let U V.
assume HVT: TransSet V.
assume HVU: V c= U.
let Phi0 Phi1.
assume HR: RespectsIndex Phi0 Phi1.
let x A B.
assume Hx0: x 0 = A.
assume HxB: forall a :e A, x 1 a = B a.
assume HA: A :e V.
assume HB: forall a :e A, B a :e V.
assume HFx: reflector U Phi0 Phi1 x :e V.
claim HG: codeGood U x.
{ prove x 0 :e U /\ forall a :e x 0, x 1 a :e U.
  rewrite Hx0.
  apply andI.
  - exact (HVU A HA).
  - let a.
    assume Ha: a :e A.
    rewrite (HxB a Ha).
    exact (HVU (B a) (HB a Ha)). }
claim HOut: familyOutput Phi0 Phi1 (x 0) (fun a => x 1 a) :e V.
{ rewrite <- (If_i_1 (codeGood U x) (familyOutput Phi0 Phi1 (x 0) (fun a => x 1 a)) 0 HG).
  exact HFx. }
apply (HR A (fun a => x 1 a) B HxB).
assume HR0: Phi0 A (fun a => x 1 a) = Phi0 A B.
assume HR1: forall c:set, Phi1 A (fun a => x 1 a) c = Phi1 A B c.
claim HRepl: {Phi1 A (fun a => x 1 a) c|c :e Phi0 A B} = {Phi1 A B c|c :e Phi0 A B}.
{ apply (ReplEq_ext (Phi0 A B) (Phi1 A (fun a => x 1 a)) (Phi1 A B)).
  let c.
  assume Hc: c :e Phi0 A B.
  exact (HR1 c). }
claim HOutAB: familyOutput Phi0 Phi1 A B :e V.
{ prove {Phi0 A B} :\/: {Phi1 A B c|c :e Phi0 A B} :e V.
  rewrite <- HRepl.
  rewrite <- HR0.
  rewrite <- Hx0.
  exact HOut. }
exact (familyOutput_members V HVT Phi0 Phi1 A B HOutAB).
Qed.

(** A closed universe closed under the reflector is closed on families under
    the operator. **)
Theorem reflector_closed_FamilyClosed : forall U V:set, ClosedUniverse V -> V c= U ->
  forall Phi0:set -> (set -> set) -> set, forall Phi1:set -> (set -> set) -> set -> set,
  RespectsIndex Phi0 Phi1 ->
  (forall x :e V, reflector U Phi0 Phi1 x :e V) ->
  FamilyClosed V Phi0 Phi1.
let U V.
assume HV: ClosedUniverse V.
assume HVU: V c= U.
let Phi0 Phi1.
assume HR: RespectsIndex Phi0 Phi1.
assume HF: forall x :e V, reflector U Phi0 Phi1 x :e V.
apply HV.
assume HV12: TransSet V /\ ZF_closed V.
assume HVomega: omega :e V.
apply HV12.
assume HVT: TransSet V.
assume HVZ: ZF_closed V.
let A.
assume HA: A :e V.
let B.
assume HB: forall a :e A, B a :e V.
claim HS: (fun a :e A => B a) :e V.
{ exact (closed_Sigma V HVT HVZ A HA B HB). }
claim Hx: (A :+: (fun a :e A => B a)) :e V.
{ exact (closed_setsum V HVT HVZ A HA (fun a :e A => B a) HS). }
claim HxB: forall a :e A, (A :+: (fun a :e A => B a)) 1 a = B a.
{ let a.
  assume Ha: a :e A.
  rewrite (pair_ap_1 A (fun a :e A => B a)).
  exact (beta A B a Ha). }
exact (reflector_code_closed U V HVT HVU Phi0 Phi1 HR (A :+: (fun a :e A => B a)) A B
  (pair_ap_0 A (fun a :e A => B a)) HxB HA HB (HF (A :+: (fun a :e A => B a)) Hx)).
Qed.

(** Mahlo reflection. Mirrors IsMahlo.mahloReflection. **)
Theorem MahloUniverse_reflects_family_operators : forall U:set, MahloUniverse U ->
  forall Phi0:set -> (set -> set) -> set, forall Phi1:set -> (set -> set) -> set -> set,
  FamilyClosed U Phi0 Phi1 -> RespectsIndex Phi0 Phi1 ->
  exists V :e U, ClosedUniverse V /\ FamilyClosed V Phi0 Phi1.
let U.
assume HM: MahloUniverse U.
let Phi0 Phi1.
assume HPhi: FamilyClosed U Phi0 Phi1.
assume HR: RespectsIndex Phi0 Phi1.
apply HM.
assume HU: ClosedUniverse U.
assume HMF: forall F:set -> set, (forall x :e U, F x :e U) ->
  exists V :e U, ClosedUniverse V /\ forall x :e V, F x :e V.
apply HU.
assume HU12: TransSet U /\ ZF_closed U.
assume HUomega: omega :e U.
apply HU12.
assume HUT: TransSet U.
assume HUZ: ZF_closed U.
apply (HMF (reflector U Phi0 Phi1) (reflector_maps U HU Phi0 Phi1 HPhi)).
let V.
assume HVex: V :e U /\ (ClosedUniverse V /\ forall x :e V, reflector U Phi0 Phi1 x :e V).
apply HVex.
assume HVU: V :e U.
assume HVrest: ClosedUniverse V /\ forall x :e V, reflector U Phi0 Phi1 x :e V.
apply HVrest.
assume HV: ClosedUniverse V.
assume HVF: forall x :e V, reflector U Phi0 Phi1 x :e V.
witness V.
apply andI.
- exact HVU.
- apply andI.
  + exact HV.
  + exact (reflector_closed_FamilyClosed U V HV (HUT V HVU) Phi0 Phi1 HR HVF).
Qed.
